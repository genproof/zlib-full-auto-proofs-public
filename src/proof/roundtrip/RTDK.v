(* Round-trip part RT-D: the invariant K of kfacts and one statement per field of kfacts.

   [Krt] = the deflate laws' invariant [Iapi W3 hinv] (copied theory RTDLT*.v: safety, counters, header bytes,
   check value) /\ [KF] (functional):
   - before the header is complete (status INIT / GZIP / EXTRA .. HCRC): no block, nothing in the bit buffer;
   - BUSY: all the bits produced are the header's bytes then Format's encoding of the blocks BS (none final);
   - FINISH: BS ends with the final block and expands to the data; either the trailer is not put yet (wrap as
     given) and the bits are the header then deflate_bits BS, or (wrap > 0, negated) the bytes produced and
     pending are the whole stream with its trailer. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Export Zlib.proof.roundtrip.RTDLTApiDefs Zlib.proof.roundtrip.RTDLTHdrKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The wrapper in Format's terms *)

(* the header deflate writes, as RTFinal.dfinal states it *)
Definition khdr (dict : list Z) (wrap : Z) (s : dstate) (HDR : list Z) : Prop :=
  if wrap =? 0 then HDR = []
  else if wrap =? 1 then
    exists flg, zflg_ok (d_w_bits s) (negb (match dict with [] => true | _ => false end)) flg /\
      HDR = [zcmf (d_w_bits s); flg] ++
            match dict with [] => [] | _ => F.be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 end
  else exists xfl, (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\ HDR = F.gz_bytes (fhdr_of (d_gzhead s) xfl).

(* the trailer: the big-endian Adler-32 of the data (zlib), its little-endian CRC-32 and length (gzip) *)
Definition ftrailer (wrap : Z) (D : list Z) : list Z :=
  if wrap =? 1 then F.be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4
  else if wrap =? 2 then
    F.le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 D) 4 ++ F.le_bytes (Zlength D mod 2 ^ 32) 4
  else [].

(** ** The invariant *)
Definition KF : rinv := fun dict wrap D O fin s tin tout adler =>
  (wrap <> 2 -> d_gzhead s = None) /\
  exists BS syms,
    kcore dict D BS syms s /\
    ((d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE /\ BS = [] /\ d_bi_valid s = 0) \/
     (d_status s = BUSY_STATE /\
      exists HDR, khdr dict wrap s HDR /\ allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false) \/
     (d_status s = FINISH_STATE /\ BS <> [] /\ F.data dict BS = D /\
      exists HDR, khdr dict wrap s HDR /\
        ((d_wrap s = wrap /\ allbits O s = F.bytes_bits HDR ++ enc_out 0 BS true) \/
         (0 < wrap /\ d_wrap s = - wrap /\ d_bi_valid s = 0 /\
          O ++ pend s = HDR ++ F.deflate_bytes BS ++ ftrailer wrap D)))).

Definition Krt : rinv := fun dict wrap D O fin s tin tout adler =>
  Iapi W3 hinv dict wrap D O fin s tin tout adler /\ KF dict wrap D O fin s tin tout adler.

(** ** The fields of kfacts for a given K (verbatim from RTDIface.kfacts) *)
Definition kf_init_stmt (K : rinv) : Prop :=
  forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ d_gzhead s = None /\
    K [] (rwrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z').

Definition kf_tune_stmt (K : rinv) : Prop :=
  forall wrap s tin tout adler good lazy nice chain z s' z' code,
    K [] wrap [] [] None s tin tout adler -> rs32 good -> rs32 lazy -> rs32 nice -> rs32 chain ->
    c_deflateTune s z good lazy nice chain = Some (s', z', code) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\ K [] wrap [] [] None s' tin tout adler.

Definition kf_dict_stmt (K : rinv) : Prop :=
  forall wrap s tin tout adler d ain aout msg s' z' code,
    K [] wrap [] [] None s tin tout adler -> rbytes d -> Zlength d <= 32768 ->
    0 <= ain <= 4294967295 -> 0 <= aout <= 4294967295 ->
    c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) ->
    (code = Z_OK \/ code = Z_STREAM_ERROR) -> (code = Z_STREAM_ERROR <-> wrap = 2) ->
    d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\
    K (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z').

Definition kf_head_stmt (K : rinv) : Prop :=
  forall dict s tin tout adler h,
    K dict 2 [] [] None s tin tout adler -> rhdr_ok h -> K dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler.

Definition kf_deflate_stmt (K : rinv) : Prop :=
  forall dict wrap D O fin s tin tout adler inb aout flush msg s' z' code,
    K dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength D + Zlength inb <= 1048576 ->
    0 <= aout <= 2097152 -> Zlength O + aout <= 4194304 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) ->
    d_gzhead s' = d_gzhead s -> rcall_ok inb aout tin tout z' ->
    (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) ->
    (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) ->
    (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout) ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := D ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict wrap (d_w_bits s) (d_gzhead s) D' O'
     else K dict wrap D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z')).

Definition kf_params_stmt (K : rinv) : Prop :=
  forall dict wrap D O s tin tout adler inb aout level strategy msg s' z' code,
    K dict wrap D O None s tin tout adler -> rs32 level -> rs32 strategy ->
    rbytes inb -> Zlength D + Zlength inb <= 1048576 -> 0 <= aout <= 2097152 -> Zlength O + aout <= 4194304 ->
    c_deflateParams s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) level strategy = Some (s', z', code) ->
    d_gzhead s' = d_gzhead s -> rcall_ok inb aout tin tout z' ->
    (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_ERROR) ->
    (code = Z_STREAM_ERROR <-> ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4)) ->
    d_w_bits s' = d_w_bits s /\
    K dict wrap (D ++ sublist 0 (Zlength inb - z_avail_in z') inb) (O ++ z_out z') None
      s' (z_total_in z') (z_total_out z') (z_adler z').

Lemma kfacts_of : forall K,
  kf_init_stmt K -> kf_tune_stmt K -> kf_dict_stmt K -> kf_head_stmt K -> kf_deflate_stmt K -> kf_params_stmt K ->
  kfacts K.
Proof. intros K A B C D E G. constructor; assumption. Qed.

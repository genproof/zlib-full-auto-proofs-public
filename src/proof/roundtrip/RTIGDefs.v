(* Round-trip part RT-I: the decode theory (rfc1951/DecodeDefs.v) GENERALIZED for
   deflate_roundtrip's gzip streams, which DecodeDefs does not cover: any gzip header (extra field, name, comment,
   header CRC: dctx_ok's gz_simple conjunct is True here) and a gz_header given to inflateGetHeader (glob_ok's
   `i_head s = false` is the trivial `i_head s = i_head s` here: no mode after the header reads state->head).
   The theory is entered at a loop head after the header (the header passes are proved directly, RTIGz*.v), so
   at_mode's header branches (HEAD, FLAGS, TIME, OS) are False here.  Everything else is DecodeDefs' (re-exported),
   and the shapes are DecodeDefs' (same conjunctions and branches), so that the decode theory's proofs (rfc1951/Dec*.v)
   carry over verbatim (copies RTIGDec*.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

Definition dctx_ok (G: dctx) : Prop :=
  stream_ok (dc_w G) (dc_wb G) (dc_hist G) (dc_bs G) /\ accepts G /\
  (forall h, dc_w G = WGzip h -> True) /\
  (forall wb fl did, dc_w G = WZlib wb fl did ->
     did = None \/ did = Some (Zlib.proof.adler32.Model.ref_adler32 1 (dc_hist G))) /\
  slen G <= Zlength (dc_src G) /\ Zlength (dc_src G) <= 2 ^ 31 - 1 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).


Definition at_mode (G: dctx) (s: istate) (c hold bits: Z) (out: list Z) : Prop :=
  let md := i_mode s in let q := 8 * c - bits in
  hold_ok G c hold bits /\
  ((md = HEAD /\ False) \/
   ((md = FLAGS \/ md = TIME \/ md = OS) /\ False) \/
   ((md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO) /\ at_type G s q bits out) \/
   (md = STORED /\ at_stored G s q bits out) \/
   ((md = COPY_ \/ md = COPY) /\ at_copy G s q bits out) \/
   (md = TABLE /\ at_table G s q bits out) \/
   (md = LENLENS /\ at_lenlens G s q bits out) \/
   (md = CODELENS /\ at_codelens G s q bits out) \/
   ((md = LEN_ \/ md = LEN) /\ at_len G s q bits out) \/
   (md = LENEXT /\ at_lenext G s q bits out) \/
   (md = DIST /\ at_dist G s q bits out) \/
   (md = DISTEXT /\ at_distext G s q bits out) \/
   (md = MATCH /\ at_match G s q bits out) \/
   (md = LIT /\ at_lit G s q bits out) \/
   (md = CHECK /\ at_check G s q bits out) \/
   (md = LENGTH /\ at_length G s q bits out) \/
   (md = DONE /\ at_done G s q bits out)).


(* the wrap: that of inflateInit2 with dc_iw, or (a gzip stream read with inflateInit2(32), whose context records
   dc_iw = 32 + wb) the same wrapper with bit 3 set, the window size coming from the header (patch F8) *)
Definition glob_ok (G: dctx) (s: istate) : Prop :=
  (exists wb0, (init_wrap_wb (dc_iw G) = Some (i_wrap s, wb0) \/
               exists wrap, reset2_wb (dc_iw G) = Some (wrap, wb0) /\ wrap <> 0 /\ i_wrap s = Z.lor wrap 8) /\
     (i_mode s = HEAD -> i_wbits s = wb0)) /\
  i_head s = i_head s /\
  (i_mode s <> HEAD -> dc_wb G <= i_wbits s <= 15) /\
  (wrapped G = true -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
     i_flags s = match dc_w G with WGzip h => 8 + 256 * gz_flg h | _ => 0 end).

(* what the trailer reads of the wrap: 0 for raw only, and bit 2 (check the trailer) as reset2_wb's wrap *)
Lemma rtig_wrap_bits G s wb0 :
  (init_wrap_wb (dc_iw G) = Some (i_wrap s, wb0) \/
   exists wrap, reset2_wb (dc_iw G) = Some (wrap, wb0) /\ wrap <> 0 /\ i_wrap s = Z.lor wrap 8) ->
  exists wrap, reset2_wb (dc_iw G) = Some (wrap, wb0) /\ (wrap = 0 -> i_wrap s = 0) /\
    Z.land (i_wrap s) 4 = Z.land wrap 4.
Proof.
  intros [R0|(wrap & R & Nz & ->)].
  - destruct (init_wrap_wb_bits _ _ _ R0) as (wrap & R & _ & _ & E4 & E0). exists wrap.
    split; [exact R|]. split; [intros X; apply E0; exact X|exact E4].
  - exists wrap. split; [exact R|]. split; [intros X; contradiction|].
    destruct (reset2_wb_cases _ _ _ R) as [(X & _)|(A & _)]; [contradiction|].
    assert (C: wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia. destruct C as [-> | [-> | ->]]; reflexivity.
Qed.


Record Kd (G: dctx) (pos: Z) (inp ob: list Z) (m: mst) : Prop := {
  kd_inp : m_inp m = inp;
  kd_at : at_mode G (m_s m) (pos + m_nx m) (m_hold m) (m_bits m) (ob ++ m_ow m);
  kd_glob : glob_ok G (m_s m);
  kd_win : m_mode m < CHECK -> win_ok G (m_s m) ob;
  kd_chk : chk_ok G (m_s m) ob (m_ow m);
  (* tout: the data before the call; after CHECK, with the call's output (CHECK counted it, out = left) *)
  kd_tout : m_tout m = Zlength (produced G (if after_check G (m_mode m) then ob ++ m_ow m else ob)) mod 2 ^ 64;
  kd_out : if after_check G (m_mode m) then m_out m = m_left m else m_out m = m_aout m;
  kd_ret : m_ret m = (if (m_mode m =? DONE) && (m_leave m =? 1) then Z_STREAM_END else Z_OK) }.

(* between calls: the state s, total_out tout, pos bytes consumed, out the output (history included) *)
Definition dinv (G: dctx) (pos: Z) (out: list Z) (s: istate) (tout: Z) : Prop :=
  at_mode G s pos (i_hold s) (i_bits s) out /\ glob_ok G s /\
  (i_mode s < CHECK -> win_ok G s out) /\ chk_ok G s out [] /\
  tout = Zlength (produced G out) mod 2 ^ 64.


(* what one pass of the switch gives from a loop head: no return (no Z_NEED_DICT, Z_MEM_ERROR, error), the
   invariant, the output only grows, and the reason when it leaves *)
Definition dstep_post (G: dctx) (pos: Z) (inp ob: list Z) (flush: Z) (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kd G pos inp ob m' /\ (exists d, m_ow m' = m_ow m ++ d) /\
               (m_leave m' = 1 -> leave_why G pos inp ob flush m')
  | IRet _ _ => False
  end.

Definition group_ok (P: Z -> Prop) : Prop :=
  forall G pos inp ob flush m,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> P (m_mode m) ->
    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).


Definition dfast_stmt : Prop :=
  forall G pos inp ob m,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    let m' := fast lenfix_list distfix_list (restore m) in
    let m' := if m_mode m' =? Zlib.proof.inflate.Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m' in
    Kd G pos inp ob m' /\ m_leave m' = 0 /\ (exists d, m_ow m' = m_ow m ++ d) /\
    (m_mode m' = LEN \/ m_mode m' = Zlib.proof.inflate.Model.TYPE).


Record dkit_stmt : Prop := {
  (* PULLBYTE *)
  dk_pull : forall G c hold bits, hold_ok G c hold bits -> c < Zlength (dc_src G) -> bits + 8 <= 64 ->
    bytes_ok (dc_src G) ->
    hold_ok G (c + 1) ((hold + Znth c (dc_src G) * 2 ^ bits) mod 2 ^ 64) (bits + 8);
  (* BITS(n) *)
  dk_bitsn : forall G c hold bits n, hold_ok G c hold bits -> 0 <= n <= bits ->
    hold mod 2 ^ n = bval (sublist (8 * c - bits) (8 * c - bits + n) (sbits G));
  (* DROPBITS(n) *)
  dk_drop : forall G c hold bits n, hold_ok G c hold bits -> 0 <= n <= bits ->
    hold_ok G c (Z.shiftr hold n) (bits - n);
  (* the hold is below 2^bits *)
  dk_hold_lt : forall G c hold bits, hold_ok G c hold bits -> bytes_ok (dc_src G) -> 0 <= hold < 2 ^ bits;
  (* the layout of the input *)
  dk_hdr : forall G, dctx_ok G -> sublist 0 (D0 G) (sbits G) = bytes_bits (hdr_bytes (dc_w G));
  dk_deflate : forall G, dctx_ok G -> sublist (D0 G) (endpos G) (sbits G) = deflate_bits (dc_bs G);
  dk_blk : forall G k, dctx_ok G -> 0 <= k < nblk G ->
    bpos G (k + 1) = bpos G k + Zlength (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) /\
    sublist (bpos G k) (bpos G (k + 1)) (sbits G) = enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k);
  dk_bpos0 : forall G, bpos G 0 = D0 G;
  dk_end : forall G, dctx_ok G -> endpos G = bpos G (nblk G) + pad8 (bpos G (nblk G)) /\
    sublist (bpos G (nblk G)) (endpos G) (sbits G) = zeros (pad8 (bpos G (nblk G)));
  dk_D0 : forall G, D0 G mod 8 = 0;
  dk_slen : forall G, dctx_ok G -> endpos G + 8 * trl_len (dc_w G) = 8 * slen G;
  (* the trailer: zlib the big-endian Adler-32 of the data, gzip the CRC-32 and the length; the end *)
  dk_trailer : forall G, dctx_ok G ->
    endpos G mod 8 = 0 /\
    sublist (endpos G / 8) (slen G) (dc_src G) =
      match dc_w G with
      | WRaw => []
      | WZlib _ _ _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 (produced G (full G))) 4
      | WGzip _ => le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (produced G (full G))) 4 ++
                   le_bytes (Zlength (produced G (full G)) mod 2 ^ 32) 4
      end;
  (* the output block by block *)
  dk_outk : forall G k, 0 <= k < nblk G -> outk G (k + 1) = block_data (outk G k) (blk G k);
  dk_outk0 : forall G, outk G 0 = dc_hist G;
  dk_full : forall G, outk G (nblk G) = full G;
  dk_full_len : forall G k, 0 <= k <= nblk G -> Zlength (outk G k) <= Zlength (full G) /\
    exists rest, full G = outk G k ++ rest;
  dk_produced : forall G d, produced G (dc_hist G ++ d) = d
}.


(* ---------------------------------------------------------------------------------------------- *)
(* THE statement of the generalized theory: the rest of an inflate() call from a loop head (Model2.loop2, then
   the return or inf_leave), as Decode.decode_call_stmt from dinv but from any loop head satisfying Kd: it returns
   Z_MEM_ERROR, or Z_OK / Z_BUF_ERROR / Z_STREAM_END with the output the next bytes of the data, all of it and
   exactly the stream consumed at Z_STREAM_END, and a reason (no input, no output space, Z_BLOCK / Z_TREES)
   otherwise.  ob: the output before the call (history included), m_ow: the output of the call so far. *)
Definition rtig_loop_stmt : Prop :=
  forall G pos inp ob flush m o res,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 ->
    (exists d0, ob = dc_hist G ++ d0) -> bytes_ok ob ->
    loop2 flush lenfix_list distfix_list m o ->
    match o with IRet r m' => res = Res r m' None | IBrk m' => inf_leave flush m' res end ->
    let m' := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m' <= Zlength inp /\ m_sow m' = Zlength (m_ow m') /\ m_aout m' = m_aout m /\
     (exists rest, full G = ob ++ m_ow m' ++ rest) /\
     (r_ret res = Z_STREAM_END -> ob ++ m_ow m' = full G /\ pos + m_snx m' = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m' = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m') = m_aout m /\ Zlength (ob ++ m_ow m') < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES)).

(* the parts (copies of rfc1951's, over these definitions; tabdec_stmt and stepf2_mwf3_stmt are unchanged) *)
Definition rtig_parts : Prop :=
  dkit_stmt /\
  (dkit_stmt -> tabdec_stmt -> group_ok md_type) /\
  (dkit_stmt -> tabdec_stmt -> stepf2_mwf3_stmt -> group_ok md_dec -> group_ok md_tab) /\
  (dkit_stmt -> dfast_stmt -> group_ok md_dec) /\
  (dkit_stmt -> dfast_stmt) /\
  (dkit_stmt -> group_ok md_trl) /\
  (dkit_stmt -> stepf2_mwf3_stmt -> group_ok md_type -> group_ok md_tab -> group_ok md_dec -> group_ok md_trl ->
     rtig_loop_stmt).

Lemma rtig_of_parts : rtig_parts -> tabdec_stmt -> stepf2_mwf3_stmt -> rtig_loop_stmt.
Proof.
  intros (K & Ty & Ta & De & Fa & Tr & C) T S.
  pose proof (De K (Fa K)) as DE.
  exact (C K S (Ty K T) (Ta K T S DE) DE (Tr K)).
Qed.

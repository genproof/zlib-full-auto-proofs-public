(* RT-D: interface v2.  RTDDefs.kdata is false for deflate_stored: at level 0 there are
   no symbols, but the window bytes [block_start, strstart) need not be in a block yet (deflate_stored returns
   need_more with block_start < strstart).  [kdata2]: the symbols expand up to block_start at level 0, up to
   strstart - match_available otherwise (the same as kdata at a level <> 0).  With it: kcore2, comp_fspec2, KF2,
   Krt2.  Together with RTDFix.v (flush_block_fspec2, fpend_fspec2, ins_fspec2) this is the interface the
   assembly RTDTheory uses. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix Zlib.proof.roundtrip.RTDK.
Import ListNotations.
Local Open Scope Z_scope.

Definition kdata2 (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\ kmatch s /\ wtrees s syms /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) =
    sublist 0 (off + (if d_level s =? 0 then d_block_start s else d_strstart s - d_match_available s)) H.

Definition kcore2 (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  kdata2 dict D BS syms s /\ khash s.

Definition comp_fspec2 (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z -> 0 <= d_wrap s <= 2 ->
    adler_pre (d_wrap s) (z_adler z) -> fn_of s = f ->
    Forall F.byte_ok dict -> bytes D -> kcore2 dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c s z flush = Some (s', z', bs) ->
    exists k x BS' syms',
      zstep (d_wrap s) z z' k x /\
      kcore2 dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> []).

Definition KF2 : rinv := fun dict wrap D O fin s tin tout adler =>
  (wrap <> 2 -> d_gzhead s = None) /\
  exists BS syms,
    kcore2 dict D BS syms s /\
    ((d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE /\ BS = [] /\ d_bi_valid s = 0) \/
     (d_status s = BUSY_STATE /\
      exists HDR, khdr dict wrap s HDR /\ allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false) \/
     (d_status s = FINISH_STATE /\ BS <> [] /\ F.data dict BS = D /\
      exists HDR, khdr dict wrap s HDR /\
        ((d_wrap s = wrap /\ allbits O s = F.bytes_bits HDR ++ enc_out 0 BS true) \/
         (0 < wrap /\ d_wrap s = - wrap /\ d_bi_valid s = 0 /\
          O ++ pend s = HDR ++ F.deflate_bytes BS ++ ftrailer wrap D)))).

Definition Krt2 : rinv := fun dict wrap D O fin s tin tout adler =>
  Iapi W3 hinv dict wrap D O fin s tin tout adler /\ KF2 dict wrap D O fin s tin tout adler.

(* at a level <> 0, kdata2 is kdata *)
Lemma kdata2_iff : forall dict D BS syms s, d_level s <> 0 ->
  (kdata2 dict D BS syms s <-> kdata dict D BS syms s).
Proof.
  intros dict D BS syms s Hl. unfold kdata2, kdata. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) Hl). rewrite Z.add_sub_assoc. tauto.
Qed.

Lemma kcore2_iff : forall dict D BS syms s, d_level s <> 0 ->
  (kcore2 dict D BS syms s <-> kcore dict D BS syms s).
Proof.
  intros dict D BS syms s Hl. unfold kcore2, kcore. rewrite (kdata2_iff dict D BS syms s Hl). tauto.
Qed.

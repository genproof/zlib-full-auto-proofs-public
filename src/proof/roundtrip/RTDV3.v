(* RT-D: interface v3 (on top of v2, RTDV2.v / RTDFix.v).  Two more defects:
   - kmatch: deflate_slow's lazy candidate may lie at distance MAX_DIST; after the next
     slide match_start wraps (u32) and the candidate's first byte is no longer in the window.  [kmatch3] states the
     candidate on the history H: q = the position in H of window[strstart - 1], dist = u32(strstart - 1 - match_start)
     (what deflate_slow emits).
   - KF: while the header is incomplete nothing tied O ++ pending to the header deflate writes (gzip
     XFL byte).  [KF3]: the bytes produced so far are a prefix of a header of [khdr].
   kdata3 = kdata2 with kmatch3; kcore3, comp_fspec3, KF3, Krt3. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2Lemmas.
Require Import Zlib.proof.roundtrip.RTDLTCMisc.
Import ListNotations.
Local Open Scope Z_scope.

Definition kmatch3 (H : list Z) (s : dstate) : Prop :=
  d_match_available s = 1 -> MIN_MATCH <= d_match_length s ->
  let q := Zlength H - d_lookahead s - 1 in
  let dist := u32 (d_strstart s - 1 - d_match_start s) in
  1 <= dist <= q /\ forall i, 0 <= i < d_match_length s -> Znth (q - dist + i) H = Znth (q + i) H.

Definition kdata3 (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\ kmatch3 H s /\ wtrees s syms /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) =
    sublist 0 (off + (if d_level s =? 0 then d_block_start s else d_strstart s - d_match_available s)) H.

Definition kcore3 (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  kdata3 dict D BS syms s /\ khash s.

Definition comp_fspec3 (f : Z) (c : dstate -> strm -> Z -> option (dstate * strm * bstate)) : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    W3 s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok z -> 0 <= d_wrap s <= 2 ->
    adler_pre (d_wrap s) (z_adler z) -> fn_of s = f ->
    Forall F.byte_ok dict -> bytes D -> kcore3 dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c s z flush = Some (s', z', bs) ->
    exists k x BS' syms',
      zstep (d_wrap s) z z' k x /\
      kcore3 dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> []).

Definition KF3 : rinv := fun dict wrap D O fin s tin tout adler =>
  (wrap <> 2 -> d_gzhead s = None) /\
  exists BS syms,
    kcore3 dict D BS syms s /\
    ((d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE /\ BS = [] /\ d_bi_valid s = 0 /\
      exists HDR, khdr dict wrap s HDR /\ O ++ pend s = sublist 0 (Zlength (O ++ pend s)) HDR) \/
     (d_status s = BUSY_STATE /\
      exists HDR, khdr dict wrap s HDR /\ allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false) \/
     (d_status s = FINISH_STATE /\ BS <> [] /\ F.data dict BS = D /\
      exists HDR, khdr dict wrap s HDR /\
        ((d_wrap s = wrap /\ allbits O s = F.bytes_bits HDR ++ enc_out 0 BS true) \/
         (0 < wrap /\ d_wrap s = - wrap /\ d_bi_valid s = 0 /\
          O ++ pend s = HDR ++ F.deflate_bytes BS ++ ftrailer wrap D)))).

Definition Krt3 : rinv := fun dict wrap D O fin s tin tout adler =>
  Iapi W3 hinv dict wrap D O fin s tin tout adler /\ KF3 dict wrap D O fin s tin tout adler.

(* without a pending byte, v3 = v2 *)
Lemma kdata3_iff : forall dict D BS syms s, d_match_available s = 0 ->
  (kdata3 dict D BS syms s <-> kdata2 dict D BS syms s).
Proof.
  intros dict D BS syms s Hm. unfold kdata3, kdata2, kmatch3, kmatch. rewrite Hm.
  split; intros (A & _ & R); (split; [exact A|]); (split; [intros E; discriminate E|exact R]).
Qed.

Lemma kcore3_iff : forall dict D BS syms s, d_match_available s = 0 ->
  (kcore3 dict D BS syms s <-> kcore2 dict D BS syms s).
Proof.
  intros dict D BS syms s Hm. unfold kcore3, kcore2. rewrite (kdata3_iff dict D BS syms s Hm). tauto.
Qed.

(* the laws' invariant: a pending byte only in deflate_slow *)
Lemma W3_ma : forall s, W3 s -> fn_of s <> 2 -> d_match_available s = 0.
Proof.
  intros s ((HW & _) & _) Hf.
  destruct HW as (_ & _ & _ & _ & _ & (_ & _ & Hm & _ & Hm1) & _).
  destruct Hm as [Hm|Hm]; [exact Hm|]. exfalso. apply Hf. exact (proj1 (Hm1 Hm)).
Qed.

(* a compression function other than deflate_slow: the v2 spec gives the v3 spec *)
Lemma comp_fix3 : Zlib.proof.huffman.Overlay.overlay_statement ->
  forall f c, f <> 2 ->
  (forall s z flush, prm s -> fn_of s = f -> c_compress_func s z flush = c s z flush) ->
  comp_fspec2 f c -> comp_fspec3 f c.
Proof.
  intros Hov f c Hf Hd Hc s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R.
  assert (Hm : d_match_available s = 0) by (apply W3_ma; congruence).
  apply (kcore3_iff _ _ _ _ _ Hm) in HK.
  destruct (Hc s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R)
    as (k & x & BS' & syms' & A & B & C & E).
  pose proof (W3_facts Hov) as CF.
  destruct (cf_compress W3 CF s z flush HW Ho Hq Hfl Hz Hw Ha) as (s1 & z1 & bs1 & evs & R1 & P1).
  rewrite (Hd s z flush (W3_prm s HW) Hfn), R in R1. inversion R1; subst s1 z1 bs1.
  destruct P1 as (HW' & _ & Hsp & _).
  assert (Hm' : d_match_available s' = 0).
  { apply W3_ma; [exact HW'|]. rewrite (fn_of_prm s s' Hsp). congruence. }
  exists k, x, BS', syms'. split; [exact A|]. split; [apply (kcore3_iff _ _ _ _ _ Hm'); exact B|].
  split; assumption.
Qed.

Lemma disp_stored : forall s z flush, prm s -> fn_of s = 0 -> c_compress_func s z flush = c_deflate_stored s z flush.
Proof. intros s z flush Hp E. rewrite (compress_dispatch s z flush Hp), E. reflexivity. Qed.
Lemma disp_fast : forall s z flush, prm s -> fn_of s = 1 -> c_compress_func s z flush = c_deflate_fast s z flush.
Proof. intros s z flush Hp E. rewrite (compress_dispatch s z flush Hp), E. reflexivity. Qed.
Lemma disp_slow : forall s z flush, prm s -> fn_of s = 2 -> c_compress_func s z flush = c_deflate_slow s z flush.
Proof. intros s z flush Hp E. rewrite (compress_dispatch s z flush Hp), E. reflexivity. Qed.
Lemma disp_huff : forall s z flush, prm s -> fn_of s = 3 -> c_compress_func s z flush = c_deflate_huff s z flush.
Proof. intros s z flush Hp E. rewrite (compress_dispatch s z flush Hp), E. reflexivity. Qed.
Lemma disp_rle : forall s z flush, prm s -> fn_of s = 4 -> c_compress_func s z flush = c_deflate_rle s z flush.
Proof. intros s z flush Hp E. rewrite (compress_dispatch s z flush Hp), E. reflexivity. Qed.

Lemma comp_fix3_all : Zlib.proof.huffman.Overlay.overlay_statement ->
  comp_fspec2 0 c_deflate_stored -> comp_fspec 1 c_deflate_fast -> comp_fspec 3 c_deflate_huff ->
  comp_fspec 4 c_deflate_rle ->
  comp_fspec3 0 c_deflate_stored /\ comp_fspec3 1 c_deflate_fast /\ comp_fspec3 3 c_deflate_huff /\
  comp_fspec3 4 c_deflate_rle.
Proof.
  intros Hov H0 H1 H3 H4.
  pose proof (comp_fix3 Hov 0 c_deflate_stored ltac:(discriminate) disp_stored H0) as G0.
  pose proof (comp_fix Hov 1 c_deflate_fast ltac:(discriminate) disp_fast H1) as F1.
  pose proof (comp_fix Hov 3 c_deflate_huff ltac:(discriminate) disp_huff H3) as F3.
  pose proof (comp_fix Hov 4 c_deflate_rle ltac:(discriminate) disp_rle H4) as F4.
  pose proof (comp_fix3 Hov 1 c_deflate_fast ltac:(discriminate) disp_fast F1) as G1.
  pose proof (comp_fix3 Hov 3 c_deflate_huff ltac:(discriminate) disp_huff F3) as G3.
  pose proof (comp_fix3 Hov 4 c_deflate_rle ltac:(discriminate) disp_rle F4) as G4.
  exact (conj G0 (conj G1 (conj G3 G4))).
Qed.

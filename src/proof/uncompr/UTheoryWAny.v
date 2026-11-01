(* uncompress2 for any sizes on ANY input: what UModelW.uncompressw_rel allows, whatever the source holds.

   For any source bytes (valid zlib stream or not) and any destination size, uncompress2_z's loop of inflate()
   calls ends with one of the codes zlib.h documents for uncompress: Z_OK, Z_MEM_ERROR, Z_BUF_ERROR or
   Z_DATA_ERROR; it reports at most the destination size written, and writes no more than it reports (destLen holds
   the number of bytes written, or stays the destination size when inflateInit_ fails and nothing is written), and it
   reports at most the source length read.  This is the theory of the law rj_uncompress_any (harness/rj_uncompress_any.c). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.uncompr.UModelW.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.uncompr.UTheoryWAnyKit.
Import ListNotations.
Local Open Scope Z_scope.

Definition uw_any_stmt : Prop :=
  forall (src: list Z) (cap r slen dlen: Z) (out: list Z),
    bytes_ok src -> Zlength src <= Int64.max_unsigned -> 0 <= cap <= Int64.max_unsigned ->
    uncompressw_rel src cap r slen dlen out ->
    (r = Z_OK \/ r = Z_MEM_ERROR \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\
    Zlength out <= dlen <= cap /\ 0 <= slen <= Zlength src.

Lemma uw_any : uw_any_stmt.
Proof.
  intros src cap r slen dlen out BS SL CAP REL.
  destruct REL as [(-> & -> & -> & ->) | (err & UL & -> & ->)].
  - split; [tauto|]. rewrite Zlength_nil. pose proof (Zlength_nonneg src). lia.
  - destruct (uwa_loop src cap BS _ _ _ _ _ _ _ _ UL (uwa_I_first src cap ltac:(lia))) as (C & NOK & OC & U).
    split; [exact (uwa_unc_ret err (Zlength src - slen) C NOK)|]. lia.
Qed.

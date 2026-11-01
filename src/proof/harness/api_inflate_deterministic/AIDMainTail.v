(* Law api_inflate_deterministic, main: the end of the do-while body (AIDMainKit.seg_tail): the six asserts
   (both calls returned the same code, left the same avail_in and avail_out, wrote the same bytes, and leave
   the same totals, msg, data_type and, for windowBits >= 0, adler), read += take - first.avail_in, the four
   free()s, back to the do-while's invariant.  The asserts are proved in AIDMainTailChkA.v to AIDMainTailChkC.v
   (each keeps AIDMainTailChkA.chk_pre); the rest is tail_rest. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTailChkA.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTailChkB.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainTailChkC.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
Local Open Scope logic.

(* after the asserts: read += take - first.avail_in (no overflow: pos + take <= Zlength src <=
   Int64.max_signed), the four free()s, the do-while's invariant at read = pos + (take - first.avail_in) *)
Lemma tail_rest {Espec: OracleKind} J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow:
  mid_facts J w inp src va vb pos take room ia ib oa ob ra za La zb Lb ow ->
  semax Delta_m (mid_at J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow) seg_rest
    (dpost J gv va vb w inp src).
Proof.
  intros MF.
  destruct MF as (GF & HJ & Hswa & Hswb & Hrawa & Hrawb & Hpos & Htake & Hpt & Hai & Hroom & Hao & Hra
                  & Eai & Eao & Etin & Etout & Edt & Emsg & Eadl & How & Pia & Pib & Poa & Pob).
  pose proof GF as GF0.
  destruct GF as (AF & Wok & Wr & Hsrc & Bok & Pinp & Pva & Pvb).
  unfold mid_at, seg_rest, dpost, Delta_m, POST_m. simplify_func_tycontext.
  rewrite (istreamA_unfold gv Tsh va za Vundef La). Intros. abbreviate_semax.
  forward. forward.
  rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr, add64_repr.
  sep_apply (istreamA_fold gv Tsh va za Vundef La); auto.
  set (pos' := pos + (take - zf_ai za)) in *.
  assert (Hpos': 0 <= pos' <= Zlength src) by (unfold pos'; lia).
  clearbody pos'.
  (* the four free()s *)
  forward_call (tarray tuchar take, ia, gv).
  { rewrite if_false by (destruct ia; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ia). cancel. }
  forward_call (tarray tuchar take, ib, gv).
  { rewrite if_false by (destruct ib; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ib). cancel. }
  forward_call (tarray tuchar room, oa, gv).
  { rewrite if_false by (destruct oa; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) oa). cancel. }
  forward_call (tarray tuchar room, ob, gv).
  { rewrite if_false by (destruct ob; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ob). cancel. }
  (* the do-while's invariant at read = pos' *)
  unfold dinv. Exists pos' za La zb Lb. unfold dinv_at.
  assert (dprop J w src pos' za La zb Lb) by (unfold dprop; auto).
  entailer!.
Qed.

Lemma tail_proof : tail_stmt.
Proof.
  intros Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF.
  rewrite seg_tail_eq.
  eapply semax_pre; [apply (chk_pre_of J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c1 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c2 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c3 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c4 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c5 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_seq'; [exact (chk_c6 Espec J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  eapply semax_pre; [apply (chk_post_of J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF) | ].
  exact (tail_rest J gv va vb w inp src pos take room ia ib oa ob ra za La zb Lb ow MF).
Qed.

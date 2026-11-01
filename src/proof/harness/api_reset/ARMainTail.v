(* Law api_reset, main: the end of the do-while body (ARMainKit.seg_tail): the asserts in phase 1
   (chk_stmt), read += take - used.avail_in, the four free()s, back to the do-while's invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.

(* phase 0: the asserts are skipped; fresh stays the raw struct offer() left *)
Lemma tail0 : tail0_stmt.
Proof.
  unfold tail0_stmt.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr cu cf ra za La zb MF.
  destruct MF as (GF & HJ & Hsw & Hraw & Hzb & Hpos & Htake & Hpt & Hai & Hroom & Hra & Piu & Pifr & Pou & Pofr).
  pose proof GF as GF0.
  destruct GF as (AF & Wok & Wr & Hsrc & Bok & Pinp & Pva & Pvb).
  unfold mid0_at, seg_tail, dpost, Delta_m, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_if (mid0_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr cu cf ra za La zb).
  { exfalso. match goal with H: _ |- _ => solve [discriminate H] end. }
  { forward. unfold mid0_at. entailer!. }
  (* read += take - used.avail_in: no overflow, pos + take <= Zlength src <= Int64.max_signed *)
  unfold mid0_at. rewrite istreamA_unfold. Intros.
  forward. forward.
  rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr, add64_repr.
  sep_apply (istreamA_fold gv Tsh va za Vundef La); auto.
  set (pos' := pos + (take - zf_ai za)) in *.
  assert (Hpos': 0 <= pos' <= Zlength src) by (unfold pos'; lia).
  clearbody pos'.
  (* the four free()s *)
  forward_call (tarray tuchar take, iu, gv).
  { rewrite if_false by (destruct iu; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu). cancel. }
  forward_call (tarray tuchar take, ifr, gv).
  { rewrite if_false by (destruct ifr; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr). cancel. }
  forward_call (tarray tuchar room, ou, gv).
  { rewrite if_false by (destruct ou; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) cu ou). cancel. }
  forward_call (tarray tuchar room, ofr, gv).
  { rewrite if_false by (destruct ofr; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) cf ofr). cancel. }
  (* the do-while's invariant at read = pos' (fresh is still raw: its live is irrelevant) *)
  unfold dinv. Exists pos' za La zb La. unfold dinv_at, fresh_mem. simpl Z.eqb. cbv iota.
  assert (dprop J0 J1 w src 0 pos' za La zb La) by (unfold dprop; simpl; auto).
  entailer!.
Qed.

(* phase 1: the asserts (chk_stmt, proved in ARMainChk.v) change nothing; both streams stay live *)
Lemma tail1 : chk_stmt -> tail1_stmt.
Proof.
  intros CHK. unfold tail1_stmt.
  intros Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF.
  pose proof MF as MF0.
  destruct MF as (GF & HJ & Hswa & Hswb & Hrawa & Hrawb & Hpos & Htake & Hpt & Hai & Hroom & Hao & Hra
                  & Eai & Eao & Etin & Etout & Edt & Emsg & Eadl & How & Piu & Pifr & Pou & Pofr).
  pose proof GF as GF0.
  destruct GF as (AF & Wok & Wr & Hsrc & Bok & Pinp & Pva & Pvb).
  unfold mid1_at, seg_tail, dpost, Delta_m, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_if (mid1_at J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow).
  2: { exfalso. match goal with H: ?a <> ?a |- _ => apply H; reflexivity end. }
  { (* the asserts (ARMainChk.v) *)
    eapply semax_pre; [ | eapply semax_post;
      [ | | | | apply (CHK Espec J0 J1 gv va vb w inp src pos take room iu ifr ou ofr ra za La zb Lb ow MF0) ] ].
    { unfold mid1_at. entailer!. }
    { intros. simpl RA_normal. apply andp_left2. apply derives_refl. }
    all: intros; apply andp_left2; intro rho; simpl; normalize. }
  (* read += take - used.avail_in: no overflow, pos + take <= Zlength src <= Int64.max_signed *)
  unfold mid1_at. rewrite (istreamA_unfold gv Tsh va za Vundef La). Intros.
  forward. forward.
  rewrite Int.unsigned_repr by rep_lia. rewrite sub64_repr, add64_repr.
  sep_apply (istreamA_fold gv Tsh va za Vundef La); auto.
  set (pos' := pos + (take - zf_ai za)) in *.
  assert (Hpos': 0 <= pos' <= Zlength src) by (unfold pos'; lia).
  clearbody pos'.
  (* the four free()s *)
  forward_call (tarray tuchar take, iu, gv).
  { rewrite if_false by (destruct iu; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) iu). cancel. }
  forward_call (tarray tuchar take, ifr, gv).
  { rewrite if_false by (destruct ifr; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep (sublist pos (pos + take) src)) ifr). cancel. }
  forward_call (tarray tuchar room, ou, gv).
  { rewrite if_false by (destruct ou; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ou). cancel. }
  forward_call (tarray tuchar room, ofr, gv).
  { rewrite if_false by (destruct ofr; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar room) (out_after (Zrepeat Vundef room) ow room) ofr). cancel. }
  (* the do-while's invariant at read = pos' *)
  unfold dinv. Exists pos' za La zb Lb. unfold dinv_at, fresh_mem. simpl Z.eqb. cbv iota.
  assert (dprop J0 J1 w src 1 pos' za La zb Lb) by (unfold dprop; simpl; auto).
  entailer!.
Qed.

Lemma tails : tail0_stmt /\ (chk_stmt -> tail1_stmt).
Proof. exact (conj tail0 tail1). Qed.

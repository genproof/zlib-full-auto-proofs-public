(* Law rt_stream (data of any length), main's setup segment from the NULL tests on (statement 12 of main's body
   onwards, USegAKit.segA_tests), data and compressed being objects: if out is NULL main returns 0, otherwise it
   goes on with new_stream (USegAInit.sa_init).  Round 1's MainSegANull.v with the sizes of round 2's harness. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream.USegAInit.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Lemma sa_tests {Espec : OracleKind} J gv vc vd va lv wv mv sv data cap bd od be oe bc oc op :
  urts_dfacts J ->
  0 <= lv <= Int.max_unsigned -> 0 <= wv <= Int.max_unsigned -> 0 <= mv <= Int.max_unsigned ->
  0 <= sv <= Int.max_unsigned -> 0 <= Zlength data <= max_size -> 0 <= cap <= max_size -> is_bytes data ->
  rparams_ok (Int.signed (Int.repr lv)) 8 (Int.signed (Int.repr wv)) (Int.signed (Int.repr mv))
    (Int.signed (Int.repr sv)) = true ->
  semax Delta_m (PRE_tests gv vc vd va lv wv mv sv data cap bd od be oe bc oc op) segA_tests
    (overridePost (EX u : setup, EX l : dls, DI gv vc vd va J u l) POST_m).
Proof.
  intros JF H H0 H1 H2 H3 H4 H6 Hpar0. unfold PRE_tests, segA_tests, POST_m.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  destruct (eq_dec op nullval) as [Po | Po].
  { subst op.
    ifpost _t'12 Int.zero; [sa_tceq | sa_nob | forward; [sa_tceq | entailer!] | ].
    ifpost _t'13 Int.one; [sa_nob | forward; entailer! | ]. forward_if; [sa_ret | sa_nob]. }
  fold (sa_buf (Zlength data) op). sa_mkptr op bout oout.
  ifpost _t'12 Int.zero; [sa_tceq | sa_nob | forward; [sa_tceq | entailer!] | ].
  ifpost _t'13 Int.zero; [sa_nob | forward; [sa_tceq | entailer!] | ].
  forward_if; [sa_nob | ].
  exact (sa_init J gv vc vd va lv wv mv sv data cap bd od be oe bc oc bout oout JF H H0 H1 H2 H3 H4 H6 Hpar0).
Qed.

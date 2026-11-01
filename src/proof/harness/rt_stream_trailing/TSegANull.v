(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's setup segment from the NULL tests on (statement
   12 of main's body onwards, TSegAKit.segA_tests_t), data and compressed being objects: if out is NULL main
   returns 0, otherwise it goes on with new_stream (TSegAInit.st_init).  The proof is rt_stream's
   (rt_stream/USegANull.v) on this program's main. *)
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
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegAInit.
Require Import Zlib.harness.rt_stream_trailing.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac st_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in st_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := st_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma st_tests {Espec : OracleKind} J gv vc vd va lv wv mv sv data cap bd od be oe bc oc op :
  urts_dfacts J ->
  0 <= lv <= Int.max_unsigned -> 0 <= wv <= Int.max_unsigned -> 0 <= mv <= Int.max_unsigned ->
  0 <= sv <= Int.max_unsigned -> 0 <= Zlength data <= max_size -> 0 <= cap <= max_size -> is_bytes data ->
  rparams_ok (Int.signed (Int.repr lv)) 8 (Int.signed (Int.repr wv)) (Int.signed (Int.repr mv))
    (Int.signed (Int.repr sv)) = true ->
  semax Delta_t (PRE_tests_t gv vc vd va lv wv mv sv data cap bd od be oe bc oc op) segA_tests_t
    (overridePost (EX u : setup, EX l : dls, DI_t gv vc vd va J u l) POST_t).
Proof.
  intros JF H H0 H1 H2 H3 H4 H6 Hpar0. unfold PRE_tests_t, segA_tests_t, POST_t.
  unfold Delta_t; simplify_func_tycontext. abbreviate_semax.
  destruct (eq_dec op nullval) as [Po | Po].
  { subst op.
    ifpost _t'12 Int.zero; [sa_tceq | sa_nob | forward; [sa_tceq | entailer!] | ].
    ifpost _t'13 Int.one; [sa_nob | forward; entailer! | ]. forward_if; [sa_ret | sa_nob]. }
  fold (sa_buf (Zlength data) op). sa_mkptr op bout oout.
  ifpost _t'12 Int.zero; [sa_tceq | sa_nob | forward; [sa_tceq | entailer!] | ].
  ifpost _t'13 Int.zero; [sa_nob | forward; [sa_tceq | entailer!] | ].
  forward_if; [sa_nob | ].
  exact (st_init J gv vc vd va lv wv mv sv data cap bd od be oe bc oc bout oout JF H H0 H1 H2 H3 H4 H6 Hpar0).
Qed.

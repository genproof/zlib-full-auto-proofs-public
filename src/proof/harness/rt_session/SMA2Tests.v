(* Law rt_session, main's statements 45 and 46: the NULL tests of the seven new objects and of got's three
   buffers, from the operand lemmas (SMA2T*.v, SMA2R*.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.proof.harness.rt_session.SMA2T41n.
Require Import Zlib.proof.harness.rt_session.SMA2T41.
Require Import Zlib.proof.harness.rt_session.SMA2T42.
Require Import Zlib.proof.harness.rt_session.SMA2T43.
Require Import Zlib.proof.harness.rt_session.SMA2T44.
Require Import Zlib.proof.harness.rt_session.SMA2T45.
Require Import Zlib.proof.harness.rt_session.SMA2T46.
Require Import Zlib.proof.harness.rt_session.SMA2T4t.
Require Import Zlib.proof.harness.rt_session.SMA2T4u.
Require Import Zlib.proof.harness.rt_session.SMA2R45.
Require Import Zlib.proof.harness.rt_session.SMA2T47.
Require Import Zlib.proof.harness.rt_session.SMA2T47p.
Require Import Zlib.proof.harness.rt_session.SMA2T48.
Require Import Zlib.proof.harness.rt_session.SMA2T48f.
Require Import Zlib.proof.harness.rt_session.SMA2R46.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* the two cases of a test, without touching the goal *)
Lemma bool_cases (b : bool) : b = true \/ b = false.
Proof. destruct b; auto. Qed.

(* a statement followed by the rest of a part *)
Lemma a2_seq {Espec : OracleKind} {cs : compspecs} Delta P Q c1 c2 X R :
  semax Delta P c1 (overridePost Q R) -> semax Delta Q c2 (overridePost X R) ->
  semax Delta P (Ssequence c1 c2) (overridePost X R).
Proof. intros H1 H2. eapply semax_seq; [rewrite overridePost_overridePost; exact H1 | exact H2]. Qed.

(* statement 45, the operands: _t'46 is 1 iff one of the seven objects is NULL *)
Lemma a2_ops45 {Espec : OracleKind} gv vh vg vc va vd u :
  semax Delta_s (NS gv vh vg vc va vd u [])
    (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence I41 I42) I43) I44) I45) I46)
    (overridePost (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))]) POST_s).
Proof.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'45 (vb (f45 u))])).
  2: destruct (bool_cases (f45 u)) as [E | E]; [apply a2_t46_t | apply a2_t46_f]; exact E.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'44 (vb (f44 u))])).
  2: destruct (bool_cases (f44 u)) as [E | E]; [apply a2_t45_t | apply a2_t45_f]; exact E.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'43 (vb (f43 u))])).
  2: destruct (bool_cases (f43 u)) as [E | E]; [apply a2_t44_t | apply a2_t44_f]; exact E.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'42 (vb (f42 u))])).
  2: destruct (bool_cases (f42 u)) as [E | E]; [apply a2_t43_t | apply a2_t43_f]; exact E.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'41 (vb (f41 u))])).
  2: destruct (bool_cases (f41 u)) as [E | E]; [apply a2_t42_t | apply a2_t42_f]; exact E.
  destruct (eq_dec (su_dcp u) nullval) as [E | E]; [apply a2_t41_n | apply a2_t41_p]; exact E.
Qed.

(* statement 46 when none of the seven objects is NULL: A47, or the return when one of got's buffers is NULL *)
Lemma a2_s46 {Espec : OracleKind} gv vh vg vc va vd u :
  f46 u = false ->
  semax Delta_s (NS gv vh vg vc va vd u []) S46
    (overridePost (EX u' : setup, A47 gv vh vg vc va vd u') POST_s).
Proof.
  intros H46. rewrite S46_split.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'48 (vb (f48 u))])).
  2: destruct (bool_cases (f48 u)) as [E | E]; [apply a2_r46_t | apply a2_r46_f]; auto.
  apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'47 (vb (f47 u))])).
  2: destruct (bool_cases (f47 u)) as [E | E]; [apply a2_t48_t | apply a2_t48_f]; exact E.
  destruct (eq_dec (su_gxp u) nullval) as [E | E]; [apply a2_t47_n | apply a2_t47_p]; exact E.
Qed.

(* statements 45 and 46 *)
Lemma a2_tests {Espec : OracleKind} gv vh vg vc va vd u :
  semax Delta_s (NS gv vh vg vc va vd u []) (Ssequence S45 S46)
    (overridePost (EX u' : setup, A47 gv vh vg vc va vd u') POST_s).
Proof.
  rewrite S45_split.
  destruct (bool_cases (f46 u)) as [E | E].
  - apply (a2_seq _ _ FF); [ | apply semax_ff].
    apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))])); [apply a2_ops45 | ].
    apply a2_r45_t. exact E.
  - apply (a2_seq _ _ (NS gv vh vg vc va vd u [])); [ | apply a2_s46; exact E].
    apply (a2_seq _ _ (NS gv vh vg vc va vd u [temp _t'46 (vb (f46 u))])); [apply a2_ops45 | ].
    apply a2_r45_f. exact E.
Qed.

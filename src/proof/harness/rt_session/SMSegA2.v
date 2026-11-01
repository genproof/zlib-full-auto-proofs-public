(* Law rt_session (harness/rt_session.c): main's statements 24-46, the copies, compressed, out, the fields of head and got and got's buffers (SMKit.v, [segA2_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.proof.harness.rt_session.SMA2Objs.
Require Import Zlib.proof.harness.rt_session.SMA2Head1.
Require Import Zlib.proof.harness.rt_session.SMA2Head2.
Require Import Zlib.proof.harness.rt_session.SMA2Head3.
Require Import Zlib.proof.harness.rt_session.SMA2Got1.
Require Import Zlib.proof.harness.rt_session.SMA2Got2.
Require Import Zlib.proof.harness.rt_session.SMA2Got3.
Require Import Zlib.proof.harness.rt_session.SMA2Tests.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* the statements 24-46 in the groups of SMA2*.v: the same statements up to the association of the sequences *)
Definition segA2_g : statement :=
  Ssequence (Ssequence S24 (Ssequence S25 (Ssequence S26 (Ssequence S27 (Ssequence S28 (Ssequence S29 S30))))))
  (Ssequence (Ssequence S31 (Ssequence S32 (Ssequence S33 S34)))
  (Ssequence (Ssequence S35 S36) (Ssequence (Ssequence S37 S38)
  (Ssequence (Ssequence S39 S40) (Ssequence (Ssequence S41 S42) (Ssequence (Ssequence S43 S44)
  (Ssequence S45 S46))))))).

Lemma segA2_groups : unfold_Ssequence segA2_g = unfold_Ssequence segA2.
Proof. rewrite segA2_split. reflexivity. Qed.

(* head complete and got not yet written: the state of statement 39 *)
Lemma QH_QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op :
  QH gv vh vg vc va vd u dcp xcp ncp ccp ep cp op (hvals u) = QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op h00 [].
Proof. unfold QH, QG. rewrite app_nil_r. reflexivity. Qed.

Lemma sm_segA2 : segA2_stmt.
Proof.
  intros Espec gv vh vg vc va vd u.
  apply (semax_unfold_Ssequence segA2_g _ segA2_groups).
  eapply a2_seq; [apply a2_objs | ].
  apply extract_exists_pre; intro dcp. apply extract_exists_pre; intro xcp.
  apply extract_exists_pre; intro ncp. apply extract_exists_pre; intro ccp.
  apply extract_exists_pre; intro ep. apply extract_exists_pre; intro cp. apply extract_exists_pre; intro op.
  eapply a2_seq; [apply a2_head1 | ].
  eapply a2_seq; [apply a2_head2 | ].
  eapply a2_seq; [apply a2_head3 | ].
  rewrite QH_QG.
  eapply a2_seq; [apply a2_got1 | ]. apply extract_exists_pre; intro gxp.
  eapply a2_seq; [apply a2_got2 | ]. apply extract_exists_pre; intro gnp.
  eapply a2_seq; [apply a2_got3 | ]. apply extract_exists_pre; intro gcp.
  apply a2_tests.
Qed.

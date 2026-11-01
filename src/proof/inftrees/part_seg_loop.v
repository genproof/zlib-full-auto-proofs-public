(* Part: the segment seg_loop of the body of inflate_table (verif_it_defs.v).
   The loop body is cut into five parts (seg_loop_defs.v), proved in seg_loop_<part>.v; here: the loop rule
   with the invariant EX s, A_loop X s and the composition of the parts. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.
Require Import Zlib.proof.inftrees.seg_loop_defs.
Require Import Zlib.proof.inftrees.seg_loop_here.
Require Import Zlib.proof.inftrees.seg_loop_rep.
Require Import Zlib.proof.inftrees.seg_loop_huff.
Require Import Zlib.proof.inftrees.seg_loop_cnt.
Require Import Zlib.proof.inftrees.seg_loop_sub.

#[local] Existing Instance Inftrees.CS.

Lemma seg_loop_sa1 {Espec: OracleKind} : forall Delta P a b c R,
  semax Delta P (Ssequence (Ssequence a b) c) R -> semax Delta P (Ssequence a (Ssequence b c)) R.
Proof. intros. apply seq_assoc; auto. Qed.

Lemma seg_loop_sa2 {Espec: OracleKind} : forall Delta P a b c R,
  semax Delta P (Ssequence a (Ssequence b c)) R -> semax Delta P (Ssequence (Ssequence a b) c) R.
Proof. intros. apply seq_assoc; auto. Qed.

Lemma seg_loop_ok : loop_facts -> seg_loop_stmt.
Proof.
intros LF Espec X WF.
pose proof (sl_here_ok LF Espec X) as Hhere.
pose proof (sl_rep_ok LF Espec X) as Hrep.
pose proof (sl_huff_ok LF Espec X) as Hhuff.
pose proof (sl_cnt_ok LF Espec X) as Hcnt.
pose proof (sl_sub_ok LF Espec X) as Hsub.
apply semax_pre with (P' := (EX s: state, A_loop X s)%argsassert).
{ apply andp_left2. Exists (init_state (c_lens X) (it_root X) (c_old X)). apply derives_refl. }
unfold seg_loop.
apply semax_loop with (Q' := (EX s: state, A_loop X s)%argsassert).
2: { eapply semax_post; [ | | | | apply semax_skip]; intros;
     simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return;
     [apply andp_left2, derives_refl | ..];
     apply andp_left2; intro rho; apply prop_left; contradiction. }
apply extract_exists_pre; intros s.
apply (proj1 (semax_skip_seq _ _ _ _)).
apply seg_loop_sa1.
eapply semax_seq; [apply (Hhere s WF) | ].
do 3 apply seg_loop_sa1.
eapply semax_seq; [do 2 apply seg_loop_sa2; apply (Hrep s WF) | ].
do 3 apply seg_loop_sa1.
eapply semax_seq; [do 2 apply seg_loop_sa2; apply (Hhuff s WF) | ].
eapply semax_seq; [apply (Hcnt s WF) | ].
apply (Hsub s WF).
Qed.

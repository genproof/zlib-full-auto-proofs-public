(* The body of inflate_table satisfies inflate_table_spec (spec.v), from its seven segments: body_from_segs.
   The segments are proved in part_seg_<segment>.v and the model's loop facts in part_loop_facts.v;
   contracts/suite.v applies body_from_segs to them. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.spec.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

(* start_function without check_normalized (written when inflate_table still copied structs; kept, it
   leaves Delta as Delta_it):
   start_function1 with the WITH tuple destructured by hand. *)
Ltac start_inflate_table :=
  leaf_function;
  unfold inflate_table_spec, NDmk_funspec;
  split3; [reflexivity | reflexivity | ];
  let Espec := fresh "Espec" in let DTL := fresh "DTL" in
  intros Espec DTL [[[[[[[[[[[[?type ?lens] ?req] ?old] ?gv] ?shg] ?shl] ?sh] ?pl] ?pw] ?ptab] ?pt] ?pb];
  simpl fn_body; simpl fn_params; simpl fn_return;
  clear DTL;
  start_function2;
  match goal with |- semax ?D (fun rho => @sepcon _ _ _ (?A rho) (stackframe_of ?F rho)) ?c ?Q =>
    change (semax D (A * stackframe_of F)%logic c Q) end;
  (* start_function3 without simplify_func_tycontext and abbreviate_semax: Delta stays
     func_tycontext f_inflate_table Vprog [] [] (= Delta_it) *)
  simpl app;
  process_stackframe_of;
  repeat rewrite <- data_at__offset_zero;
  try simple apply start_function_aux1;
  repeat (apply semax_extract_PROP; intro).

Lemma seq_assoc1 {Espec: OracleKind} : forall Delta P a b c R,
  semax Delta P (Ssequence (Ssequence a b) c) R -> semax Delta P (Ssequence a (Ssequence b c)) R.
Proof. intros. apply seq_assoc; auto. Qed.

(* The body from the segments (verif_it_defs.v). *)
Lemma body_from_segs :
  seg_counts_stmt -> seg_max0_stmt -> seg_check_stmt -> seg_sort_stmt -> seg_init_stmt ->
  seg_loop_stmt -> seg_fin_stmt -> body_inflate_table_stmt.
Proof.
intros S1 S2 S3 S4 S5 S6 S7. unfold body_inflate_table_stmt. intros Es.
start_inflate_table.
set (X := mkCtx type lens req old gv shg shl sh pl pw ptab pt pb v_here v_count v_offs).
assert (WF: it_wf X) by (unfold it_wf; simpl; tauto).
change (semax Delta_it (A_start X) (fn_body f_inflate_table) (POST_it X)).
simpl fn_body.
do 7 apply seq_assoc1.
eapply semax_seq; [apply S1; exact WF | ].
eapply semax_seq; [apply S2; exact WF | ].
do 4 apply seq_assoc1.
eapply semax_seq; [apply S3; exact WF | ].
do 2 apply seq_assoc1.
eapply semax_seq; [apply S4; exact WF | ].
do 10 apply seq_assoc1.
eapply semax_seq; [apply S5; exact WF | ].
eapply semax_seq; [apply S6; exact WF | ].
apply extract_exists_pre; intros s.
do 2 apply seq_assoc1.
apply S7; exact WF.
Qed.

(** * The body of deflate.c's deflateStateCheck against its shared specification (DSpec.deflateStateCheck_spec): ob_deflateStateCheck. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** EXPERIMENT: the spec with strm->next_in (offset 0: [strm == Z_NULL] needs strm weakly valid). *)
Definition deflateStateCheck_spec_fix :=
 DECLARE _deflateStateCheck
 WITH os : option dstate, strmp : val, sp : val, za : val, zf : val, ni : val, gv : globals
 PRE [ tptr t_strm ]
  PROP ()
  PARAMS (strmp) GLOBALS (gv)
  SEP (dcheck_at os strmp sp za zf gv; @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp)
 POST [ tint ]
  PROP () RETURN (vi (c_deflateStateCheck os))
  SEP (dcheck_at os strmp sp za zf gv; @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp).

Ltac tc_valid0 fld :=
  apply denote_tc_test_eq_split; [|auto with valid_pointer];
  sep_apply (field_at_valid_ptr0 Ews t_strm (DOT fld)); try reflexivity; auto with valid_pointer.

Ltac cmp_null :=
  match goal with |- context [sem_cmp_pp Ceq ?x _] => destruct x; try contradiction; reflexivity end.

Lemma int_eq_repr_z a c :
  Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= c <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr c) = (a =? c).
Proof.
  intros. destruct (Z.eqb_spec a c).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply n. apply repr_inj_signed; auto.
Qed.

Ltac ust := unfold status_ok, DState.INIT_STATE, DState.GZIP_STATE, DState.EXTRA_STATE, DState.NAME_STATE,
  DState.COMMENT_STATE, DState.HCRC_STATE, DState.BUSY_STATE, DState.FINISH_STATE in *.

Ltac bad := exfalso; first [ lia | contradiction Int.one_not_zero | discriminate
  | match goal with H: _ <> _ |- _ => apply H; reflexivity end ].

Ltac bfin := cbn; intros; try reflexivity; try discriminate; try lia.

Ltac bcase x c :=
  try (let E := fresh "E" in destruct (Z.eqb_spec x c) as [E|E]; [try rewrite E; bfin|]).

Ltac bclose x :=
  repeat rewrite int_eq_repr_z by rep_lia;
  repeat match goal with H: context [Z.eqb _ _] |- _ => revert H end;
  bcase x 42; bcase x 57; bcase x 69; bcase x 73; bcase x 91; bcase x 103; bcase x 113; bcase x 666;
  bfin.

Lemma body_deflateStateCheck_fix :
  @semax_body DSpec.Vprog Gprog_deflateStateCheck DCS.CS f_deflateStateCheck deflateStateCheck_spec_fix.
Proof.
  start_function.
  unfold dcheck_at, zfuncs.
  destruct os as [s|].
  - Intros. rewrite <- H, <- H0.
    assert_PROP (isptr strmp /\ isptr za /\ isptr zf) by entailer!.
    forward_if (temp _t'1 (Vint Int.zero)).
    { tc_valid0 _next_in. }
    { subst strmp. destruct H2 as [[] _]. }
    { forward. forward. entailer!. cmp_null. }
    forward_if (temp _t'2 (Vint Int.zero)).
    { exfalso; lia. }
    { forward. forward. entailer!. cmp_null. }
    forward_if.
    { exfalso; lia. }
    forward.
    assert_PROP (isptr sp) by entailer!.
    forward_if (temp _t'3 (Vint Int.zero)).
    { apply denote_tc_test_eq_split; [|auto with valid_pointer].
      sep_apply (field_at_valid_ptr0 Ews t_ds (DOT _strm)); try reflexivity; auto with valid_pointer. }
    { subst sp. contradiction. }
    { forward. forward.
      - entailer!. apply denote_tc_test_eq_split;
          sep_apply (field_at_valid_ptr0 Ews t_strm (DOT _next_in)); try reflexivity; auto with valid_pointer.
      - entailer!. destruct strmp; try (destruct H2; contradiction). simpl. unfold sem_cmp_pp. simpl.
        destruct (EqDec_block b b); [|congruence]; destruct (EqDec_ptr i i); [|congruence]; reflexivity. }
    set (st := d_status s) in *.
    forward_if (temp _t'4 (Val.of_bool (negb (status_ok st)))).
    { exfalso; lia. }
    { forward.
      forward_if (temp _t'5 (Val.of_bool (negb (st =? 42) && negb (st =? 57)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if (temp _t'6 (Val.of_bool (negb (st =? 42) && negb (st =? 57) && negb (st =? 69)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if (temp _t'7 (Val.of_bool (negb (st =? 42) && negb (st =? 57) && negb (st =? 69) &&
                                          negb (st =? 73)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if (temp _t'8 (Val.of_bool (negb (st =? 42) && negb (st =? 57) && negb (st =? 69) &&
                                          negb (st =? 73) && negb (st =? 91)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if (temp _t'9 (Val.of_bool (negb (st =? 42) && negb (st =? 57) && negb (st =? 69) &&
                                          negb (st =? 73) && negb (st =? 91) && negb (st =? 103)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if (temp _t'10 (Val.of_bool (negb (st =? 42) && negb (st =? 57) && negb (st =? 69) &&
                                          negb (st =? 73) && negb (st =? 91) && negb (st =? 103) &&
                                          negb (st =? 113)))).
      { forward. forward. entailer!. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. try unfold st in *; bclose (d_status s). }
      forward_if.
      { forward. forward. forward. entailer!. ust. try unfold st in *; bclose (d_status s). }
      { forward. entailer!. ust. try unfold st in *; bclose (d_status s). } }
    forward_if.
    { forward. unfold dcheck_at, zfuncs. entailer!. all: unfold c_deflateStateCheck in *; ust.
      all: try unfold st in *; bclose (d_status s). }
    { forward. unfold dcheck_at, zfuncs. entailer!. all: unfold c_deflateStateCheck in *; ust.
      all: try unfold st in *; bclose (d_status s). }
  - Intros. rename H into Hsp, H0 into Hza, H1 into Hzf. subst sp.
    remember (gv _zcalloc) as zca eqn:Ezca. remember (gv _zcfree) as zcf eqn:Ezcf.
    assert_PROP (isptr strmp /\ isptr zca /\ isptr zcf) by entailer!.
    destruct H as (Hs & Hca & Hcf).
    destruct Hza as [-> | ->].
    + forward_if (temp _t'1 (Vint Int.one)).
      { tc_valid0 _next_in. }
      { forward. entailer!. }
      { forward. forward. entailer!. }
      forward_if (temp _t'2 (Vint Int.one)).
      { forward. entailer!. }
      { bad. }
      forward_if.
      { forward. unfold dcheck_at, zfuncs. entailer!. }
      { bad. }
    + forward_if (temp _t'1 (Vint Int.zero)).
      { tc_valid0 _next_in. }
      { subst strmp. destruct Hs. }
      { forward. forward. entailer!. cmp_null. }
      destruct Hzf as [-> | ->].
      * forward_if (temp _t'2 (Vint Int.one)).
        { bad. }
        { forward. forward. entailer!. }
        forward_if.
        { forward. unfold dcheck_at, zfuncs. entailer!. }
        { bad. }
      * forward_if (temp _t'2 (Vint Int.zero)).
        { bad. }
        { forward. forward. entailer!. cmp_null. }
        forward_if.
        { bad. }
        forward.
        forward_if (temp _t'3 (Vint Int.one)).
        { forward. entailer!. }
        { exfalso. apply H0. reflexivity. }
        forward_if (temp _t'4 (Vint Int.one)).
        { forward. entailer!. }
        { bad. }
        forward_if.
        { forward. unfold dcheck_at, zfuncs. entailer!. }
        { bad. }
Qed.

Lemma body_deflateStateCheck : ob_deflateStateCheck.
Proof. exact body_deflateStateCheck_fix. Qed.

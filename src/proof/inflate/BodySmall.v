(* The bodies of inflate_fixed (inftrees.c) and inflateStateCheck (inflate.c) against Callees.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseCommon.
Require Zlib.proof.inftrees.spec.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma body_inflate_fixed {Espec: OracleKind} :
  semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.inftrees.code.f_inflate_fixed inflate_fixed_spec.
Proof.
  clear Espec. start_function.
  forward. forward. forward. forward. entailer!.
Qed.

Lemma func_ptr'_prop (f: funspec) (v: val) : func_ptr' f v = !! isptr v && func_ptr' f v.
Proof.
  apply pred_ext.
  - apply andp_right; [unfold func_ptr'; apply andp_left1; apply func_ptr_isptr | apply derives_refl].
  - apply andp_left2, derives_refl.
Qed.

#[local] Hint Resolve func_ptr'_valid_pointer : valid_pointer.

Lemma state_strm_valid_pointer (v p: val) : field_at Ews t_state (DOT _strm) v p |-- valid_pointer p.
Proof. apply field_at_valid_ptr0; [auto with share | simpl; lia | reflexivity]. Qed.

#[local] Hint Resolve state_strm_valid_pointer : valid_pointer.

Ltac fif_temp i v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp i v :: Q) (SEPx R))) end.

Ltac dead := exfalso; first [contradiction | discriminate | match goal with H: Int.one = Int.zero |- _ => inv H end
  | match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end | auto; fail].

Ltac cmpfix := unfold Int.lt; rewrite ?Int.signed_repr by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b); try lia end; try reflexivity.

Ltac retfix Ez := first [ rewrite Ez; cancel | reflexivity
  | unfold HEAD, SYNC; repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end;
    simpl; try reflexivity; lia ].

Lemma body_inflateStateCheck {Espec: OracleKind} :
  semax_body Vprog [] f_inflateStateCheck inflateStateCheck_spec.
Proof.
  clear Espec. start_function.
  destruct (eq_dec strmp nullval) as [Hn|Hn].
  - subst strmp.
    fif_temp _t'1 (Vint Int.one).
    { forward. entailer!. }
    { dead. }
    fif_temp _t'2 (Vint Int.one).
    { forward. entailer!. }
    { dead. }
    forward_if False.
    { forward. }
    { dead. }
  - destruct H as [H|[Hsh Hok]]; [contradiction|].
    change ((val*(val*(val*(val*(val*(val*(val*(val*(val*(val*(val*(val*(val*val))))))))))))))%type in sv.
    destruct sv as (a1,(a2,(a3,(a4,(a5,(a6,(a7,(st,(za,(zf,(a11,(a12,(a13,a14))))))))))))).
    destruct Hok as (-> & -> & ->).
    assert (Ez: zfuncs gv = (func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc) *
       func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) (gv _zcfree))%logic) by reflexivity.
    remember (gv _zcalloc) as za eqn:Eza. remember (gv _zcfree) as zf eqn:Ezf.
    rewrite Ez.
    rewrite (func_ptr'_prop _ za), (func_ptr'_prop _ zf).
    Intros.
    destruct za; try contradiction. destruct zf; try contradiction.
    assert_PROP (isptr strmp) as Ps by entailer!.
    destruct strmp; try contradiction.
    fif_temp _t'1 (Vint Int.zero).
    { dead. }
    { forward. forward. entailer!. }
    fif_temp _t'2 (Vint Int.zero).
    { dead. }
    { forward. forward. entailer!. }
    forward_if True.
    { dead. }
    { forward. entailer!. }
    Intros.
    destruct live.
    + specialize (H0 eq_refl). destruct sp; try contradiction.
      Intros.
      forward. forward.
      fif_temp _t'3 (Vint Int.zero).
      { dead. }
      { forward. forward. entailer!. rewrite if_true by auto. reflexivity. }
      destruct (Z_lt_le_dec md 16180) as [Hlo|Hlo]; [|destruct (Z_le_gt_dec md 16211) as [Hhi|Hhi]].
      * fif_temp _t'4 (Vint Int.one).
        { dead. }
        { forward. forward. entailer!; cmpfix. }
        fif_temp _t'5 (Vint Int.one).
        { forward. entailer!. }
        { dead. }
        forward_if False.
        { forward. entailer!; retfix Ez. }
        { dead. }
      * fif_temp _t'4 (Vint Int.zero).
        { dead. }
        { forward. forward. entailer!; cmpfix. }
        fif_temp _t'5 (Vint Int.zero).
        { dead. }
        { forward. forward. entailer!; cmpfix. }
        forward_if True.
        { dead. }
        { forward. entailer!. }
        forward. entailer!; retfix Ez.
      * fif_temp _t'4 (Vint Int.zero).
        { dead. }
        { forward. forward. entailer!; cmpfix. }
        fif_temp _t'5 (Vint Int.one).
        { dead. }
        { forward. forward. entailer!; cmpfix. }
        forward_if False.
        { forward. entailer!; retfix Ez. }
        { dead. }
    + Intros. forward. forward.
      fif_temp _t'3 (Vint Int.one).
      { forward. entailer!. }
      { dead. }
      fif_temp _t'4 (Vint Int.one).
      { forward. entailer!. }
      { dead. }
      fif_temp _t'5 (Vint Int.one).
      { forward. entailer!. }
      { dead. }
      forward_if False.
      { forward. entailer!; retfix Ez. }
      { dead. }
Qed.

Lemma bodies_small {Espec: OracleKind} :
  semax_body Zlib.proof.inftrees.spec.Vprog [] Zlib.inftrees.code.f_inflate_fixed inflate_fixed_spec /\
  semax_body Vprog [] f_inflateStateCheck inflateStateCheck_spec.
Proof. split; [apply body_inflate_fixed | apply body_inflateStateCheck]. Qed.

(* Law inflate_codes, main, branch `op >= 24`, part A (MainInfKit.v): after r = inflate(&s, flush), the asserts
   up to the finality check, then B ; C (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.harness.inflate_codes.MainInfKit.

Lemma mi_eq_s a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro X. apply repr_inj_signed in X; auto.
Qed.

Ltac inteq := repeat match goal with |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] =>
  rewrite (mi_eq_s a b) by rep_lia end.

Ltac vcmp := repeat first [ progress (simpl Int.eq; simpl Int.ltu)
  | match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end
  | match goal with |- context [zeq ?a ?b] => destruct (zeq a b) end
  | match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end ];
  first [ reflexivity | lia | exfalso; lia | discriminate | idtac ].

Ltac reprs := rewrite ?Int.neg_repr in *; repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ =>
      first [ apply repr_inj_unsigned in H; [ | rep_lia | rep_lia ] | apply repr_inj_signed in H; [ | rep_lia | rep_lia ] ]
  | H: Int.repr ?a <> Int.repr ?b |- _ => assert (a <> b) by (intro; subst; contradiction); clear H
  end.

Lemma mi_mapsto_valid sh p: readable_share sh -> mapsto_ sh tschar p |-- valid_pointer p.
Proof.
  intros Hsh. unfold mapsto_, mapsto. destruct p; try apply FF_left.
  cbv beta iota zeta delta [access_mode type_is_volatile tschar]. rewrite if_true by auto. apply orp_left.
  - apply andp_left1. apply prop_left. intros X. inversion X.
  - apply andp_left2. apply exp_left. intros v2.
    replace (Vptr b i) with (Vptr b (Ptrofs.repr (Ptrofs.unsigned i + 0)))
      by (rewrite Z.add_0_r, Ptrofs.repr_unsigned; auto).
    pose proof (valid_pointer.address_mapsto_valid_pointer Mint8signed v2 sh b (Ptrofs.unsigned i) 0
             ltac:(pose proof (Ptrofs.unsigned_range i); simpl; lia) ltac:(simpl; lia)) as X.
    constructor. exact X.
Qed.

Lemma mi_msg_valid gv m: msg_lits gv |-- valid_pointer (gv (msg_ident m)).
Proof.
  unfold msg_lits. pose proof (all_msgs_complete m) as Hm. induction all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + apply sepcon_valid_pointer1. apply mi_mapsto_valid. auto with share.
    + apply sepcon_valid_pointer2. auto.
Qed.

Lemma mi_msg_ptr gv m: msg_lits gv |-- !! isptr (gv (msg_ident m)).
Proof.
  unfold msg_lits. pose proof (all_msgs_complete m) as Hm. induction all_msgs as [ | a l IH].
  - inversion Hm.
  - simpl. destruct Hm as [<- | Hm].
    + sep_apply (mapsto__local_facts Ers tschar (gv (msg_ident a))). entailer!.
    + sep_apply IH. entailer!.
Qed.

Section TestEq.
Local Transparent denote_tc_test_eq.
Lemma mi_test_eq (P: mpred) p: isptr p -> P |-- valid_pointer p -> P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hp H. destruct p; try contradiction. unfold denote_tc_test_eq. cbv [Archi.ptr64].
  apply andp_right; [apply prop_right; reflexivity | ]. apply valid_pointer_weak'. exact H.
Qed.
End TestEq.

Ltac ifabsurd := exfalso; match goal with
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
  | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
  end.

Ltac fin := entailer!; try (change Int.zero with (Int.repr 0) in *; reprs; inteq; cbn [Z.opp] in *; vcmp);
  try (exfalso; apply Int.one_not_zero; assumption).

Lemma mi_A_ok {Espec: OracleKind} gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull
    stop ibp obp r z' sp Rest (Q: environ -> mpred) :
  mi_facts w src pos final indict ain aout flush innull outnull r z' -> isptr srcp ->
  semax Delta_m
    (mi_pre_B gv vs vo vosn vb vdl w srcp src pos final indict ain aout innull outnull stop ibp obp r z' sp Rest)
    seg_inf_BC (normal_ret_assert Q) ->
  semax Delta_m
    (mi_pre_A gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull stop ibp obp r z' sp Rest)
    seg_inf_rest (normal_ret_assert Q).
Proof.
  intros MF Psrc HBC.
  unfold mi_facts in MF. cbv zeta in MF.
  destruct MF as (Hw & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hfl & Hin & Hout & Hfr & Hidr & Hz' & Hcode & Hai & Hao
                  & Hbad & Hok & Hbuf & Hdata & Hfin & Hnd).
  assert (Hr: -5 <= r <= 2).
  { unfold code_okb in Hcode. repeat rewrite orb_true_iff in Hcode.
    repeat match goal with H: _ \/ _ |- _ => destruct H end; apply Z.eqb_eq in H; subst; cbv; split; congruence. }
  unfold Z_OK, Z_STREAM_END, Z_NEED_DICT, Z_STREAM_ERROR, Z_DATA_ERROR, Z_MEM_ERROR, Z_BUF_ERROR, Z_FINISH in *.
  unfold mi_pre_A, seg_inf_rest, mi_tup.
  forward_call r.
  rewrite Hcode.
  forward_call (Int.repr 1).
  forward.
  ifpost _t'39 (Int.repr 1).
  { forward. forward. entailer!. vcmp. }
  { forward. entailer!. }
  forward_call (Int.repr 1).
  forward. forward.
  forward. forward.
  rewrite !sub_repr.
  ifpost _t'40 (Int.repr (if mi_bad innull outnull ain then 1 else 0)).
  { forward. entailer!; try (reprs; subst; reflexivity). }
  { reprs. ifpost _t'40 (Int.repr (if mi_bad innull outnull ain then 1 else 0)).
    { forward. forward. entailer!; try (reprs; subst; unfold mi_bad; vcmp). }
    { forward. entailer!; try (unfold mi_bad; vcmp). } }
  forward.
  forward_call (Int.repr 1).
  { entailer!. inteq. cbn [Z.opp]. destruct (Z.eqb_spec r (-2)) as [E|E].
    - rewrite (proj1 Hbad E). reflexivity.
    - destruct (mi_bad innull outnull ain) eqn:EB; [exfalso; apply E, Hbad; auto | reflexivity]. }
  (* if (r == Z_OK) *)
  ifsame.
  { reprs. destruct (Hok ltac:(assumption)) as [Hpr Hfl4].
    ifpost _t'41 (Int.repr 1).
    { forward. entailer!. }
    { forward. entailer!. reprs. inteq. vcmp. }
    ifpost _t'42 (Int.repr 1).
    { forward. entailer!. inteq. vcmp. }
    { forward. fin. }
    forward_call (Int.repr 1).
    entailer!. }
  { forward. entailer!. }
  (* if (r == Z_BUF_ERROR) *)
  ifsame.
  { reprs. assert (Hb := Hbuf ltac:(assumption)).
    destruct (Z.eq_dec (ain - zf_ai z') 0) as [U0|U0]; [destruct (Z.eq_dec (aout - zf_ao z') 0) as [M0|M0] | ].
    - ifpost _t'43 (Int.repr 1).
      { forward. fin. }
      { forward. fin. }
      ifpost _t'44 (Int.repr 1).
      { forward. fin. }
      { forward. fin. }
      forward_call (Int.repr 1). entailer!.
    - assert (flush = 4) by (destruct Hb as [[? ?] | ?]; [contradiction | auto]).
      ifpost _t'43 (Int.repr 0).
      { forward. fin. }
      { forward. fin. }
      ifpost _t'44 (Int.repr 1).
      { forward. fin. }
      { forward. fin. }
      forward_call (Int.repr 1). entailer!.
    - assert (flush = 4) by (destruct Hb as [[? ?] | ?]; [contradiction | auto]).
      ifpost _t'43 (Int.repr 0).
      { forward. fin. }
      { forward. fin. }
      ifpost _t'44 (Int.repr 1).
      { forward. fin. }
      { forward. fin. }
      forward_call (Int.repr 1). entailer!. }
  { forward. entailer!. }
  (* if (r == Z_DATA_ERROR) *)
  ifsame.
  { reprs. assert (Hd := Hdata ltac:(assumption)).
    destruct (zf_msg z') as [m|] eqn:Em; [ | contradiction ].
    pose proof (mi_msg_ptr gv m) as MP. pose proof (mi_msg_valid gv m) as MV.
    unfold POSTCONDITION, abbreviate. change (msg_val gv (Some m)) with (gv (msg_ident m)).
    set (mp := gv (msg_ident m)) in *. clearbody mp.
    rewrite (add_andp _ _ MP). Intros.
    forward.
    forward_call (Int.repr 1).
    { entailer!; first [ apply mi_test_eq; [auto | apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2; exact MV]
                       | destruct mp; try contradiction; reflexivity ]. }
    { entailer!; first [ apply mi_test_eq; [auto | apply sepcon_valid_pointer1, sepcon_valid_pointer1, sepcon_valid_pointer2; exact MV]
                       | destruct mp; try contradiction; reflexivity ]. }
    }
  { forward. entailer!. }
  (* the finality check *)
  destruct (mi_bad innull outnull ain) eqn:EB.
  - ifpost _t'46 (Int.repr 0).
    { forward. fin. }
    { forward. fin. }
    ifsame.
    { ifabsurd. }
    { forward. entailer!. }
    eapply semax_pre; [ | unfold MORE_COMMANDS, POSTCONDITION, Delta, abbreviate; exact HBC ]. unfold mi_pre_B. rewrite EB. entailer!.
  - destruct (Z.eq_dec final 0) as [F0|F0].
    + ifpost _t'46 (Int.repr 0).
      { forward. fin. }
      { forward. fin. }
      ifsame.
      { ifabsurd. }
      { forward. entailer!. }
      eapply semax_pre; [ | unfold MORE_COMMANDS, POSTCONDITION, Delta, abbreviate; exact HBC ]. unfold mi_pre_B. rewrite EB. entailer!.
    + destruct (Hfin eq_refl F0) as (Er & Hu & Hm).
      ifpost _t'46 (Int.repr 1).
      { forward. fin. }
      { forward. fin. }
      ifsame.
      { forward_call (Int.repr 1).
        { fin. }
        ifpost _t'45 (Int.repr 1).
        { forward. fin. }
        { forward. fin. }
        forward_call (Int.repr 1). entailer!. }
      { ifabsurd. }
      eapply semax_pre; [ | unfold MORE_COMMANDS, POSTCONDITION, Delta, abbreviate; exact HBC ]. unfold mi_pre_B. rewrite EB. entailer!.
Qed.

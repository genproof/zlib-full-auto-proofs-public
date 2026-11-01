(** * Body proof of deflateInit2_ against the v9 spec (DSpec9.deflateInit2__spec_v9; v8 proof: Api_init.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations9.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.ZeroBytes Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2.
Require Import Zlib.proof.deflate.InitFacts Zlib.proof.deflate.InitTac.
Require Import Zlib.proof.deflate.InitParts.

Arguments zrest : simpl never.
Arguments zpad : simpl never.
Arguments zlate : simpl never.

Ltac btrue :=
  match goal with H: typed_true _ ?v |- _ =>
    match v with
    | context [if ?b then _ else _] =>
        let Hb := fresh "Hb" in assert (Hb: b = true) by (destruct b; [reflexivity | inv H]); rewrite Hb in *
    end end; cbn [orb] in *.
Ltac bfalse :=
  match goal with H: typed_false _ ?v |- _ =>
    match v with
    | context [if ?b then _ else _] =>
        let Hb := fresh "Hb" in assert (Hb: b = false) by (destruct b; [inv H | reflexivity]); rewrite Hb in *
    end end; cbn [orb] in *.

Ltac brw :=
  repeat match goal with
  | H : ?b = true |- context [?b] => rewrite H
  | H : ?b = false |- context [?b] => rewrite H end;
  cbn [orb]; try reflexivity.

Lemma body_deflateInit2_9 : ob_deflateInit2_9.
Proof.
  unfold ob_deflateInit2_9. start_function. rename H6 into Hv0. rename H7 into H6.
  eapply (make_func_ptr _zcfree _ _ _ _ _ _ (snd Zlib.proof.zutil.Spec.zcfree_spec)); [reflexivity|reflexivity|reflexivity|split; reflexivity|].
  eapply (make_func_ptr _zcalloc _ _ _ _ _ _ (snd Zlib.proof.zutil.Spec.zcalloc_spec)); [reflexivity|reflexivity|reflexivity|split; reflexivity|].
  forward.
  forward_if (temp _t'1 (Vint (if Znth 0 vers =? 49 then Int.zero else Int.one))).
  { subst vp. assert_PROP False by (entailer!; match goal with H: field_compatible _ _ nullval |- _ => destruct H; contradiction end). contradiction. }
  { forward.
    { entailer!. rep_lia. }
    unfold deflate_globals. Intros. forward.
    { entailer!. compute; split; congruence. }
    forward. entailer!.
    2: unfold deflate_globals; cancel.
    destruct (Z.eqb_spec (Znth 0 vers) 49) as [E|E];
      [ rewrite E; reflexivity
      | rewrite Int.eq_false; [reflexivity|]; intro X; apply (f_equal Int.signed) in X;
        change (Znth 0 [49; 46; 51; 46; 50; 0]) with 49 in X; rewrite !Int.signed_repr in X by rep_lia; lia ]. }
  forward_if (temp _t'2 (Vint (if andb (Znth 0 vers =? 49) (ssize =? 112) then Int.zero else Int.one))).
  { forward. entailer!. destruct (Znth 0 vers =? 49); [exfalso; auto | reflexivity]. }
  { forward. entailer!. destruct (Znth 0 vers =? 49); [|contradiction Int.one_not_zero; auto].
    unfold s32_ok in H4. rewrite Int.signed_repr by rep_lia. change (sizeof (Tstruct _z_stream_s noattr)) with 112. cbn [andb].
    unfold Int64.cmpu. destruct (Z.eqb_spec ssize 112) as [E|E]; [subst; reflexivity|].
    rewrite Int64.eq_false; [reflexivity|]. intro X; apply (f_equal Int64.signed) in X.
    rewrite !Int64.signed_repr in X by rep_lia. lia. }
  forward_if.
  { assert (Hb: andb (Znth 0 vers =? 49) (ssize =? 112) = false)
      by (destruct (andb (Znth 0 vers =? 49) (ssize =? 112)); auto; contradiction).
    forward.
    Exists false false false false false (@None dstate, zrst0, Z_VERSION_ERROR).
    cbn [fst snd]. Exists st0 (@nullval) (@nullval) op dt msgv.
    change (Z_VERSION_ERROR =? Z_OK) with false. change (Z_VERSION_ERROR =? Z_VERSION_ERROR) with true.
    unfold rfv, zfuncs. cbv iota.
    entailer!.
    unfold c_deflateInit2_. destruct (Znth 0 vers =? 49), (ssize =? 112); try discriminate; reflexivity. }
  assert (Hok: Znth 0 vers =? 49 = true /\ ssize =? 112 = true)
    by (destruct (Znth 0 vers =? 49), (ssize =? 112); auto; exfalso; apply Int.one_not_zero; exact H7).
  destruct Hok as [Hv1 Hs1]. rewrite Hv1, Hs1 in H6. clear H7.
  unfold reset_fields. Intros.
  forward_if.
  { apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
    eapply derives_trans; [ | apply (ni_valid ni strmp)]. cancel. }
  { subst strmp. assert_PROP False by (entailer!; match goal with H: field_compatible _ _ nullval |- _ => destruct H; contradiction end). contradiction. }
  forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  freeze [0;1;2;3;4;6;10;11;12;13;14;15] FR.
  forward_if (PROP () LOCAL (temp _wrap (Vint (Int.repr 1)); gvars gv; temp _strm strmp;
     temp _level (vi level); temp _method (vi method); temp _windowBits (vi wbits); temp _memLevel (vi mem);
     temp _strategy (vi strategy))
    SEP (FRZL FR; field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp;
         field_at Ews t_strm (DOT _zfree) nullval strmp;
         field_at Ews t_strm (DOT _opaque) nullval strmp)).
  { forward. forward. entailer!. }
  { contradiction. }
  forward.
  forward_if (PROP () LOCAL (temp _wrap (Vint (Int.repr 1)); gvars gv; temp _strm strmp;
     temp _level (vi level); temp _method (vi method); temp _windowBits (vi wbits); temp _memLevel (vi mem);
     temp _strategy (vi strategy))
    SEP (FRZL FR; field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp;
         field_at Ews t_strm (DOT _zfree) (gv _zcfree) strmp;
         field_at Ews t_strm (DOT _opaque) nullval strmp)).
  { forward. entailer!. }
  { contradiction. }
  forward_if (temp _level (vi (if level =? -1 then 6 else level))).
  { forward. entailer!.
    match goal with Hx : Int.repr level = Int.repr _ |- _ =>
      apply repr_inj_s32 in Hx; [|auto|unfold s32_ok; rep_lia] end.
    subst level. reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq level (-1))); auto. intro; subst; contradiction. }
  forward_if (PROP (-15 <= wbits) LOCAL (
     temp _wrap (vi (if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1));
     temp _windowBits (vi (if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits));
     gvars gv; temp _strm strmp;
     temp _level (vi (if level =? -1 then 6 else level)); temp _method (vi method); temp _memLevel (vi mem);
     temp _strategy (vi strategy))
    SEP (FRZL FR; field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp;
         field_at Ews t_strm (DOT _zfree) (gv _zcfree) strmp;
         field_at Ews t_strm (DOT _opaque) nullval strmp)).
  { forward.
    forward_if.
    { forward. thaw FR.
      Exists false false false false false (@None dstate, set_z_msg zrst0 None, Z_STREAM_ERROR).
      cbn [fst snd]. Exists st0 (gv _zcalloc) (gv _zcfree) (@nullval) dt (@nullval).
      change (Z_STREAM_ERROR =? Z_OK) with false. change (Z_STREAM_ERROR =? Z_VERSION_ERROR) with false.
      unfold rfv, zfuncs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
      entailer!.
      unfold s32_ok in H1. rewrite !Int.signed_repr in * by rep_lia.
      rewrite Hv1, Hs1. unfold c_deflateInit2_. cbn [negb orb].
      rewrite (proj2 (Z.ltb_lt wbits 0)) by lia. rewrite (proj2 (Z.ltb_lt wbits (-15))) by lia. reflexivity. }
    unfold s32_ok in H1. rewrite ?Int.neg_repr in *. rewrite !Int.signed_repr in * by rep_lia.
    forward.
    { entailer!. change (Int.signed Int.zero) with 0. rep_lia. }
    entailer!. rewrite (proj2 (Z.ltb_lt wbits 0)) by lia. auto. }
  { forward_if.
    { unfold s32_ok in H1. rewrite !Int.signed_repr in * by rep_lia.
      forward. forward.
      entailer!. rewrite (proj2 (Z.ltb_ge wbits 0)) by lia. rewrite (proj2 (Z.gtb_lt wbits 15)) by lia. auto. }
    { unfold s32_ok in H1. rewrite !Int.signed_repr in * by rep_lia.
      forward. entailer!. rewrite (proj2 (Z.ltb_ge wbits 0)) by lia.
      destruct (Z.gtb_spec wbits 15); [lia|]. auto. } }
  Intros. match goal with Hx : -15 <= wbits |- _ => rename Hx into Hwm end.
  forward_if (temp _t'3 (Val.of_bool ((mem <? 1) || (mem >? 9)))).
  { forward. entailer!. cmp_solve. }
  { forward. entailer!. cmp_solve. }
  forward_if (temp _t'4 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'5 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'6 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'7 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'8 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0) || ((if level =? -1 then 6 else level) >? 9)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'9 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0) || ((if level =? -1 then 6 else level) >? 9) || (strategy <? 0)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'10 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0) || ((if level =? -1 then 6 else level) >? 9) || (strategy <? 0) || (strategy >? 4)))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward. entailer!. brw. cmp_solve. }
  forward_if (temp _t'11 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0) || ((if level =? -1 then 6 else level) >? 9) || (strategy <? 0) || (strategy >? 4) || (((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) =? 8) && negb ((if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1) =? 1))))).
  { btrue. forward. entailer!. brw. }
  { bfalse. forward_if (temp _t'11 (Val.of_bool ((mem <? 1) || (mem >? 9) || negb (method =? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) <? 8) || ((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) >? 15) || ((if level =? -1 then 6 else level) <? 0) || ((if level =? -1 then 6 else level) >? 9) || (strategy <? 0) || (strategy >? 4) || (((if wbits <? 0 then - wbits else if wbits >? 15 then wbits - 16 else wbits) =? 8) && negb ((if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1) =? 1))))).
    { forward. forward. entailer!. brw. cmp_solve. }
    { forward. entailer!. rewrite Hb. cbn [orb]. match goal with Hn : _ <> 8 |- _ => rewrite (proj2 (Z.eqb_neq _ 8) Hn) end. reflexivity. }
    entailer!. }
  forward_if.
  { match goal with H: typed_true _ (if ?b then _ else _) |- _ =>
      assert (Hb: b = true) by (destruct b; [reflexivity | inv H]) end.
    assert (Hbad: i_bad level method wbits mem strategy = true) by exact Hb. clear Hb.
    forward. thaw FR.
    Exists false false false false false (@None dstate, set_z_msg zrst0 None, Z_STREAM_ERROR).
    cbn [fst snd]. Exists st0 (gv _zcalloc) (gv _zcfree) (@nullval) dt (@nullval).
    change (Z_STREAM_ERROR =? Z_OK) with false. change (Z_STREAM_ERROR =? Z_VERSION_ERROR) with false.
    unfold rfv, zfuncs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
    entailer!.
    rewrite Hv1, Hs1. apply init_bad_err; auto. }
  match goal with H: typed_false _ (if ?b then _ else _) |- _ =>
    assert (Hb: b = false) by (destruct b; [inv H | reflexivity]) end.
  assert (Hbad: i_bad level method wbits mem strategy = false) by exact Hb. clear Hb.
  forward_if (temp _windowBits (vi (i_wb9 wbits))).
  { forward. entailer!. unfold i_wb9, i_wb.
    destruct (Z.ltb_spec wbits 0); [|destruct (Z.gtb_spec wbits 15)];
    match goal with H: Int.repr ?x = Int.repr 8 |- _ =>
      apply repr_inj_s32 in H; [rewrite H; reflexivity | unfold s32_ok in *; rep_lia | unfold s32_ok; rep_lia] end. }
  { forward. entailer!. unfold i_wb9, i_wb. cmp_solve. }
  drop_LOCALs [_t'3;_t'4;_t'5;_t'6;_t'7;_t'8;_t'9;_t'10;_t'11].
  assert (Hf: 1 <= mem <= 9 /\ method = 8 /\ 9 <= i_wb9 wbits <= 15 /\ 0 <= i_lv level <= 9 /\ 0 <= strategy <= 4 /\ 0 <= i_wr wbits <= 2).
  { clear - Hbad Hwm. unfold i_bad in Hbad.
    repeat match goal with H: (_ || _) = false |- _ => apply orb_false_iff in H; destruct H end.
    unfold i_wb9, i_wr, i_wb, i_lv in *.
    destruct (Z.ltb_spec wbits 0); [|destruct (Z.gtb_spec wbits 15)]; destruct (Z.eqb_spec level (-1));
    repeat match goal with
    | H: (Z.ltb _ _) = false |- _ => apply Z.ltb_ge in H
    | H: (Z.gtb ?x ?y) = false |- _ => rewrite Z.gtb_ltb in H; apply Z.ltb_ge in H
    | H: negb _ = false |- _ => apply negb_false_iff in H
    | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H: (_ && _) = false |- _ => apply andb_false_iff in H; destruct H
    | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
    end; repeat split; lia. }
  destruct Hf as (Hmem & Hmeth & Hwb9 & Hlv & Hstr & Hwr). subst method.
  change (vi (if wbits <? 0 then 0 else if wbits >? 15 then 2 else 1)) with (vi (i_wr wbits)).
  change (vi (if level =? -1 then 6 else level)) with (vi (i_lv level)).
  thaw FR.
  forward. forward.
  forward_call (t_ds, gv, nullval, 1, 5968).
  Intros sp. forward.
  destruct (eq_dec sp nullval) as [Hsp|Hsp].
  { subst sp. forward_if.
    2: { contradiction. }
    forward.
    Exists false false false false false (@None dstate, set_z_msg zrst0 None, Z_MEM_ERROR).
    cbn [fst snd]. Exists st0 (gv _zcalloc) (gv _zcfree) (@nullval) dt (@nullval).
    change (Z_MEM_ERROR =? Z_OK) with false. change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false.
    unfold rfv, zfuncs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
    entailer!.
    rewrite Hv1, Hs1. apply init_mem1; auto. }
  Intros.
  forward_if.
  { contradiction. }
  assert_PROP (field_compatible t_ds [] sp) as FCs by entailer!.
  sep_apply (data_at__bytes Ews t_ds sp FCs). change (sizeof t_ds) with 5968.
  forward_call (Ews, sp, 5968, 0).
  change (0 mod 256) with 0. rewrite zbytes_byte_vals by lia.
  sep_apply (zero_ds sp FCs). rewrite zds_split, zset0_vals. Intros.
  freeze [23;24;29;30;31;32;33;35;36;37] FZ.
  assert (Eshl: forall k, 0 <= k < 32 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (Z.shiftl 1 k))
    by (intros k Hk; unfold Int.shl; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  assert (Epow: forall k, 0 <= k <= 16 -> 1 <= Z.shiftl 1 k <= 65536).
  { intros k Hk. rewrite Z.shiftl_1_l. pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_le_mono_r 2 k 16 ltac:(lia) ltac:(lia)). simpl in *. lia. }
  pose proof (Epow (i_wb9 wbits) ltac:(lia)) as HW. pose proof (Epow (mem + 7) ltac:(lia)) as HHS.
  pose proof (Epow (mem + 6) ltac:(lia)) as HLB.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  forward. forward. forward. forward. forward. forward.
  forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite Eshl by lia.
  forward. forward. forward. rewrite !add_repr, !sub_repr.
  forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. rewrite ?Int.unsigned_repr by rep_lia. lia. }
  rewrite Eshl by lia.
  forward. forward. rewrite !sub_repr.
  forward. forward. rewrite !add_repr, !sub_repr.
  forward. forward. forward.
  forward_call (tarray tuchar (2 * Z.shiftl 1 (i_wb9 wbits)), gv, nullval, Z.shiftl 1 (i_wb9 wbits), 2).
  { simpl. rewrite Z.max_r by lia. lia. }
  Intros pw. forward.
  forward. forward. forward.
  forward_call (tarray tushort (Z.shiftl 1 (i_wb9 wbits)), gv, nullval, Z.shiftl 1 (i_wb9 wbits), 2).
  { simpl. rewrite Z.max_r by lia. lia. }
  Intros pp. forward.
  forward. forward. forward.
  forward_call (tarray tushort (Z.shiftl 1 (mem + 7)), gv, nullval, Z.shiftl 1 (mem + 7), 2).
  { simpl. rewrite Z.max_r by lia. lia. }
  Intros ph. forward.
  forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. rewrite ?Int.unsigned_repr by rep_lia. lia. }
  rewrite add_repr, Eshl by lia.
  forward. forward. forward.
  forward_call (tarray tuchar (4 * Z.shiftl 1 (mem + 6)), gv, nullval, Z.shiftl 1 (mem + 6), 4).
  { simpl. rewrite Z.max_r by lia. lia. }
  Intros pb. forward.
  forward. forward.
  assert (VP: forall t n p, 0 < n -> 0 < sizeof t -> sizeof t * n <= Ptrofs.max_unsigned ->
     (library.malloc_token Ews (tarray t n) p * data_at_ Ews (tarray t n) p * TT)%logic |-- valid_pointer p).
  { intros t n p Hn Ht Hb. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply data_at__valid_ptr; [auto | ].
    replace (sizeof (tarray t n)) with (sizeof t * Z.max 0 n) by reflexivity. rewrite Z.max_r by lia. nia. }
  forward.
  forward_if (temp _t'19 (Val.of_bool ((if eq_dec pw nullval then true else false) ||
                                       (if eq_dec pp nullval then true else false)))).
  { destruct (eq_dec pw nullval); [entailer! | ].
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
    eapply derives_trans; [ | apply (VP tuchar (2 * Z.shiftl 1 (i_wb9 wbits)) pw); [lia | simpl; lia | simpl; rep_lia] ].
    cancel. }
  { forward. entailer!. }
  { destruct (eq_dec pw nullval); [contradiction|]. Intros. forward.
    destruct (eq_dec pp nullval).
    - subst pp. forward. entailer!.
    - Intros. forward. entailer!.
      destruct pp; try contradiction;
      try (match goal with H: field_compatible _ _ (Vlong _) |- _ => destruct H; contradiction end);
      simpl; try reflexivity. }
  forward_if (temp _t'20 (Val.of_bool ((if eq_dec pw nullval then true else false) || (if eq_dec pp nullval then true else false) || (if eq_dec ph nullval then true else false)))).
  { btrue. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity. }
  { bfalse. forward.
    destruct (eq_dec ph nullval).
    - subst ph. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity.
    - Intros. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity.
      all: destruct ph; try contradiction;
      try (match goal with H: field_compatible _ _ (Vlong _) |- _ => destruct H; contradiction end);
      simpl; try reflexivity. }
  forward_if (temp _t'21 (Val.of_bool ((if eq_dec pw nullval then true else false) || (if eq_dec pp nullval then true else false) || (if eq_dec ph nullval then true else false) || (if eq_dec pb nullval then true else false)))).
  { btrue. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity. }
  { bfalse. forward.
    destruct (eq_dec pb nullval).
    - subst pb. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity.
    - Intros. forward. entailer!. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity.
      all: destruct pb; try contradiction;
      try (match goal with H: field_compatible _ _ (Vlong _) |- _ => destruct H; contradiction end);
      simpl; try reflexivity. }
  forward_if.
  { match goal with H: typed_true _ (if ?b then _ else _) |- _ =>
      assert (Hb21: b = true) by (destruct b; [reflexivity | inv H]) end.
    forward.
    forward_if (temp _t'17 (Vint (Int.repr 0))).
    { match goal with H: typed_true _ _ |- _ => vm_compute in H; discriminate end. }
    { forward. entailer!. }
    forward_if (temp _t'18 (Vint (Int.repr 6))).
    { match goal with H: ?x <> ?x |- _ => contradiction H; reflexivity end. }
    { forward. entailer!. }
    thaw FZ. unfold deflate_globals, errmsg_at. Intros vs.
    forward.
    { entailer!. assert (HZ: is_pointer_or_null (Znth 6 vs)) by (apply Forall_Znth; auto; lia).
      destruct (Znth 6 vs); try contradiction; simpl in *; auto. }
    forward.
    assert (HZ6: is_pointer_or_null (Znth 6 vs)) by (apply Forall_Znth; auto; lia).
    pose proof (init_end_stream wbits mem strmp sp pw pp ph pb dt gv
      (Vint (Int.repr (i_wr wbits))) (Vlong (Int64.repr (Int.signed (Int.repr 0))))
      (Vint (Int.repr (i_wb9 wbits))) (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits))))
      (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits) - 1))) (Vint (Int.repr (mem + 7)))
      (Vint (Int.repr (Z.shiftl 1 (mem + 7)))) (Vint (Int.repr (Z.shiftl 1 (mem + 7) - 1)))
      (Vint (Int.divu (Int.repr (mem + 7 + 3 - 1)) (Int.repr 3))) (Vlong (Int64.repr (Int.signed (Int.repr 0))))
      (Vint (Int.repr (Z.shiftl 1 (mem + 6))))
      (Vlong (Int64.mul (Int64.repr (Int.unsigned (Int.repr (Z.shiftl 1 (mem + 6))))) (Int64.repr (Int.signed (Int.repr 4)))))
      FCs) as IES.
    cbv zeta in IES. sep_apply IES. clear IES.
    set (z0 := zrst0).
    set (z1 := set_z_msg (set_z_msg z0 None) (Some Z_MEM_ERROR)).
    forward_call (Some (i_end_state wbits mem), strmp, ni, z1, (@None dstate, z1, Z_OK), gv).
    cbn [fst snd]. unfold dstream. Intros za zf op' dt'.
    forward.
    Exists true (negb (if eq_dec pw nullval then true else false)) (negb (if eq_dec pp nullval then true else false))
      (negb (if eq_dec ph nullval then true else false)) (negb (if eq_dec pb nullval then true else false))
      (@None dstate, z1, Z_MEM_ERROR).
    cbn [fst snd]. Exists nullval za zf op' dt' (Znth 6 vs).
    change (Z_MEM_ERROR =? Z_OK) with false. change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false.
    unfold rfv. cbv iota.
    unfold zfuncs, deflate_globals, errmsg_at, reset_fields. Exists vs.
    entailer!.
    rewrite Hv1, Hs1, init_mem2; auto.
    - split; [ | intros X; inv X]. unfold i_end_state, z1, z0. rewrite end_finish. reflexivity.
    - clear - Hb21. repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) | H: context [EqDec_val ?q nullval] |- _ => destruct (EqDec_val q nullval) end; simpl in *; try discriminate; try contradiction; try reflexivity. }
  match goal with H: typed_false _ (if ?b then _ else _) |- _ =>
    assert (Hb21: b = false) by (destruct b; [inv H | reflexivity]) end.
  assert (pw <> nullval /\ pp <> nullval /\ ph <> nullval /\ pb <> nullval) as (Ew & Ep & Eh & Eb)
    by (clear - Hb21; destruct (EqDec_val pw nullval), (EqDec_val pp nullval), (EqDec_val ph nullval),
          (EqDec_val pb nullval); simpl in Hb21; try discriminate; auto).
  rewrite !if_false by auto.
  Intros.
  forward. forward.
  assert_PROP (field_compatible (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) [] pp) as FCp by entailer!.
  sep_apply (data_at__bytes Ews (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) pp FCp).
  replace (sizeof (tarray tushort (Z.shiftl 1 (i_wb9 wbits)))) with (2 * Z.shiftl 1 (i_wb9 wbits))
    by (simpl; rewrite Z.max_r by lia; lia).
  forward_call (Ews, pp, 2 * Z.shiftl 1 (i_wb9 wbits), 0).
  { entailer!. destruct pp; try contradiction;
    try (match goal with H: field_compatible _ _ (Vlong _) |- _ => destruct H; contradiction end).
    simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.unsigned_repr by rep_lia.
    f_equal. f_equal. f_equal. rewrite Z.mul_comm. reflexivity. }
  change (0 mod 256) with 0.
  sep_apply (prev_zero (Z.shiftl 1 (i_wb9 wbits)) pp ltac:(lia) FCp).
  forward. forward. forward. forward. forward. forward. forward. forward.
  replace (Int.divu (Int.repr (mem + 7 + 3 - 1)) (Int.repr 3)) with (Int.repr ((mem + 7 + 3 - 1) / 3))
    by (unfold Int.divu; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  replace (Int64.mul (Int64.repr (Int.unsigned (Int.repr (Z.shiftl 1 (mem + 6))))) (Int64.repr (Int.signed (Int.repr 4))))
    with (Int64.repr (Z.shiftl 1 (mem + 6) * 4))
    by (rewrite Int.unsigned_repr, Int.signed_repr by rep_lia; rewrite mul64_repr; reflexivity).
  assert_PROP (isptr pb) as Ppb by entailer!.
  replace (force_val (sem_add_ptr_int tuchar Unsigned pb (Vint (Int.repr (Z.shiftl 1 (mem + 6))))))
    with (offset_val (Z.shiftl 1 (mem + 6)) pb).
  2: { destruct pb; try contradiction. unfold sem_add_ptr_int. simpl. f_equal.
       rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_intu, Ptrofs.of_int.
       rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite sub_repr, mul_repr.
  change (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 8))) with (Int.repr 8).
  thaw FZ.
  pose proof (init_ok_stream level wbits mem strategy strmp sp pw pp ph pb dt gv Hwm Hbad H H3 H2 FCs) as IOK.
  cbv zeta in IOK. sep_apply IOK. clear IOK.
  destruct (H6 true true true true true) as [r0 Hr0].
  rewrite init_ok in Hr0 by auto.
  set (z0 := zrst0) in *.
  change (set_z_msg z0 None) with z0 in Hr0.
  destruct (c_deflateReset (i_state level 8 wbits mem strategy) z0) as [[[s1 z1] ret]|] eqn:ER;
    [ | discriminate].
  assert (Eret: ret = Z_OK) by (apply (reset_code _ _ _ ER); reflexivity). subst ret.
  forward_call (0, Some (i_state level 8 wbits mem strategy), strmp, nullval, ni, tin, tout, nullval, adler,
    (Some s1, z1, Z_OK), gv).
  { unfold reset_fields. cancel. }
  { unfold on_state, c_on_state. rewrite ER. reflexivity. }
  Intros msgv'.
  forward.
  Exists true true true true true (Some s1, z1, Z_OK).
  cbn [fst snd]. Exists msgv'.
  change (Z_OK =? Z_VERSION_ERROR) with false. change (Z_OK =? Z_OK) with true. cbv iota.
  entailer!.
  rewrite Hv1, Hs1, init_ok by auto. change (set_z_msg z0 None) with z0. rewrite ER. reflexivity.
Qed.
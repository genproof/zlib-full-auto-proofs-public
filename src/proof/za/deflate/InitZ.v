(* The body of deflateInit2_ with a caller-supplied allocator ([za_deflateInit2__spec], ZSpec.v): the proof of
   src/proof/deflate/Api_init9.v with the five ZALLOC calls through strm->zalloc (zalloc_spec, each recorded as an
   event of the allocator) and the branch that installs zcalloc / zcfree not taken (strm->zalloc and strm->zfree
   are the caller's, not Z_NULL).  The proof is cut at the test of the four buffer allocations (InitZKit.v): the
   branch where one failed is InitZFail.v, the rest of the function InitZOk.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.ZeroBytes Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2.
Require Import Zlib.proof.deflate.InitFacts Zlib.proof.deflate.InitTac.
Require Import Zlib.proof.deflate.InitParts.
Require Import Zlib.proof.za.deflate.InitZParts.
Require Import Zlib.proof.za.deflate.InitZKit.
Require Import Zlib.proof.za.deflate.InitZFail.
Require Import Zlib.proof.za.deflate.InitZOk.

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

Lemma sizeof_tarray_eq {cs : compspecs} t n : sizeof (tarray t n) = sizeof t * Z.max 0 n.
Proof. reflexivity. Qed.

(** ZALLOC(strm, items, size) through strm->zalloc, with the allocator's events so far. *)
Ltac cap_tac :=
  rewrite ?za_now_zalloc_ev, ?za_now_alloc;
  repeat match goal with |- context [eq_dec ?q nullval] => destruct (eq_dec q nullval) end; lia.

Ltac zalloc_call gv T I S :=
  match goal with |- context [za_res gv ?TR] => forward_call (T, I, S, gv, TR) end;
  try (split; [rewrite sizeof_tarray_eq; simpl sizeof; rewrite Z.max_r by lia; lia | cap_tac]).

Section ZA.
Context {ZA : zallocator}.

Lemma body_za_deflateInit2_ :
  @semax_body DSpec.Vprog (@Gprog_za_deflateInit2_ ZA) DCS.CS f_deflateInit2_ (@za_deflateInit2__spec ZA).
Proof.
  start_function. rename H6 into Hv0. rename H7 into H6. rename H8 into Hza. rename H9 into Hzf. rename H10 into Hop.
  rename H11 into Hcap.
  unfold za_funcs. Intros.
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
    cbn [fst snd]. Exists tr st0 dt msgv.
    change (Z_VERSION_ERROR =? Z_OK) with false. change (Z_VERSION_ERROR =? Z_VERSION_ERROR) with true.
    unfold rfv, za_funcs. cbv iota.
    entailer!. split; [ | discriminate].
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
  freeze [0;1;2;4;8;9;10;11;14;15] FR.
  assert_PROP (isptr za_alloc /\ isptr za_free) as Pzz by entailer!. destruct Pzz as [Pza Pzf].
  forward_if (PROP () LOCAL (temp _wrap (Vint (Int.repr 1)); gvars gv; temp _strm strmp;
     temp _level (vi level); temp _method (vi method); temp _windowBits (vi wbits); temp _memLevel (vi mem);
     temp _strategy (vi strategy))
    SEP (FRZL FR; func_ptr' zalloc_spec za_alloc; func_ptr' zfree_spec za_free;
         field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) za_alloc strmp;
         field_at Ews t_strm (DOT _zfree) za_free strmp;
         field_at Ews t_strm (DOT _opaque) za_opaque strmp)).
  { contradiction. }
  { forward. entailer!. }
  forward.
  forward_if (PROP () LOCAL (temp _wrap (Vint (Int.repr 1)); gvars gv; temp _strm strmp;
     temp _level (vi level); temp _method (vi method); temp _windowBits (vi wbits); temp _memLevel (vi mem);
     temp _strategy (vi strategy))
    SEP (FRZL FR; func_ptr' zalloc_spec za_alloc; func_ptr' zfree_spec za_free;
         field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) za_alloc strmp;
         field_at Ews t_strm (DOT _zfree) za_free strmp;
         field_at Ews t_strm (DOT _opaque) za_opaque strmp)).
  { contradiction. }
  { forward. entailer!. }
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
    SEP (FRZL FR; func_ptr' zalloc_spec za_alloc; func_ptr' zfree_spec za_free;
         field_at Ews t_strm (DOT _msg) nullval strmp;
         field_at Ews t_strm (DOT _zalloc) za_alloc strmp;
         field_at Ews t_strm (DOT _zfree) za_free strmp;
         field_at Ews t_strm (DOT _opaque) za_opaque strmp)).
  { forward.
    forward_if.
    { forward. thaw FR.
      Exists false false false false false (@None dstate, set_z_msg zrst0 None, Z_STREAM_ERROR).
      cbn [fst snd]. Exists tr st0 dt (@nullval).
      change (Z_STREAM_ERROR =? Z_OK) with false. change (Z_STREAM_ERROR =? Z_VERSION_ERROR) with false.
      unfold rfv, za_funcs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
      entailer!. split; [ | discriminate].
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
    cbn [fst snd]. Exists tr st0 dt (@nullval).
    change (Z_STREAM_ERROR =? Z_OK) with false. change (Z_STREAM_ERROR =? Z_VERSION_ERROR) with false.
    unfold rfv, za_funcs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
    entailer!. split; [ | discriminate].
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
  pose proof (shl_bounds (i_wb9 wbits) 9 15 ltac:(lia) ltac:(lia)) as BW.
  pose proof (shl_bounds (mem + 7) 8 16 ltac:(lia) ltac:(lia)) as BH.
  pose proof (shl_bounds (mem + 6) 7 15 ltac:(lia) ltac:(lia)) as BL.
  cbn in BW, BH, BL. unfold dinit_max in Hcap.
  forward_call (t_ds, 1, 5968, gv, tr).
  Intros sp. rewrite zalloc_post_eq. Intros. forward.
  destruct (eq_dec sp nullval) as [Hsp|Hsp].
  { subst sp. rewrite zalloc_ev_null. forward_if.
    2: { contradiction. }
    forward.
    Exists false false false false false (@None dstate, set_z_msg zrst0 None, Z_MEM_ERROR).
    cbn [fst snd]. Exists (tr ++ [ZFail]) st0 dt (@nullval).
    change (Z_MEM_ERROR =? Z_OK) with false. change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false.
    unfold rfv, za_funcs, reset_fields. cbv iota. cbn [z_msg set_z_msg zrst0 zmk].
    rewrite za_now_fail, za_failed_fail.
    entailer!.
    rewrite Hv1, Hs1. apply init_mem1; auto. }
  rewrite (zalloc_ev_nn sp) by auto. Intros.
  forward_if.
  { contradiction. }
  assert_PROP (field_compatible t_ds [] sp) as FCs by entailer!.
  sep_apply (data_at__bytes Ews t_ds sp FCs). change (sizeof t_ds) with 5968.
  forward_call (Ews, sp, 5968, 0).
  change (0 mod 256) with 0. rewrite zbytes_byte_vals by lia.
  sep_apply (zero_ds sp FCs). rewrite zds_split, zset0_vals. Intros.
  freeze [23;24;27;28;29;30;31;33;34;35] FZ.
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
  zalloc_call gv (tarray tuchar (2 * Z.shiftl 1 (i_wb9 wbits))) (Z.shiftl 1 (i_wb9 wbits)) 2.
  Intros pw. rewrite zalloc_post_eq. Intros. forward.
  forward. forward. forward.
  zalloc_call gv (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) (Z.shiftl 1 (i_wb9 wbits)) 2.
  Intros pp. rewrite zalloc_post_eq. Intros. forward.
  forward. forward. forward.
  zalloc_call gv (tarray tushort (Z.shiftl 1 (mem + 7))) (Z.shiftl 1 (mem + 7)) 2.
  Intros ph. rewrite zalloc_post_eq. Intros. forward.
  forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. rewrite ?Int.unsigned_repr by rep_lia. lia. }
  rewrite add_repr, Eshl by lia.
  forward. forward. forward.
  zalloc_call gv (tarray tuchar (4 * Z.shiftl 1 (mem + 6))) (Z.shiftl 1 (mem + 6)) 4.
  Intros pb. rewrite zalloc_post_eq. Intros. forward.
  forward. forward.
  assert (VP: forall t n p, 0 < n -> 0 < sizeof t -> sizeof t * n <= Ptrofs.max_unsigned ->
     (@za_tok ZA DCS.CS (tarray t n) p * data_at_ Ews (tarray t n) p * TT)%logic |-- valid_pointer p).
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
    thaw FZ.
    apply (iz_fail_part strmp level wbits mem strategy vp vsh vers ssize ni tin tout msgv adler dt st0 gv tr
             sp pw pp ph pb); auto. }
  match goal with H: typed_false _ (if ?b then _ else _) |- _ =>
    assert (Hb21: b = false) by (destruct b; [inv H | reflexivity]) end.
  thaw FZ.
  apply (iz_ok_part strmp level wbits mem strategy vp vsh vers ssize ni tin tout msgv adler dt st0 gv tr
           sp pw pp ph pb); auto.
Qed.

End ZA.

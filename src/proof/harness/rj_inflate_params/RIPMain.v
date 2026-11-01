(* Law rj_inflate_params, main: draw window_bits, compute the harness's classification (raw, wrapped), new_stream,
   inflateInit2, and the check.  inflateInit2__spec (inflate_api/Spec5.v) gives the return code: Z_MEM_ERROR when
   the state allocation fails, otherwise Z_OK when wbits_ok w (inflateReset2's test, ApiModel.reset2_wb) and
   Z_STREAM_ERROR when not; rip_class_ok shows that the harness's classification is wbits_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_inflate_params.RIPLawCS Zlib.proof.harness.rj_inflate_params.RIPGlobals.
Require Import Zlib.harness.rj_inflate_params.code.

(* zlib.h's windowBits for inflateInit2, as the harness states them: raw (-15..-8) or wrapped (0..47 with the low
   four bits 0 or 8..15) *)
Definition rip_raw (w: Z) : bool := ((-15 <=? w) && (w <=? -8))%bool.
Definition rip_wrapped (w: Z) : bool := ((0 <=? w) && (w <? 48) && ((Z.land w 15 =? 0) || (8 <=? Z.land w 15)))%bool.

(* the harness's classification is exactly the windowBits inflateReset2 accepts *)
Lemma rip_class_ok w : wbits_ok w = (rip_raw w || rip_wrapped w)%bool.
Proof.
  unfold wbits_ok, reset2_wb, rip_raw, rip_wrapped.
  assert (B: 0 <= Z.land w 15 <= 15).
  { change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia. }
  destruct (w <? 0) eqn:E0.
  - apply Z.ltb_lt in E0. destruct (w <? -15) eqn:E1.
    + apply Z.ltb_lt in E1. destruct (-15 <=? w) eqn:E2; [apply Z.leb_le in E2; lia|].
      destruct (0 <=? w) eqn:E3; [apply Z.leb_le in E3; lia|]. reflexivity.
    + apply Z.ltb_ge in E1. destruct (0 <=? w) eqn:E3; [apply Z.leb_le in E3; lia|].
      rewrite andb_false_l, orb_false_r. rewrite (proj2 (Z.leb_le (-15) w) E1).
      destruct (8 <=? - w) eqn:E4, (- w <=? 15) eqn:E5, (w <=? -8) eqn:E6; simpl; try reflexivity;
        rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
  - apply Z.ltb_ge in E0.
    destruct (-15 <=? w) eqn:E2, (w <=? -8) eqn:E6; rewrite ?Z.leb_le, ?Z.leb_gt in E2, E6; try lia; simpl;
      rewrite (proj2 (Z.leb_le 0 w) E0); simpl.
    destruct (w <? 48) eqn:E7; simpl.
    * destruct (Z.land w 15 =? 0); simpl; [reflexivity|].
      destruct (8 <=? Z.land w 15) eqn:E8; simpl; [|reflexivity].
      apply Z.leb_le in E8. rewrite (proj2 (Z.leb_le (Z.land w 15) 15) ltac:(lia)). reflexivity.
    * apply Z.ltb_ge in E7. destruct (w =? 0) eqn:E9; [apply Z.eqb_eq in E9; lia|].
      destruct (8 <=? w) eqn:E8; simpl; [|reflexivity].
      rewrite (proj2 (Z.leb_gt w 15) ltac:(lia)). reflexivity.
Qed.

Definition Gmain : funspecs :=
  [inflateInit2__spec; zcalloc_i; zcfree_i; new_stream_spec; nondet_u32_spec; gp_assert_spec].

(* The local z_stream at the three compspecs: the law's (main's frame), the compress unit's (new_stream_spec) and
   the inflate unit's (inflateInit2__spec's raw_strm). *)
Definition rip_tz : type := Tstruct _z_stream_s noattr.

Lemma rip_zs_raw gv sh q ni ai ti no ao to msgv stv za zf opq dt ad rs :
  @data_at Zlib.units.Compress.CS sh t_zs (zs_val ni ai ti no ao to msgv stv za zf opq dt ad rs) q =
  raw_strm gv sh q (RF ni ai ti no ao to dt ad rs) msgv stv za zf opq.
Proof.
  unfold raw_strm, zs_val, t_zs. simpl.
  transitivity (@data_at CS sh rip_tz (ni, (ai, (ti, (no, (ao, (to, (msgv, (stv, (za, (zf, (opq, (dt, (ad, rs))))))))))))) q).
  - apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
  - symmetry. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

Lemma rip_undef_zs sh q :
  @data_at_ CS sh rip_tz q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof.
  unfold data_at_, zs_val, t_zs. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

Lemma rip_raw_undef gv sh q r msgv stv za zf opq :
  raw_strm gv sh q r msgv stv za zf opq |-- @data_at_ CS sh rip_tz q.
Proof.
  destruct r. rewrite <- rip_zs_raw. sep_apply (@data_at_data_at_ Zlib.units.Compress.CS).
  unfold data_at_. apply derives_refl'.
  apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity].
Qed.

(* whatever inflateInit2_ returned, the memory of the stream gives back main's local variable *)
Lemma rip_init_mem_undef gv sh q r msgv stv opq ret sp w :
  isptr q -> init_mem gv sh q r msgv stv opq ret sp w |-- @data_at_ CS sh rip_tz q * TT.
Proof.
  intros P. unfold init_mem. rewrite if_false by (destruct q; try contradiction; discriminate).
  destruct (ret =? Z_VERSION_ERROR), (ret =? Z_MEM_ERROR), (ret =? Z_OK);
    try (sep_apply rip_raw_undef; cancel);
    unfold istream_raw; Intros; sep_apply rip_raw_undef; cancel.
Qed.

(* the comparisons of window_bits and low with constants, as booleans *)
Ltac rip_cmp :=
  unfold rip_raw, rip_wrapped, bool2val, Int.lt, Int.eq in *;
  change Int.zero with (Int.repr 0) in *; change Int.one with (Int.repr 1) in *;
  rewrite ?Int.signed_repr in * by rep_lia; rewrite ?Int.unsigned_repr in * by rep_lia;
  repeat match goal with
         | |- context [zlt ?a ?b] => destruct (zlt a b)
         | |- context [zeq ?a ?b] => destruct (zeq a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         | H: context [zlt ?a ?b] |- _ => destruct (zlt a b)
         | H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b)
         | H: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
         end; simpl in *; try reflexivity; try lia; try congruence;
  try (rewrite ?Int.unsigned_repr in * by rep_lia; lia).

Lemma body_main : semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  forward.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  rewrite and_repr.
  assert (B: 0 <= Z.land w 15 <= 15).
  { change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia. }
  forward_if (temp _t'2 (Vint (Int.repr (if rip_raw w then 1 else 0)))).
  { forward. entailer!. rip_cmp. }
  { forward. entailer!. rip_cmp. }
  forward.
  forward_if (temp _t'3 (Vint (Int.repr (if ((0 <=? w) && (w <? 48))%bool then 1 else 0)))).
  { forward. entailer!. rip_cmp. }
  { forward. entailer!. rip_cmp. }
  forward_if (temp _t'4 (Vint (Int.repr (if rip_wrapped w then 1 else 0)))).
  { forward_if.
    { forward. entailer!. rip_cmp. }
    { forward. forward. entailer!. rip_cmp. } }
  { forward. entailer!. rip_cmp. }
  forward.
  change (Tstruct _z_stream_s noattr) with rip_tz. rewrite rip_undef_zs.
  forward_call (v_strm, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite rip_zs_raw with (gv := gv).
  assert_PROP (isptr v_strm) as Ps by entailer!.
  assert_PROP (isptr (gv ___stringlit_rj_inflate_params_1)) as Pver by (unfold rip_hversion_lit; entailer!).
  unfold rip_hversion_lit.
  forward_call (gv, Tsh, v_strm,
                RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef,
                Vundef, Vundef, nullval, w, gv ___stringlit_rj_inflate_params_1, Ers, rip_hver_vals, 49, 112).
  { rewrite if_false by (destruct v_strm; try contradiction; discriminate). cancel. }
  { change (Zlength rip_hver_vals) with 6. rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  set (ret := init_ret v_strm 49 112 w alloc_ok) in *.
  assert (Hret: ret = if alloc_ok then (if wbits_ok w then 0 else -2) else -4).
  { subst ret. unfold init_ret. simpl. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    destruct alloc_ok; reflexivity. }
  clearbody ret.
  rewrite rip_class_ok in Hret.
  forward_if.
  { (* Z_MEM_ERROR: the run ends *)
    forward. Exists (Int.repr 0). entailer!. sep_apply rip_init_mem_undef; auto. cancel. }
  forward_if (temp _t'6 (Vint (Int.repr (if (rip_raw w || rip_wrapped w)%bool then 1 else 0)))).
  { forward. entailer!. rip_cmp. }
  { forward. entailer!. rip_cmp. }
  assert (Hc: ret = if (rip_raw w || rip_wrapped w)%bool then 0 else -2).
  { destruct alloc_ok; auto. subst ret. exfalso.
    match goal with H: Int.repr _ <> _ |- _ => apply H; reflexivity end. }
  clear Hret. destruct (rip_raw w || rip_wrapped w)%bool eqn:C; subst ret.
  - (* accepted windowBits: Z_OK *)
    forward_if True.
    + forward_call (Int.repr 1). entailer!.
    + exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end.
    + forward. Exists (Int.repr 0). entailer!. sep_apply rip_init_mem_undef; auto. cancel.
  - (* rejected windowBits: Z_STREAM_ERROR *)
    forward_if True.
    + exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end.
    + forward_call (Int.repr 1). entailer!.
    + forward. Exists (Int.repr 0). entailer!. sep_apply rip_init_mem_undef; auto. cancel.
Qed.

(* The main of harness/inflate_check.c, proved against MainLib.main_core_spec R (IKGlobals.v) for ANY invariant
   I with the facts of IKFacts.v (check_facts I), calling inflate.c's API through its shared specifications
   (inflate_api/Spec5.v, at the inflate unit's compspecs: moved to the law's with IKLawCS's instances) and the
   harness helpers through theirs (inflate_common/HarnessLib.v, HarnessLe32.v, adler32/HarnessRef.v,
   crc32/HarnessRef.v), as inflate_codes/Main*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit Zlib.proof.harness.inflate_check.IKMainLoop.


Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; Zlib.proof.crc32.HarnessRef.ref_crc32_spec; be32_spec; le32_spec;
   exact_copy_spec; exact_space_spec; stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].


(* ---------------------------------------------------------------------------------------------- *)
(* Helpers of the init part (as inflate_codes/MainHelp.v)                                        *)

Lemma ikm_tschar_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) v q = @data_at CS sh (tarray tschar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition ikm_hver : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma ikm_hver_lit gv:
  ik_hversion_lit gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ikm_hver)) ikm_hver
    (gv Zlib.harness.x_inflate_check.code.___stringlit_x_inflate_check_1).
Proof. unfold ik_hversion_lit. rewrite (ikm_tschar_cs Ers (Zlength ikm_hver)). reflexivity. Qed.

Lemma ikm_hver_to gv:
  ik_hversion_lit gv |--
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ikm_hver)) ikm_hver
    (gv Zlib.harness.x_inflate_check.code.___stringlit_x_inflate_check_1).
Proof. rewrite ikm_hver_lit. apply derives_refl. Qed.

(* a stream left by a failed inflateInit2_ is the local variable's memory *)
Lemma ikm_init_fail_mem gv vs r msgv stv opq ret sp w:
  isptr vs -> ret <> Z_OK ->
  init_mem gv Tsh vs r msgv stv opq ret sp w |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec vs nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; apply ik_strm_to_undef | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; apply ik_strm_to_undef | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; apply ik_strm_to_undef.
Qed.

(* the stream after a successful inflateInit2_ *)
Definition ikm_z_init (adl rs: Z) (L: live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then adl else Z.land (i_wrap (l_s L)) 1)
     (Vlong (Int64.repr rs)).

Lemma ikm_init_istream gv vs tin tout adl dt rs L:
  0 <= adl <= Int64.max_unsigned ->
  istream_raw gv Tsh vs
    (raw_after_init (RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
       (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))) (l_s L)) L
  = istream gv Tsh vs (ikm_z_init adl rs L) (Some L).
Proof.
  intros A. rewrite <- istream_raw_istream.
  - unfold raw_after_init, ikm_z_init; simpl. f_equal. f_equal. destruct (i_wrap (l_s L) =? 0); reflexivity.
  - unfold zf_ok, ikm_z_init; simpl. split; [rep_lia | ]. split; [rep_lia | ]. split; [rep_lia | ].
    split; [rep_lia | ]. split; [rep_lia | ].
    destruct (i_wrap (l_s L) =? 0); [auto | ].
    assert (M: Z.land (i_wrap (l_s L)) 1 = i_wrap (l_s L) mod 2) by (apply (Z.land_ones _ 1); lia).
    rewrite M. pose proof (Z.mod_pos_bound (i_wrap (l_s L)) 2 ltac:(lia)). rep_lia.
  - reflexivity.
Qed.

(* a raw stream: inflateInit2_ leaves s.adler as it was *)
Lemma ikm_raw_wrap sp w: w < 0 -> wbits_ok w = true -> i_wrap (l_s (init_live sp w)) = 0.
Proof.
  intros Hw Ok. unfold wbits_ok in Ok. unfold init_live.
  destruct (reset2_wb w) as [[wrap wb] | ] eqn:E; [ | discriminate].
  unfold reset2_wb in E. rewrite (proj2 (Z.ltb_lt w 0) Hw) in E.
  destruct (w <? -15); [discriminate | ].
  destruct ((8 <=? - w) && (- w <=? 15))%bool eqn:B; [ | discriminate].
  inversion E; subst.
  (* a raw stream has windowBits -w in 8..15: bit 3 of wrap stays clear (reset2_wrap 0 (-w) = 0) *)
  apply andb_prop in B. destruct B as [B1 B2]. apply Z.leb_le in B1.
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap.
  rewrite (proj2 (Z.eqb_neq (- w) 0)) by lia. reflexivity.
Qed.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac ikm_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Ltac ikm_dz := repeat match goal with
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zle ?a ?b] => destruct (zle a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | H: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
  | H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b)
  | H: context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
  end; simpl in *; try reflexivity; try lia;
  try (exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
                              | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end).

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

Lemma ikm_init_ret (vs: val) w a: isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros P. unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct vs; try contradiction; discriminate). destruct a; reflexivity.
Qed.

Lemma ikm_raw_eq w: Int.min_signed <= w <= Int.max_signed ->
  (if Int.lt (Int.repr w) (Int.repr 0) then Int.one else Int.zero) = Int.repr (ik_raw w).
Proof.
  intros. unfold Int.lt, ik_raw. rewrite !Int.signed_repr by rep_lia.
  destruct (zlt w 0), (Z.ltb_spec w 0); try lia; reflexivity.
Qed.

Ltac ikm_fail gv src srcp := forward_call (tarray tuchar (Zlength src), srcp, gv);
  [ rewrite if_false by auto; sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))); cancel | ];
  forward; Exists (Int.repr 0);
  match goal with Ps: isptr ?vs |- context [init_mem ?gv _ _ ?rr _ _ _ ?ret ?sp ?w] =>
    sep_apply (ikm_init_fail_mem gv vs rr Vundef Vundef nullval ret sp w Ps ltac:(discriminate)) end;
  entailer!.

Lemma body_main I : check_facts I -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros CF. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  forward_call tt. Intros n.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  forward_call (Int.repr (if n <=? 2^24 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 24)) with (Int.repr (2 ^ 24)). arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros srcp.
  destruct (eq_dec srcp nullval) as [PS|PS].
  { subst srcp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward_call (srcp, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros src. rewrite if_false by auto.
  match goal with H: Zlength src = n |- _ => rename H into Hsrcn end.
  match goal with H: Forall _ src |- _ => rename H into Hsrcb end.
  subst n. fold (bytes_rep src).
  forward_call (v_s, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  match goal with |- context [@data_at ?cs Tsh t_strm ?v v_s] =>
    replace (@data_at cs Tsh t_strm v v_s) with (@data_at CS Tsh (Tstruct _z_stream_s noattr) v v_s)
      by (symmetry; apply (ik_strm_cs Tsh v v_s)) end.
  forward.
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  match goal with |- context [@data_at ?cs Tsh (Tstruct _z_stream_s noattr) ?v v_s] =>
    replace (@data_at cs Tsh (Tstruct _z_stream_s noattr) v v_s)
      with (raw_strm gv Tsh v_s rr Vundef Vundef nullval nullval nullval)
      by (unfold raw_strm; apply (ik_strm_cs Tsh _ v_s)) end.
  assert_PROP (isptr v_s) as Ps by entailer!.
  replace (raw_strm gv Tsh v_s rr Vundef Vundef nullval nullval nullval)
    with (if eq_dec v_s nullval then emp else raw_strm gv Tsh v_s rr Vundef Vundef nullval nullval nullval)
    by (rewrite if_false by (destruct v_s; try contradiction; discriminate); reflexivity).
  replace_SEP 9 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ikm_hver)) ikm_hver
                   (gv Zlib.harness.x_inflate_check.code.___stringlit_x_inflate_check_1)).
  { entailer!. apply ikm_hver_to. }
  assert_PROP (isptr (gv Zlib.harness.x_inflate_check.code.___stringlit_x_inflate_check_1)) as Pver by entailer!.
  forward_call (gv, Tsh, v_s, rr, Vundef, Vundef, nullval, w,
                gv Zlib.harness.x_inflate_check.code.___stringlit_x_inflate_check_1, Ers, ikm_hver, 49, 112).
  { repeat match goal with |- _ /\ _ => split end; try exact Pver; change (Zlength ikm_hver) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  rewrite (ikm_init_ret v_s w alloc_ok Ps).
  destruct alloc_ok; [destruct (wbits_ok w) eqn:WOK | ].
  2: { forward_if; [ ikm_fail gv src srcp | ikm_infeas ]. }
  2: { forward_if; [ ikm_fail gv src srcp | ikm_infeas ]. }
  forward_if.
  { ikm_infeas. }
  (* the live stream *)
  unfold init_mem.
  rewrite if_false by (destruct v_s; try contradiction; discriminate).
  remember (init_live sp w) as L0 eqn:HL0. simpl.
  replace (istream_raw gv Tsh v_s (raw_after_init rr (l_s L0)) L0)
    with (istream gv Tsh v_s (ikm_z_init adl rs L0) (Some L0)) by (symmetry; apply ikm_init_istream; auto).
  assert_PROP (live_ok L0 /\ zf_ok (ikm_z_init adl rs L0)) as LZ by (unfold istream; entailer!).
  destruct LZ as [LOK ZOK].
  assert (Psp: isptr sp) by auto.
  assert (HI0: I w src 0 [] (ikm_z_init adl rs L0) L0).
  { subst L0. apply (ck_init I CF); auto; reflexivity. }
  assert (Hraw0: w < 0 -> zf_adler (ikm_z_init adl rs L0) = adl).
  { intros Hn. unfold ikm_z_init; simpl. subst L0. rewrite ikm_raw_wrap by auto. reflexivity. }
  rewrite <- ikm_hver_lit.
  forward.
  match goal with |- context [temp _raw (Vint ?x)] =>
    replace x with (Int.repr (ik_raw w))
      by (unfold ik_raw; destruct (Z.ltb_spec w 0); destruct (zlt w 0); try lia; reflexivity) end.
  ifpostv _t'5 (Vint (Int.repr (ik_gzv w src))).
  { assert (Hw0: 0 <= w) by (unfold ik_raw in *; ikm_dz).
    assert (ZB: forall i (d: val), 0 <= i < Zlength src -> @Znth val d i (bytes_rep src) = Vint (Int.repr (Znth i src))).
    { intros i d R. unfold bytes_rep, Znth. rewrite !if_false by lia. rewrite nth_map' with (d' := 0); [reflexivity | ].
      rewrite Zlength_correct in R. lia. }
    ifpostv _t'6 (Vint (Int.repr (if andb (16 <=? w) (w <? 32) then 1 else 0))).
    { forward. entailer!. ikm_dz. }
    { forward. entailer!. ikm_dz. }
    forward_if.
    { forward. entailer!. unfold ik_gzv, ik_gz. ikm_dz. }
    ifpostv _t'7 (Vint (Int.repr (if andb (32 <=? w) (2 <=? Zlength src) then 1 else 0))).
    { forward. entailer!. ikm_dz. }
    { forward. entailer!. ikm_dz. }
    ifpostv _t'8 (Vint (Int.repr (if andb (andb (32 <=? w) (2 <=? Zlength src)) (Znth 0 src =? 31) then 1 else 0))).
    { assert (Hn2: 32 <= w /\ 2 <= Zlength src) by ikm_dz. destruct Hn2 as [Hw32 Hn2].
      assert (B0: 0 <= Znth 0 src <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth _ _) Hsrcb); lia).
      forward.
      { entailer!. rewrite (ZB 0 Vundef) by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
      rewrite (ZB 0 Vundef) by lia.
      forward. entailer!. unfold bool2val. ikm_dz. }
    { forward. entailer!. ikm_dz. }
    forward_if.
    { assert (Hn2: 32 <= w /\ 2 <= Zlength src /\ Znth 0 src = 31) by ikm_dz. destruct Hn2 as (Hw32 & Hn2 & Hs0).
      assert (B1: 0 <= Znth 1 src <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth _ _) Hsrcb); lia).
      forward.
      { entailer!. rewrite (ZB 1 Vundef) by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
      rewrite (ZB 1 Vundef) by lia.
      forward. forward. forward. entailer!. unfold bool2val, ik_gzv, ik_gz. ikm_dz. }
    { forward. forward. entailer!. unfold ik_gzv, ik_gz. ikm_dz. } }
  { forward. entailer!. unfold ik_gzv, ik_raw in *. ikm_dz. }
  forward. forward. forward. forward. forward.
  assert_PROP (isptr srcp) as Psrc by entailer!.
  assert (G: ik_glob I w srcp src adl) by (unfold ik_glob; auto 10).
  forward_loop (ik_inv I gv v_s v_osnap w srcp src adl (ik_hversion_lit gv * version_lit gv)%logic)
    break: (ik_inv I gv v_s v_osnap w srcp src adl (ik_hversion_lit gv * version_lit gv)%logic).
  { unfold ik_inv. Exists 0 (@nil Z) (ikm_z_init adl rs L0) L0. entailer!.
    constructor. }
  { unfold ik_inv at 1. Intros pos out z L.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (proj1 (semax_seq_skip _ _ _ _)).
    eapply semax_pre; [ | apply (seg_loop_ok I gv v_s v_osnap w srcp src adl (ik_hversion_lit gv * version_lit gv)%logic
                                   pos out z L); auto ].
    unfold ik_at. entailer!. }
  unfold ik_inv. Intros pos out z L.
  rewrite <- (ik_istream_opt gv Tsh v_s z (Some L)) by auto.
  forward_call (gv, Tsh, v_s, z, Some L).
  rewrite (ik_istream_opt gv Tsh v_s z None) by auto.
  sep_apply (ik_istream_to_undef gv v_s z None).
  forward_call (tarray tuchar (Zlength src), srcp, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))). cancel. }
  forward. Exists (Int.repr 0). entailer!.
Qed.

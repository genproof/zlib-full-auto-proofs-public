(* The main of harness/inflate_codes.c, proved against MainLib.main_core_spec R (Globals.v) for ANY invariant I
   with the facts of Facts.v (codes_facts I), calling inflate.c's API through its shared specifications
   (inflate_api/Spec5.v, at the inflate unit's compspecs: moved to the law's with LawCS's instances) and the
   harness helpers through theirs (inflate_common/HarnessLib.v, adler32/HarnessRef.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_codes.MainKit Zlib.proof.harness.inflate_codes.MainSD
               Zlib.proof.harness.inflate_codes.MainInf Zlib.proof.harness.inflate_codes.MainTail.
Require Import Zlib.proof.harness.inflate_codes.MainHelp Zlib.proof.harness.inflate_codes.MainLoop.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateSetDictionary_spec; inflateEnd_spec; inflateReset_spec;
   inflateReset2_spec; inflateGetDictionary_spec; inflateSync_spec; inflatePrime_spec; inflateValidate_spec;
   inflateMark_spec; inflateCodesUsed_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; be32_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; inflate_code_ok_spec;
   stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Ltac ret_init r src srcp gv := forward_call (tarray tuchar (Zlength src), srcp, gv);
  [ destruct (eq_dec srcp nullval) as [?|_]; [contradiction | ];
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))); cancel | ];
  forward; Exists (Int.repr 0);
  match goal with Ps: isptr ?vs |- context [init_mem ?gv _ (strm_arg _ ?ns) ?rr _ _ _ _ ?sp ?w] =>
    sep_apply (init_fail_mem gv vs ns rr Vundef Vundef nullval r sp w Ps ltac:(discriminate)) end;
  match goal with |- context [ver_rest ?gv ?vo ?vsel ?vbyte] => sep_apply (ver_back gv vo vsel vbyte) end;
  entailer!.

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

Lemma body_main I : codes_facts I -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros CF. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  forward_call tt. Intros n.
  forward_call tt. Intros ssz.
  forward_call tt. Intros vsel.
  forward_call tt. Intros ssel.
  forward_call tt. Intros nullstrm.
  forward_call tt. Intros vbyte.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  assert (Es: Int.repr ssz = Int.repr (Int.signed (Int.repr ssz))) by (rewrite Int.repr_signed; auto).
  rewrite Es. clear Es. set (ss := Int.signed (Int.repr ssz)).
  assert (Hss: Int.min_signed <= ss <= Int.max_signed) by apply Int.signed_range. clearbody ss.
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
  forward. forward.
  ifpostv _t'9 (if zeq vsel 0 then v_other else gv ___stringlit_x_inflate_codes_1).
  { forward. entailer!. rewrite if_false by auto. auto. }
  { forward. entailer!. }
  forward.
  ifpostv _t'10 (Vint (Int.repr (if zeq ssel 0 then ss else 112))).
  { forward. entailer!. rewrite if_false by auto. reflexivity. }
  { forward. entailer!. }
  forward.
  forward_call (v_s, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  ifpostv _t'11 (strm_arg v_s nullstrm).
  { forward. entailer!; unfold strm_arg; rewrite if_true by auto; reflexivity. }
  { forward. entailer!; unfold strm_arg; rewrite if_false by auto; reflexivity. }
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  match goal with |- context [@data_at ?cs Tsh t_strm ?v v_s] =>
    replace (@data_at cs Tsh t_strm v v_s) with (raw_strm gv Tsh v_s rr Vundef Vundef nullval nullval nullval)
      by reflexivity end.
  assert_PROP (isptr v_s) as Ps by entailer!.
  rewrite (strm_split gv v_s nullstrm rr Vundef Vundef nullval Ps).
  match goal with |- context [data_at Tsh (tarray tschar 2) ?l v_other] =>
    replace l with (other_vals vbyte)
      by (unfold other_vals; rewrite Int.sign_ext_idem by lia; reflexivity) end.
  gather_SEP (data_at Tsh (tarray tschar 2) (other_vals vbyte) v_other) (hversion_lit gv).
  rewrite (ver_split gv v_other vsel vbyte). rewrite <- tschar_cs.
  assert_PROP (isptr (ver_p gv v_other vsel)) as Pver by entailer!.
  Intros.
  forward_call (gv, Tsh, strm_arg v_s nullstrm, rr, Vundef, Vundef, nullval, w, ver_p gv v_other vsel,
                ver_sh vsel, ver_vc vsel vbyte, ver_c vsel vbyte, if zeq ssel 0 then ss else 112).
  { pose proof (ver_vc_len vsel vbyte). pose proof (ver_c_range vsel vbyte). rewrite ver_vc_0.
    split; [unfold ver_sh; destruct (zeq vsel 0); auto | ].
    split; [rep_lia | ]. split; [reflexivity | ]. split; [lia | ]. destruct (zeq ssel 0); rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  set (ssv := if zeq ssel 0 then ss else 112) in *.
  assert (Hssv: Int.min_signed <= ssv <= Int.max_signed) by (subst ssv; destruct (zeq ssel 0); rep_lia).
  clearbody ssv.
  set (c0 := ver_c vsel vbyte) in *. pose proof (ver_c_range vsel vbyte) as Hc0. fold c0 in Hc0.
  pose proof (ver_vc_len vsel vbyte) as Hvl. pose proof (ver_vc_0 vsel vbyte) as Hv0. fold c0 in Hv0.
  clearbody c0.
  set (ret := init_ret (strm_arg v_s nullstrm) c0 ssv w alloc_ok) in *.
  forward.
  assert (Rv: readable_share (ver_sh vsel)) by (unfold ver_sh; destruct (zeq vsel 0); auto).
  forward.
  { entailer!. match goal with |- context [@Znth ?A ?d 0 (ver_vc vsel vbyte)] =>
      replace (@Znth A d 0 (ver_vc vsel vbyte)) with (Vint (Int.repr c0)) by (symmetry; apply Hv0) end.
    simpl. rewrite Int.signed_repr by rep_lia. rep_lia. }
  match goal with |- context [@Znth ?A ?d 0 (ver_vc vsel vbyte)] =>
    replace (@Znth A d 0 (ver_vc vsel vbyte)) with (Vint (Int.repr c0)) by (symmetry; apply Hv0) end.
  ifpost _t'13 (Int.repr (if orb (negb (c0 =? 49)) (negb (ssv =? 112)) then 1 else 0)).
  { forward. entailer!. match goal with Hc: c0 <> 49 |- _ => rewrite (proj2 (Z.eqb_neq _ 49) Hc) end.
    reflexivity. }
  { forward. entailer!. change (Int64.unsigned (Int64.repr (sizeof _))) with 112.
    destruct (Z.eqb_spec ssv 112) as [E1|E1]; [rewrite E1; reflexivity | ].
    rewrite Int.eq_false; [reflexivity | ]. intro X. apply repr_inj_signed in X; rep_lia. }
  forward.
  assert (Hret: ret = init_ret (strm_arg v_s nullstrm) c0 ssv w alloc_ok) by reflexivity. clearbody ret.
  set (verr := (negb (c0 =? 49) || negb (ssv =? 112))%bool) in *.
  assert (Hverr: verr = (negb (c0 =? 49) || negb (ssv =? 112))%bool) by reflexivity. clearbody verr.
  pose proof (init_cases v_s nullstrm c0 ssv w alloc_ok Ps) as IC.
  destruct IC as [(EV & ER) | [(EV & EN & ER) | [(EV & EN & EA & ER) | [(EV & EN & EA & EW & ER) |
                  (EV & EN & EA & EW & ER)]]]];
    rewrite ER in Hret; rewrite EV in Hverr; subst ret verr.
  - gpa.
    ifsame.
    { infeas. }
    { forward; try entailer!. }
    forward_if.
    { ret_init (-6) src srcp gv. }
    { infeas. }
  - gpa.
    ifsame.
    { ifpost _t'14 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      ifpost _t'15 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      gpa.
      ifsame.
      { ifpost _t'16 (Int.repr 1).
        { forward. entailer!. }
        { infeas. }
        gpa. entailer!. }
      { infeas. }
      entailer!. }
    { infeas. }
    forward_if.
    { forward_call (tarray tuchar (Zlength src), srcp, gv).
      { destruct (eq_dec srcp nullval) as [?|_]; [contradiction | ]. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))). cancel. }
      forward. Exists (Int.repr 0).
      replace (strm_arg v_s 0) with nullval by reflexivity.
      destruct (eq_dec nullval nullval) as [_|X]; [ | contradiction X; reflexivity].
      unfold raw_strm. sep_apply strm_to_undef. sep_apply (ver_back gv v_other vsel vbyte). entailer!. }
    { infeas. }
  - gpa.
    ifsame.
    { ifpost _t'14 (Int.repr 0).
      { infeas. }
      { forward. entailer!. }
      ifpost _t'15 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      gpa.
      ifsame.
      { infeas. }
      { forward; try entailer!. }
      entailer!. }
    { infeas. }
    forward_if.
    { ret_init (-4) src srcp gv. }
    { infeas. }
  - gpa.
    ifsame.
    { ifpost _t'14 (Int.repr 1).
      { infeas. }
      { forward. entailer!. }
      ifpost _t'15 (Int.repr 1).
      { forward. entailer!. }
      { infeas. }
      gpa.
      ifsame.
      { ifpost _t'16 (Int.repr 1).
        { infeas. }
        { forward_call w. forward. entailer!. rewrite EW. reflexivity. }
        gpa. entailer!. }
      { infeas. }
      entailer!. }
    { infeas. }
    forward_if.
    { ret_init (-2) src srcp gv. }
    { infeas. }
  - gpa.
  ifsame.
  { ifpost _t'14 (Int.repr 1).
    { forward. entailer!. }
    { infeas. }
    ifpost _t'15 (Int.repr 1).
    { forward. entailer!. }
    { infeas. }
    gpa.
    ifsame.
    { ifpost _t'16 (Int.repr 0).
      { infeas. }
      { forward_call w. forward. entailer!. rewrite EW. reflexivity. }
      gpa. entailer!. }
    { infeas. }
    entailer!. }
  { infeas. }
  forward_if.
  { infeas. }
  (* the live stream *)
  assert (Snn: strm_arg v_s nullstrm = v_s) by (unfold strm_arg; destruct (zeq nullstrm 0); [contradiction | auto]).
  rewrite Snn. unfold init_mem.
  destruct (eq_dec v_s nullval) as [X|_]; [subst; contradiction | ].
  remember (init_live sp w) as L0 eqn:HL0. simpl.
  replace (istream_raw gv Tsh v_s (raw_after_init rr (l_s L0)) L0)
    with (istream gv Tsh v_s (z_init adl rs L0) (Some L0)) by (symmetry; apply init_istream; auto).
  sep_apply (ver_back gv v_other vsel vbyte).
  assert_PROP (live_ok L0 /\ zf_ok (z_init adl rs L0)) as LZ by (unfold istream; entailer!).
  destruct LZ as [LOK ZOK].
  assert (HI0: I w src 0 Z_OK 0 (z_init adl rs L0) L0).
  { subst L0. apply (cf_init I CF); auto; reflexivity. }
  Intros.
  ifpost _t'18 (Int.repr (if zlib_okb w then 1 else 0)).
  { ifpost _t'18 (Int.repr (if zlib_okb w then 1 else 0)).
    { forward. entailer!. unfold zlib_okb.
      destruct (Z.leb_spec 0 w); destruct (Z.ltb_spec w 16); destruct (Z.leb_spec 32 w); try lia; reflexivity. }
    { forward. forward. entailer!. unfold zlib_okb.
      destruct (Z.leb_spec 0 w); destruct (Z.ltb_spec w 16); destruct (zlt w 32); destruct (Z.leb_spec 32 w);
        try lia; reflexivity. } }
  { forward. entailer!. unfold zlib_okb. destruct (Z.leb_spec 0 w); try lia; reflexivity. }
  forward. forward. forward. forward.
  assert_PROP (isptr srcp) as Psrc by entailer!.
  forward_loop (loop_inv I gv v_s v_other v_osnap v_b v_dl w srcp src (hversion_lit gv * version_lit gv)%logic)
    break: (loop_inv I gv v_s v_other v_osnap v_b v_dl w srcp src (hversion_lit gv * version_lit gv)%logic).
  { unfold loop_inv. Exists 0 Z_OK 0 (z_init adl rs L0) L0. entailer!. }
  { unfold loop_inv at 1. Intros pos final indict z L.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (proj1 (semax_seq_skip _ _ _ _)).
    eapply semax_pre; [ | apply (seg_loop_ok I gv v_s v_other v_osnap v_b v_dl w srcp src
                                   (hversion_lit gv * version_lit gv)%logic pos final indict z L); auto;
                          exact Hsrcb ].
    entailer!. }
  unfold loop_inv. Intros pos final indict z L.
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  apply semax_seq with FF; [ | apply semax_ff ].
  eapply semax_post; [ | | | | eapply semax_pre;
     [ | apply (seg_tail_ok gv v_s v_other v_osnap v_b v_dl srcp src z L
                 (msg_lits gv * (hversion_lit gv * version_lit gv))%logic); auto ] ].
  5: { unfold tail_pre. entailer!. }
  all: unfold POST_m; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
  all: first [ apply andp_left2; intro rho; simpl; normalize | apply andp_left2; apply derives_refl
             | intros vl; apply andp_left2; apply derives_refl ].
Qed.

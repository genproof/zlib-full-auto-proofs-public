(* The bridge from the allocator-generic port of inflate's proofs (src/proof/za/inflate_api/USpec.v) to the
   wide specifications of SpecW.v, at zlib's default allocator (SpecWLib.zc_alloc): each of the port's
   specifications, a general_intersection over the allocator and the adler cell, is a funspec_sub of
   SpecW's (resp. Spec5's inflateStateCheck_spec), choosing the member at zc_alloc gv and the adler cell
   av_any on a raw stream (strm->adler any contents), av_defined otherwise. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.inflate_api.SpecWBridgeWrap.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* zcalloc / zcfree as the allocator zc_alloc gv                                                   *)

(* zutil.c's zcalloc_spec (any opaque, malloc's resource) meets the allocator interface's zalloc_spec at
   zc_alloc gv (opaque Z_NULL, resource mem_mgr, malloc tokens): the events are not recorded *)
Lemma zc_zalloc_sub: forall gv,
  funspec_sub (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS))
              (@zalloc_spec Zlib.units.Inflate.CS (zc_alloc gv)).
Proof.
  intros gv0. do_funspec_sub. destruct w as [[[[t items] size] gv] tr].
  Exists (t, gv, nullval, items, size) emp. simpl. Intros.
  apply andp_right; [apply prop_right | cancel]. split.
  - intros rho'. apply andp_left2. rewrite emp_sepcon.
    Intros p. Exists p. entailer!. if_tac; cancel.
  - repeat split; auto; lia.
Qed.

Lemma zc_zfree_sub: forall gv,
  funspec_sub (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS))
              (@zfree_spec Zlib.units.Inflate.CS (zc_alloc gv)).
Proof.
  intros gv0. do_funspec_sub. destruct w as [[[t p] gv] tr].
  Exists (t, p, gv, nullval) emp. simpl. Intros.
  sep_apply (data_at__local_facts Ews t p). Intros.
  apply andp_right; [apply prop_right | ].
  - split; [intros rho'; apply andp_left2; rewrite emp_sepcon; entailer! | repeat split; auto].
  - if_tac; [subst p; destruct H2; contradiction | cancel].
Qed.

(* a function pointer is duplicable *)
Lemma func_ptr'_dup: forall phi v, func_ptr' phi v |-- func_ptr' phi v * func_ptr' phi v.
Proof.
  intros phi v. unfold func_ptr'. rewrite corable_andp_sepcon1 by apply corable_func_ptr.
  rewrite emp_sepcon. apply andp_right; [apply andp_left1, derives_refl | apply derives_refl].
Qed.

(* the stream's function pointers as zlib's default allocator, keeping a copy for the caller *)
Lemma zc_zfuncs: forall gv, zfuncs gv |-- zfuncs gv * @zfuncs_za (zc_alloc gv) gv.
Proof.
  intros gv. unfold zfuncs, zfuncs_za, za_funcs. simpl za_alloc. simpl za_free.
  sep_apply (func_ptr'_dup (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc)).
  sep_apply (func_ptr'_dup (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) (gv _zcfree)).
  sep_apply (func_ptr'_mono (zc_zalloc_sub gv) (v := gv _zcalloc)).
  sep_apply (func_ptr'_mono (zc_zfree_sub gv) (v := gv _zcfree)).
  cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream: SpecW's istreamA and the port's istream_za at zc_alloc gv                           *)

(* the member strm->adler of a z_stream may be forgotten (Vundef: any contents) *)
Lemma strm_adler_any: forall sh p (ni ai tin no ao tout msg sp za zf op dt adv res: val),
  data_at sh t_strm (ni, (ai, (tin, (no, (ao, (tout, (msg, (sp, (za, (zf, (op, (dt, (adv, res))))))))))))) p
  |-- data_at sh t_strm (ni, (ai, (tin, (no, (ao, (tout, (msg, (sp, (za, (zf, (op, (dt, (Vundef, res))))))))))))) p.
Proof.
  intros. unfold data_at.
  sep_apply (field_at_local_facts sh t_strm []
    (ni, (ai, (tin, (no, (ao, (tout, (msg, (sp, (za, (zf, (op, (dt, (adv, res))))))))))))) p). Intros.
  assert (FC: field_compatible t_strm [StructField _adler] p)
    by (apply field_compatible_cons; split; [cbv; tauto | auto]).
  clear H H0.
  eapply derives_trans;
    [eapply (gfield_ramif sh t_strm [] (StructField _adler) _ _ p); [apply JMeq_refl | exact FC] |].
  match goal with |- field_at _ _ _ ?v0 _ * _ |-- _ => sep_apply (field_at_field_at_ sh t_strm [StructField _adler] v0 p) end.
  unfold field_at_ at 1.
  eapply derives_trans.
  { apply sepcon_derives; [apply derives_refl |].
    apply allp_left with (default_val (nested_field_type t_strm (DOT _adler))). apply derives_refl. }
  eapply derives_trans; [apply modus_ponens_wand |].
  apply derives_refl.
Qed.

(* the cell of a stream: av_any on a live raw stream, av_defined otherwise *)
Definition cell_of (st: option live) : adler_cell := AdlerCell (raw_live st).

(* the caller's stream is the port's, with the cell of the stream (on a raw stream strm->adler is
   forgotten) *)
Lemma istreamA_za: forall gv shs strmp z av st,
  istreamA_opt gv shs strmp z av st |-- @istream_opt_za (zc_alloc gv) (cell_of st) gv shs strmp z st.
Proof.
  intros. unfold istreamA_opt, istream_opt_za. if_tac; [apply derives_refl |].
  unfold istreamA, istream_za, zstrm_atA, zstrm_at_za, strm_rep_za, adler_v, adler_val, cell_of. simpl av_undef.
  destruct st as [L |]; [| apply derives_refl].
  destruct (raw_live (Some L)); [| apply derives_refl].
  Intros. repeat (apply andp_right; [apply prop_right; auto |]).
  apply sepcon_derives; [apply strm_adler_any | apply derives_refl].
Qed.

(* the port's stream after a call that kept the cell is the caller's, strm->adler forgotten on a raw stream *)
Lemma za_istreamA: forall gv shs strmp z st b, b = raw_live st ->
  @istream_opt_za (zc_alloc gv) (AdlerCell b) gv shs strmp z st |-- istreamA_opt gv shs strmp z Vundef st.
Proof.
  intros gv shs strmp z st b ->. unfold istreamA_opt, istream_opt_za. if_tac; [apply derives_refl |].
  unfold istreamA, istream_za, zstrm_atA, zstrm_at_za, strm_rep_za, adler_v, adler_val. simpl av_undef.
  destruct (raw_live st); apply derives_refl.
Qed.

(* the allocator's function pointers may be dropped *)
Lemma zfuncs_za_emp: forall ZA gv, @zfuncs_za ZA gv |-- emp.
Proof.
  intros. unfold zfuncs_za, za_funcs. sep_apply func_ptr'_emp. sep_apply func_ptr'_emp. apply derives_refl.
Qed.

(* inflate() keeps a stream raw or not *)
Lemma inflate_rel_raw: forall flush strmp z st ib inp ob r z' st' ow,
  inflate_rel flush strmp z st ib inp ob r z' st' ow -> raw_live st' = raw_live st.
Proof.
  intros flush strmp z st ib inp ob r z' st' ow H.
  destruct H as [(_ & _ & _ & -> & _) | (_ & L & o & res & winp & -> & _ & Hrun & _ & _ & _ & _ & _ & ->)];
    [reflexivity |].
  apply run2_wrap in Hrun. unfold raw_live. simpl l_s. rewrite Hrun. unfold m_init. simpl m_s.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity.
Qed.

(* inflateSetDictionary keeps a stream raw or not *)
Lemma setdict_raw: forall strmp z st dict alloc_ok winp,
  raw_live (thd3 (on_live strmp z st (setdict_f dict alloc_ok winp))) = raw_live st.
Proof.
  intros. unfold on_live, is_live. if_tac; [reflexivity |]. destruct st as [L |]; [| reflexivity].
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [| destruct alloc_ok]; unfold raw_live; simpl;
    try (unfold setdict_s; simpl; rewrite updatewindow_w); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The three subsumptions                                                                       *)

Lemma specw_inflate_sub: funspec_sub (snd (@inflate_uspec globals zc_alloc)) (snd inflate_specW).
Proof.
  unfold inflate_uspec, uspec, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs.
  destruct x2 as [[[[[[[[[[[[[gv shs] strmp] z] av] st] ib] inp] ob] flush] gsh] tsh] itok] otok].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : zai => (globals * share * val * zfields * option live * inbuf * list Z *
      option outbuf * Z * share * share * bool * bool * list zev)%type) ((gv, raw_live st) : @zai globals)
    (gv, shs, strmp, z, st, ib, inp, ob, flush, gsh, tsh, itok, otok, @nil zev)) (zfuncs gv).
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  apply andp_right.
  - destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
    sep_apply (istreamA_za gv shs strmp z av st). unfold cell_of.
    eapply derives_trans; [do 6 (apply sepcon_derives; [apply derives_refl |]); apply zc_zfuncs |].
    apply andp_right; [apply prop_right; repeat split; auto; rep_lia | cancel].
  - apply prop_right. intros rho'.
    apply andp_left2. rewrite exp_sepcon2. Intros r. rewrite exp_sepcon2. Intros z'.
    rewrite exp_sepcon2. Intros st'. rewrite exp_sepcon2. Intros ow.
    Exists r z' st' ow. unfold_for_go_lower. simpl. normalize.
    pose proof (inflate_rel_raw _ _ _ _ _ _ _ _ _ _ _ H) as R.
    apply andp_right; [apply prop_right; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
      [apply (za_istreamA gv shs strmp z' st' (raw_live st) (eq_sym R)) | apply derives_refl]] |].
    eapply derives_trans; [do 7 (apply sepcon_derives; [apply derives_refl |]); apply zfuncs_za_emp |].
    cancel.
Qed.

Lemma specw_setdict_sub:
  funspec_sub (snd (@inflateSetDictionary_uspec globals zc_alloc)) (snd inflateSetDictionary_specW).
Proof.
  unfold inflateSetDictionary_uspec, uspec, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs.
  destruct x2 as [[[[[[[[[[[[gv shs] strmp] z] av] st] dsh] p] lo] n] c] dict] tok].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : zai => (globals * share * val * zfields * option live * share * val * Z * Z *
      list val * list Z * bool * list zev)%type) ((gv, raw_live st) : @zai globals)
    (gv, shs, strmp, z, st, dsh, p, lo, n, c, dict, tok, @nil zev)) (zfuncs gv).
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  apply andp_right.
  - destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
    sep_apply (istreamA_za gv shs strmp z av st). unfold cell_of.
    eapply derives_trans; [do 4 (apply sepcon_derives; [apply derives_refl |]); apply zc_zfuncs |].
    apply andp_right; [apply prop_right; repeat split; auto; rep_lia | cancel].
  - apply prop_right. intros rho'.
    apply andp_left2. rewrite exp_sepcon2. Intros alloc_ok. rewrite exp_sepcon2. Intros winp.
    Exists alloc_ok winp. unfold_for_go_lower. simpl. normalize.
    pose proof (setdict_raw strmp z st dict alloc_ok winp) as R.
    apply andp_right; [apply prop_right; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
      [apply (za_istreamA gv shs strmp _ _ (raw_live st) (eq_sym R)) | apply derives_refl]] |].
    eapply derives_trans; [do 5 (apply sepcon_derives; [apply derives_refl |]); apply zfuncs_za_emp |].
    cancel.
Qed.

Lemma specw_check_sub:
  funspec_sub (snd (@inflateStateCheck_uspec globals zc_alloc)) (snd inflateStateCheck_spec).
Proof.
  unfold inflateStateCheck_uspec, uspec, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs.
  destruct x2 as [[[[[[strmp shs] sv] sp] md] live] gv].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : zai => (val * share * reptype t_strm * val * Z * bool * globals)%type)
      ((gv, false) : @zai globals) (strmp, shs, sv, sp, md, live, gv)) (zfuncs gv).
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  apply andp_right.
  - destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
    eapply derives_trans; [do 1 (apply sepcon_derives; [apply derives_refl |]); apply zc_zfuncs |].
    apply andp_right; [apply prop_right; repeat split; auto | cancel].
  - apply prop_right. intros rho'.
    apply andp_left2. unfold_for_go_lower. simpl. normalize.
    eapply derives_trans; [do 2 (apply sepcon_derives; [apply derives_refl |]); apply zfuncs_za_emp |].
    cancel.
Qed.

Lemma specw_bridge : specw_bridge_stmt.
Proof.
  split; [exact specw_inflate_sub | split; [exact specw_setdict_sub | exact specw_check_sub]].
Qed.

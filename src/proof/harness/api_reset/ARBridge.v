(* Law api_reset: inflateReset's allocator-generic specification of the za port (USpec.inflateReset_uspec) at
   zlib's default allocator (SpecWLib.zc_alloc) gives the main's view ARSpec.inflateReset_specA (a stream
   through inflate_specW: on a raw stream strm->adler may be undefined, the adler cell av_any) and Spec5's
   inflateReset_spec (inflateReset2's body calls it: the cell av_defined).  As SpecWBridge.v does for inflate(). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.SpecWBridge.
Require Import Zlib.proof.harness.api_reset.ARSpec.
Require Zlib.proof.inflate_api.Body5_reset.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* at zc_alloc with the defined adler cell the port's streams are Spec5's *)
Lemma ar_rstream_def: forall gv shs strmp z r,
  @rstream_opt_za (zc_alloc gv) av_defined gv shs strmp z r = rstream_opt gv shs strmp z r.
Proof. reflexivity. Qed.

Lemma ar_reset_post_def: forall gv shs strmp z r f,
  @reset_post_za (zc_alloc gv) av_defined gv shs strmp z r f = reset_post gv shs strmp z r f.
Proof. reflexivity. Qed.

(* a live stream as the reset functions take it (the four fields they only write hold the state's values) *)
Lemma ar_istream_rstream: forall gv shs strmp z L b,
  isptr strmp ->
  @istream_opt_za (zc_alloc gv) (AdlerCell b) gv shs strmp z (Some L) |--
  @rstream_opt_za (zc_alloc gv) (AdlerCell b) gv shs strmp z (rst_of gv (Some L)).
Proof.
  intros gv shs strmp z L b P. unfold istream_opt_za, rstream_opt_za.
  destruct (eq_dec strmp nullval) as [E|_]; [subst; contradiction|].
  unfold istream_za, rstream_za, rst_of, state_mem_za. Intros.
  match goal with H: live_ok L |- _ => destruct H as (SP & SW & _) end.
  pose proof (sw_mode _ SW). pose proof (sw_wbits _ SW).
  apply andp_right; [apply prop_right; split; [assumption | split; [assumption | split; [exact SP | split; lia]]] |].
  rewrite state_rep_v_eq. cancel.
Qed.

Lemma ar_istreamA_opt: forall gv shs strmp z av st,
  isptr strmp -> istreamA gv shs strmp z av st |-- istreamA_opt gv shs strmp z av st.
Proof.
  intros. unfold istreamA_opt. destruct (eq_dec strmp nullval); [subst; contradiction | apply derives_refl].
Qed.

(* za_istreamA for a stream argument that is not Z_NULL *)
Lemma ar_za_istreamA: forall gv shs strmp z st b, isptr strmp -> b = raw_live st ->
  @istream_za (zc_alloc gv) (AdlerCell b) gv shs strmp z st |-- istreamA gv shs strmp z Vundef st.
Proof.
  intros gv shs strmp z st b P E. pose proof (za_istreamA gv shs strmp z st b E) as D.
  unfold istream_opt_za, istreamA_opt in D.
  destruct (eq_dec strmp nullval) as [N|_]; [subst; contradiction | exact D].
Qed.

(* inflateReset keeps a stream raw or not *)
Lemma ar_reset_raw: forall z L, raw_live (Some (thd3 (reset_f z L))) = raw_live (Some L).
Proof.
  intros. unfold reset_f, thd3, raw_live. cbn [snd l_s set_l_s].
  rewrite Zlib.proof.inflate_api.Body5_reset.wrap_reset_full. reflexivity.
Qed.

Lemma ar_reset_subA: funspec_sub (snd (@inflateReset_uspec globals zc_alloc)) (snd inflateReset_specA).
Proof.
  unfold inflateReset_uspec, uspec, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs.
  destruct x2 as [[[[[gv shs] strmp] z] av] L].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : zai => (globals * share * val * zfields * rst * list zev)%type)
      ((gv, raw_live (Some L)) : @zai globals) (gv, shs, strmp, z, rst_of gv (Some L), @nil zev)) (zfuncs gv).
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
  apply andp_right.
  - (* the pure part: the postcondition and the precondition's facts *)
    apply prop_right.
    split; [| split; [split; [| split; [reflexivity | exact I]] | split; [reflexivity | split; [assumption | exact I]]]].
    + intros rho'. apply andp_left2. normalize.
      assert (R: reset_ret strmp (rst_of gv (Some L)) reset_f z = fst3 (reset_f z L))
        by (unfold reset_ret, rs_live; destruct (eq_dec strmp nullval); [subst; contradiction | reflexivity]).
      simpl rst_of in R. rewrite R in *.
      unfold reset_post_za, rs_live. destruct (eq_dec strmp nullval) as [E|_]; [subst; contradiction|].
      replace (fst3 (reset_f z L) =? Z_OK) with true by reflexivity.
      apply andp_right; [apply prop_right; auto |].
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
        [apply (ar_za_istreamA gv shs strmp (snd3 (reset_f z L)) (Some (thd3 (reset_f z L))) (raw_live (Some L))
                   Pstrmp (eq_sym (ar_reset_raw z L))) | apply derives_refl]] |].
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
        [apply derives_refl | apply sepcon_derives; [apply derives_refl | apply zfuncs_za_emp]]] |].
      cancel. apply derives_refl.
    + unfold reset_pre, rs_live. destruct (eq_dec strmp nullval); [subst; contradiction|]. assumption.
  - (* the stream as the port's reset functions take it *)
    sep_apply (ar_istreamA_opt gv shs strmp z av (Some L) ltac:(assumption)).
    sep_apply (istreamA_za gv shs strmp z av (Some L)). unfold cell_of.
    sep_apply (ar_istream_rstream gv shs strmp z L (raw_live (Some L)) ltac:(assumption)).
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
      [apply derives_refl | apply zc_zfuncs]] |].
    cancel. apply derives_refl.
Qed.

Lemma ar_reset_sub5: funspec_sub (snd (@inflateReset_uspec globals zc_alloc)) (snd inflateReset_spec).
Proof.
  unfold inflateReset_uspec, uspec, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs.
  destruct x2 as [[[[gv shs] strmp] z] r].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : zai => (globals * share * val * zfields * rst * list zev)%type)
      ((gv, false) : @zai globals) (gv, shs, strmp, z, r, @nil zev)) (zfuncs gv).
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  apply andp_right.
  - destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
    eapply derives_trans; [do 2 (apply sepcon_derives; [apply derives_refl |]); apply zc_zfuncs |].
    apply andp_right; [apply prop_right; repeat split; auto | cancel; try apply derives_refl].
  - apply prop_right. intros rho'.
    apply andp_left2. unfold_for_go_lower. simpl. normalize.
    eapply derives_trans; [do 3 (apply sepcon_derives; [apply derives_refl |]); apply zfuncs_za_emp |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives;
      [apply (derives_refl' _ _ (ar_reset_post_def gv shs strmp z r reset_f)) | apply derives_refl]] |].
    cancel.
Qed.

Lemma ar_bridge : ar_bridge_stmt.
Proof. split; [exact ar_reset_subA | exact ar_reset_sub5]. Qed.

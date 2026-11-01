(* The body of inflate() against SpecWSelf.inflate_specW_s (any uInt sizes, an output pointer into the stream
   itself allowed).

   As SpecWBridge does for inflate_specW: the port's body against its self variant (BodyWSelfZ.inflate_spec_za_s)
   holds for every allocator and adler cell, hence against their general_intersection in the context of uspecs
   GU_inflate (ULib's semax_body_gi, semax_body_ctx_pw); at zlib's default allocator zc_alloc, choosing the
   adler cell of the stream (av_any on a raw one), that intersection is a funspec_sub of inflate_specW_s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.SpecWSelf.
Require Import Zlib.proof.inflate_api.SpecWBridge.
Require Import Zlib.proof.inflate_api.BodyWSelfZ.
Require Import Zlib.proof.za.inflate_api.ULib.
Require Import Zlib.proof.za.inflate.CasesAllZ.
Require Import Zlib.proof.za.inflate.StepZ.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the self variant of the port's inflate() specification for every allocator of a family A and every adler
   cell, as one specification (the uspec of USpec.v for inflate_spec_za_s); here at zc_alloc *)
Lemma inflate_s_sig {K: Type} (A: K -> zallocator) : forall i : @zai K,
  typesig_of_funspec (snd (@inflate_spec_za_s (zai_a A i) (zai_v i)))
  = typesig_of_funspec (snd (@inflate_spec_za_s za0 av_defined)).
Proof. intros i. unfold inflate_spec_za_s. simpl. reflexivity. Qed.
Lemma inflate_s_cc {K: Type} (A: K -> zallocator) : forall i : @zai K,
  callingconvention_of_funspec (snd (@inflate_spec_za_s (zai_a A i) (zai_v i))) = cc_default.
Proof. intros i. unfold inflate_spec_za_s. simpl. reflexivity. Qed.
Definition inflate_s_uspec : funspec :=
  @uspec globals (fun i => snd (@inflate_spec_za_s (zai_a zc_alloc i) (zai_v i)))
    (typesig_of_funspec (snd (@inflate_spec_za_s za0 av_defined))) cc_default
    (inflate_s_sig zc_alloc) (inflate_s_cc zc_alloc).

(* its body, in the context of uspecs a law's program gives inflate()'s callees *)
Lemma body_inflate_s_u : forall {Espec: OracleKind},
  semax_body Vprog_inflate (@GU_inflate globals zc_alloc) f_inflate (_inflate, inflate_s_uspec).
Proof.
  intros Espec.
  pose proof Zlib.proof.inflate_api.LibProof5.stepf2_hd_proof as HD.
  pose proof (za_step_proof stepf2_mwf3W) as HS.
  unfold inflate_s_uspec, uspec.
  eapply (semax_body_gi _ _ _ _ _ _ _ _ (snd (@inflate_spec_za_s za0 av_defined)) eq_refl).
  - apply semax_body_pair; [reflexivity |].
    exact (@body_inflate_s_za za0 av_defined (za_cases_proof _ _) HS HD Espec).
  - intros i. destruct (proj1 (za_ulib _ zc_alloc) i) as (S_inf & S_fast & S_uw & S_chk & _).
    eapply semax_body_ctx_pw.
    + apply semax_body_pair; [reflexivity |].
      exact (@body_inflate_s_za (zai_a zc_alloc i) (zai_v i) (za_cases_proof _ _) HS HD Espec).
    + unfold Gprog_inflate3_za, Gprog_cases3_za, GU_inflate. cbn [app].
      pw_refl. pw_refl. pw_sub S_fast. pw_refl. pw_refl. pw_refl. pw_sub S_chk. pw_sub S_uw.
      apply Forall2_nil.
Qed.

(* at the member (zc_alloc gv, the stream's adler cell): SpecWBridge.specw_inflate_sub with the self output *)
Lemma inflate_s_uspec_sub : funspec_sub inflate_s_uspec (snd inflate_specW_s).
Proof.
  unfold inflate_s_uspec, uspec, general_intersection. simpl snd.
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

Lemma body_inflate_ws : body_inflate_ws_stmt.
Proof.
  intros Espec.
  eapply semax_body_funspec_sub; [exact body_inflate_s_u | exact inflate_s_uspec_sub |].
  apply compute_list_norepet_e; reflexivity.
Qed.

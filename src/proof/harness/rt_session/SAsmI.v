(* Law rt_session: inflate()'s body against SMainStmt.inflate_fs_ses, the intersection of SpecW.inflate_specW
   and RTH9Spec.inflate_spec9, at inflate.c's compspecs.

   The two shared bodies of inflate() are proved in different contexts: the allocator-generic port's
   (SpecWLib.specw_lib_stmt: USpec.GU_inflate, with the port's specifications of inflate_fast, updatewindow and
   inflateStateCheck at zlib's allocator) and RTH9's (RTH8Spec.Gprog_inflate8 RTH9Fast.fast9: inflate_fast at
   fast9, Callees3's updatewindow_spec3 and Callees' inflateStateCheck_spec).  The law has one specification per
   function, so inflate_fast and updatewindow get the intersections of their two specifications ([fast_spec_ses],
   [upd_spec_ses]: general intersections over bool, with their two shared bodies) and inflateStateCheck the
   port's (stronger than Callees' by SpecWBridge).  [GI] is inflate()'s context with these specifications; both
   bodies of inflate() move into it, and their intersection is [body_inflate_ses]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Assembly.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Zlib.proof.inffast.Body.
Require Zlib.proof.inflate.Callees Zlib.proof.inflate.Callees3 Zlib.proof.inflate.Callees5.
Require Zlib.proof.inflate.BodyUpdatewindow Zlib.proof.inflate.BodyUw5.
Require Zlib.proof.inflate_api.SpecWLib Zlib.proof.inflate_api.SpecWLibProof.
Require Zlib.proof.roundtrip.RTH8Spec Zlib.proof.roundtrip.RTH9Spec Zlib.proof.roundtrip.RTH9Fast.
Require Zlib.proof.roundtrip.RTH9Asm Zlib.proof.roundtrip.RTH9Hdr Zlib.proof.roundtrip.RTH9Exit
        Zlib.proof.roundtrip.RTH9Pro.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.za.inflate_api.ULib.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
#[local] Existing Instance Zlib.units.Inflate.CS.

Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.

(* the signature of a specification proved of a body is the function's *)
Lemma sig_of_body {cs : compspecs} V G f i phi :
  @semax_body V G cs f (i, phi) -> typesig_of_funspec phi = (map snd (fn_params f), fn_return f).
Proof.
  destruct phi as [[ts t] cc A P Q Pne Qne]. intros [H1 [H2 _]]. simpl in *. subst. reflexivity.
Qed.

(* inflate_fast: the port's specification at zlib's allocator (true) and RTH9's fast9 (false) *)
Definition fast_fam (b : bool) : funspec :=
  if b then snd (@ZU.inflate_fast_uspec globals SWL.zc_alloc) else Zlib.proof.roundtrip.RTH9Fast.fast9.

Lemma fast_fam_sig : forall b, typesig_of_funspec (fast_fam b) =
  (map snd (fn_params Zlib.inffast.code.f_inflate_fast), fn_return Zlib.inffast.code.f_inflate_fast).
Proof.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL _].
  destruct (ZL NullExtension.Espec) as (_ & U_fast & _).
  intros [|]; simpl fast_fam.
  - exact (sig_of_body _ _ _ _ _ U_fast).
  - exact (sig_of_body _ _ _ _ _ (@Zlib.proof.roundtrip.RTH9Fast.fast9_body NullExtension.Espec)).
Qed.

Lemma fast_fam_cc : forall b, callingconvention_of_funspec (fast_fam b) = cc_default.
Proof. intros [|]; reflexivity. Qed.

Definition fast_fs_ses : funspec := general_intersection fast_fam fast_fam_sig fast_fam_cc.
Definition fast_spec_ses : ident * funspec := (Zlib.inffast.code._inflate_fast, fast_fs_ses).

Lemma fast_ses_sub :
  funspec_sub fast_fs_ses (snd (@ZU.inflate_fast_uspec globals SWL.zc_alloc)) /\
  funspec_sub fast_fs_ses Zlib.proof.roundtrip.RTH9Fast.fast9.
Proof.
  split; apply funspec_sub_iff.
  - exact (generalintersection_sub _ fast_fam_sig fast_fam_cc _ eq_refl true).
  - exact (generalintersection_sub _ fast_fam_sig fast_fam_cc _ eq_refl false).
Qed.

(* updatewindow: the port's specification at zlib's allocator (true) and Callees3's (false) *)
Definition upd_fam (b : bool) : funspec :=
  if b then snd (@ZU.updatewindow_uspec globals SWL.zc_alloc) else snd Zlib.proof.inflate.Callees3.updatewindow_spec3.

Lemma upd_fam_sig : forall b, typesig_of_funspec (upd_fam b) =
  (map snd (fn_params f_updatewindow), fn_return f_updatewindow).
Proof.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL _].
  destruct (ZL NullExtension.Espec) as (_ & _ & U_upd & _).
  intros [|]; simpl upd_fam.
  - exact (sig_of_body _ _ _ _ _ U_upd).
  - exact (sig_of_body _ _ _ _ _ (@Zlib.proof.inflate.BodyUw5.body_updatewindow5 NullExtension.Espec)).
Qed.

Lemma upd_fam_cc : forall b, callingconvention_of_funspec (upd_fam b) = cc_default.
Proof. intros [|]; reflexivity. Qed.

Definition upd_fs_ses : funspec := general_intersection upd_fam upd_fam_sig upd_fam_cc.
Definition upd_spec_ses : ident * funspec := (_updatewindow, upd_fs_ses).

Lemma upd_ses_sub :
  funspec_sub upd_fs_ses (snd (@ZU.updatewindow_uspec globals SWL.zc_alloc)) /\
  funspec_sub upd_fs_ses (snd Zlib.proof.inflate.Callees3.updatewindow_spec3).
Proof.
  split; apply funspec_sub_iff.
  - exact (generalintersection_sub _ upd_fam_sig upd_fam_cc _ eq_refl true).
  - exact (generalintersection_sub _ upd_fam_sig upd_fam_cc _ eq_refl false).
Qed.

(* the bodies of inflate_fast and updatewindow against the intersections *)
Lemma body_fast_ses {Espec : OracleKind} :
  semax_body Zlib.proof.inffast.Body.Vprog_fast Zlib.proof.inffast.Body.Gprog_fast
    Zlib.inffast.code.f_inflate_fast fast_spec_ses.
Proof.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL _].
  destruct (ZL Espec) as (_ & U_fast & _).
  pose proof (@Zlib.proof.roundtrip.RTH9Fast.fast9_body Espec) as B9.
  apply (Zlib.proof.za.inflate_api.ULib.semax_body_gi _ _ _ _ _ _ _ _ _ (fast_fam_sig false) B9).
  intros [|]; simpl fast_fam.
  - exact U_fast.
  - exact B9.
Qed.

Lemma body_upd_ses {Espec : OracleKind} :
  semax_body Zlib.proof.inflate.Callees5.Vprog_inflate Zlib.proof.inflate.BodyUpdatewindow.Gprog_updatewindow
    f_updatewindow upd_spec_ses.
Proof.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL _].
  destruct (ZL Espec) as (_ & _ & U_upd & _).
  pose proof (@Zlib.proof.inflate.BodyUw5.body_updatewindow5 Espec) as B3.
  apply (Zlib.proof.za.inflate_api.ULib.semax_body_gi _ _ _ _ _ _ _ _ _ (upd_fam_sig false) B3).
  intros [|]; simpl upd_fam.
  - assert (U : semax_body Zlib.proof.inflate.Callees5.Vprog_inflate
                  Zlib.proof.inflate.BodyUpdatewindow.Gprog_updatewindow f_updatewindow
                  (@ZU.updatewindow_uspec globals SWL.zc_alloc)).
    { apply (semax_body_lift _ _ _ _ _ _ _ U_upd).
      + apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity.
      + apply Forall_cons; [reflexivity | apply Forall_nil].
      + apply compute_list_norepet_e; vm_compute; reflexivity. }
    exact U.
  - exact B3.
Qed.

(* inflate()'s context in the law *)
Definition GI : funspecs :=
  [Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.crc32.Spec.crc32_spec;
   fast_spec_ses; Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS));
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; upd_spec_ses].

(* RTH9's context, listed *)
Definition G9 : funspecs :=
  [Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.crc32.Spec.crc32_spec;
   (Zlib.inffast.code._inflate_fast, Zlib.proof.roundtrip.RTH9Fast.fast9);
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS));
   Zlib.proof.inflate.Callees.inflateStateCheck_spec; Zlib.proof.inflate.Callees3.updatewindow_spec3].

Lemma G9_eq : Zlib.proof.roundtrip.RTH8Spec.Gprog_inflate8 Zlib.proof.roundtrip.RTH9Fast.fast9 = G9.
Proof.
  unfold Zlib.proof.roundtrip.RTH8Spec.Gprog_inflate8, Zlib.proof.inflate.Callees3.Gprog_inflate3,
    Zlib.proof.inflate.Callees3.Gprog_cases3, G9.
  cbn [map app fst].
  repeat match goal with |- context [ident_eq ?a ?b] =>
    let E := fresh "E" in
    destruct (ident_eq a b) as [E|E];
    [ try (exfalso; lazy in E; discriminate) | try (exfalso; apply E; lazy; reflexivity) ]
  end.
  reflexivity.
Qed.

(* the moves of the port's (side true) and RTH9's (side false) callee specifications to GI, chosen by the callee's
   identifier (a failing comparison of two different specifications is slow) *)
Ltac gi_sub_at side X :=
  let x := eval compute in X in
  let fa := eval compute in Zlib.inffast.code._inflate_fast in
  let uw := eval compute in _updatewindow in
  let sc := eval compute in _inflateStateCheck in
  tryif constr_eq x fa then
    (tryif constr_eq side true then exact (proj1 fast_ses_sub) else exact (proj2 fast_ses_sub))
  else tryif constr_eq x uw then
    (tryif constr_eq side true then exact (proj1 upd_ses_sub) else exact (proj2 upd_ses_sub))
  else tryif constr_eq x sc then
    (tryif constr_eq side true then apply funspec_sub_refl
     else exact (proj2 (proj2 Zlib.proof.inflate_api.SpecWBridge.specw_bridge)))
  else apply funspec_sub_refl.

Ltac gi_ctx side :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (lazymatch type of E with
          | (if Memory.EqDec_ident _ ?X then _ else _) = _ =>
            if_tac in E; [ inv E; eexists; split; [ reflexivity | gi_sub_at side X ] | ]
          end);
  try discriminate.

Lemma ctx_GU_GI : ctx_sub (@ZU.GU_inflate globals SWL.zc_alloc) GI.
Proof. gi_ctx true. Qed.

Lemma ctx_G9_GI : ctx_sub G9 GI.
Proof. gi_ctx false. Qed.

(* a body moves to a stronger context of the same unit *)
Lemma semax_body_ctx {cs : compspecs} (V : varspecs) (G1 G2 : funspecs) f spec :
  @semax_body V G1 cs f spec ->
  complete_vars_b cs f = true ->
  forallb (fun x => match initial_world.find_id (fst x) V with Some t => eqb_type t (snd x) | None => false end)
    V = true ->
  compute_list_norepet (map fst V ++ map fst G1) = true ->
  compute_list_norepet (map fst V ++ map fst G2) = true ->
  ctx_sub G1 G2 ->
  @semax_body V G2 cs f spec.
Proof.
  intros B C HV L1 L2 S.
  apply (semax_body_move V V G1 G2 f spec B cspecs_sub_refl); auto.
  - unfold complete_vars_b in C. rewrite forallb_forall in C. rewrite Forall_forall. auto.
  - apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; exact HV.
  - apply compute_list_norepet_e; exact L1.
  - apply compute_list_norepet_e; exact L2.
Qed.

(* inflate()'s body against the intersection, in GI *)
Lemma body_inflate_ses {Espec : OracleKind} :
  semax_body Zlib.proof.inflate.Callees5.Vprog_inflate GI f_inflate inflate_spec_ses.
Proof.
  destruct Zlib.proof.inflate_api.SpecWLibProof.specw_lib as [ZL BR].
  destruct (ZL Espec) as (U_inflate & _).
  assert (BW : semax_body Zlib.proof.inflate.Callees5.Vprog_inflate GI f_inflate
                 Zlib.proof.inflate_api.SpecW.inflate_specW).
  { apply (semax_body_ctx _ (@ZU.GU_inflate globals SWL.zc_alloc)); [ | vm_compute; reflexivity | vm_compute; reflexivity
                                            | vm_compute; reflexivity | vm_compute; reflexivity | exact ctx_GU_GI ].
    apply (semax_body_funspec_sub U_inflate (proj1 BR)).
    apply compute_list_norepet_e; vm_compute; reflexivity. }
  assert (B9 : semax_body Zlib.proof.inflate.Callees5.Vprog_inflate GI f_inflate
                 Zlib.proof.roundtrip.RTH9Spec.inflate_spec9).
  { apply (semax_body_ctx _ G9); [ | vm_compute; reflexivity | vm_compute; reflexivity
                                 | vm_compute; reflexivity | vm_compute; reflexivity | exact ctx_G9_GI ].
    rewrite <- G9_eq.
    exact (@Zlib.proof.roundtrip.RTH9Asm.body9_of Zlib.proof.roundtrip.RTH9Fast.fast9
             Zlib.proof.roundtrip.RTH9Fast.fast9_sub_hl Zlib.proof.roundtrip.RTH9Fast.rth9_cases
             Zlib.proof.roundtrip.RTH9Hdr.cases9h_proof Zlib.proof.roundtrip.RTH9Exit.exit_part9
             Zlib.proof.roundtrip.RTH9Pro.pro_part9 Espec). }
  exact (semax_body_binaryintersection'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BW B9 eq_refl eq_refl).
Qed.

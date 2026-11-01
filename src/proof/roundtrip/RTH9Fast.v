(* The specification of inflate_fast for inflate()'s body against RTH9Spec.inflate_spec9, with its body and the
   headless switch cases of the modes after the header for calls of any uInt size (RTH9Defs.fast9_stmt).

   The cases and inflate_fast's body come from the generated port src/proof/hlza/ (docs/port-hl/cfg_hlza.py): the
   allocator-generic, wide proofs of src/proof/za/ with the application's header replaced by the headless port's
   (HlLoop.head_part_hl).  At zlib's allocator (SpecWLib.zc_alloc gv) and a defined strm->adler (ZAV.av_defined) the
   port's memory and loop states are the narrow headless ones of src/proof/hl/ (by conversion), and its machine
   invariant mwf3_za is InvW.mwf3W (StepZ.mwf3_za_mwf3W).

   [fast9] is the intersection, over the globals g, of the port's inflate_fast specification at zc_alloc g: it is
   stronger than each of them (so the port's cases move into Delta_cases9 fast9) and than the narrow headless
   inflate_fast_spec3_hl (choosing g = f_gv F; a narrow machine is a wide one). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTH9Defs.
Require Import Zlib.proof.roundtrip.RTH8Fast.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.InvQ5.
Require Import Zlib.proof.inffast.Body.
Require Zlib.proof.inflate_api.SpecWLib.
Require Zlib.proof.za.inflate_api.ULib.
Require Zlib.proof.za.inflate.StepZ.
Require Zlib.proof.hlza.za.inffast.HzBodyF5.
Require Zlib.proof.hlza.za.inflate.HzCasesHdZ.
Require Zlib.proof.hlza.za.inflate.HzCasesTyZ.
Require Zlib.proof.hlza.za.inflate.HzCasesStZ.
Require Zlib.proof.hlza.za.inflate.HzCasesTlZ.
Require Zlib.proof.hlza.za.inflate.HzCasesClZ.
Require Zlib.proof.hlza.za.inflate.HzCasesLenZ.
Require Zlib.proof.hlza.za.inflate.HzCasesLdZ.
Require Zlib.proof.hlza.za.inflate.HzCasesDmZ.
Require Zlib.proof.hlza.za.inflate.HzCasesCkZ.
Require Zlib.proof.hlza.za.inflate.HzCasesEndZ.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module HZ3 := Zlib.proof.hlza.za.inflate.HzCallees3.
Module HZK := Zlib.proof.hlza.za.inflate.HzCaseKit5.

(* ---------------------------------------------------------------------------------------------- *)
(* the headless switch cases of the port, for any allocator and adler cell                         *)

(* the cases of the modes DICTID .. SYNC chained backwards along the fallthroughs (as round 1's RTH8CasesNH.v) *)
Lemma hz_cases_nh (ZA : Zlib.proof.zutil.ZAlloc.zallocator) (ZAV : Zlib.proof.za.inflate.ZAV.adler_cell)
    {Espec: OracleKind} (F: frame) :
  frame_ok5 F -> forall i, (9 <= i < 32)%nat -> @HZK.case_ok5_za_hz ZA ZAV Espec F (IM.HEAD + Z.of_nat i) i.
Proof.
  intros HF.
  pose proof cover3_proof as C3. pose proof fixed_ok5_proof as FX.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesDmZ.za_cases5_DM_hz ZA ZAV Espec F HF) as [DM1 MAT].
  pose proof (DM1 MAT) as DEX.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesLdZ.za_cases5_LD_hz ZA ZAV Espec F HF) as [LD1 LD2].
  pose proof (LD2 DEX) as DST. pose proof (LD1 DST) as LXT.
  pose proof (@Zlib.proof.hlza.za.inflate.HzCasesLenZ.za_cases5_LEN_next_hz ZA ZAV Espec F HF LXT) as LN.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesEndZ.za_cases5_end_hz ZA ZAV Espec F HF)
    as (LEN_ & LT & DN & BD & MM & SY).
  pose proof (LEN_ LN) as LN_.
  pose proof (@Zlib.proof.hlza.za.inflate.HzCasesClZ.za_cases5_CL_hz ZA ZAV Espec F HF C3 LN_) as CL.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesTlZ.za_cases5_TL_hz ZA ZAV Espec F HF C3) as [TL1 TL2].
  pose proof (TL2 CL) as LL. pose proof (TL1 LL) as TB.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesStZ.za_cases5_ST_hz ZA ZAV Espec F HF) as (ST1 & ST2 & CP).
  pose proof (ST2 CP) as CP_. pose proof (ST1 CP_) as STD.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesTyZ.za_cases5_TY_hz ZA ZAV Espec F HF FX) as [TY TYD].
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesHdZ.za_cases5_HD_hz ZA ZAV Espec F HF) as (HD2 & HD3).
  pose proof (HD3 TY) as DCT. pose proof (HD2 DCT) as DID.
  destruct (@Zlib.proof.hlza.za.inflate.HzCasesCkZ.za_cases5_CK_hz ZA ZAV Espec F HF) as [CK1 CK2].
  pose proof (CK2 DN) as LG. pose proof (CK1 LG) as CK.
  intros i Hi.
  do 32 (destruct i as [|i]; [first [exfalso; lia | eassumption] | ]).
  exfalso; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the specification [fast9]                                                                      *)

(* the port's specification at zlib's allocator for the globals g, strm->adler defined *)
Definition fast9_member (g : globals) : funspec :=
  snd (@HZ3.inflate_fast_spec3_za_hz (SpecWLib.zc_alloc g) Zlib.proof.za.inflate.ZAV.av_defined).

Lemma fast9_sig : forall g, typesig_of_funspec (fast9_member g) = typesig_of_funspec (fast9_member (fun _ => Vundef)).
Proof. intros g. unfold fast9_member, HZ3.inflate_fast_spec3_za_hz. simpl. reflexivity. Qed.

Lemma fast9_cc : forall g, callingconvention_of_funspec (fast9_member g) = cc_default.
Proof. intros g. unfold fast9_member, HZ3.inflate_fast_spec3_za_hz. simpl. reflexivity. Qed.

Definition fast9 : funspec := general_intersection fast9_member fast9_sig fast9_cc.

(* [fast9] is stronger than each member *)
Lemma fast9_sub_member : forall g, funspec_sub fast9 (fast9_member g).
Proof. intros g. apply funspec_sub_iff. exact (generalintersection_sub _ fast9_sig fast9_cc _ eq_refl g). Qed.

(* the body of inflate_fast against [fast9]: the port's body at every member *)
Lemma fast9_body {Espec: OracleKind} :
  semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast (_inflate_fast, fast9).
Proof.
  unfold fast9.
  eapply (ULib.semax_body_gi _ _ _ _ _ _ _ _ (fast9_member (fun _ => Vundef)) eq_refl).
  - apply ULib.semax_body_pair; [reflexivity |].
    exact (@Zlib.proof.hlza.za.inffast.HzBodyF5.body_inflate_fast5_za_hz
             (SpecWLib.zc_alloc (fun _ => Vundef)) Zlib.proof.za.inflate.ZAV.av_defined Espec).
  - intros g. apply ULib.semax_body_pair; [reflexivity |].
    exact (@Zlib.proof.hlza.za.inffast.HzBodyF5.body_inflate_fast5_za_hz
             (SpecWLib.zc_alloc g) Zlib.proof.za.inflate.ZAV.av_defined Espec).
Qed.

(* the port's memory at zlib's allocator of the frame's globals, strm->adler defined, is the narrow headless one *)
Lemma hz_mem_rep F m :
  @Zlib.proof.hlza.za.inflate.HzLoop.mem_rep_za_hz (SpecWLib.zc_alloc (f_gv F)) Zlib.proof.za.inflate.ZAV.av_defined F m =
  mem_rep_hl F m.
Proof. reflexivity. Qed.

(* a narrow machine for inflate_fast is a wide one *)
Lemma fast_ok_hz m : fast_ok m -> HZ3.fast_ok_za_hz m.
Proof.
  intros [W T]. split; [| exact T].
  apply Zlib.proof.za.inflate.StepZ.mwf_za_mwfW, Zlib.proof.inflate.InvW.mwf_mwfW. exact W.
Qed.

(* [fast9] is stronger than the narrow headless specification: the member at the frame's globals *)
Lemma fast9_sub_hl : funspec_sub fast9 (snd inflate_fast_spec3_hl).
Proof.
  unfold fast9, general_intersection. simpl snd.
  split; [split; reflexivity |].
  intros ts2 x2 gargs. destruct x2 as [F m].
  eapply derives_trans, fupd_intro.
  Exists ts2 (existT (fun _ : globals => (frame * mst)%type) (f_gv F) (F, m)) emp.
  unfold iPre, iPost, generalSUMArgs, generalSUM, intersectionPRE, intersectionPOST. simpl.
  apply andp_right.
  - destruct gargs as [g args]. unfold_for_go_lower. simpl. normalize.
    rewrite hz_mem_rep.
    apply andp_right; [apply prop_right; repeat match goal with |- _ /\ _ => split end;
      first [apply fast_ok_hz; assumption | assumption | auto] | cancel].
  - apply prop_right. intros rho'.
    apply andp_left2. unfold_for_go_lower. simpl. normalize.
    rewrite hz_mem_rep. cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the port's cases in the context of [fast9]                                                    *)

(* the port's context at any member is a sub-context of Delta_cases9 fast9 *)
Lemma hz_delta_sub (g : globals) :
  tycontext_sub (@Zlib.proof.hlza.za.inflate.HzCallees5.Delta_cases5_za_hz (SpecWLib.zc_alloc g)
                   Zlib.proof.za.inflate.ZAV.av_defined)
                (Delta_cases9 fast9).
Proof.
  unfold Zlib.proof.hlza.za.inflate.HzCallees5.Delta_cases5_za_hz, Delta_cases9. apply rth8_tsub.
  unfold HZ3.Gprog_cases3_za_hz, Gprog_cases9, Gprog_cases3. cbn [map].
  (* the name tests are decided by lazy reduction, which never unfolds the funspecs *)
  repeat match goal with |- context [ident_eq ?a ?b] =>
    let E := fresh "E" in
    destruct (ident_eq a b) as [E|E]; [ | ];
    [ try (exfalso; lazy in E; discriminate) | try (exfalso; apply E; lazy; reflexivity) ]
  end.
  do 2 (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]).
  apply Forall2_cons; [split; [change (_inflate_fast = _inflate_fast); reflexivity | exact (fast9_sub_member g)] | ].
  repeat (apply Forall2_cons; [split; [reflexivity | apply funspec_sub_refl] | ]). apply Forall2_nil.
Qed.

Lemma rth9_cases : cases_nh9 fast9.
Proof.
  intros Espec F HF i Hi m HM HL W.
  pose proof (hz_cases_nh (SpecWLib.zc_alloc (f_gv F)) Zlib.proof.za.inflate.ZAV.av_defined F HF i Hi m HM HL
                (proj2 (Zlib.proof.za.inflate.StepZ.mwf3_za_mwf3W m) W)) as S.
  eapply semax_Delta_subsumption; [apply hz_delta_sub | exact S].
Qed.

Lemma rth9_fast : fast9_stmt.
Proof.
  exists fast9. split; [reflexivity |]. split; [intros Espec; exact fast9_body |].
  split; [exact fast9_sub_hl | exact rth9_cases].
Qed.

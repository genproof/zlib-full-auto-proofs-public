(* Law api_reset, the theory: one inflate() call on each of two streams related at a call boundary (IRinv), for
   calls of up to 2^32-1 bytes: x_inflate_reset's IRRunLoop.irl_loop and IRRunCall.irc_call under the wide
   machine invariant (StepW.stepf2_mwf3W).  Only the lemmas whose statements mention the narrow invariant
   (Inv3.mwf3) are restated here; the exit (IRRunLoop.irl_exit, irl_lf), the initial relation
   (IRRunCall.irc_kr0) and the other one-stream facts are x_inflate_reset's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARSimDefs.
Require Import Zlib.proof.harness.inflate_reset.IRPassNs.
Require Import Zlib.proof.harness.inflate_reset.IRPassOut.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Require Import Zlib.proof.inflate_api.StepInv5Kit.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.harness.inflate_pieces.Theory.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* One-stream facts of one pass                                                                   *)

(* IRPassOut.irps_out without the machine invariant (its proof does not use it): `out` stays between `left`
   and avail_out on entry, and HEAD has no output *)
Lemma arc_out (flush: Z) (m: mst) :
  m_leave m = 0 -> irp_out m ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => irp_out m' | IRet _ _ => True end.
Proof.
  intros Hlv Hout.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply irp_c_HEAD; auto.
  - pose proof (stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m']; [|exact I].
    unfold wgood, wrel in G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
    unfold irp_out, m_left, m_mode in *. destruct Hout as (O1 & O2 & O3).
    split; [lia|]. split; [lia|]. intros; contradiction.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop on both machines (IRRunLoop.irl_loop under mwf3W)                                    *)

Definition arc_post (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (oa ob: iout) : Prop :=
  match oa, ob with
  | IBrk ma', IBrk mb' =>
      Kr W0 wrap src pos inp aout ma' mb' /\ mwf3W ma' /\ mwf3W mb' /\ m_leave mb' = 1 /\ irp_out mb' /\
      m_mode mb' <> SYNC
  | IRet ra ma', IRet rb mb' =>
      ra = rb /\ Kr W0 wrap src pos inp aout ma' mb' /\ mwf3W ma' /\ mwf3W mb' /\
      (ra = Z_MEM_ERROR \/
       (ra = Z_NEED_DICT /\ m_mode mb' = DICT /\ m_sow ma' = Zlength (m_ow ma') /\
        m_sow mb' = Zlength (m_ow mb')))
  | _, _ => False
  end.

Lemma arc_loop : sgroup_okW (fun _ => True) ->
  forall W0 wrap src pos inp aout flush ma oa,
  ir_ctx src pos inp -> loop2 flush lenfix_list distfix_list ma oa ->
  forall mb ob, loop2 flush lenfix_list distfix_list mb ob ->
  Kr W0 wrap src pos inp aout ma mb -> mwf3W ma -> mwf3W mb -> m_leave mb = 0 -> irp_out mb ->
  m_mode mb <> SYNC ->
  arc_post W0 wrap src pos inp aout oa ob.
Proof.
  intros ST W0 wrap src pos inp aout flush ma oa C LA.
  induction LA as [ma r ma' E | ma ma' E L1 | ma ma' oa E L1 LA IH];
    intros mb ob LB K Wa Wb L0 Ob NS;
    pose proof (irl_leave_eq _ _ _ _ _ _ _ _ K) as LE;
    pose proof (ST W0 wrap src pos inp aout flush ma mb C K Wa Wb L0 I) as P;
    pose proof (stepf2_mwf3W flush ma Wa ltac:(congruence)) as Wa';
    pose proof (stepf2_mwf3W flush mb Wb L0) as Wb';
    pose proof (arc_out flush mb L0 Ob) as Ob';
    pose proof (irps_nosync flush mb (sw_mode _ (mwW_s _ (proj1 Wb))) NS) as Gb;
    pose proof (irps_nosync flush ma (sw_mode _ (mwW_s _ (proj1 Wa)))
                  ltac:(rewrite (irl_mode_eq _ _ _ _ _ _ _ _ K); exact NS)) as Ga;
    rewrite E in P, Wa', Ga;
    destruct (stepf2 flush lenfix_list distfix_list mb) as [mb'|rb mb'] eqn:Eb; cbn in P; try contradiction.
  - (* return *)
    destruct P as [-> K'].
    inversion LB; subst; try congruence.
    match goal with H: stepf2 _ _ _ mb = IRet _ _ |- _ => rewrite Eb in H; inversion H; subst end.
    cbn. split; [reflexivity|]. split; [exact K'|]. split; [exact Wa'|]. split; [exact Wb'|].
    cbn in Ga, Gb. destruct Gb as [Gb|(Gb1 & Gb2 & Gb3)]; [left; exact Gb|].
    destruct Ga as [Ga|(Ga1 & Ga2 & Ga3)]; [left; exact Ga|].
    right. auto.
  - (* leave *)
    assert (L1': m_leave mb' = 1) by (rewrite <- (irl_leave_eq _ _ _ _ _ _ _ _ P); exact L1).
    inversion LB; subst; try congruence;
      match goal with H: stepf2 _ _ _ mb = _ |- _ => rewrite Eb in H; inversion H; subst end.
    cbn in Gb |- *. auto 10.
  - (* next *)
    assert (L1': m_leave mb' <> 1) by (rewrite <- (irl_leave_eq _ _ _ _ _ _ _ _ P); exact L1).
    assert (L0': m_leave mb' = 0) by (pose proof (mwW_leave _ (proj1 Wb')); lia).
    inversion LB; subst; try congruence;
      match goal with H: stepf2 _ _ _ mb = _ |- _ => rewrite Eb in H; inversion H; subst end.
    eapply IH; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head (IRRunCall.irc_init for calls of up to 2^32-1 bytes)              *)

Lemma arc_init (z: zfields) (L: live) (ni no: val) (ain aout: Z) (inp: list Z) :
  live_ok L -> zf_ok z -> swfW (l_s L) -> 0 <= ain <= Int.max_unsigned -> 0 <= aout <= Int.max_unsigned ->
  Zlength inp <= Int.max_unsigned -> bytes_ok inp ->
  let m0 := m_init (ir_call z ni ain no aout) L inp in
  mwf3W m0 /\ m_leave m0 = 0 /\ irp_out m0.
Proof.
  intros LV ZF SW AI AO ZI BI. cbv zeta.
  split; [|split; [reflexivity|]].
  - apply Zlib.proof.harness.inflate_pieces.Theory.pc_m_init_mwf3W; try assumption.
    destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zf_ok, ir_call.
    exact (conj AI (conj AO (conj Z3 (conj Z4 (conj Z5 Z6))))).
  - unfold irp_out, m_left, m_mode; cbn. split; [lia|]. split; [lia|]. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

Lemma ar_call : ar_call_stmt.
Proof.
  intros ST W0 wrap src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa rb zb' stb' owb
    IV LVa LVb ZFa ZFb SWa SWb SNa SNb P0 A0 PA BS AO IBa IBb EI RA NA RB NB.
  destruct (irc_ctx src pos ain P0 (proj1 A0) PA BS) as (C & LI & BI). rewrite <- EI in C, LI, BI.
  destruct RA as [(BD & _) | (_ & L0 & o & resa & winpa & EL & EO & RUN & SNX & -> & -> & -> & _ & ->)];
    [exfalso; exact (irc_notbad strma _ La iba oa SNa IBa BD)|].
  destruct RB as [(BD & _) | (_ & L1 & o1 & resb & winpb & EL1 & EO1 & RUNb & SNXb & -> & -> & -> & _ & ->)];
    [exfalso; exact (irc_notbad strmb _ Lb ibb ob SNb IBb BD)|].
  inversion EL; subst L0. inversion EO; subst o. inversion EL1; subst L1. inversion EO1; subst o1.
  clear EL EO EL1 EO1.
  destruct RUN as (ota & LPa & RESa). destruct RUNb as (otb & LPb & RESb).
  set (ma0 := m_init (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) La inp) in *.
  set (mb0 := m_init (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) Lb inp) in *.
  assert (ZI: Zlength inp <= Int.max_unsigned) by lia.
  destruct (arc_init za La (in_ptr iba 0) (out_ptr oa 0) ain aout inp LVa ZFa SWa A0 AO ZI BI) as (Wa0 & La0 & Oa0).
  destruct (arc_init zb Lb (in_ptr ibb 0) (out_ptr ob 0) ain aout inp LVb ZFb SWb A0 AO ZI BI) as (Wb0 & Lb0 & Ob0).
  pose proof (irc_kr0 W0 wrap src pos za La zb Lb (in_ptr iba 0) (out_ptr oa 0) (in_ptr ibb 0) (out_ptr ob 0)
                ain aout inp IV) as K0.
  assert (NS0: m_mode mb0 <> SYNC).
  { unfold m_mode, mb0. rewrite irc_m0_s. apply (irc_s0_keep (l_s Lb)). exact (iv_sync _ _ _ _ _ _ _ _ IV). }
  pose proof (arc_loop ST W0 wrap src pos inp aout flush ma0 ota C LPa mb0 otb LPb K0 Wa0 Wb0 Lb0 Ob0 NS0) as LR.
  destruct IV as [IVr IVw IVh IVwa IVwb IVhd IVs IVtin IVtout IVmsg IVdt IVad].
  destruct ota as [ma' | ra' ma']; destruct otb as [mb' | rb' mb']; cbn in LR; try contradiction.
  - (* the loop broke: inf_leave on both *)
    destruct LR as (K & Wa & Wb & Lv & O & NS).
    destruct RESa as [_ _ | ]; [cbn in NA; congruence|].
    destruct RESb as [_ _ | ]; [cbn in NB; congruence|].
    destruct (irl_exit W0 wrap src pos inp aout flush ma' mb' K O)
      as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
    destruct (irl_lf flush ma') as (_ & _ & F3 & F4 & F5 & _ & F7 & F8 & _).
    destruct (irc_exit1 flush ma') as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct (irc_exit1 flush mb') as (H1 & H2 & H3 & H4 & H5 & H6).
    destruct (kr_rel _ _ _ _ _ _ _ _ K) as [_ Hinp Haout Hnx How Hhold Hbits _ _ _ _ _ _ _ _ _ _].
    pose proof (kr_inp _ _ _ _ _ _ _ _ K) as KI. pose proof (kr_aout _ _ _ _ _ _ _ _ K) as KA.
    pose proof (mwW_ow _ (proj1 Wa)) as OWa.
    eexists; eexists; split; [reflexivity|]. split; [reflexivity|].
    cbn [z_after zf_ai zf_ao zf_tin zf_tout zf_msg zf_dt zf_adler l_s].
    rewrite F3, F4, F5, F7, F8 in *.
    split; [exact E1|]. split; [rewrite E3, E7; reflexivity|]. split; [rewrite E4, E8; reflexivity|].
    split; [rewrite <- F5, <- E5, F5; reflexivity|].
    split; [rewrite Haout, KA; lia|].
    split; [rewrite Hinp, KI, LI; split; lia|].
    split; [rewrite Haout, KA in *; pose proof (Zlength_nonneg (m_ow ma')); lia|].
    constructor; cbn [l_s].
    + exact E12.
    + rewrite H2. exact (kr_wrap _ _ _ _ _ _ _ _ K).
    + rewrite H3. exact (kr_head _ _ _ _ _ _ _ _ K).
    + rewrite G4. exact (kr_wa _ _ _ _ _ _ _ _ K).
    + rewrite H4. exact (kr_wb _ _ _ _ _ _ _ _ K).
    + intros W HD. rewrite H1 in HD. destruct (kr_hd _ _ _ _ _ _ _ _ K W HD) as (HH & _).
      rewrite H5, H6. rewrite Hinp, KI, LI, Hnx. replace (pos + (ain - (ain - m_nx mb'))) with (pos + m_nx mb') by lia.
      exact HH.
    + rewrite H1. exact NS.
    + exact E9.
    + exact E10.
    + exact E6.
    + unfold z_after; cbn [zf_dt]. rewrite E2. destruct (r_dtype (leave_fin flush mb')); [reflexivity | exact IVdt].
    + exact E11.
  - (* the loop returned *)
    destruct LR as (-> & K & Wa & Wb & [M|(ND & MD & SOa & SOb)]); [subst resa; cbn in NA; congruence|].
    subst resa resb.
    destruct (kr_rel _ _ _ _ _ _ _ _ K) as [S Hinp Haout Hnx How Hhold Hbits Hin Hout Hret Hleave Hadler Hmsg
                                           Htin Htout Hsnx Hsow].
    pose proof (kr_inp _ _ _ _ _ _ _ _ K) as KI. pose proof (kr_aout _ _ _ _ _ _ _ _ K) as KA.
    pose proof (mwW_ow _ (proj1 Wa)) as OWa.
    eexists; eexists; split; [reflexivity|]. split; [reflexivity|].
    cbn [z_after zf_ai zf_ao zf_tin zf_tout zf_msg zf_dt zf_adler l_s r_ret r_m r_dtype] in *.
    split; [reflexivity|]. split; [rewrite Hinp, Hsnx; reflexivity|]. split; [rewrite Haout, Hsow; reflexivity|].
    split; [exact How|].
    split; [rewrite SOa, Haout, KA; lia|].
    split; [rewrite Hinp, KI, LI; split; lia|].
    split; [rewrite SOa, Haout, KA in *; pose proof (Zlength_nonneg (m_ow ma')); lia|].
    constructor; cbn [l_s].
    + exact (irl_srel_weak _ True _ _ (fun _ => I) S).
    + exact (kr_wrap _ _ _ _ _ _ _ _ K).
    + exact (kr_head _ _ _ _ _ _ _ _ K).
    + exact (kr_wa _ _ _ _ _ _ _ _ K).
    + exact (kr_wb _ _ _ _ _ _ _ _ K).
    + intros _ HD. unfold m_mode in MD. rewrite MD in HD. exfalso. irl_md.
    + unfold m_mode in MD. rewrite MD. irl_md.
    + exact Htin.
    + exact Htout.
    + exact Hmsg.
    + exact IVdt.
    + exact Hadler.
Qed.

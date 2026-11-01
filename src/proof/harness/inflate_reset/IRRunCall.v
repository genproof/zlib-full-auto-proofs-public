(* Law inflate_reset, theory: one inflate() call on two related streams, from Spec5's inflate_rel (the machine
   at the loop head after the prologue, the loop, the exit), with the invariant IRinv kept at call boundaries. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRPassNs.
Require Import Zlib.proof.harness.inflate_reset.IRPassOut.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head                                                                   *)

Lemma irc_typedo_swf (s: istate) : swf s -> swf (set_i_mode s TYPEDO).
Proof. intros S. destruct S; constructor; cbn; auto. unfold HEAD, TYPEDO, SYNC; lia. Qed.

Lemma irc_typedo_modewf (s: istate) : modewf s -> modewf (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Lemma irc_typedo_swf3 (s: istate) : swf3 s -> swf3 (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold HEAD, TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Definition irc_s0 (s: istate) : istate :=
  if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s.

Lemma irc_m0_s (z: zfields) (L: live) (inp: list Z) : m_s (m_init z L inp) = irc_s0 (l_s L).
Proof. reflexivity. Qed.

Lemma irc_init (z: zfields) (L: live) (ni no: val) (ain aout: Z) (inp: list Z) :
  live_ok L -> zf_ok z -> 0 <= aout <= 2 ^ 20 -> Zlength inp <= 2 ^ 24 -> bytes_ok inp ->
  let m0 := m_init (ir_call z ni ain no aout) L inp in
  mwf3 m0 /\ m_leave m0 = 0 /\ irp_out m0.
Proof.
  intros LV ZF AO ZI BI. cbv zeta.
  destruct LV as (SP & SW & MW & HW & S3 & WS & LV1 & LV2 & LV3).
  destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  set (s := l_s L) in *.
  assert (Hs: forall P: istate -> Prop, P s -> (P s -> P (set_i_mode s TYPEDO)) -> P (irc_s0 s)).
  { intros P A B. unfold irc_s0. destruct (_ =? _); auto. }
  assert (SW': swf (irc_s0 s)) by (apply Hs; auto; apply irc_typedo_swf).
  assert (MW': modewf (irc_s0 s)) by (apply Hs; auto; apply irc_typedo_modewf).
  assert (S3': swf3 (irc_s0 s)) by (apply Hs; auto; apply irc_typedo_swf3).
  assert (HD': irc_s0 s = irc_s0 s) by reflexivity.
  unfold m_init. fold s. fold (irc_s0 s). cbn [zf_ao zf_adler zf_msg zf_tin zf_tout ir_call].
  split; [|split; [reflexivity|]].
  - split; [constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
                              m_tin m_tout m_snx m_sow] | exact S3'].
    all: rewrite ?Zlength_nil; unfold urange, lrange, Z_OK in *;
      try solve [auto | split; [rep_lia | exact BI] | split; [lia | constructor] | apply (sw_hold _ SW') |
                 apply (sw_bits _ SW') | rep_lia | lia | left; reflexivity].
  - unfold irp_out, m_left, m_mode; cbn. split; [lia|]. split; [lia|]. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant at call boundaries (both phases: phase 1 with the same stream twice)            *)

Record IRinv (W0 wrap: Z) (src: list Z) (pos: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop := {
  iv_rel : srel True (l_s La) (l_s Lb);
  iv_wrap : i_wrap (l_s Lb) = wrap;
  iv_head : i_head (l_s Lb) = false;
  iv_wa : wcl W0 wrap src (i_wbits (l_s La));
  iv_wb : wcl W0 wrap src (i_wbits (l_s Lb));
  iv_hd : wrap <> 0 -> i_mode (l_s Lb) = HEAD -> ir_hd src pos (i_hold (l_s Lb)) (i_bits (l_s Lb));
  iv_sync : i_mode (l_s Lb) <> SYNC;
  iv_tin : zf_tin za = zf_tin zb;
  iv_tout : zf_tout za = zf_tout zb;
  iv_msg : zf_msg za = zf_msg zb;
  iv_dt : zf_dt za = zf_dt zb;
  iv_adler : zf_adler za = zf_adler zb }.

Lemma irc_srel_s0 (P: Prop) (sa sb: istate) : srel P sa sb -> srel P (irc_s0 sa) (irc_s0 sb).
Proof.
  intros S. unfold irc_s0. rewrite (sr_mode _ _ _ S).
  destruct (Z.eqb_spec (i_mode sb) Zlib.proof.inflate.Model.TYPE) as [T|T]; [|exact S].
  destruct S; constructor; unfold lenlive, decode_mode;
    cbn [set_i_mode i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave
         i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits
         i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was] in *;
    rewrite ?T in *; try assumption; try reflexivity;
    try (intros X; exfalso; irl_md).
  - destruct sr_wbits as [W|[W|W]]; [left; exact W | exfalso; irl_md | exfalso; irl_md].
  - destruct sr_check as [C|[C|[[C|C] _]]]; [left; exact C | right; left; exact C | exfalso; irl_md | exfalso; irl_md].
Qed.

Lemma irc_s0_keep (s: istate) :
  i_wrap (irc_s0 s) = i_wrap s /\ i_head (irc_s0 s) = i_head s /\ i_wbits (irc_s0 s) = i_wbits s /\
  i_hold (irc_s0 s) = i_hold s /\ i_bits (irc_s0 s) = i_bits s /\
  (i_mode (irc_s0 s) = HEAD -> i_mode s = HEAD) /\ (i_mode s <> SYNC -> i_mode (irc_s0 s) <> SYNC).
Proof.
  unfold irc_s0. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE) as [T|T]; cbn;
    repeat split; auto; intros; irl_md.
Qed.

Lemma irc_kr0 (W0 wrap: Z) (src: list Z) (pos: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live)
    (ni1 no1 ni2 no2: val) (ain aout: Z) (inp: list Z) :
  IRinv W0 wrap src pos za La zb Lb ->
  Kr W0 wrap src pos inp aout (m_init (ir_call za ni1 ain no1 aout) La inp) (m_init (ir_call zb ni2 ain no2 aout) Lb inp).
Proof.
  intros IV.
  assert (S0: srel True (irc_s0 (l_s La)) (irc_s0 (l_s Lb))) by (apply irc_srel_s0; exact (iv_rel _ _ _ _ _ _ _ _ IV)).
  destruct (irc_s0_keep (l_s La)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  destruct (irc_s0_keep (l_s Lb)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct IV.
  constructor; unfold m_mode; rewrite ?irc_m0_s.
  - constructor; rewrite ?irc_m0_s; cbn [m_init ir_call m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
                                          m_adler m_msg m_tin m_tout m_snx m_sow zf_ao zf_adler zf_msg zf_tin zf_tout];
      try reflexivity; try assumption.
    + apply (irl_srel_weak True); auto.
    + exact (sr_hold _ _ _ S0).
    + exact (sr_bits _ _ _ S0).
  - reflexivity.
  - reflexivity.
  - rewrite B1. assumption.
  - rewrite B2. assumption.
  - rewrite A3. assumption.
  - rewrite B3. assumption.
  - intros W H. cbn [m_init m_nx m_hold m_bits m_ow]. rewrite Z.add_0_r.
    fold (irc_s0 (l_s Lb)). rewrite B4, B5. split; [|reflexivity]. apply iv_hd0; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit of one machine                                                                        *)

Lemma irc_s4_keep (upd: bool) (m: mst) :
  let s := irl_s4 upd m in
  i_mode s = m_mode m /\ i_wrap s = i_wrap (m_s m) /\ i_head s = i_head (m_s m) /\
  i_wbits s = i_wbits (m_s m) /\ i_hold s = m_hold m /\ i_bits s = m_bits m.
Proof.
  cbv zeta. unfold irl_s4, irl_s3, irl_s2, irl_s1, m_mode.
  destruct (irl_ck m), upd; try rewrite irl_uw_shape; cbn; repeat split.
Qed.

Lemma irc_exit1 (flush: Z) (m: mst) :
  let s := m_s (r_m (leave_fin flush m)) in
  i_mode s = m_mode m /\ i_wrap s = i_wrap (m_s m) /\ i_head s = i_head (m_s m) /\
  i_wbits s = i_wbits (m_s m) /\ i_hold s = m_hold m /\ i_bits s = m_bits m.
Proof.
  cbv zeta. destruct (irl_lf flush m) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E). rewrite E.
  apply irc_s4_keep.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

Lemma irc_ctx (src: list Z) (pos ain: Z) :
  0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> bytes_ok src ->
  let inp := sublist pos (pos + ain) src in
  ir_ctx src pos inp /\ Zlength inp = ain /\ bytes_ok inp.
Proof.
  intros P A S B. cbv zeta.
  assert (Z: Zlength (sublist pos (pos + ain) src) = ain) by (rewrite Zlength_sublist; lia).
  split; [|split; [exact Z|]].
  - split; [lia|]. split; [lia|]. split; [auto|].
    intros k K. rewrite Z in K. rewrite Znth_sublist by lia. f_equal; lia.
  - unfold bytes_ok in *. apply Forall_sublist. exact B.
Qed.

Lemma irc_notbad (strmp: val) (z: zfields) (L: live) (ib: inbuf) (o: outbuf) :
  strmp <> nullval -> ib <> InNull -> ~ inflate_bad strmp z (Some L) ib (Some o).
Proof.
  intros N I. unfold inflate_bad, is_live. destruct (eq_dec strmp nullval); [contradiction|].
  intros [H|[H|[H _]]]; congruence.
Qed.

Lemma irc_call : stepf2_mwf3_stmt -> sgroup_ok (fun _ => True) ->
  forall W0 wrap src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout
         ra za' sta' owa rb zb' stb' owb,
  IRinv W0 wrap src pos za La zb Lb -> live_ok La -> live_ok Lb -> zf_ok za -> zf_ok zb ->
  strma <> nullval -> strmb <> nullval ->
  0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
  0 <= aout <= 2 ^ 20 -> iba <> InNull -> ibb <> InNull -> inp = sublist pos (pos + ain) src ->
  inflate_rel flush strma (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) (Some La) iba inp (Some oa)
    ra za' sta' owa ->
  ra <> Z_MEM_ERROR ->
  inflate_rel flush strmb (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) (Some Lb) ibb inp (Some ob)
    rb zb' stb' owb ->
  rb <> Z_MEM_ERROR ->
  exists La' Lb', sta' = Some La' /\ stb' = Some Lb' /\
    ra = rb /\ zf_ai za' = zf_ai zb' /\ zf_ao za' = zf_ao zb' /\ owa = owb /\
    Zlength owa = aout - zf_ao za' /\ 0 <= zf_ai za' <= ain /\ 0 <= zf_ao za' <= aout /\
    IRinv W0 wrap src (pos + (ain - zf_ai za')) za' La' zb' Lb'.
Proof.
  intros SM ST W0 wrap src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa rb zb' stb' owb
    IV LVa LVb ZFa ZFb SNa SNb P0 A0 PA SL BS AO IBa IBb EI RA NA RB NB.
  destruct (irc_ctx src pos ain P0 A0 PA BS) as (C & LI & BI). rewrite <- EI in C, LI, BI.
  destruct RA as [(BD & _) | (_ & L0 & o & resa & winpa & EL & EO & RUN & SNX & -> & -> & -> & _ & ->)];
    [exfalso; exact (irc_notbad strma _ La iba oa SNa IBa BD)|].
  destruct RB as [(BD & _) | (_ & L1 & o1 & resb & winpb & EL1 & EO1 & RUNb & SNXb & -> & -> & -> & _ & ->)];
    [exfalso; exact (irc_notbad strmb _ Lb ibb ob SNb IBb BD)|].
  inversion EL; subst L0. inversion EO; subst o. inversion EL1; subst L1. inversion EO1; subst o1.
  clear EL EO EL1 EO1.
  destruct RUN as (ota & LPa & RESa). destruct RUNb as (otb & LPb & RESb).
  set (ma0 := m_init (ir_call za (in_ptr iba 0) ain (out_ptr oa 0) aout) La inp) in *.
  set (mb0 := m_init (ir_call zb (in_ptr ibb 0) ain (out_ptr ob 0) aout) Lb inp) in *.
  assert (ZI: Zlength inp <= 2 ^ 24) by lia.
  destruct (irc_init za La (in_ptr iba 0) (out_ptr oa 0) ain aout inp LVa ZFa AO ZI BI) as (Wa0 & La0 & Oa0).
  destruct (irc_init zb Lb (in_ptr ibb 0) (out_ptr ob 0) ain aout inp LVb ZFb AO ZI BI) as (Wb0 & Lb0 & Ob0).
  pose proof (irc_kr0 W0 wrap src pos za La zb Lb (in_ptr iba 0) (out_ptr oa 0) (in_ptr ibb 0) (out_ptr ob 0)
                ain aout inp IV) as K0.
  assert (NS0: m_mode mb0 <> SYNC).
  { unfold m_mode, mb0. rewrite irc_m0_s. apply (irc_s0_keep (l_s Lb)). exact (iv_sync _ _ _ _ _ _ _ _ IV). }
  pose proof (irl_loop SM ST W0 wrap src pos inp aout flush ma0 ota C LPa mb0 otb LPb K0 Wa0 Wb0 Lb0 Ob0 NS0) as LR.
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
    pose proof (mw_ow _ (mwf3_mwf _ Wa)) as OWa.
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
    pose proof (mw_ow _ (mwf3_mwf _ Wa)) as OWa.
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

(* Law inflate_check, theory part: the call level: the invariant I of the harness's loop and check_facts I (IKFacts.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict.
Require Import Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.harness.inflate_codes.TheoryCall.
Require Import Zlib.proof.harness.inflate_codes.TheoryApi.
Require Import Zlib.proof.harness.inflate_codes.TheoryHead Zlib.proof.harness.inflate_codes.TheoryHdr
  Zlib.proof.harness.inflate_codes.TheoryDict Zlib.proof.harness.inflate_codes.TheoryBlock
  Zlib.proof.harness.inflate_codes.TheoryFast Zlib.proof.harness.inflate_codes.TheoryDec
  Zlib.proof.harness.inflate_codes.TheoryTab.
Require Zlib.proof.harness.uncompress_any.UAStepMwf.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ikc_kc_all : group_ok (fun _ => True).
Proof.
  exact (rn_step Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 th_head th_hdr th_dict th_block
           th_fast th_dec th_tab).
Qed.

(* the pass lemma with bytes_ok out (as IKTheoryDefs.groupx_okb) *)
Definition ikc_groupx_okb (P: Z -> Prop) : Prop :=
  forall wrap src pos out a0 inp aout flush m,
    ctx_ok src pos inp -> Kc wrap src pos inp aout m -> Kx wrap src pos out a0 m -> mwf3 m ->
    m_leave m = 0 -> P (m_mode m) -> bytes_ok out ->
    stepx_post wrap src pos out a0 (stepf2 flush lenfix_list distfix_list m).

Lemma ikc_groupx_okb_of (P: Z -> Prop) : groupx_ok P -> ikc_groupx_okb P.
Proof. intros G wrap src pos out a0 inp aout flush m C K X W L HP _. exact (G _ _ _ _ _ _ _ _ _ C K X W L HP). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant of the harness's loop                                                            *)

Definition ikc_I (w: Z) (src: list Z) (pos: Z) (out: list Z) (z: zfields) (L: live) : Prop :=
  (exists final indict, inv w src pos final indict z L) /\ bytes_ok out /\
  Kx (wrap_of w) src pos out (zf_adler z) (m_init z L []).

Ltac ikc_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH] in *; lia.

(* ---------------------------------------------------------------------------------------------- *)
(* The wrapper                                                                                    *)

Lemma ikc_wrap_neg (w: Z) : wbits_ok w = true -> w < 0 -> wrap_of w = 0.
Proof.
  intros W N. apply (proj2 (wrap_of_low w)). revert W N.
  unfold wbits_ok, wrap_low, reset2_wb. intros W N.
  destruct (Z.ltb_spec w 0); [|lia].
  destruct (w <? -15); [discriminate|]. destruct (andb _ _); [reflexivity | discriminate].
Qed.

Lemma ikc_wrap_pos (w: Z) (src: list Z) : wbits_ok w = true -> 0 <= w ->
  wrap_of w <> 0 /\ ik_gz w src = ik_gzw (wrap_of w) src.
Proof.
  intros W N. unfold ik_gzw. rewrite (proj2 (wrap_of_low w)), (proj1 (wrap_of_low w)). revert W N.
  unfold wbits_ok, wrap_low, reset2_wb, ik_gz. intros W N.
  destruct (Z.ltb_spec w 0); [lia|].
  destruct (Z.ltb_spec w 48).
  - destruct (orb _ _) eqn:E; [|discriminate]. clear W.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    assert (D: (0 <= w < 16 /\ w / 16 = 0) \/ (16 <= w < 32 /\ w / 16 = 1) \/ (32 <= w < 48 /\ w / 16 = 2)).
    { assert (0 <= w / 16 < 3) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      pose proof (Z.div_mod w 16 ltac:(lia)); pose proof (Z.mod_pos_bound w 16 ltac:(lia)). lia. }
    destruct D as [(D1 & D2)|[(D1 & D2)|(D1 & D2)]]; rewrite D2; cbn -[Z.leb Z.ltb]; split; try lia.
  - destruct (orb (w =? 0) (andb (8 <=? w) (w <=? 15))) eqn:E; [|discriminate].
    apply orb_true_iff in E. destruct E as [E|E]; [apply Z.eqb_eq in E; lia|].
    apply andb_true_iff in E. destruct E as [_ E]. apply Z.leb_le in E. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Lemma ikc_modes (md: Z) : HEAD <= md <= SYNC -> md <> SYNC ->
  ik_pre_mode md \/ ik_post_mode md \/ md = BAD \/ md = MEM.
Proof.
  intros R N. unfold ik_pre_mode, ik_gzhdr_mode, ik_post_mode, decode_mode.
  destruct (rn_mode_groups md R) as [G|[G|[G|[G|[G|[G|G]]]]]];
    unfold md_head, md_hdr, md_dict, md_block, md_tab, decode_mode in G; tauto.
Qed.

Lemma ikc_pre_post (md: Z) : ik_pre_mode md -> ik_post_mode md -> False.
Proof. unfold ik_pre_mode, ik_gzhdr_mode, ik_post_mode, decode_mode. intros A B. ikc_md. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx at the call's start from Kx at the boundary machine                                        *)

Lemma ikc_Kx_m0 (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a: Z) (m m': mst) :
  Kx wrap src pos out a m -> m_s m' = m_s m -> m_nx m' = m_nx m -> m_hold m' = m_hold m -> m_bits m' = m_bits m ->
  m_ow m' = [] -> m_ow m = [] -> m_out m' = m_aout m' -> m_out m = m_aout m -> m_adler m' = m_adler m ->
  m_tout m' = m_tout m -> Kx wrap src pos out a m'.
Proof.
  intros [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13] S NX HO BI OW' OW O' O AD TO.
  unfold m_mode, m_left, ik_pre, ik_post, ik_trail, ik_bitbuf in *.
  rewrite O, OW, Z.sub_diag in *.
  constructor; unfold m_mode, m_left, ik_pre, ik_post, ik_trail, ik_bitbuf;
    rewrite ?S, ?NX, ?HO, ?BI, ?OW', ?O', ?AD, ?TO, ?Z.sub_diag; auto.
  all: unfold m_mode, m_left in *; rewrite ?Zlength_nil, ?Z.sub_0_r in *.
  all: try (intros W MD; destruct (X8 W MD) as (A1 & A2 & A3); auto; fail).
  all: try (intros W MD; destruct (X12 W MD) as [(A1 & A2 & A3)|A]; auto; fail).
  all: rewrite ?S, ?OW', ?Zlength_nil, ?Z.sub_0_r; rewrite ?OW, ?Zlength_nil, ?Z.sub_0_r in X13;
    intros W; destruct (X13 W) as (T1 & T2 & T3); split; [exact T1|];
    split; intros E; [destruct (T2 E) as (_ & B) | destruct (T3 E) as (_ & B)]; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop keeps Kx                                                                              *)

Lemma ikc_dict_ret_hold (flush: Z) (m: mst) (r: Z) (m': mst) :
  c_DICT flush m = IRet r m' -> i_hold (m_s m') = m_hold m'.
Proof.
  unfold c_DICT. destruct (i_havedict (m_s m) =? 0).
  - intros E; inversion E; subst. reflexivity.
  - destruct (rn_type_brk flush (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE))
      as [m2 E2]. rewrite E2. discriminate.
Qed.

Lemma ikc_nd_hold (flush: Z) (m: mst) (r: Z) (m': mst) :
  (m_mode m = DICTID \/ m_mode m = DICT) -> stepf2 flush lenfix_list distfix_list m = IRet r m' ->
  i_hold (m_s m') = m_hold m'.
Proof.
  intros [E|E]; unfold stepf2, step2; rewrite E; cbn -[c_DICTID c_DICT].
  - unfold c_DICTID. destruct (m_leave _ =? 1); [discriminate|]. apply ikc_dict_ret_hold.
  - apply ikc_dict_ret_hold.
Qed.

Lemma ikc_loop (GX: ikc_groupx_okb (fun _ => True)) : forall wrap src pos inp aout out a0 flush m o,
  ctx_ok src pos inp -> loop2 flush lenfix_list distfix_list m o ->
  Kc wrap src pos inp aout m -> mwf3 m -> m_leave m = 0 -> Kx wrap src pos out a0 m -> bytes_ok out ->
  Kx wrap src pos out a0 (match o with IBrk m' => m' | IRet _ m' => m' end) /\
  match o with IRet r m' => r = Z_NEED_DICT -> i_hold (m_s m') = m_hold m' | IBrk _ => True end.
Proof.
  intros wrap src pos inp aout out a0 flush m o C LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K W L0 X B.
  - pose proof (GX wrap src pos out a0 inp aout flush m C K X W L0 I B) as P. rewrite E in P.
    split; [exact P|]. intros RN.
    pose proof (ikc_kc_all wrap src pos inp aout flush m C K W L0 I) as Q. rewrite E in Q. cbn in Q.
    destruct Q as [(R & _)|(_ & MD & _)]; [subst r; ikc_md|]. exact (ikc_nd_hold flush m r m' MD E).
  - pose proof (GX wrap src pos out a0 inp aout flush m C K X W L0 I B) as P. rewrite E in P. split; [exact P | exact I].
  - pose proof (GX wrap src pos out a0 inp aout flush m C K X W L0 I B) as P. rewrite E in P. cbn in P.
    pose proof (ikc_kc_all wrap src pos inp aout flush m C K W L0 I) as Q. rewrite E in Q. destruct Q as [K' _].
    pose proof (Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 flush m W L0) as W'. rewrite E in W'.
    assert (L': m_leave m' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ W')); lia).
    apply IH; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit: what the final machine mF keeps of the loop's exit machine mE                       *)

Definition ikc_fin (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (mE mF: mst) : Prop :=
  i_mode (m_s mF) = m_mode mE /\ i_hold (m_s mF) = m_hold mE /\ i_bits (m_s mF) = m_bits mE /\
  i_flags (m_s mF) = i_flags (m_s mE) /\ i_wrap (m_s mF) = i_wrap (m_s mE) /\ i_head (m_s mF) = i_head (m_s mE) /\
  i_total (m_s mF) = Zlength (out ++ m_ow mE) mod 2 ^ 64 /\ m_tout mF = Zlength (out ++ m_ow mE) mod 2 ^ 64 /\
  (wrap <> 0 -> ik_post wrap src pos out mE ->
     i_check (m_s mF) = ik_chk (negb (i_flags (m_s mE) =? 0)) (out ++ m_ow mE) /\ m_adler mF = i_check (m_s mF)) /\
  (wrap = 0 -> m_adler mF = m_adler mE) /\
  m_ow mF = m_ow mE /\ m_snx mF = m_nx mE /\ m_sow mF = Zlength (m_ow mE) /\ m_inp mF = m_inp mE /\
  m_aout mF = m_aout mE.

Lemma ikc_mod32 (x: Z) : (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
  rewrite <- Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 32). reflexivity.
Qed.

Lemma ikc_post (w: Z) (src: list Z) (pos: Z) (out: list Z) (ain aout r: Z) (z z': zfields) (L': live)
    (inp: list Z) (mE mF: mst) :
  wbits_ok w = true -> bytes_ok out ->
  Kx (wrap_of w) src pos out (zf_adler z) mE -> Kc (wrap_of w) src pos inp aout mE -> mwf3 mE ->
  ikc_fin (wrap_of w) src pos out mE mF -> Zlength inp = ain ->
  zf_ai z' = Zlength (m_inp mF) - m_snx mF -> zf_ao z' = m_aout mF - m_sow mF ->
  zf_adler z' = m_adler mF -> zf_tout z' = m_tout mF ->
  0 <= zf_ai z' <= ain -> 0 <= zf_ao z' <= aout ->
  (r = Z_STREAM_END -> m_mode mE = DONE) ->
  ikc_I w src (pos + m_nx mE) (out ++ m_ow mE) z' L' ->
  check_post ikc_I w src pos out ain aout r z z' L' (m_ow mE).
Proof.
  intros WO BO X K W FIN LA AI AO AD TO RI RO RS IN.
  destruct FIN as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  pose proof (kc_inp _ _ _ _ _ _ K) as KI. pose proof (kc_aout _ _ _ _ _ _ K) as KA.
  destruct (mwf3_mwf _ W) as [_ SW _ _ _ NX [OWL OWB] _ _ _ _ _ _ _ _ _ _ _ _].
  assert (U: ain - zf_ai z' = m_nx mE) by (rewrite AI, F14, F12, KI; lia).
  assert (MD: aout - zf_ao z' = Zlength (m_ow mE)) by (rewrite AO, F15, F13, KA; lia).
  unfold check_post. cbv zeta. rewrite U, MD.
  set (wrap := wrap_of w) in *. set (ow := m_ow mE) in *.
  assert (MODES: ik_pre_mode (m_mode mE) \/ ik_post_mode (m_mode mE) \/ m_mode mE = BAD \/ m_mode mE = MEM).
  { apply ikc_modes; [exact (sw_mode _ SW) | exact (kc_sync _ _ _ _ _ _ K)]. }
  assert (PST: wrap <> 0 -> (out ++ ow <> [] \/ r = Z_STREAM_END) -> ik_post wrap src pos out mE).
  { intros WN H. destruct MODES as [M|[M|M]].
    - exfalso. destruct (kx_pre _ _ _ _ _ _ X WN M) as (O1 & O2 & _). fold ow in O2.
      destruct H as [H|H]; [rewrite O1, O2 in H; apply H; reflexivity|].
      apply RS in H. unfold ik_pre_mode, ik_gzhdr_mode in M. rewrite H in M. ikc_md.
    - exact (kx_post _ _ _ _ _ _ X WN M).
    - destruct (kx_bad _ _ _ _ _ _ X WN M) as [(O1 & O2 & _)|P]; [|exact P]. exfalso. fold ow in O2.
      destruct H as [H|H]; [rewrite O1, O2 in H; apply H; reflexivity|].
      apply RS in H. destruct M as [M|M]; rewrite H in M; ikc_md. }
  assert (GZ: 0 <= w -> wrap <> 0 /\ ik_gz w src = ik_gzw wrap src) by (intros; apply ikc_wrap_pos; auto).
  assert (HDR: forall P: Prop, ik_post wrap src pos out mE -> 
     ((ik_gzw wrap src = false -> i_flags (m_s mE) = 0 -> ik_zhdr src -> P) ->
      (ik_gzw wrap src = true -> i_flags (m_s mE) <> 0 -> ik_ghdr src -> P) -> P)).
  { intros P (Hd & _) A B. destruct Hd as [(H1 & H2 & H3 & _)|(H1 & H2 & H3 & _)]; [apply A; auto|].
    apply B; auto. intros E. rewrite E in H1. discriminate. }
  split; [exact RI|]. split; [exact RO|]. split; [reflexivity|]. split; [exact OWB|].
  split.
  { intros N. rewrite AD. assert (WZ: wrap = 0) by (apply ikc_wrap_neg; auto). rewrite (F10 WZ).
    exact (proj1 (kx_raw _ _ _ _ _ _ X WZ)). }
  split.
  { intros P0 NE. destruct (GZ P0) as (WN & G). pose proof (PST WN (or_introl NE)) as PS.
    rewrite G. apply (HDR _ PS); intros E1 _ H; rewrite E1; exact H. }
  split.
  { intros P0 H. destruct (GZ P0) as (WN & G). pose proof (PST WN H) as PS.
    destruct (F9 WN PS) as (C1 & C2). rewrite AD, C2, C1, G.
    apply (HDR _ PS); intros E1 E2 _; rewrite E1; f_equal.
    - rewrite E2. reflexivity.
    - destruct (Z.eqb_spec (i_flags (m_s mE)) 0); [contradiction | reflexivity]. }
  split.
  { intros P0 H. destruct (GZ P0) as (WN & G). pose proof (PST WN (or_intror H)) as PS.
    pose proof (RS H) as DN.
    split; [rewrite TO, F8; reflexivity|].
    destruct (kx_trail _ _ _ _ _ _ X WN) as (_ & _ & T3). destruct (T3 DN) as (T4 & T5 & T6 & T7).
    destruct PS as (PH & PC & PA).
    assert (SL: sublist 0 (m_aout mE - m_out mE) ow = ow).
    { rewrite T4. unfold m_left. fold ow. replace (m_aout mE - (m_aout mE - Zlength ow)) with (Zlength ow) by lia.
      apply sublist_same; lia. }
    fold ow in PC. rewrite SL in PC.
    pose proof (kx_total _ _ _ _ _ _ X) as TT.
    rewrite G. unfold ik_trailer.
    destruct PH as [(H1 & H2 & H3 & _)|(H1 & H2 & H3 & _)]; rewrite H3.
    - destruct (T6 H1) as (A1 & A2). split; [exact A1|]. rewrite A2, PC, H1. reflexivity.
    - assert (FN: i_flags (m_s mE) <> 0) by (intros E; rewrite E in H1; discriminate).
      destruct (T7 FN) as (A1 & A2 & A3). split; [exact A1|]. split.
      + rewrite A2, PC. destruct (Z.eqb_spec (i_flags (m_s mE)) 0); [contradiction | reflexivity].
      + rewrite A3, TT, ikc_mod32, Zlength_app. f_equal. rewrite T4. unfold m_left. fold ow. lia. }
  exact IN.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx at the next call boundary                                                                   *)

Lemma ikc_Kx_next (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a0: Z) (mE mF: mst) (z': zfields) (L': live) :
  Kx wrap src pos out a0 mE -> mwf mE -> ikc_fin wrap src pos out mE mF -> l_s L' = m_s mF ->
  zf_adler z' = m_adler mF -> zf_tout z' = m_tout mF ->
  Kx wrap src (pos + m_nx mE) (out ++ m_ow mE) (zf_adler z') (m_init z' L' []).
Proof.
  intros X W FIN LS AD TO.
  destruct FIN as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15).
  destruct (mw_ow _ W) as [OWL OWB].
  set (ow := m_ow mE) in *.
  (* LENGTH / DONE: nothing counted after CHECK's out = left *)
  assert (LD: wrap <> 0 -> m_mode mE = LENGTH \/ m_mode mE = DONE ->
              i_check (m_s mF) = i_check (m_s mE) /\ i_total (m_s mF) = i_total (m_s mE)).
  { intros WN MD.
    destruct (kx_trail _ _ _ _ _ _ X WN) as (_ & T2 & T3).
    assert (OL: m_out mE = m_left mE) by (destruct MD as [MD|MD]; [apply (T2 MD) | apply (T3 MD)]).
    assert (PM: ik_post_mode (m_mode mE)) by (unfold ik_post_mode; tauto).
    destruct (kx_post _ _ _ _ _ _ X WN PM) as (_ & PC & _).
    pose proof (kx_total _ _ _ _ _ _ X) as TT.
    unfold m_left in OL. fold ow in OL.
    replace (m_aout mE - m_out mE) with (Zlength ow) in PC, TT by lia.
    fold ow in PC. rewrite sublist_same in PC by lia.
    destruct (F9 WN (kx_post _ _ _ _ _ _ X WN PM)) as (C1 & _).
    split; [congruence|]. rewrite F7, TT, Zlength_app. reflexivity. }
  unfold m_init. rewrite LS.
  set (s := m_s mF) in *.
  set (s1 := if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s).
  assert (Hs: forall P: istate -> Prop, P s -> (P s -> P (set_i_mode s TYPEDO)) -> P s1).
  { intros P A B. unfold s1. destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); auto. }
  assert (E1: i_hold s1 = m_hold mE /\ i_bits s1 = m_bits mE /\ i_flags s1 = i_flags (m_s mE) /\
              i_total s1 = i_total s /\ i_check s1 = i_check s).
  { apply (Hs (fun t => i_hold t = m_hold mE /\ i_bits t = m_bits mE /\ i_flags t = i_flags (m_s mE) /\
              i_total t = i_total s /\ i_check t = i_check s)); [auto|].
    intros A; exact A. }
  destruct E1 as (H1 & H2 & H3 & H4 & H5).
  assert (EM: i_mode s1 = m_mode mE \/ (m_mode mE = Zlib.proof.inflate.Model.TYPE /\ i_mode s1 = TYPEDO)).
  { unfold s1. rewrite <- F1. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [right|left]; auto. }
  assert (NT: forall md, i_mode s1 = md -> md <> TYPEDO -> m_mode mE = md).
  { intros md E N. destruct EM as [E2 | [_ E2]]; congruence. }
  assert (PO: ik_post_mode (i_mode s1) -> ik_post_mode (m_mode mE)).
  { intros P. destruct EM as [E2 | [E2 _]]; [rewrite <- E2; exact P | rewrite E2; unfold ik_post_mode; tauto]. }
  assert (POST1: wrap <> 0 -> ik_post wrap src pos out mE ->
     ik_post wrap src (pos + m_nx mE) (out ++ ow)
       (MS s1 (l_h L') [] (zf_ao z') 0 [] (i_hold s1) (i_bits s1) (Zlength (@nil Z)) (zf_ao z') Z_OK 0
           (zf_adler z') (zf_msg z') (zf_tin z') (zf_tout z') 0 0)).
  { intros WN PS. destruct (F9 WN PS) as (C1 & C2). destruct PS as (PH & _ & _).
    unfold ik_post. cbn [m_s m_nx m_bits m_aout m_out m_ow m_adler]. rewrite H2, H3, H5, Z.add_0_r, Z.sub_diag.
    rewrite sublist_nil, app_nil_r. split; [exact PH|]. split; [exact C1|]. rewrite AD, C2. reflexivity. }
  constructor; unfold m_mode; cbn [m_s m_nx m_bits m_aout m_out m_ow m_adler m_hold m_tout]; rewrite ?Z.add_0_r.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - rewrite H1, H2. exact (kx_buf _ _ _ _ _ _ X).
  - destruct (kx_bits0 _ _ _ _ _ _ X) as (B1 & B2). rewrite H2, H3. split.
    + intros MD. apply B1. destruct MD as [MD|[MD|[MD|[MD|MD]]]];
        apply NT in MD; try ikc_md; unfold m_mode in *; auto 6.
    + intros MD. apply B2. apply NT; auto. ikc_md.
  - left. reflexivity.
  - rewrite H4, Z.sub_diag, Z.add_0_r. exact F7.
  - rewrite TO, Z.sub_diag, Z.add_0_r. exact F8.
  - intros WZ. destruct (kx_raw _ _ _ _ _ _ X WZ) as (_ & R2 & R3 & R4). split; [reflexivity|].
    destruct EM as [E2 | [_ E2]]; rewrite E2; [unfold m_mode in *; auto|].
    unfold ik_gzhdr_mode. split; [|split]; ikc_md.
  - intros WN PM. assert (PM': ik_pre_mode (m_mode mE)).
    { destruct EM as [E2 | [_ E2]]; [rewrite <- E2; exact PM|]. rewrite E2 in PM.
      unfold ik_pre_mode, ik_gzhdr_mode in PM. ikc_md. }
    destruct (kx_pre _ _ _ _ _ _ X WN PM') as (O1 & O2 & _). unfold ik_pre. cbn.
    fold ow in O2. rewrite O1, O2. auto.
  - intros WN PM. assert (PM': ik_gzhdr_mode (m_mode mE)).
    { destruct EM as [E2 | [_ E2]]; [rewrite <- E2; exact PM|]. rewrite E2 in PM.
      unfold ik_gzhdr_mode in PM. ikc_md. }
    rewrite H2, H3. destruct EM as [E2 | [E3 E2]]; [|rewrite E3 in PM'; unfold ik_gzhdr_mode in PM'; ikc_md].
    rewrite E2. exact (kx_gzh _ _ _ _ _ _ X WN PM').
  - intros WN PM. rewrite H2, H3. destruct EM as [E2 | [E3 E2]]; [|rewrite E2 in PM; ikc_md].
    rewrite E2 in PM. exact (kx_zh _ _ _ _ _ _ X WN PM).
  - intros WN PM. apply POST1; auto. exact (kx_post _ _ _ _ _ _ X WN (PO PM)).
  - intros WN PM. assert (PM': m_mode mE = BAD \/ m_mode mE = MEM).
    { destruct PM as [PM|PM]; [left|right]; apply NT; auto; ikc_md. }
    destruct (kx_bad _ _ _ _ _ _ X WN PM') as [(O1 & O2 & _)|PS].
    + left. unfold ik_pre. cbn. fold ow in O2. rewrite O1, O2. auto.
    + right. apply POST1; auto.
  - intros WN. destruct (kx_trail _ _ _ _ _ _ X WN) as (T1 & T2 & T3).
    unfold ik_trail, m_mode, m_left. cbn [m_s m_nx m_bits m_aout m_out m_ow].
    rewrite H2, H3, Z.add_0_r, Zlength_nil, Z.sub_0_r. split; [|split].
    + intros MD. apply T1. apply NT; auto. ikc_md.
    + intros MD. assert (MD': m_mode mE = LENGTH) by (apply NT; auto; ikc_md).
      destruct (LD WN (or_introl MD')) as (C1 & _). rewrite H5, C1.
      destruct (T2 MD') as (_ & A2 & A3). auto.
    + intros MD. assert (MD': m_mode mE = DONE) by (apply NT; auto; ikc_md).
      destruct (LD WN (or_intror MD')) as (C1 & C2). rewrite H5, C1, H4, C2.
      destruct (T3 MD') as (_ & A2 & A3). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave                                                                                      *)

Lemma ikc_uw (s: istate) (d: list Z) :
  i_mode (updatewindow s d) = i_mode s /\ i_bits (updatewindow s d) = i_bits s /\
  i_hold (updatewindow s d) = i_hold s /\ i_wrap (updatewindow s d) = i_wrap s /\
  i_head (updatewindow s d) = i_head s /\ i_check (updatewindow s d) = i_check s /\
  i_flags (updatewindow s d) = i_flags s /\ i_total (updatewindow s d) = i_total s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
Qed.

Lemma ikc_lf (flush: Z) (m: mst) :
  let mF := r_m (leave_fin flush m) in
  let oc := u32 (m_out m - m_left m) in
  let upd := andb (negb (Z.land (i_wrap (m_s m)) 4 =? 0)) (negb (oc =? 0)) in
  let c := update_check (i_flags (m_s m)) (i_check (m_s m))
             (sublist (Zlength (m_ow m) - oc) (Zlength (m_ow m)) (m_ow m)) in
  i_mode (m_s mF) = m_mode m /\ i_hold (m_s mF) = m_hold m /\ i_bits (m_s mF) = m_bits m /\
  i_flags (m_s mF) = i_flags (m_s m) /\ i_wrap (m_s mF) = i_wrap (m_s m) /\ i_head (m_s mF) = i_head (m_s m) /\
  i_total (m_s mF) = u64 (i_total (m_s m) + oc) /\
  i_check (m_s mF) = (if upd then c else i_check (m_s m)) /\
  m_adler mF = (if upd then c else m_adler m) /\
  m_tout mF = u64 (m_tout m + oc) /\
  m_ow mF = m_ow m /\ m_snx mF = m_nx m /\ m_sow mF = Zlength (m_ow m) /\ m_inp mF = m_inp m /\
  m_aout mF = m_aout m.
Proof.
  cbv zeta. unfold leave_fin. cbv zeta.
  set (upd0 := leave_ok flush m).
  set (m1 := restore m).
  set (m2 := if upd0 then _ else m1).
  assert (E2: m_snx m2 = m_nx m /\ m_sow m2 = Zlength (m_ow m) /\ m_inp m2 = m_inp m /\ m_aout m2 = m_aout m /\
              m_ow m2 = m_ow m /\ m_out m2 = m_out m /\ m_tout m2 = m_tout m /\ m_adler m2 = m_adler m /\
              i_mode (m_s m2) = m_mode m /\ i_bits (m_s m2) = m_bits m /\ i_hold (m_s m2) = m_hold m /\
              i_wrap (m_s m2) = i_wrap (m_s m) /\ i_head (m_s m2) = i_head (m_s m) /\
              i_check (m_s m2) = i_check (m_s m) /\ i_flags (m_s m2) = i_flags (m_s m) /\
              i_total (m_s m2) = i_total (m_s m)).
  { unfold m2, m1. destruct upd0; cbn.
    - match goal with |- context [updatewindow ?s ?d] => destruct (ikc_uw s d) as (A & B & C & D & E & F & G & H) end.
      rewrite A, B, C, D, E, F, G, H. cbn. unfold m_mode. repeat split.
    - unfold m_mode. repeat split. }
  clearbody m2.
  destruct E2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
  unfold m_left. rewrite A4, A5, A6.
  set (oc := u32 (m_out m - (m_aout m - Zlength (m_ow m)))) in *.
  set (m3 := upd_s (set_m_tout _ _) _).
  assert (B: i_wrap (m_s m3) = i_wrap (m_s m) /\ i_flags (m_s m3) = i_flags (m_s m) /\
             i_check (m_s m3) = i_check (m_s m) /\ m_ow m3 = m_ow m /\ m_adler m3 = m_adler m /\
             i_mode (m_s m3) = m_mode m /\ i_hold (m_s m3) = m_hold m /\ i_bits (m_s m3) = m_bits m /\
             i_head (m_s m3) = i_head (m_s m) /\ i_total (m_s m3) = u64 (i_total (m_s m) + oc) /\
             m_tout m3 = u64 (m_tout m + oc) /\ m_snx m3 = m_nx m /\ m_sow m3 = Zlength (m_ow m) /\
             m_inp m3 = m_inp m /\ m_aout m3 = m_aout m).
  { unfold m3, upd_s. cbn [m_s set_m_s set_m_tout set_m_tin i_wrap i_flags i_check i_mode i_hold i_bits i_head
      i_total set_i_total m_ow m_adler m_tout m_snx m_sow m_inp m_aout].
    rewrite A1, A2, A3, A4, A5, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16. repeat split. }
  clearbody m3. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
  rewrite B1, B4.
  destruct (andb (negb (Z.land (i_wrap (m_s m)) 4 =? 0)) (negb (oc =? 0))); cbn [r_m];
    unfold upd_s; cbn [m_s set_m_s set_m_adler i_wrap i_flags i_check i_mode i_hold i_bits i_head
      i_total set_i_check m_ow m_adler m_tout m_snx m_sow m_inp m_aout];
    rewrite ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10, ?B11, ?B12, ?B13, ?B14, ?B15; repeat split.
Qed.

Lemma ikc_upd (K: ik_kit) (flags: Z) (out ow: list Z) : bytes_ok out -> bytes_ok ow ->
  update_check flags (ik_chk (negb (flags =? 0)) out) ow = ik_chk (negb (flags =? 0)) (out ++ ow).
Proof.
  intros B1 B2. unfold update_check, ik_chk.
  destruct (flags =? 0); cbn [negb].
  - apply (kk_adler_upd K); auto.
  - apply (kk_crc_upd K); auto.
Qed.

Lemma ikc_fin_lf (K: ik_kit) (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (out: list Z) (a0 flush: Z)
    (mE: mst) :
  Kx wrap src pos out a0 mE -> Kc wrap src pos inp aout mE -> mwf3 mE -> bytes_ok out ->
  ikc_fin wrap src pos out mE (r_m (leave_fin flush mE)).
Proof.
  intros X KC W BO.
  destruct (ikc_lf flush mE) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15).
  set (mF := r_m (leave_fin flush mE)) in *.
  destruct (mwf3_mwf _ W) as [_ _ _ _ AO _ [OWL OWB] _ _ _ _ _ _ _ _ _ _ _ _].
  set (ow := m_ow mE) in *.
  pose proof (Zlength_nonneg ow) as OW0.
  pose proof (kx_total _ _ _ _ _ _ X) as TT. pose proof (kx_tout _ _ _ _ _ _ X) as TO.
  unfold m_left in *. fold ow in L7, L8, L9, L10.
  assert (WR: i_wrap (m_s mE) = wrap) by exact (kc_wrap _ _ _ _ _ _ KC).
  assert (CASES: (m_out mE = m_aout mE /\ u32 (m_out mE - (m_aout mE - Zlength ow)) = Zlength ow) \/
                 (m_out mE = m_aout mE - Zlength ow /\ u32 (m_out mE - (m_aout mE - Zlength ow)) = 0)).
  { destruct (kx_out _ _ _ _ _ _ X) as [E|E]; [left|right]; unfold m_left in E; fold ow in E; rewrite E;
      split; auto; [replace (m_aout mE - (m_aout mE - Zlength ow)) with (Zlength ow) by lia | rewrite Z.sub_diag];
      apply cl_u32_id; rep_lia. }
  assert (TOT: forall t, t = (Zlength out + (m_aout mE - m_out mE)) mod 2 ^ 64 ->
            u64 (t + u32 (m_out mE - (m_aout mE - Zlength ow))) = Zlength (out ++ ow) mod 2 ^ 64).
  { intros t ->. unfold u64. rewrite Zlength_app.
    destruct CASES as [(E1 & E2)|(E1 & E2)]; rewrite E2, E1.
    - rewrite Z.sub_diag, Z.add_0_r, Zplus_mod_idemp_l. reflexivity.
    - replace (m_aout mE - (m_aout mE - Zlength ow)) with (Zlength ow) by lia.
      rewrite Z.add_0_r, Zmod_mod. reflexivity. }
  unfold ikc_fin. fold ow.
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|].
  split; [exact L6|]. split; [rewrite L7; apply TOT; exact TT|]. split; [rewrite L10; apply TOT; exact TO|].
  split.
  { intros WN (PH & PC & PA).
    assert (W4: negb (Z.land (i_wrap (m_s mE)) 4 =? 0) = true).
    { rewrite WR. destruct (kx_wrap _ _ _ _ _ _ X) as [E|[E|[E|[E|[E|[E|E]]]]]]; [exfalso; exact (WN E)| | | | | |];
        rewrite E; reflexivity. }
    rewrite W4 in L8, L9. cbn [andb] in L8, L9.
    destruct CASES as [(E1 & E2)|(E1 & E2)]; rewrite E2 in L8, L9.
    - rewrite E1, Z.sub_diag, sublist_nil, app_nil_r in PC.
      destruct (Z.eqb_spec (Zlength ow) 0) as [Z0|Z0]; cbn [negb] in L8, L9.
      + rewrite L8, L9. apply Zlength_nil_inv in Z0. rewrite Z0, app_nil_r. auto.
      + rewrite L8, L9. rewrite Z.sub_diag, sublist_same by lia. rewrite PC.
        split; [apply ikc_upd; auto | reflexivity].
    - cbn [negb] in L8, L9. rewrite L8, L9.
      replace (m_aout mE - m_out mE) with (Zlength ow) in PC by lia. fold ow in PC.
      rewrite sublist_same in PC by lia. auto. }
  split.
  { intros WZ. rewrite L9, WR, WZ. reflexivity. }
  split; [exact L11|]. split; [exact L12|]. split; [exact L13|]. split; [exact L14|]. exact L15.
Qed.

Lemma ikc_fin_dict (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a0: Z) (mE: mst) :
  Kx wrap src pos out a0 mE -> wrap <> 0 -> m_mode mE = DICT -> i_bits (m_s mE) = m_bits mE ->
  i_hold (m_s mE) = m_hold mE -> m_snx mE = m_nx mE -> m_sow mE = Zlength (m_ow mE) ->
  ikc_fin wrap src pos out mE mE.
Proof.
  intros X WN MD IB IH SN SO.
  assert (PM: ik_pre_mode (m_mode mE)) by (unfold ik_pre_mode; tauto).
  destruct (kx_pre _ _ _ _ _ _ X WN PM) as (O1 & O2 & O3).
  pose proof (kx_total _ _ _ _ _ _ X) as TT. pose proof (kx_tout _ _ _ _ _ _ X) as TO.
  rewrite O3, Z.sub_diag, Z.add_0_r in TT, TO.
  unfold ikc_fin. rewrite O2, app_nil_r.
  split; [reflexivity|]. split; [exact IH|]. split; [exact IB|]. do 3 (split; [reflexivity|]).
  split; [exact TT|]. split; [exact TO|].
  split.
  { intros _ (_ & PC & PA). rewrite O3, Z.sub_diag, O2, sublist_nil, app_nil_r in PC. auto. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact SN|]. split; [rewrite SO, O2; reflexivity|].
  split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* After inflateInit2_                                                                            *)

Lemma ikc_wrap_vals (w: Z) : wbits_ok w = true ->
  wrap_of w = 0 \/ wrap_of w = 5 \/ wrap_of w = 6 \/ wrap_of w = 7 \/ wrap_of w = 13 \/ wrap_of w = 14 \/ wrap_of w = 15.
Proof.
  unfold wbits_ok, wrap_of. intros W. destruct (reset2_wb w) as [[wr wb]|] eqn:E; [|discriminate].
  unfold reset2_wrap. destruct (reset2_wb_cases w wr wb E) as [[-> B]|[A B]].
  - destruct (Z.eqb_spec wb 0); [lia | left; reflexivity].
  - assert (C: wr = 5 \/ wr = 6 \/ wr = 7) by lia.
    destruct C as [->|[->| ->]]; destruct (wb =? 0); cbn; lia.
Qed.

Lemma ikc_Kx_init (wrap: Z) (src: list Z) (z: zfields) (L: live) :
  wrap = 0 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7 \/ wrap = 13 \/ wrap = 14 \/ wrap = 15 ->
  i_mode (l_s L) = HEAD -> i_hold (l_s L) = 0 -> i_bits (l_s L) = 0 -> i_total (l_s L) = 0 -> zf_tout z = 0 ->
  Kx wrap src 0 [] (zf_adler z) (m_init z L []).
Proof.
  intros WR MD HO BI TO ZT. unfold m_init. rewrite MD.
  replace (HEAD =? Zlib.proof.inflate.Model.TYPE) with false by reflexivity. cbv iota.
  constructor; unfold m_mode, ik_pre, ik_trail, m_left;
    cbn [m_s m_nx m_bits m_aout m_out m_ow m_adler m_hold m_tout]; rewrite ?MD, ?HO, ?BI, ?TO, ?ZT.
  - exact WR.
  - unfold ik_bitbuf. rewrite sublist_nil. cbn. split; [lia | reflexivity].
  - split; intros; ikc_md.
  - left; reflexivity.
  - rewrite Z.sub_diag. reflexivity.
  - rewrite Z.sub_diag. reflexivity.
  - intros _. unfold ik_gzhdr_mode. repeat split; ikc_md.
  - intros _ _. auto.
  - unfold ik_gzhdr_mode. intros _ H. ikc_md.
  - intros _ H. ikc_md.
  - unfold ik_post_mode, decode_mode. intros _ H. ikc_md.
  - intros _ H. ikc_md.
  - intros _. repeat split; intros; unfold m_mode in *; cbn [m_s] in *; rewrite ?MD in *;
      first [rewrite BI; reflexivity | exfalso; ikc_md].
Qed.

Lemma ikc_init (w: Z) (src: list Z) (z: zfields) (sp: val) :
  wbits_ok w = true -> zf_msg z = None -> zf_tout z = 0 -> ikc_I w src 0 [] z (init_live sp w).
Proof.
  intros W M ZT. split; [exists Z_OK, 0; apply ap_init; auto|]. split; [constructor|].
  apply ikc_Kx_init; auto; [apply ikc_wrap_vals; auto| | | |];
    unfold init_live; cbn [l_s]; destruct (reset2_wb w) as [[wr wb]|] eqn:E;
    try (unfold wbits_ok in W; rewrite E in W; discriminate);
    unfold init_s, reset2_s, reset_s, reset_keep_s, zero_s; cbn; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One inflate() call                                                                             *)

Lemma ikc_inflate (K: ik_kit) (GX: ikc_groupx_okb (fun _ => True)) :
  forall w src pos out z L strmp flush ib inp o ain aout r z' st' ow,
    ikc_I w src pos out z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) src ->
    inflate_rel flush strmp (ik_set_zf_call z (in_ptr ib 0) ain (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    exists L', st' = Some L' /\ (r <> Z_MEM_ERROR -> check_post ikc_I w src pos out ain aout r z z' L' ow).
Proof.
  intros w src pos out z L strmp flush ib inp o ain aout r z' st' ow
    IV LV ZF SN P0 A0 PA SL BS AO FL NIB EINP REL.
  destruct IV as ((final & indict & INV) & BO & KX0).
  assert (CI: call_in_ok src pos ain ib inp) by (right; split; auto).
  destruct (cl_inflate Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 ikc_kc_all th_nodict
              w src pos final indict z L strmp flush ib inp (Some o) ain aout r z' st' ow
              INV LV ZF SN P0 A0 PA SL BS AO FL CI REL) as (L' & EST & IP).
  exists L'. split; [exact EST|]. intros RM.
  assert (BP: badptr ib (Some o) ain = false) by (destruct ib; [contradiction | reflexivity]).
  rewrite BP in IP.
  destruct IP as (_ & RI & RO & _ & _ & _ & _ & _ & _ & INV').
  destruct (cl_in_ok src pos ain ib inp P0 A0 PA BS CI) as (C & LI & _).
  pose proof (LI NIB) as LA.
  destruct REL as [(BD & _) | (NB & L0 & o0 & res & winp & EL & EO & RUN & SNX & Er & Eow & Ez' & WIN & Est)].
  { exfalso. destruct BD as [B|[B|(B & _)]]; [|discriminate|contradiction].
    unfold is_live in B. destruct (eq_dec strmp nullval); [contradiction | discriminate]. }
  inversion EL; subst L0. clear EL. inversion EO; subst o0. clear EO.
  rewrite EST in Est. inversion Est. clear Est. subst L'.
  set (L' := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L))
    in *.
  destruct RUN as (ot & LP & RES).
  change (m_init (ik_set_zf_call z (in_ptr ib 0) ain (out_ptr o 0) aout) L inp)
    with (cl_m0 z L ib (Some o) ain aout inp) in LP.
  destruct (cl_init w src pos final indict z L ib (Some o) ain aout inp INV LV ZF AO C SL)
    as (W0 & K0 & L00 & OW0 & NX0 & SNX0 & SOW0 & OUT0 & MSG0 & RET0 & MD0).
  set (m0 := cl_m0 z L ib (Some o) ain aout inp) in *.
  assert (X0: Kx (wrap_of w) src pos out (zf_adler z) m0).
  { apply (ikc_Kx_m0 _ _ _ _ _ _ _ KX0); reflexivity. }
  destruct (ikc_loop GX (wrap_of w) src pos inp aout out (zf_adler z) flush m0 ot C LP K0 W0 L00 X0 BO)
    as (XE & HE).
  pose proof (rn_loop Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 ikc_kc_all th_nodict
                (wrap_of w) src pos inp aout flush _ ot C LP K0 W0 L00 (fun _ => OW0)) as LR.
  assert (WO: wbits_ok w = true) by (destruct INV; auto).
  assert (LSL: l_s L' = m_s (r_m res)) by reflexivity.
  assert (ZAI: zf_ai z' = Zlength (m_inp (r_m res)) - m_snx (r_m res)) by (subst z'; reflexivity).
  assert (ZAO: zf_ao z' = m_aout (r_m res) - m_sow (r_m res)) by (subst z'; reflexivity).
  assert (ZAD: zf_adler z' = m_adler (r_m res)) by (subst z'; reflexivity).
  assert (ZTO: zf_tout z' = m_tout (r_m res)) by (subst z'; reflexivity).
  clear Ez'.
  destruct ot as [mE | r' mE].
  - (* inf_leave *)
    destruct LR as (KE & WE & LE & DE).
    destruct RES as [LO WF | ]; [subst r; cbn in RM; contradiction|].
    pose proof (ikc_fin_lf K _ _ _ _ _ _ _ flush mE XE KE WE BO) as FIN.
    destruct (ikc_lf flush mE) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G11 & G12 & _ & G14 & _).
    assert (OWE: ow = m_ow mE) by (rewrite Eow; exact G11).
    rewrite OWE.
    assert (UE: ain - zf_ai z' = m_nx mE).
    { rewrite ZAI, G14, G12, (kc_inp _ _ _ _ _ _ KE). lia. }
    apply (ikc_post w src pos out ain aout r z z' L' inp mE (r_m (leave_fin flush mE)) WO BO XE KE WE FIN LA
             ZAI ZAO ZAD ZTO RI RO).
    + intros RS. destruct (rn_leave_fin flush mE) as (R1 & _). rewrite Er, R1 in RS.
      unfold rn_bufret in RS. cbv zeta in RS.
      destruct (andb _ (m_ret mE =? Z_OK)) eqn:C1 in RS; [ikc_md|].
      destruct (Z.eq_dec (m_mode mE) DONE) as [D|D]; [exact D|].
      destruct (Z.eq_dec (m_mode mE) BAD) as [B|B].
      * rewrite (proj2 (kc_retx _ _ _ _ _ _ KE LE) B) in RS. ikc_md.
      * rewrite (kc_ret _ _ _ _ _ _ KE B D) in RS. ikc_md.
    + split; [exists (final_after false final r), (indict_after false indict r); rewrite <- UE; exact INV'|].
      split; [apply Forall_app; split; auto; exact (proj2 (mw_ow _ (mwf3_mwf _ WE)))|].
      exact (ikc_Kx_next _ _ _ _ _ _ _ z' L' XE (mwf3_mwf _ WE) FIN LSL ZAD ZTO).
  - (* Z_NEED_DICT / Z_MEM_ERROR *)
    subst res. cbn [r_ret r_m] in Er, Eow, ZAI, ZAO, ZAD, ZTO, LSL. subst r'.
    destruct LR as (WE & KE & [(RR & _) | (RR & MD & SN1 & SO & IB & _)]); [contradiction|].
    pose proof (HE RR) as IH.
    assert (WN: wrap_of w <> 0).
    { destruct (kc_dict _ _ _ _ _ _ KE MD) as (D1 & _). intros E. rewrite E in D1. apply D1. reflexivity. }
    pose proof (ikc_fin_dict _ _ _ _ _ _ XE WN MD IB IH SN1 SO) as FIN.
    subst ow.
    assert (UE: ain - zf_ai z' = m_nx mE).
    { rewrite ZAI, SN1, (kc_inp _ _ _ _ _ _ KE). lia. }
    apply (ikc_post w src pos out ain aout r z z' L' inp mE mE WO BO XE KE WE FIN LA
             ZAI ZAO ZAD ZTO RI RO).
    + intros RS. rewrite RR in RS. ikc_md.
    + split; [exists (final_after false final r), (indict_after false indict r); rewrite <- UE; exact INV'|].
      split; [apply Forall_app; split; auto; exact (proj2 (mw_ow _ (mwf3_mwf _ WE)))|].
      exact (ikc_Kx_next _ _ _ _ _ _ _ z' L' XE (mwf3_mwf _ WE) FIN LSL ZAD ZTO).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The theory                                                                                     *)

Lemma ikx_callb : ik_kit -> ikc_groupx_okb (fun _ => True) -> ik_theory_stmt.
Proof.
  intros K GX. exists ikc_I. constructor.
  - intros w src z sp W _ _ M ZT _ _ _ _. apply ikc_init; auto.
  - intros w src pos out z L ((final & indict & (_ & _ & H & _)) & _). exact H.
  - exact (ikc_inflate K GX).
Qed.

Lemma ikx_call : callx_stmt.
Proof.
  intros K G. exact (ikx_callb K (ikc_groupx_okb_of _ G)).
Qed.

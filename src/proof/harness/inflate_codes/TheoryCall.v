(* Law inflate_codes, theory: one inflate() call from the harness's invariant (inv) to inflate_post. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict.
Require Import Zlib.proof.harness.inflate_codes.TheoryRun.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head                                                                   *)

Lemma cl_in_ok (src: list Z) (pos ain: Z) (ib: inbuf) (inp: list Z) :
  0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> bytes_ok src -> call_in_ok src pos ain ib inp ->
  ctx_ok src pos inp /\ (ib <> InNull -> Zlength inp = ain) /\ (ib = InNull -> inp = []).
Proof.
  intros P A S B [[-> ->] | [N ->]].
  - split; [|split; [intros H; congruence | auto]].
    split; [lia|]. split; [rewrite Zlength_nil; lia|]. split; [auto|]. intros k K. rewrite Zlength_nil in K. lia.
  - assert (Z: Zlength (sublist pos (pos + ain) src) = ain) by (rewrite Zlength_sublist; lia).
    split; [|split; [auto | intros; congruence]].
    split; [lia|]. split; [lia|]. split; [auto|].
    intros k K. rewrite Z in K. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

Lemma cl_bytes_ok (src: list Z) (pos: Z) (inp: list Z) : ctx_ok src pos inp -> bytes_ok inp.
Proof.
  intros (P & S & B & E). unfold bytes_ok in *. apply Forall_Znth. intros k K.
  rewrite E by lia. apply Forall_Znth; first [exact B | lia].
Qed.

Definition cl_m0 (z: zfields) (L: live) (ib: inbuf) (ob: option outbuf) (ain aout: Z) (inp: list Z) : mst :=
  m_init (set_zf_call z (in_ptr ib 0) ain (ob_ptr ob) aout) L inp.

Lemma cl_set_typedo_swf (s: istate) : swf s -> swf (set_i_mode s TYPEDO).
Proof. intros S. destruct S; constructor; cbn; auto. unfold HEAD, TYPEDO, SYNC; lia. Qed.

Lemma cl_set_typedo_modewf (s: istate) : modewf s -> modewf (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Lemma cl_set_typedo_swf3 (s: istate) : swf3 s -> swf3 (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold HEAD, TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Lemma cl_init (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ib: inbuf) (ob: option outbuf)
    (ain aout: Z) (inp: list Z) :
  inv w src pos final indict z L -> live_ok L -> zf_ok z -> 0 <= aout <= 2 ^ 20 ->
  ctx_ok src pos inp -> Zlength src <= 2 ^ 24 ->
  let m0 := cl_m0 z L ib ob ain aout inp in
  mwf3 m0 /\ Kc (wrap_of w) src pos inp aout m0 /\ m_leave m0 = 0 /\ m_ow m0 = [] /\ m_nx m0 = 0 /\
  m_snx m0 = 0 /\ m_sow m0 = 0 /\ m_out m0 = aout /\ m_msg m0 = zf_msg z /\ m_ret m0 = Z_OK /\
  i_mode (m_s m0) = (if i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE then TYPEDO else i_mode (l_s L)).
Proof.
  intros IV LV ZF AO C SL. cbv zeta.
  destruct IV as (WO & WR & HD & SY & FM & BM & BT & HH & DI & DC & ID).
  destruct LV as (SP & SW & MW & HW & S3 & WS & LV1 & LV2 & LV3).
  destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  pose proof (cl_bytes_ok _ _ _ C) as BI.
  destruct C as (P0 & PS & BS & EZ).
  set (s := l_s L) in *.
  assert (Hs: forall P: istate -> Prop, P s -> (P s -> P (set_i_mode s TYPEDO)) ->
            P (if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s)).
  { intros P A B. destruct (_ =? _); auto. }
  unfold cl_m0, m_init. fold s. cbn [zf_ao zf_adler zf_msg zf_tin zf_tout set_zf_call].
  set (s' := if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s).
  assert (SW': swf s') by (unfold s'; apply Hs; auto; apply cl_set_typedo_swf).
  assert (MW': modewf s') by (unfold s'; apply Hs; auto; apply cl_set_typedo_modewf).
  assert (S3': swf3 s') by (unfold s'; apply Hs; auto; apply cl_set_typedo_swf3).
  assert (Ewr: i_wrap s' = i_wrap s) by (unfold s'; apply (Hs (fun t => i_wrap t = i_wrap s)); auto).
  assert (Ehd: i_head s' = i_head s) by (unfold s'; apply (Hs (fun t => i_head t = i_head s)); auto).
  assert (Ech: i_check s' = i_check s) by (unfold s'; apply (Hs (fun t => i_check t = i_check s)); auto).
  assert (Emd: i_mode s' = (if i_mode s =? Zlib.proof.inflate.Model.TYPE then TYPEDO else i_mode s))
    by (unfold s'; destruct (_ =? _); reflexivity).
  assert (Emd2: i_mode s' = i_mode s \/ (i_mode s = Zlib.proof.inflate.Model.TYPE /\ i_mode s' = TYPEDO)).
  { rewrite Emd. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); auto. }
  assert (ZI: Zlength inp <= 2 ^ 24) by lia.
  split; [|split; [|repeat split; auto]].
  - split; [constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
                              m_tin m_tout m_snx m_sow]; auto | exact S3'].
    all: rewrite ?Zlength_nil; unfold urange, lrange, Z_OK in *;
      try solve [split; [rep_lia | exact BI] | split; [lia | constructor] | apply (sw_hold _ SW') |
                 apply (sw_bits _ SW') | rep_lia | lia].
  - unfold m_mode. cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
                         m_tin m_tout m_snx m_sow m_msg].
    assert (NT: forall md, i_mode s' = md -> md <> TYPEDO -> i_mode s = md).
    { intros md E N. destruct Emd2 as [E2 | [_ E2]]; congruence. }
    constructor; unfold m_mode; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler
                         m_tin m_tout m_snx m_sow m_msg]; auto.
    + rewrite Ewr; auto.
    + rewrite Ehd; auto.
    + intros E. destruct Emd2 as [E2 | [_ E2]]; [apply SY; congruence | rewrite E2 in E; discriminate].
    + intros. discriminate.
    + intros E. apply BM. apply NT; auto. unfold BAD, TYPEDO; lia.
    + intros N1 N2.
      replace (i_bits s') with (i_bits s) by (unfold s'; destruct (_ =? _); reflexivity).
      destruct Emd2 as [E2 | [E1 E2]].
      * rewrite E2 in N1, N2. apply BT; auto.
      * apply BT; rewrite E1; unfold Zlib.proof.inflate.Model.TYPE, BAD, MEM; lia.
    + intros N. lia.
    + intros W E. apply NT in E; [|unfold HEAD, TYPEDO; lia].
      replace (i_bits s') with (i_bits s) by (unfold s'; destruct (_ =? _); reflexivity).
      replace (i_hold s') with (i_hold s) by (unfold s'; destruct (_ =? _); reflexivity).
      rewrite Z.add_0_r. apply HH; auto.
    + intros E. apply NT in E; [|unfold DICTID, TYPEDO; lia].
      replace (i_bits s') with (i_bits s) by (unfold s'; destruct (_ =? _); reflexivity).
      replace (i_hold s') with (i_hold s) by (unfold s'; destruct (_ =? _); reflexivity).
      rewrite Z.add_0_r. apply DI; auto.
    + intros E. apply NT in E; [|unfold DICT, TYPEDO; lia].
      destruct (DC E) as (D1 & D2 & D3 & D4 & D5). rewrite Ech, Z.add_0_r. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Small facts                                                                                    *)

Lemma cl_badptr (strmp: val) (z: zfields) (L: live) (ib: inbuf) (ob: option outbuf) (ni no: val) (ain aout: Z) :
  strmp <> nullval ->
  (inflate_bad strmp (set_zf_call z ni ain no aout) (Some L) ib ob <-> badptr ib ob ain = true).
Proof.
  intros N. unfold inflate_bad, is_live, badptr. cbn [set_zf_call zf_ai].
  destruct (eq_dec strmp nullval); [contradiction|].
  split.
  - intros [H|[H|[H1 H2]]]; [discriminate | subst ob; reflexivity |].
    subst ib. destruct ob; [|reflexivity]. destruct (Z.eqb_spec ain 0); [contradiction | reflexivity].
  - destruct ob as [o|]; [|intros; right; left; reflexivity].
    destruct ib; [|discriminate]. intros H. right; right. split; [reflexivity|].
    destruct (Z.eqb_spec ain 0); [discriminate | auto].
Qed.

Lemma cl_inv_z (w: Z) (src: list Z) (pos final indict: Z) (z z': zfields) (L: live) :
  inv w src pos final indict z L -> zf_msg z' = zf_msg z -> zf_adler z' = zf_adler z ->
  inv w src pos final indict z' L.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) M D.
  refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj _ (conj A7 (conj A8 (conj A9 (conj _ A11)))))))))).
  - rewrite M; auto.
  - intros E; destruct (A10 E) as (B1 & B2 & B3 & B4 & B5).
    refine (conj B1 (conj B2 (conj B3 (conj B4 _)))). congruence.
Qed.

Lemma cl_zlib (w: Z) : wbits_ok w = true -> Z.land (wrap_of w) 1 <> 0 -> zlib_okb w = true.
Proof.
  intros W N. rewrite (wrap_of_land w 1) in N by lia. revert W N.
  unfold wbits_ok, wrap_low, zlib_okb, reset2_wb. intros W N.
  destruct (Z.ltb_spec w 0).
  - destruct (Z.ltb_spec w (-15)); [discriminate|].
    destruct (andb (8 <=? - w) (- w <=? 15)); [|discriminate]. contradiction N; reflexivity.
  - destruct (Z.ltb_spec w 48).
    + match type of N with context [if ?c then _ else _] => destruct c end; [|contradiction N; reflexivity].
      cbv iota beta in N. rewrite Z.shiftr_div_pow2 in N by lia. change (2 ^ 4) with 16 in N.
      assert (D: w / 16 = 0 \/ w / 16 = 1 \/ w / 16 = 2).
      { assert (0 <= w / 16 < 3) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
      destruct D as [D|[D|D]]; rewrite D in N.
      * assert (w < 16) by (pose proof (Z.div_mod w 16 ltac:(lia)); pose proof (Z.mod_pos_bound w 16 ltac:(lia)); lia).
        destruct (Z.leb_spec 0 w); [|lia]. destruct (Z.ltb_spec w 16); [reflexivity | lia].
      * contradiction N; reflexivity.
      * assert (32 <= w) by (pose proof (Z.div_mod w 16 ltac:(lia)); pose proof (Z.mod_pos_bound w 16 ltac:(lia)); lia).
        destruct (Z.leb_spec 0 w); [|lia]. destruct (Z.leb_spec 32 w); [|lia]. rewrite orb_true_r. reflexivity.
    + destruct (orb (w =? 0) (andb (8 <=? w) (w <=? 15))) eqn:E; [|discriminate].
      apply orb_true_iff in E. destruct E as [E|E]; [apply Z.eqb_eq in E; lia|].
      apply andb_true_iff in E. destruct E as [_ E]. apply Z.leb_le in E. lia.
Qed.

Lemma cl_step_mode (flush: Z) (m: mst) :
  (m_mode m = DONE -> stepf2 flush lenfix_list distfix_list m = c_DONE m) /\
  (m_mode m = BAD -> stepf2 flush lenfix_list distfix_list m = c_BAD m) /\
  (m_mode m = MEM -> stepf2 flush lenfix_list distfix_list m = IRet Z_MEM_ERROR m).
Proof.
  unfold stepf2, step2. repeat split; intros E; rewrite E; reflexivity.
Qed.

Lemma cl_final (flush: Z) (m: mst) (o: iout) :
  loop2 flush lenfix_list distfix_list m o ->
  (m_mode m = DONE -> o = IBrk (set_leave (set_m_ret m Z_STREAM_END))) /\
  (m_mode m = BAD -> o = IBrk (set_leave (set_m_ret m Z_DATA_ERROR))) /\
  (m_mode m = MEM -> o = IRet Z_MEM_ERROR m).
Proof.
  intros LP. destruct (cl_step_mode flush m) as (A & B & C).
  repeat split; intros E.
  - specialize (A E). unfold c_DONE in A.
    inversion LP; subst; rewrite A in *; try discriminate.
    + congruence.
    + match goal with H: IBrk _ = IBrk _ |- _ => inversion H; subst end. cbn in *. contradiction.
  - specialize (B E). unfold c_BAD in B.
    inversion LP; subst; rewrite B in *; try discriminate.
    + congruence.
    + match goal with H: IBrk _ = IBrk _ |- _ => inversion H; subst end. cbn in *. contradiction.
  - specialize (C E).
    inversion LP; subst; rewrite C in *; try discriminate. congruence.
Qed.

Lemma cl_fin (w: Z) (src: list Z) (pos final indict ain aout flush r: Z) (zR: zfields) (L': live) (u d: Z) :
  zf_ai zR = ain - u -> zf_ao zR = aout - d -> 0 <= u <= ain -> 0 <= d <= aout ->
  code_okb r = true -> r <> Z_STREAM_ERROR ->
  (r = Z_OK -> (u <> 0 \/ d <> 0) /\ flush <> Z_FINISH) ->
  (r = Z_BUF_ERROR -> (u = 0 /\ d = 0) \/ flush = Z_FINISH) ->
  (r = Z_DATA_ERROR -> zf_msg zR <> None) ->
  (final <> Z_OK -> r = final /\ u = 0 /\ d = 0) ->
  (r = Z_NEED_DICT -> zlib_okb w = true /\ pos + u = 6 /\ Z.land (Znth 1 src) 32 <> 0 /\
     zf_adler zR = be32 (sublist 2 6 src) /\ (indict <> 0 -> u = 0 /\ d = 0)) ->
  inv w src (pos + u) (final_after false final r) (indict_after false indict r) zR L' ->
  inflate_post inv w src pos final indict ain aout flush false r zR L'.
Proof.
  intros AI AO U D C1 C2 C3 C4 C5 C6 C7 C8.
  unfold inflate_post. cbv zeta. rewrite AI, AO.
  replace (ain - (ain - u)) with u by lia. replace (aout - (aout - d)) with d by lia.
  split; [exact C1|]. split; [lia|]. split; [lia|].
  split; [split; [intros E; contradiction | intros E; discriminate]|].
  split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
  split; [intros _; exact C6|]. split; [exact C7|]. exact C8.
Qed.

Lemma cl_no_mem (flush: Z) (m: mst) :
  swf (m_s m) -> m_out m = m_left m -> leave_ok flush m = true -> i_win (m_s m) = true.
Proof.
  intros S O E. unfold leave_ok in E. destruct (Z.eqb_spec (i_wsize (m_s m)) 0) as [Z0|Z0].
  - rewrite O, Z.eqb_refl in E. discriminate.
  - destruct (sw_wsize _ S) as [Z1|[W _]]; [contradiction | exact W].
Qed.

Ltac cl_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH] in *; lia.

(* the result of a Z_MEM_ERROR / Z_NEED_DICT return of the loop *)
Lemma cl_case_ret (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ain aout flush r: Z)
    (inp: list Z) (zR: zfields) (L': live) (mE: mst) :
  inv w src pos final indict z L -> Zlength inp = ain ->
  rn_ret (wrap_of w) src pos inp aout r mE ->
  zf_ai zR = Zlength (m_inp mE) - m_snx mE -> zf_ao zR = m_aout mE - m_sow mE -> zf_msg zR = m_msg mE ->
  zf_adler zR = m_adler mE -> l_s L' = m_s mE ->
  (final <> Z_OK -> r = final /\ m_snx mE = 0 /\ m_sow mE = 0) ->
  inflate_post inv w src pos final indict ain aout flush false r zR L'.
Proof.
  intros IV LA (W & K & RR) AI AO AM AD LS SP.
  pose proof (kc_inp _ _ _ _ _ _ K) as KI. pose proof (kc_aout _ _ _ _ _ _ K) as KA.
  destruct (mwf3_mwf _ W) as [_ _ _ _ _ _ [OW _] _ _ _ _ _ _ _ _ _ SNX SOW _].
  rewrite KI in AI, SNX. rewrite KA in AO, OW.
  assert (FM: final_mode final (i_mode (l_s L))) by (destruct IV as (_ & _ & _ & _ & F & _); exact F).
  destruct RR as [(-> & MM) | (-> & MD & SN & SO & IB & OWP)].
  - apply cl_fin with (u := m_snx mE) (d := m_sow mE); try lia; try reflexivity;
      try (intros N; destruct (SP N) as (A & B & C); solve [auto]); try (intros; cl_md).
    unfold inv. rewrite LS. change (final_after false final Z_MEM_ERROR) with Z_MEM_ERROR.
      change (indict_after false indict Z_MEM_ERROR) with 0.
      destruct IV as (A1 & _).
      refine (conj A1 (conj (kc_wrap _ _ _ _ _ _ K) (conj (kc_head _ _ _ _ _ _ K) (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); unfold m_mode in MM; rewrite ?MM.
      + cl_md.
      + right; right; right. split; reflexivity.
      + intros; cl_md.
      + intros _ N; contradiction.
      + intros _ E; cl_md.
      + intros E; cl_md.
      + intros E; cl_md.
      + right. split; [reflexivity | cl_md].
  - assert (FO: final = Z_OK).
    { destruct (Z.eq_dec final Z_OK) as [|N]; auto. destruct (SP N) as (A & _).
      destruct FM as [(F & _)|[(F & _)|[(F & _)|(F & _)]]]; subst final; cl_md. }
    subst final.
    destruct (kc_dict _ _ _ _ _ _ K MD) as (D1 & D2 & D3 & D4 & D5).
    pose proof (mw_nx _ (mwf3_mwf _ W)) as NX.
    apply cl_fin with (u := m_snx mE) (d := m_sow mE); try lia; try reflexivity; try (intros; cl_md).
    + intros _. split; [apply cl_zlib; auto; destruct IV; auto|].
      split; [lia|]. split; [exact D2|]. rewrite AD. split; [exact D5|].
      intros ID. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A10 & A11).
      destruct A11 as [(_ & MS)|(I0 & _)]; [|contradiction].
      destruct (A10 MS) as (_ & _ & P6 & _). split; [lia|].
      destruct OWP as [OW0|P5]; [rewrite SO, OW0; reflexivity | lia].
    + unfold inv. rewrite LS. change (final_after false Z_OK Z_NEED_DICT) with Z_OK.
      change (indict_after false indict Z_NEED_DICT) with 1.
      destruct IV as (A1 & _).
      unfold m_mode in MD.
      refine (conj A1 (conj (kc_wrap _ _ _ _ _ _ K) (conj (kc_head _ _ _ _ _ _ K) (conj _ (conj _
        (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))); rewrite ?MD.
      * cl_md.
      * left. split; [reflexivity | cl_md].
      * intros; cl_md.
      * intros _ _. rewrite IB. apply (kc_bits _ _ _ _ _ _ K); unfold m_mode; rewrite MD; cl_md.
      * intros _ E; cl_md.
      * intros E; cl_md.
      * intros _. split; [exact D1|]. split; [exact D2|]. split; [lia|]. split; [exact D4|]. rewrite AD; exact D5.
      * left. split; reflexivity.
Qed.

(* inf_leave's failed window allocation: Z_MEM_ERROR, mode MEM *)
Lemma cl_case_mem (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ain aout flush: Z)
    (inp: list Z) (zR: zfields) (L': live) (mE: mst) :
  inv w src pos final indict z L -> Zlength inp = ain ->
  Kc (wrap_of w) src pos inp aout mE -> mwf3 mE ->
  let mR := set_mode (restore mE) MEM in
  zf_ai zR = Zlength (m_inp mR) - m_snx mR -> zf_ao zR = m_aout mR - m_sow mR -> l_s L' = m_s mR ->
  (final <> Z_OK -> Z_MEM_ERROR = final /\ m_snx mR = 0 /\ m_sow mR = 0) ->
  inflate_post inv w src pos final indict ain aout flush false Z_MEM_ERROR zR L'.
Proof.
  intros IV LA K W mR AI AO LS SP.
  pose proof (kc_inp _ _ _ _ _ _ K) as KI. pose proof (kc_aout _ _ _ _ _ _ K) as KA.
  destruct (mwf3_mwf _ W) as [_ _ _ _ _ NX [OW _] _ _ _ _ _ _ _ _ _ _ _ _].
  unfold mR in *. cbn [set_mode restore upd_s set_m_s set_m_snx set_m_sow m_s m_inp m_aout m_snx m_sow m_nx m_ow] in AI, AO, LS, SP.
  rewrite KI in AI, NX. rewrite KA in AO, OW. pose proof (Zlength_nonneg (m_ow mE)).
  apply cl_fin with (u := m_nx mE) (d := Zlength (m_ow mE)); try lia; try reflexivity;
    try (intros N; destruct (SP N) as (A & B & C); solve [auto]); try (intros; cl_md).
  unfold inv. rewrite LS. change (final_after false final Z_MEM_ERROR) with Z_MEM_ERROR.
  change (indict_after false indict Z_MEM_ERROR) with 0.
  destruct IV as (A1 & _). cbn [set_i_mode set_i_bits set_i_hold i_mode i_wrap i_head].
  refine (conj A1 (conj (kc_wrap _ _ _ _ _ _ K) (conj (kc_head _ _ _ _ _ _ K) (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  + cl_md.
  + right; right; right. split; reflexivity.
  + intros; cl_md.
  + intros _ N; contradiction.
  + intros _ E; cl_md.
  + intros E; cl_md.
  + intros E; cl_md.
  + right. split; [reflexivity | cl_md].
Qed.

Lemma cl_u32_id (x: Z) : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small; lia. Qed.

(* inf_leave's normal exit *)
Lemma cl_case_ok (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ain aout flush: Z)
    (inp: list Z) (zR: zfields) (L': live) (mE: mst) :
  inv w src pos final indict z L -> Zlength inp = ain -> Zlength inp <= 2 ^ 24 -> 0 <= aout <= 2 ^ 20 ->
  Kc (wrap_of w) src pos inp aout mE -> mwf3 mE -> m_mode mE <> DICT -> m_leave mE = 1 ->
  let res := leave_fin flush mE in
  zf_ai zR = Zlength (m_inp (r_m res)) - m_snx (r_m res) -> zf_ao zR = m_aout (r_m res) - m_sow (r_m res) ->
  zf_msg zR = m_msg (r_m res) -> l_s L' = m_s (r_m res) ->
  (final <> Z_OK -> r_ret res = final /\ m_snx (r_m res) = 0 /\ m_sow (r_m res) = 0) ->
  inflate_post inv w src pos final indict ain aout flush false (r_ret res) zR L'.
Proof.
  intros IV LA LI AO K W ND LV res AI AOZ AM LS SP.
  destruct (rn_leave_fin flush mE) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  fold res in R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12.
  rewrite R2, R4 in AI. rewrite R3, R5 in AOZ. rewrite R6 in AM. rewrite R2, R3 in SP.
  pose proof (kc_inp _ _ _ _ _ _ K) as KI. pose proof (kc_aout _ _ _ _ _ _ K) as KA.
  destruct (mwf3_mwf _ W) as [_ _ _ _ _ NX [OW _] _ _ MIN _ _ _ _ _ _ _ _ _].
  rewrite KI in AI, NX, MIN. rewrite KA in AOZ, OW.
  assert (INN: u32 (m_in mE - m_have mE) = m_nx mE).
  { unfold m_have. rewrite MIN, KI. replace (Zlength inp - (Zlength inp - m_nx mE)) with (m_nx mE) by lia.
    apply cl_u32_id. lia. }
  assert (OUT: m_out mE = m_aout mE -> u32 (m_out mE - m_left mE) = Zlength (m_ow mE)).
  { intros E. unfold m_left. rewrite E.
    replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by lia.
    apply cl_u32_id. pose proof (Zlength_nonneg (m_ow mE)). lia. }
  assert (KO := kc_out _ _ _ _ _ _ K).
  assert (RET: (m_mode mE = DONE /\ m_ret mE = Z_STREAM_END) \/ (m_mode mE = BAD /\ m_ret mE = Z_DATA_ERROR) \/
               (m_mode mE <> DONE /\ m_mode mE <> BAD /\ m_ret mE = Z_OK)).
  { destruct (Z.eq_dec (m_mode mE) DONE) as [D|D].
    - left. split; auto. apply (proj1 (kc_retx _ _ _ _ _ _ K LV)); auto.
    - destruct (Z.eq_dec (m_mode mE) BAD) as [B|B].
      + right; left. split; auto. apply (proj2 (kc_retx _ _ _ _ _ _ K LV)); auto.
      + right; right. split; [auto|]. split; [auto|]. apply (kc_ret _ _ _ _ _ _ K); auto. }
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  assert (OUTEQ: m_nx mE = 0 -> m_out mE = m_aout mE).
  { intros N0. destruct (Z.eq_dec (m_out mE) (m_aout mE)); auto. specialize (KO n). lia. }
  assert (BR: rn_bufret flush mE = Z_BUF_ERROR \/ rn_bufret flush mE = m_ret mE).
  { unfold rn_bufret. destruct (andb _ _); auto. }
  assert (BR1: rn_bufret flush mE = Z_BUF_ERROR -> m_ret mE = Z_OK /\
                ((m_nx mE = 0 /\ Zlength (m_ow mE) = 0) \/ flush = Z_FINISH)).
  { unfold rn_bufret. cbv zeta. rewrite INN.
    destruct (andb (orb (andb (m_nx mE =? 0) (u32 (m_out mE - m_left mE) =? 0)) (flush =? Z_FINISH)) (m_ret mE =? Z_OK)) eqn:C.
    - intros _. apply andb_true_iff in C. destruct C as [C1 C2]. apply Z.eqb_eq in C2. split; [exact C2|].
      apply orb_true_iff in C1. destruct C1 as [C1|C1]; [left|right; apply Z.eqb_eq; exact C1].
      apply andb_true_iff in C1. destruct C1 as [C1 C3]. apply Z.eqb_eq in C1, C3.
      split; [exact C1|]. rewrite OUT in C3 by auto. exact C3.
    - intros E. destruct RET as [(_ & R)|[(_ & R)|(_ & _ & R)]]; rewrite E in R; cl_md. }
  assert (BR2: rn_bufret flush mE = Z_OK -> (m_nx mE <> 0 \/ Zlength (m_ow mE) <> 0) /\ flush <> Z_FINISH).
  { unfold rn_bufret. cbv zeta. rewrite INN.
    destruct (andb (orb (andb (m_nx mE =? 0) (u32 (m_out mE - m_left mE) =? 0)) (flush =? Z_FINISH)) (m_ret mE =? Z_OK)) eqn:C.
    - cl_md.
    - intros E. rewrite E in C. rewrite Z.eqb_refl, andb_true_r in C.
      apply orb_false_iff in C. destruct C as [C1 C2]. apply Z.eqb_neq in C2. split; [|exact C2].
      destruct (Z.eq_dec (m_nx mE) 0) as [N0|N0]; [right|left; exact N0].
      rewrite N0, Z.eqb_refl in C1. cbn in C1. apply Z.eqb_neq in C1. rewrite OUT in C1 by auto. exact C1. }
  rewrite R1 in SP |- *.
  apply cl_fin with (u := m_nx mE) (d := Zlength (m_ow mE)); try lia.
  all: try solve [
    destruct BR as [-> | ->]; [reflexivity|]; destruct RET as [(_ & ->)|[(_ & ->)|(_ & _ & ->)]]; reflexivity |
    destruct BR as [-> | ->]; [cl_md|]; destruct RET as [(_ & ->)|[(_ & ->)|(_ & _ & ->)]]; cl_md |
    exact BR2 |
    intros E; destruct (BR1 E) as [_ X]; exact X |
    intros E; rewrite AM; destruct BR as [B|B]; [rewrite B in E; cl_md|];
      destruct RET as [(_ & R)|[(MB & R)|(_ & _ & R)]]; rewrite B, R in E; try cl_md;
      apply (kc_msg _ _ _ _ _ _ K MB) |
    intros N; destruct (SP N) as (A & B & C); auto |
    intros E; destruct BR as [B|B]; rewrite B in E; [cl_md|];
      destruct RET as [(_ & R)|[(_ & R)|(_ & _ & R)]]; rewrite R in E; cl_md ].
  (* the invariant afterwards *)
    assert (FM: final_mode final (i_mode (l_s L))) by (destruct IV as (_ & _ & _ & _ & F & _); exact F).
    assert (RF: final_mode (final_after false final (rn_bufret flush mE)) (m_mode mE)).
    { destruct RET as [(MD & R)|[(MD & R)|(MD1 & MD2 & R)]].
      - assert (B: rn_bufret flush mE = Z_STREAM_END) by (destruct BR as [B|B]; rewrite B; auto;
          destruct (BR1 B) as [X _]; rewrite R in X; cl_md).
        rewrite B. right; left. split; [reflexivity | exact MD].
      - assert (B: rn_bufret flush mE = Z_DATA_ERROR) by (destruct BR as [B|B]; rewrite B; auto;
          destruct (BR1 B) as [X _]; rewrite R in X; cl_md).
        rewrite B. right; right; left. split; [reflexivity | exact MD].
      - assert (B: rn_bufret flush mE = Z_BUF_ERROR \/ rn_bufret flush mE = Z_OK) by (rewrite <- R; exact BR).
        assert (FO: final = Z_OK).
        { destruct (Z.eq_dec final Z_OK) as [|N]; auto. destruct (SP N) as (A & _).
          destruct FM as [(F & _)|[(F & _)|[(F & _)|(F & _)]]]; subst final; destruct B as [B|B]; rewrite B in A; cl_md. }
        subst final. destruct B as [B|B]; rewrite B; left; auto. }
    unfold inv. rewrite LS, R8, R9, R10, R11, R12.
    change (indict_after false indict (rn_bufret flush mE)) with (if rn_bufret flush mE =? Z_NEED_DICT then 1 else 0).
    assert (NND: rn_bufret flush mE <> Z_NEED_DICT).
    { destruct BR as [B|B]; rewrite B; [cl_md|]. destruct RET as [(_ & R)|[(_ & R)|(_ & _ & R)]]; rewrite R; cl_md. }
    rewrite (proj2 (Z.eqb_neq _ _) NND).
    destruct IV as (A1 & _).
    refine (conj A1 (conj (kc_wrap _ _ _ _ _ _ K) (conj (kc_head _ _ _ _ _ _ K) (conj (kc_sync _ _ _ _ _ _ K)
      (conj RF (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + intros MB. rewrite AM. exact (kc_msg _ _ _ _ _ _ K MB).
    + exact (kc_bits _ _ _ _ _ _ K).
    + exact (kc_hd _ _ _ _ _ _ K).
    + exact (kc_did _ _ _ _ _ _ K).
    + intros MD. contradiction.
    + right. split; [reflexivity | exact ND].
Qed.

(* a final stream: the call returns the final code at once *)
Lemma cl_spec (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ib: inbuf) (ob: option outbuf)
    (ain aout flush: Z) (inp: list Z) (ot: iout) (res: result) :
  inv w src pos final indict z L -> live_ok L -> zf_ok z -> 0 <= aout <= 2 ^ 20 ->
  ctx_ok src pos inp -> Zlength src <= 2 ^ 24 ->
  loop2 flush lenfix_list distfix_list (cl_m0 z L ib ob ain aout inp) ot ->
  match ot with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  final <> Z_OK -> r_ret res = final /\ m_snx (r_m res) = 0 /\ m_sow (r_m res) = 0.
Proof.
  intros IV LV ZF AO C SL LP RES NF.
  destruct (cl_init w src pos final indict z L ib ob ain aout inp IV LV ZF AO C SL)
    as (W0 & K0 & L00 & OW0 & NX0 & SNX0 & SOW0 & OUT0 & MSG0 & RET0 & MD0).
  set (m0 := cl_m0 z L ib ob ain aout inp) in *.
  destruct (cl_final flush m0 ot LP) as (FD & FB & FM).
  assert (FMd: final_mode final (i_mode (l_s L))) by (destruct IV as (_ & _ & _ & _ & F & _); exact F).
  assert (EXa: forall r', m_ret m0 = Z_OK -> m_mode m0 <> MEM ->
      ot = IBrk (set_leave (set_m_ret m0 r')) -> r' <> Z_OK -> r_ret res = r' /\ m_snx (r_m res) = 0 /\ m_sow (r_m res) = 0).
  { intros r' R0 NM E NR. subst ot. destruct RES as [LO WF | ].
    - exfalso. assert (WT: i_win (m_s (set_leave (set_m_ret m0 r'))) = true).
      { apply cl_no_mem with flush; auto.
        - exact (mw_s _ (mwf3_mwf _ W0)).
        - unfold m_left. cbn. pose proof (kc_aout _ _ _ _ _ _ K0).
          rewrite ?OUT0, ?OW0, ?Zlength_nil. lia. }
      congruence.
    - destruct (rn_leave_fin flush (set_leave (set_m_ret m0 r'))) as (R1 & R2 & R3 & _).
      rewrite R1, R2, R3. cbn. rewrite ?NX0, ?OW0, ?Zlength_nil. split; [|auto].
      unfold rn_bufret. cbv zeta. cbn [m_ret set_leave set_m_leave set_m_ret].
      rewrite (proj2 (Z.eqb_neq r' Z_OK) NR), andb_false_r. reflexivity. }
  assert (NT: forall md, i_mode (l_s L) = md -> md <> Zlib.proof.inflate.Model.TYPE -> m_mode m0 = md).
  { intros md E N. unfold m_mode. rewrite MD0, E. destruct (Z.eqb_spec md Zlib.proof.inflate.Model.TYPE); [contradiction | reflexivity]. }
  destruct FMd as [(F & _)|[(F & MD)|[(F & MD)|(F & MD)]]]; [contradiction| | |].
  - subst final. apply (EXa Z_STREAM_END RET0); [rewrite (NT _ MD) by cl_md; cl_md | apply FD; apply NT; auto; cl_md | cl_md].
  - subst final. apply (EXa Z_DATA_ERROR RET0); [rewrite (NT _ MD) by cl_md; cl_md | apply FB; apply NT; auto; cl_md | cl_md].
  - subst final. assert (E: ot = IRet Z_MEM_ERROR m0) by (apply FM; apply NT; auto; cl_md).
    subst ot. subst res. cbn. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* cf_inflate                                                                                     *)

Lemma cl_inflate : stepf2_mwf3_stmt -> group_ok (fun _ => True) -> nodict_stmt ->
  forall w src pos final indict z L strmp flush ib inp ob ain aout r z' st' ow,
    inv w src pos final indict z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    call_in_ok src pos ain ib inp ->
    inflate_rel flush strmp (set_zf_call z (in_ptr ib 0) ain (ob_ptr ob) aout) (Some L) ib inp ob r z' st' ow ->
    exists L', st' = Some L' /\ inflate_post inv w src pos final indict ain aout flush (badptr ib ob ain) r z' L'.
Proof.
  intros SM ST ND w src pos final indict z L strmp flush ib inp ob ain aout r z' st' ow
    IV LV ZF SN P0 A0 PA SL BS AO FL CI REL.
  destruct (cl_in_ok src pos ain ib inp P0 A0 PA BS CI) as (C & LI & LN).
  destruct REL as [(BD & -> & -> & -> & ->) | (NB & L0 & o & res & winp & EL & EO & RUN & SNX & -> & -> & -> & WIN & ->)].
  - exists L. split; [reflexivity|].
    assert (BP: badptr ib ob ain = true) by (apply (cl_badptr strmp z L ib ob (in_ptr ib 0) (ob_ptr ob) ain aout SN); exact BD).
    rewrite BP. unfold inflate_post. cbv zeta. cbn [set_zf_call zf_ai zf_ao].
    replace (ain - ain) with 0 by lia. replace (aout - aout) with 0 by lia.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [tauto|].
    split; [intros; cl_md|]. split; [intros; cl_md|]. split; [intros; cl_md|]. split; [intros; discriminate|].
    split; [intros; cl_md|].
    rewrite Z.add_0_r. apply cl_inv_z with z; auto.
  - inversion EL; subst L0. clear EL.
    assert (BP: badptr ib ob ain = false).
    { destruct (badptr ib ob ain) eqn:E; auto. exfalso. apply NB.
      apply (cl_badptr strmp z L ib ob (in_ptr ib 0) (ob_ptr ob) ain aout SN); exact E. }
    rewrite BP.
    assert (LA: Zlength inp = ain).
    { destruct ib as [|sh p lo n cont].
      - rewrite (LN eq_refl), Zlength_nil. subst ob. cbn in BP. destruct (Z.eqb_spec ain 0); [auto | discriminate].
      - apply LI. discriminate. }
    destruct RUN as (ot & LP & RES).
    change (m_init (set_zf_call z (in_ptr ib 0) ain (ob_ptr ob) aout) L inp) with (cl_m0 z L ib ob ain aout inp) in LP.
    pose proof (cl_spec w src pos final indict z L ib ob ain aout flush inp ot res IV LV ZF AO C SL LP RES) as SP.
    destruct (cl_init w src pos final indict z L ib ob ain aout inp IV LV ZF AO C SL)
      as (W0 & K0 & L00 & OW0 & NX0 & SNX0 & SOW0 & OUT0 & MSG0 & RET0 & MD0).
    pose proof (rn_loop SM ST ND (wrap_of w) src pos inp aout flush _ ot C LP K0 W0 L00 (fun _ => OW0)) as LR.
    eexists; split; [reflexivity|].
    subst ob.
    assert (SLI: Zlength src <= 2 ^ 24) by exact SL.
    destruct ot as [mE | r' mE].
    + destruct LR as (KE & WE & LE & DE).
      destruct RES as [LO WF | ].
      * apply (cl_case_mem w src pos final indict z L ain aout flush inp _ _ mE IV LA KE WE);
          first [reflexivity | exact SP].
      * apply (cl_case_ok w src pos final indict z L ain aout flush inp _ _ mE IV LA ltac:(lia) AO KE WE DE LE);
          first [reflexivity | exact SP].
    + subst res. apply (cl_case_ret w src pos final indict z L ain aout flush r' inp _ _ mE IV LA LR);
        first [reflexivity | exact SP].
Qed.

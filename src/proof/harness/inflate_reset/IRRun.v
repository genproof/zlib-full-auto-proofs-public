(* Law inflate_reset, theory part: the invariants I1 (phase 1, stream a) and I2 (phase 2, streams a and b) of the
   harness's loop and the facts of IRFacts.v (reset_facts), from the parts (the sgroup statements, inflate_fast,
   the table determinism) via IRRunLoop.v (the loop and the exit on related machines) and IRRunCall.v (one call
   from Spec5's inflate_rel, the boundary invariant IRinv; phase 1 is the same with the stream a twice). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRPassNs.
Require Import Zlib.proof.harness.inflate_reset.IRPassOut.
Require Import Zlib.proof.harness.inflate_reset.IRRunLoop.
Require Import Zlib.proof.harness.inflate_reset.IRRunCall.
Require Import Zlib.proof.inflate_api.ResetFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* windowBits                                                                                     *)

Definition ir_wrap (w: Z) : Z := match reset2_wb w with Some (wr, _) => wr | None => 0 end.
Definition ir_wb0 (w: Z) : Z := match reset2_wb w with Some (_, wb) => wb | None => 0 end.

Lemma irr_wb (w wrap wb: Z) : reset2_wb w = Some (wrap, wb) ->
  (wb = 0 \/ 8 <= wb <= 15) /\ (w < 0 -> wrap = 0 /\ 8 <= wb) /\ (0 <= w -> 5 <= wrap <= 7).
Proof.
  unfold reset2_wb. intros E.
  destruct (Z.ltb_spec w 0).
  - destruct (w <? -15); [discriminate|].
    destruct ((8 <=? - w) && (- w <=? 15))%bool eqn:C; [|discriminate].
    inversion E; subst. apply andb_true_iff in C. destruct C as [C1 C2]. apply Z.leb_le in C1, C2.
    split; [right; lia|]. split; [intros _; split; [reflexivity | lia] | lia].
  - destruct (Z.ltb_spec w 48).
    + destruct ((Z.land w 15 =? 0) || ((8 <=? Z.land w 15) && (Z.land w 15 <=? 15)))%bool eqn:C; [|discriminate].
      inversion E; subst. clear E.
      assert (S: 0 <= Z.shiftr w 4 <= 2).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
        split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]. }
      split; [|split; [lia | lia]].
      apply orb_true_iff in C. destruct C as [C|C]; [left; apply Z.eqb_eq; exact C|].
      apply andb_true_iff in C. destruct C as [C1 C2]. apply Z.leb_le in C1, C2. right; lia.
    + destruct ((w =? 0) || ((8 <=? w) && (w <=? 15)))%bool eqn:C; [|discriminate].
      apply orb_true_iff in C. destruct C as [C|C]; [apply Z.eqb_eq in C; lia|].
      apply andb_true_iff in C. destruct C as [_ C]. apply Z.leb_le in C. lia.
Qed.

Lemma irr_wb_some (w: Z) : wbits_ok w = true -> reset2_wb w = Some (ir_wrap w, ir_wb0 w).
Proof. unfold wbits_ok, ir_wrap, ir_wb0. destruct (reset2_wb w) as [[a b]|]; [reflexivity | discriminate]. Qed.

Lemma irr_land3 (wrap: Z) : 5 <= wrap <= 7 -> Z.land wrap 3 <> 0.
Proof. intros H. assert (E: wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia. destruct E as [E|[E|E]]; rewrite E; discriminate. Qed.

(* the wrap that inflateInit2_ / inflateReset2 store for windowBits w (fix F8: bit 3 when the window size comes
   from the header, wb = 0) *)
Definition ir_iw (w: Z) : Z := reset2_wrap (ir_wrap w) (ir_wb0 w).

Lemma irr_iw (w: Z) : wbits_ok w = true ->
  0 <= ir_wrap w <= 7 /\
  (0 <= ir_iw w <= 7 \/ 9 <= ir_iw w <= 11 \/ 13 <= ir_iw w <= 15) /\
  (ir_iw w = 0 <-> ir_wrap w = 0) /\ (Z.land (ir_iw w) 8 =? 0) = negb (ir_wb0 w =? 0).
Proof.
  intros W. pose proof (irr_wb_some w W) as E.
  destruct (init_s_wrap w _ _ E) as (_ & A & _ & C & D).
  split; [destruct (reset2_wb_cases w _ _ E); lia|]. auto.
Qed.

(* a non-negative windowBits has a zlib or gzip wrapper, also with bit 3 *)
Lemma irr_iw_land3 (w: Z) : 0 <= w -> wbits_ok w = true -> Z.land (ir_iw w) 3 <> 0.
Proof.
  intros N W. pose proof (irr_wb_some w W) as E. destruct (irr_wb w _ _ E) as (_ & _ & R).
  specialize (R N). unfold ir_iw, reset2_wrap.
  assert (C: ir_wrap w = 5 \/ ir_wrap w = 6 \/ ir_wrap w = 7) by lia.
  destruct (ir_wb0 w =? 0); destruct C as [C|[C|C]]; rewrite C; discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The resets                                                                                     *)

Definition irr_clear (s: istate) : istate := set_i_wdata (set_i_wnext (set_i_whave (set_i_wsize s 0) 0) 0) [].

Lemma irr_reset_s (s: istate) : reset_s s = reset_keep_s (irr_clear s).
Proof. reflexivity. Qed.

(* inflateReset2 (on an accepted windowBits: wrap from reset2_wb) as inflateResetKeep after the window is
   emptied; the window is freed when its size changes or comes from the header (wb = 0) *)
Lemma irr_reset2_s (wrap wb: Z) (s: istate) : 0 <= wrap <= 7 ->
  reset2_s wrap wb s =
  reset_keep_s (irr_clear (set_i_wbits (set_i_wrap
    (if ((i_win s && negb (i_wbits s =? wb)) || (wb =? 0))%bool then set_i_win s false else s)
    (reset2_wrap wrap wb)) wb)).
Proof. intros H. rewrite (reset2_s_eq wrap wb s H). reflexivity. Qed.

(* inflateReset: the same after reset_hdr_s (window freed, wbits 0 when bit 3 of wrap is set) *)
Lemma irr_reset_full (s: istate) : reset_full_s s = reset_keep_s (irr_clear (reset_hdr_s s)).
Proof. reflexivity. Qed.

Ltac irr_simpl := unfold reset_keep_s, irr_clear, set_l_s; simpl.

Lemma irr_live_rk (L: live) (t: istate) :
  isptr (l_sp L) -> hwf (l_h L) -> writable_share (l_hsh L) -> swf t -> i_wsize t = 0 ->
  (i_wbits t = 0 -> Z.land (i_wrap t) 3 <> 0 /\ i_win t = false) ->
  live_ok (set_l_s L (reset_keep_s t)).
Proof.
  intros P HW HS W Z0 WB.
  unfold live_ok. cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s].
  split; [exact P|]. split; [|split; [|split; [exact HW|split; [|split; [exact HS|]]]]].
  - destruct W. constructor; irr_simpl; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
  - constructor; irr_simpl; try (intros X; exfalso; unfold decode_mode in X; irl_md);
      repeat split; intros X; exfalso; irl_md.
  - constructor; irr_simpl; try (intros X; exfalso; unfold decode_mode in X; irl_md).
    intros _ B R. split; [exact Z0 | exact (proj2 (WB B))].
  - irr_simpl. split; [exact WB|]. split; [intro; discriminate|].
    intros _ _. split; [reflexivity | left; reflexivity].
Qed.

Lemma irr_swf_clear (s: istate) (wrap wb: Z) (b: bool) :
  swf s -> (0 <= wrap <= 7 \/ 9 <= wrap <= 11 \/ 13 <= wrap <= 15) -> 0 <= wb <= 23 ->
  swf (irr_clear (set_i_wbits (set_i_wrap (if b then set_i_win s false else s) wrap) wb)) /\ swf (irr_clear s).
Proof.
  intros W R B. split; [destruct b|]; destruct W; constructor; irr_simpl; auto; try lia;
    try (left; reflexivity); try (split; [reflexivity | constructor]).
Qed.

Lemma irr_srel_rk (ta tb: istate) :
  i_wrap ta = i_wrap tb -> i_wsize ta = i_wsize tb -> i_whave ta = i_whave tb -> i_wnext ta = i_wnext tb ->
  i_wdata ta = i_wdata tb -> srel True (reset_keep_s ta) (reset_keep_s tb).
Proof.
  intros A B C D E. constructor; unfold lenlive; irr_simpl; auto;
    try (right; left; reflexivity); try (right; right; split; [left; reflexivity | exact I]);
    try (intros X; exfalso; unfold decode_mode in X; irl_md).
Qed.

Lemma irr_swf_hdr (s: istate) : swf s -> swf (irr_clear (reset_hdr_s s)).
Proof.
  intros W. unfold reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0);
    destruct W; constructor; irr_simpl; auto; try lia;
    try (left; reflexivity); try (split; [reflexivity | constructor]).
Qed.

Lemma irr_init_s (wrap wb: Z) : 0 <= wrap <= 7 ->
  i_mode (init_s wrap wb) = HEAD /\ i_wrap (init_s wrap wb) = reset2_wrap wrap wb /\ i_head (init_s wrap wb) = false /\
  i_wbits (init_s wrap wb) = wb /\ i_hold (init_s wrap wb) = 0 /\ i_bits (init_s wrap wb) = 0.
Proof.
  intros R. destruct (init_s_fields wrap wb R) as (A & B & _ & D & _ & _ & _ & _ & _ & _ & H & Ho & Bi & _).
  repeat split; assumption.
Qed.

Lemma irr_hd0 (src: list Z) : ir_hd src 0 0 0.
Proof. unfold ir_hd. rewrite sublist_nil. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariants                                                                                 *)

Definition I1 (w: Z) (src: list Z) (pos: Z) (z: zfields) (L: live) : Prop :=
  wbits_ok w = true /\ IRinv (ir_wb0 w) (ir_iw w) src pos z L z L.

Definition I2 (w2: Z) (src: list Z) (pos: Z) (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  wbits_ok w2 = true /\ IRinv (ir_wb0 w2) (ir_iw w2) src pos za La zb Lb.

Lemma ir_run : head_sim_stmt -> hdr_sim_stmt -> dict_sim_stmt -> block_sim_stmt -> fast_sim_stmt -> dec_sim_stmt -> tab_sim_stmt -> (Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt) -> ir_theory_stmt.
Proof.
  intros HE HD DI BL FA DE TA TDc SM CV FX.
  pose proof (irl_step SM CV (TDc CV) HE HD DI BL FA DE TA) as ST.
  exists I1, I2. constructor.
  - (* inflateInit2_ *)
    intros w src z sp W _ _ _ _ _ _ _. split; [exact W|].
    destruct (irr_iw w W) as (WRr & _ & _ & _).
    unfold init_live. rewrite (irr_wb_some w W). cbn [l_s].
    destruct (irr_init_s (ir_wrap w) (ir_wb0 w) WRr) as (M & Wr & H & Wb & Ho & Bi).
    constructor; cbn [l_s];
      [apply irl_srel_refl | exact Wr | exact H | left; exact Wb | left; exact Wb |
       intros _ _; rewrite Ho, Bi; apply irr_hd0 | rewrite M; irl_md | reflexivity ..].
  - intros w src pos z L (_ & IV). exact (iv_head _ _ _ _ _ _ _ _ IV).
  - intros w2 src pos za La zb Lb (_ & IV). split; [|exact (iv_head _ _ _ _ _ _ _ _ IV)].
    rewrite (sr_head _ _ _ (iv_rel _ _ _ _ _ _ _ _ IV)). exact (iv_head _ _ _ _ _ _ _ _ IV).
  - (* phase 1 *)
    intros w src pos z L strmp flush ib inp o ain aout r z' st' ow (W & IV) LV ZF SN P0 A0 PA SL BS AO FL IB EI
      REL NM.
    destruct (irc_call SM ST _ _ src pos z L z L strmp strmp flush ib ib inp o o ain aout r z' st' ow r z' st' ow
                IV LV LV ZF ZF SN SN P0 A0 PA SL BS AO IB IB EI REL NM REL NM)
      as (La' & Lb' & E1 & E2 & _ & _ & _ & _ & _ & B1 & B2 & IV').
    rewrite E1 in E2. inversion E2; subst Lb'.
    exists La'. split; [exact E1|]. split; [lia|]. split; [lia|]. split; [exact W | exact IV'].
  - (* the reset *)
    intros w src pos za La rst1 w2 (W & IV) LV ZF R1 W2 RG.
    pose proof (irr_wb_some w2 W2) as E2.
    destruct (irr_wb w2 _ _ E2) as (WB1 & WB2 & WB3).
    destruct (irr_iw w2 W2) as (WRr & WRg & WR0 & WR8).
    destruct LV as (SP & SW & MW & HW & S3 & WS & LV1 & LV2 & LV3).
    destruct IV as [IVr IVw IVh IVwa IVwb IVhd IVs IVtin IVtout IVmsg IVdt IVad].
    destruct (irr_init_s (ir_wrap w2) (ir_wb0 w2) WRr) as (M & Wr & H & Wb & Ho & Bi).
    assert (WBr: 0 <= ir_wb0 w2 <= 23) by lia.
    assert (NZ: 0 <= w2 -> ir_iw w2 <> 0) by (intros N Z; apply WR0 in Z; specialize (WB3 N); lia).
    destruct rst1.
    + specialize (R1 eq_refl). subst w2.
      (* bit 3 of wrap: the window size came from the header (wb = 0, a wrapped stream) *)
      assert (HW8: Z.land (i_wrap (l_s La)) 8 <> 0 -> ir_wb0 w = 0 /\ 0 <= w).
      { rewrite IVw. intros B. destruct (Z.eqb_spec (ir_wb0 w) 0) as [Q|Q].
        - split; [exact Q|]. destruct (Z_lt_le_dec w 0) as [N|N]; [specialize (WB2 N); lia | exact N].
        - cbn [negb] in WR8. apply Z.eqb_eq in WR8. contradiction. }
      destruct (reset_full_fields (l_s La)) as (FW & FB & _).
      unfold reset_out, reset_f, fst3, snd3, thd3. cbn [fst snd].
      split; [reflexivity|]. split.
      * rewrite irr_reset_full. apply irr_live_rk; [exact SP | exact HW | exact WS | exact (irr_swf_hdr _ SW) | reflexivity |].
        unfold reset_hdr_s. destruct (Z.eqb_spec (Z.land (i_wrap (l_s La)) 8) 0) as [B8|B8].
        -- exact LV1.
        -- destruct (HW8 B8) as [_ N]. intros _. split; [|reflexivity].
           change (Z.land (i_wrap (l_s La)) 3 <> 0). rewrite IVw. exact (irr_iw_land3 w N W).
      * intros zb sp SPb LVb ZFb T0 O0 M0 D0 AN AP. split; [exact W|].
        unfold init_live in *. rewrite E2 in *. cbn [l_s set_l_s] in *.
        constructor; cbn [l_s set_l_s].
        -- rewrite irr_reset_full, (init_s_eq _ _ WRr), irr_reset_s.
           apply irr_srel_rk; unfold reset_hdr_s;
             destruct (Z.land (i_wrap (l_s La)) 8 =? 0); irr_simpl; try reflexivity; exact IVw.
        -- exact Wr.
        -- exact H.
        -- rewrite FB. destruct (Z.eqb_spec (Z.land (i_wrap (l_s La)) 8) 0) as [B8|B8]; [exact IVwa|].
           left. symmetry. exact (proj1 (HW8 B8)).
        -- left; exact Wb.
        -- intros _ _. rewrite Ho, Bi. apply irr_hd0.
        -- rewrite M. irl_md.
        -- rewrite T0. reflexivity.
        -- rewrite O0. reflexivity.
        -- rewrite M0. reflexivity.
        -- rewrite D0. reflexivity.
        -- destruct (Z_lt_le_dec w 0) as [N|N]; [rewrite (AN N); reflexivity|].
           rewrite (AP N), Wr. unfold reset_keep_z. cbn [zf_adler].
           rewrite FW, IVw. fold (ir_iw w).
           destruct (Z.eqb_spec (ir_iw w) 0) as [Z|Z]; [exfalso; exact (NZ N Z) | reflexivity].
    + unfold reset_out, reset2_f, fst3, snd3, thd3. rewrite E2. cbn [fst snd].
      split; [reflexivity|]. split.
      * rewrite (irr_reset2_s _ _ _ WRr). apply irr_live_rk; [exact SP | exact HW | exact WS | | reflexivity |].
        -- exact (proj1 (irr_swf_clear (l_s La) (ir_iw w2) (ir_wb0 w2) _ SW WRg WBr)).
        -- irr_simpl. intros B. assert (N: 0 <= w2) by (destruct (Z_lt_le_dec w2 0) as [N|N]; [specialize (WB2 N); lia | exact N]).
           split; [apply irr_iw_land3; [exact N | exact W2]|].
           rewrite B. cbn. rewrite orb_true_r. reflexivity.
      * intros zb sp SPb LVb ZFb T0 O0 M0 D0 AN AP. split; [exact W2|].
        unfold init_live in *. rewrite E2 in *. cbn [l_s set_l_s] in *.
        constructor; cbn [l_s set_l_s].
        -- rewrite (irr_reset2_s _ _ _ WRr), (init_s_eq _ _ WRr), irr_reset_s.
           apply irr_srel_rk; irr_simpl; reflexivity.
        -- exact Wr.
        -- exact H.
        -- left. rewrite (irr_reset2_s _ _ _ WRr). irr_simpl. reflexivity.
        -- left; exact Wb.
        -- intros _ _. rewrite Ho, Bi. apply irr_hd0.
        -- rewrite M. irl_md.
        -- rewrite T0. reflexivity.
        -- rewrite O0. reflexivity.
        -- rewrite M0. reflexivity.
        -- rewrite D0. reflexivity.
        -- destruct (Z_lt_le_dec w2 0) as [N|N]; [rewrite (AN N); reflexivity|].
           rewrite (AP N), Wr. unfold reset_keep_z. cbn [zf_adler].
           rewrite (irr_reset2_s _ _ _ WRr). irr_simpl. fold (ir_iw w2).
           destruct (Z.eqb_spec (ir_iw w2) 0) as [Z|Z]; [exfalso; exact (NZ N Z) | reflexivity].
  - (* phase 2 *)
    intros w2 src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa rb zb' stb' owb
      (W & IV) LVa LVb ZFa ZFb SNa SNb P0 A0 PA SL BS AO FL IBa IBb EI RA NA RB NB.
    destruct (irc_call SM ST _ _ src pos za La zb Lb strma strmb flush iba ibb inp oa ob ain aout ra za' sta' owa
                rb zb' stb' owb IV LVa LVb ZFa ZFb SNa SNb P0 A0 PA SL BS AO IBa IBb EI RA NA RB NB)
      as (La' & Lb' & E1 & E2 & R & AI & AO' & OW & LO & B1 & B2 & IV').
    exists La', Lb'.
    do 7 (split; [assumption|]).
    split; [exact (iv_tin _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_tout _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_dt _ _ _ _ _ _ _ _ IV')|].
    split; [exact (iv_msg _ _ _ _ _ _ _ _ IV')|].
    split; [intros _; exact (iv_adler _ _ _ _ _ _ _ _ IV')|].
    split; [exact B1|]. split; [exact B2|].
    split; [exact W | exact IV'].
Qed.

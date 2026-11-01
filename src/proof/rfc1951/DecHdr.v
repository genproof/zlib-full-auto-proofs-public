(* Part of the decode theory: inflateInit2's state; the passes from HEAD, FLAGS, TIME, OS.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateInit2's windowBits                                                                      *)

Lemma dh_wb_cases wb : 8 <= wb <= 15 ->
  wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15.
Proof. lia. Qed.

Lemma dh_reset2_vals wb : 8 <= wb <= 15 ->
  reset2_wb (- wb) = Some (0, wb) /\ reset2_wb wb = Some (5, wb) /\ reset2_wb 0 = Some (5, 0) /\
  reset2_wb (16 + wb) = Some (6, wb) /\ reset2_wb (32 + wb) = Some (7, wb).
Proof.
  intros H. apply dh_wb_cases in H.
  repeat destruct H as [H|H]; subst wb; repeat split; reflexivity.
Qed.

(* the wrap and wbits inflateInit2 gives an accepting windowBits *)
Definition dh_wrapwb (G: dctx) (wrap wb0: Z) : Prop :=
  match dc_w G with
  | WRaw => wrap = 0 /\ wb0 = dc_wb G
  | WZlib _ _ _ => wrap = 5 /\ (wb0 = dc_wb G \/ wb0 = 0) \/ wrap = 7 /\ wb0 = dc_wb G
  | WGzip _ => (wrap = 6 \/ wrap = 7) /\ wb0 = dc_wb G
  end.

Lemma dh_reset2 G wrap wb0 : dctx_ok G -> reset2_wb (dc_iw G) = Some (wrap, wb0) -> dh_wrapwb G wrap wb0.
Proof.
  intros (Hs & Ha & _) E. destruct Hs as (Hwb & _).
  destruct (dh_reset2_vals _ Hwb) as (R1 & R2 & R3 & R4 & R5).
  unfold accepts in Ha. unfold dh_wrapwb.
  destruct (dc_w G).
  - rewrite Ha, R1 in E. inversion E; auto.
  - destruct Ha as [A|[A|A]]; rewrite A in E.
    + rewrite R2 in E. inversion E; auto.
    + rewrite R3 in E. inversion E; auto.
    + rewrite R5 in E. inversion E; auto.
  - destruct Ha as [A|A]; rewrite A in E.
    + rewrite R4 in E. inversion E; auto.
    + rewrite R5 in E. inversion E; auto.
Qed.

Lemma dh_reset2_ok G : dctx_ok G -> exists wrap wb0, reset2_wb (dc_iw G) = Some (wrap, wb0).
Proof.
  intros (Hs & Ha & _). destruct Hs as (Hwb & _).
  destruct (dh_reset2_vals _ Hwb) as (R1 & R2 & R3 & R4 & R5).
  unfold accepts in Ha. destruct (dc_w G).
  - rewrite Ha; eauto.
  - destruct Ha as [A|[A|A]]; rewrite A; eauto.
  - destruct Ha as [A|A]; rewrite A; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* (1) inflateInit2's state                                                                       *)

(* the wrap inflateInit2 stores: with fix F8, bit 3 set when the window size comes from the header (wb0 = 0) *)
Lemma dh_rw wrap wb0 : wb0 <> 0 -> reset2_wrap wrap wb0 = wrap.
Proof. intros H. unfold reset2_wrap. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma dh_init_fields wrap wb0 : 0 <= wrap <= 7 ->
  let s := init_s wrap wb0 in
  i_mode s = HEAD /\ i_hold s = 0 /\ i_bits s = 0 /\ i_last s = 0 /\ i_wsize s = 0 /\
  i_wrap s = reset2_wrap wrap wb0 /\ i_wbits s = wb0 /\ i_head s = false /\ i_total s = 0.
Proof.
  intros H. assert (L: Z.land (reset2_wrap wrap wb0) 8 = if wb0 =? 0 then 8 else 0).
  { unfold reset2_wrap. assert (C: wrap = 0 \/ wrap = 1 \/ wrap = 2 \/ wrap = 3 \/ wrap = 4 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7)
      by lia.
    destruct (wb0 =? 0); destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity. }
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s. cbn [i_win andb]. cbn [i_wrap set_i_wbits set_i_wrap].
  rewrite L. destruct (Z.eqb_spec wb0 0) as [E|E]; cbn; [subst wb0|]; repeat split; reflexivity.
Qed.

Lemma dh_init : decode_init_stmt.
Proof.
  intros G sp Hok Hh Hnd.
  destruct (dh_reset2_ok G Hok) as (wrap & wb0 & E).
  unfold init_live. cbn [l_s]. rewrite E.
  assert (Rw : 0 <= wrap <= 7) by (destruct (reset2_wb_cases _ _ _ E); lia).
  destruct (dh_init_fields wrap wb0 Rw) as (Fm & Fh & Fb & Fl & Fw & Fwr & Fwb & Fhd & Ft).
  set (s := init_s wrap wb0) in *.
  unfold dinv. split; [|split; [|split; [|split]]].
  - unfold at_mode. rewrite Fh, Fb. split.
    + unfold hold_ok. split; [lia|]. split; [apply Zlength_nonneg|]. rewrite sublist_nil. reflexivity.
    + left. split; [exact Fm|]. unfold at_head. rewrite Hh, Fl, Ft.
      repeat split; try lia; try (intros; lia).
      intros wb fl i Ew. specialize (Hnd _ _ _ Ew). discriminate.
  - unfold glob_ok. split; [exists wb0; rewrite Fwr; split; [apply init_wrap_wb_of; exact E|auto]|]. split; [exact Fhd|].
    rewrite Fm. split; intros; congruence.
  - intros _. left. split; auto.
  - unfold chk_ok. rewrite Fm. intros _ N. congruence.
  - unfold produced. rewrite Hh. reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The machine: moving the bit buffer, NEEDBITS                                                   *)

Definition dh_mv (m: mst) (nx hold bits: Z) : mst := set_m_bits (set_m_hold (set_m_nx m nx) hold) bits.

Lemma dh_mv_id m : dh_mv m (m_nx m) (m_hold m) (m_bits m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma dh_mv_mv m a b c a' b' c' : dh_mv (dh_mv m a b c) a' b' c' = dh_mv m a' b' c'.
Proof. destruct m; reflexivity. Qed.

(* the input offered: the next bytes of src *)
Definition dh_in (G: dctx) (pos: Z) (m: mst) : Prop :=
  0 <= pos /\ pos + Zlength (m_inp m) <= Zlength (dc_src G) /\
  m_inp m = sublist pos (pos + Zlength (m_inp m)) (dc_src G) /\ bytes_ok (dc_src G) /\
  0 <= m_nx m <= Zlength (m_inp m).

Lemma dh_nbS k n m :
  needbits_f (S k) n m =
  if m_bits m <? n then if m_have m =? 0 then set_leave m else needbits_f k n (pull m) else m.
Proof. reflexivity. Qed.

Lemma dh_nb (K: dkit_stmt) G pos : forall k n m,
  dh_in G pos m -> hold_ok G (pos + m_nx m) (m_hold m) (m_bits m) -> 0 <= m_bits m -> n <= 32 ->
  n <= m_bits m + 8 * Z.of_nat k ->
  exists nx' hold' bits' (lv: bool),
    needbits_f k n m = (if lv then set_leave (dh_mv m nx' hold' bits') else dh_mv m nx' hold' bits') /\
    m_nx m <= nx' <= Zlength (m_inp m) /\ bits' = m_bits m + 8 * (nx' - m_nx m) /\
    hold_ok G (pos + nx') hold' bits' /\
    (if lv then nx' = Zlength (m_inp m) /\ bits' < n
     else n <= bits' /\ (m_bits m < n -> bits' < n + 8) /\ (n <= m_bits m -> nx' = m_nx m)).
Proof.
  intros k; induction k as [|k IH]; intros n m Hin Hh Hb Hn Hk.
  { exists (m_nx m), (m_hold m), (m_bits m), false. rewrite dh_mv_id.
    destruct Hin as (_ & _ & _ & _ & Hnx). split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [exact Hh|]. change (Z.of_nat 0) with 0 in Hk. lia. }
  rewrite dh_nbS.
  destruct (Z.ltb_spec (m_bits m) n) as [Lt|Ge].
  2: { exists (m_nx m), (m_hold m), (m_bits m), false. rewrite dh_mv_id.
       destruct Hin as (_ & _ & _ & _ & Hnx). split; [reflexivity|]. split; [lia|]. split; [lia|].
       split; [exact Hh|]. lia. }
  pose proof Hin as (Hp & Hl & Hs & Hby & Hnx).
  destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
  { exists (m_nx m), (m_hold m), (m_bits m), true. rewrite dh_mv_id.
    unfold m_have in H0. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hh|]. lia. }
  unfold m_have in H0.
  assert (Eb : Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src G)).
  { rewrite Hs at 1. rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Ep : pull m = dh_mv m (m_nx m + 1) ((m_hold m + Znth (pos + m_nx m) (dc_src G) * 2 ^ m_bits m) mod 2 ^ 64)
                         (m_bits m + 8)).
  { unfold pull, dh_mv, u64, u32. rewrite Eb. f_equal. apply Z.mod_small. lia. }
  assert (Hh1 : hold_ok G (pos + (m_nx m + 1))
                  ((m_hold m + Znth (pos + m_nx m) (dc_src G) * 2 ^ m_bits m) mod 2 ^ 64) (m_bits m + 8)).
  { replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia. apply (dk_pull K); auto; lia. }
  set (m1 := pull m) in *.
  assert (Hin1 : dh_in G pos m1).
  { rewrite Ep. unfold dh_in, dh_mv. cbn [m_inp m_nx set_m_bits set_m_hold set_m_nx]. repeat split; auto; lia. }
  assert (B1 : m_bits m1 = m_bits m + 8) by (rewrite Ep; reflexivity).
  assert (N1 : m_nx m1 = m_nx m + 1) by (rewrite Ep; reflexivity).
  assert (I1 : m_inp m1 = m_inp m) by (rewrite Ep; reflexivity).
  assert (H1 : m_hold m1 = (m_hold m + Znth (pos + m_nx m) (dc_src G) * 2 ^ m_bits m) mod 2 ^ 64)
    by (rewrite Ep; reflexivity).
  destruct (IH n m1 Hin1) as (nx' & hold' & bits' & lv & E & R1 & R2 & R3 & R4);
    [rewrite N1, H1, B1; exact Hh1 | lia | lia | rewrite B1; lia |].
  exists nx', hold', bits', lv. rewrite E.
  assert (EE : forall a b c, dh_mv m1 a b c = dh_mv m a b c) by (intros; rewrite Ep; apply dh_mv_mv).
  rewrite !EE. rewrite N1, B1, I1 in *. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact R3|].
  destruct lv; [exact R4|]. destruct R4 as (R4 & R5 & R6). split; [lia|]. split; [|lia].
  intros _. destruct (Z_lt_le_dec (m_bits m + 8) n); [auto|]. specialize (R6 l). lia.
Qed.

Lemma dh_mv_fields m a b c :
  m_s (dh_mv m a b c) = m_s m /\ m_h (dh_mv m a b c) = m_h m /\ m_inp (dh_mv m a b c) = m_inp m /\
  m_ow (dh_mv m a b c) = m_ow m /\ m_out (dh_mv m a b c) = m_out m /\ m_aout (dh_mv m a b c) = m_aout m /\
  m_ret (dh_mv m a b c) = m_ret m /\ m_tout (dh_mv m a b c) = m_tout m /\ m_leave (dh_mv m a b c) = m_leave m /\
  m_nx (dh_mv m a b c) = a /\ m_hold (dh_mv m a b c) = b /\ m_bits (dh_mv m a b c) = c.
Proof. destruct m; repeat split; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header bytes                                                                               *)

Lemma dh_Zlength_bits_le v : Zlength (bits_le v 8) = 8.
Proof. reflexivity. Qed.

Lemma dh_Zlength_bb l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, dh_Zlength_bits_le, Zlength_cons. lia.
Qed.

Lemma dh_bb_app a b : bytes_bits (a ++ b) = bytes_bits a ++ bytes_bits b.
Proof. unfold bytes_bits. apply flat_map_app. Qed.

Lemma dh_sub_bb l1 l2 l3 :
  sublist (8 * Zlength l1) (8 * Zlength l1 + 8 * Zlength l2) (bytes_bits (l1 ++ l2 ++ l3)) = bytes_bits l2.
Proof.
  rewrite !dh_bb_app. rewrite sublist_app2 by (rewrite dh_Zlength_bb; pose proof (Zlength_nonneg l1); lia).
  rewrite dh_Zlength_bb. replace (8 * Zlength l1 - 8 * Zlength l1) with 0 by lia.
  replace (8 * Zlength l1 + 8 * Zlength l2 - 8 * Zlength l1) with (Zlength (bytes_bits l2))
    by (rewrite dh_Zlength_bb; lia).
  rewrite sublist_app1 by (pose proof (Zlength_nonneg (bytes_bits l2)); lia).
  apply sublist_same; reflexivity.
Qed.

Lemma dh_hdr_prefix w hist bs : exists rest, stream_bytes w hist bs = hdr_bytes w ++ rest.
Proof.
  destruct w; cbn [stream_bytes hdr_bytes].
  - exists (deflate_bytes bs). reflexivity.
  - eexists. rewrite <- app_assoc. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma dh_hdr_slen G : Zlength (hdr_bytes (dc_w G)) <= slen G.
Proof.
  unfold slen. destruct (dh_hdr_prefix (dc_w G) (dc_hist G) (dc_bs G)) as (r & E). rewrite E, Zlength_app.
  pose proof (Zlength_nonneg r). lia.
Qed.

(* bits [x, y) of the input inside the header *)
Lemma dh_hdr_bits (K: dkit_stmt) G x y : dctx_ok G -> 0 <= x <= y -> y <= D0 G ->
  sublist x y (sbits G) = sublist x y (bytes_bits (hdr_bytes (dc_w G))).
Proof.
  intros Hok Hx Hy. rewrite <- (dk_hdr K G Hok). rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the zlib headers *)
Lemma dh_fl_cases fl : 0 <= fl <= 3 -> fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3.
Proof. lia. Qed.

Definition dh_zhdr_okb (wb fl: Z) : bool :=
  let H := bval (bytes_bits (zlib_hdr wb fl false)) in
  negb (H =? 35615) && (((H mod 256) * 256 + Z.shiftr H 8) mod 31 =? 0) && (H mod 16 =? 8) &&
  (Z.shiftr H 4 mod 16 + 8 =? wb) && (Z.land (Z.shiftr H 4) 512 =? 0).

Lemma dh_zhdr_ok wb fl : 8 <= wb <= 15 -> 0 <= fl <= 3 -> dh_zhdr_okb wb fl = true.
Proof.
  intros Hw Hf. apply dh_wb_cases in Hw. apply dh_fl_cases in Hf.
  repeat destruct Hw as [Hw|Hw]; subst wb; repeat destruct Hf as [Hf|Hf]; subst fl; vm_compute; reflexivity.
Qed.

Lemma dh_zhdr wb fl : 8 <= wb <= 15 -> 0 <= fl <= 3 ->
  let H := bval (bytes_bits (zlib_hdr wb fl false)) in
  (H =? 35615) = false /\ ((H mod 256) * 256 + Z.shiftr H 8) mod 31 = 0 /\ H mod 16 = 8 /\
  Z.shiftr H 4 mod 16 + 8 = wb /\ Z.land (Z.shiftr H 4) 512 = 0.
Proof.
  intros Hw Hf. pose proof (dh_zhdr_ok wb fl Hw Hf) as E. unfold dh_zhdr_okb in E. cbv zeta in *.
  rewrite !andb_true_iff in E. destruct E as ((((E1 & E2) & E3) & E4) & E5).
  apply negb_true_iff in E1. apply Z.eqb_eq in E2, E3, E4, E5. auto.
Qed.

Lemma dh_zlib_len wb fl : Zlength (zlib_hdr wb fl false) = 2.
Proof. reflexivity. Qed.

(* the gzip headers covered *)
Lemma dh_gz_simple_bytes h : gz_simple h ->
  gz_bytes h = [31; 139] ++ [8; if gz_text h then 1 else 0] ++ (le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h]) /\
  gz_flg h = (if gz_text h then 1 else 0).
Proof.
  intros (E1 & E2 & E3 & E4). unfold gz_bytes, gz_bytes0, gz_flg. rewrite E1, E2, E3, E4.
  rewrite !app_nil_r. destruct (gz_text h); split; reflexivity.
Qed.

Lemma dh_gz_len h : gz_simple h -> Zlength (gz_bytes h) = 10.
Proof. intros S. rewrite (proj1 (dh_gz_simple_bytes h S)). reflexivity. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The passes, on the machine                                                                     *)

(* what the header passes keep *)
Definition dh_keep (s s': istate) : Prop :=
  i_last s' = i_last s /\ i_total s' = i_total s /\ i_wrap s' = i_wrap s /\ i_head s' = i_head s /\
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\ i_wdata s' = i_wdata s.

Definition dh_same (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_ow m' = m_ow m /\ m_out m' = m_out m /\ m_aout m' = m_aout m /\
  m_ret m' = m_ret m /\ m_tout m' = m_tout m /\ dh_keep (m_s m) (m_s m').

Lemma dh_same_refl m : dh_same m m.
Proof. repeat split; reflexivity. Qed.

Lemma dh_same_trans m1 m2 m3 : dh_same m1 m2 -> dh_same m2 m3 -> dh_same m1 m3.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14)
         (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14).
  repeat split; congruence.
Qed.

Ltac dh_red := cbn [set_mode upd_s set_m_s initbits set_m_adler dropbits set_m_bits set_m_hold set_m_nx dh_mv
  set_m_leave set_leave upd_h set_m_h
  set_i_check set_i_flags set_i_dmax set_i_wbits set_i_mode set_i_length m_s m_h m_inp m_ow m_out m_aout m_ret m_tout
  m_leave m_nx m_hold m_bits m_adler i_last i_total i_wrap i_head i_wsize i_whave i_wnext i_wdata i_mode i_wbits
  i_flags i_check].

(* HEAD: the only lemma that unfolds the case HEAD (Model.c_HEAD2; Model2.c_HEAD2 after F7): the raw stream,
   NEEDBITS(16) running out, a valid zlib header without FDICT, the gzip magic *)
Lemma dh_head_step flush fx dx m :
  m_mode m = HEAD -> i_head (m_s m) = false -> m_leave m = 0 ->
  (i_wrap (m_s m) = 0 -> stepf2 flush fx dx m = IBrk (set_mode m TYPEDO)) /\
  (forall nx h b, i_wrap (m_s m) <> 0 -> needbits 16 m = set_leave (dh_mv m nx h b) ->
     stepf2 flush fx dx m = IBrk (set_leave (dh_mv m nx h b))) /\
  (forall nx h wb, (i_wrap (m_s m) = 5 \/ i_wrap (m_s m) = 7 \/ i_wrap (m_s m) = 13) -> needbits 16 m = dh_mv m nx h 16 ->
     (h =? 35615) = false -> ((h mod 256) * 256 + Z.shiftr h 8) mod 31 = 0 -> h mod 16 = 8 ->
     Z.shiftr h 4 mod 16 + 8 = wb -> Z.land (Z.shiftr h 4) 512 = 0 -> 8 <= wb <= 15 ->
     (i_wbits (m_s m) = 0 \/ i_wbits (m_s m) = wb) ->
     exists m2, stepf2 flush fx dx m = IBrk m2 /\ dh_same m m2 /\ m_leave m2 = 0 /\ m_nx m2 = nx /\
       m_hold m2 = 0 /\ m_bits m2 = 0 /\ i_mode (m_s m2) = Zlib.proof.inflate.Model.TYPE /\
       i_wbits (m_s m2) = wb /\ i_flags (m_s m2) = 0 /\ i_check (m_s m2) = 1) /\
  (forall nx, (i_wrap (m_s m) = 6 \/ i_wrap (m_s m) = 7) -> needbits 16 m = dh_mv m nx 35615 16 ->
     i_wbits (m_s m) <> 0 ->
     exists m2, stepf2 flush fx dx m = IBrk m2 /\ dh_same m m2 /\ m_leave m2 = 0 /\ m_nx m2 = nx /\
       m_hold m2 = 0 /\ m_bits m2 = 0 /\ i_mode (m_s m2) = FLAGS /\ i_wbits (m_s m2) = i_wbits (m_s m)).
Proof.
  intros Hmd Hhd Hlv.
  assert (St : stepf2 flush fx dx m = c_HEAD2 m).
  { unfold stepf2, step2. cbv zeta. rewrite Hmd. reflexivity. }
  rewrite St. clear St.
  split; [|split; [|split]].
  - intros W. unfold c_HEAD2. rewrite W. reflexivity.
  - intros nx h b W E. unfold c_HEAD2. cbv zeta. rewrite E.
    rewrite <- Z.eqb_neq in W. rewrite W. reflexivity.
  - intros nx h wb W E H1 H2 H3 H4 H5 Hwb Hwb0. unfold c_HEAD2. cbv zeta. rewrite E.
    dh_red. rewrite Hhd, Hlv. dh_red. replace (Z.shiftr h 4 mod 16 + 8) with wb by lia. rewrite H5, H1, H2, H3.
    assert (L1 : Z.land (i_wrap (m_s m)) 2 = 0 \/ Z.land (i_wrap (m_s m)) 2 = 2)
      by (destruct W as [W|[W|W]]; rewrite W; auto).
    assert (L2 : Z.land (i_wrap (m_s m)) 1 = 1) by (destruct W as [W|[W|W]]; rewrite W; auto).
    rewrite L2. cbn [Z.eqb negb andb orb Pos.eqb].
    rewrite andb_false_r.
    assert (Ew : (if i_wbits (m_s m) =? 0 then wb else i_wbits (m_s m)) = wb).
    { destruct Hwb0 as [B|B]; rewrite B; [reflexivity|]. replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      reflexivity. }
    (* patch F7 (Model2.c_HEAD2): the window size is checked before it is stored *)
    assert (Ck : (15 <? wb) || (negb (i_wbits (m_s m) =? 0) && (i_wbits (m_s m) <? wb)) = false).
    { replace (15 <? wb) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct Hwb0 as [B|B]; rewrite B; [reflexivity|]. rewrite Z.ltb_irrefl. apply andb_false_r. }
    rewrite Ck.
    replace (i_wrap (m_s m) =? 0) with false by (destruct W as [W|[W|W]]; rewrite W; reflexivity).
    eexists; split; [reflexivity|]. unfold dh_same, dh_keep. dh_red. rewrite Ew.
    repeat split; try reflexivity; auto.
  - intros nx W E Hw0. unfold c_HEAD2. cbv zeta. rewrite E. dh_red. rewrite Hlv.
    replace (i_wrap (m_s m) =? 0) with false by (destruct W as [W|W]; rewrite W; reflexivity).
    replace (Z.land (i_wrap (m_s m)) 2) with 2 by (destruct W as [W|W]; rewrite W; reflexivity).
    cbn [Z.eqb negb andb Pos.eqb].
    eexists; split; [reflexivity|]. unfold dh_same, dh_keep. dh_red.
    rewrite (proj2 (Z.eqb_neq _ _) Hw0).
    repeat split; try reflexivity; auto.
Qed.


(* the gzip flags of a covered header (FTEXT at most): 8 + 256 * FLG *)
Definition dh_gzf (f: Z) : Prop := f = 8 \/ f = 264.

Lemma dh_gzf_land f : dh_gzf f ->
  Z.land f 512 = 0 /\ Z.land f 1024 = 0 /\ Z.land f 2048 = 0 /\ Z.land f 4096 = 0 /\
  Z.land f 255 = 8 /\ Z.land f 57344 = 0 /\ s32 f = f.
Proof. intros [E|E]; subst f; repeat split; reflexivity. Qed.

Lemma dh_os1 m nx h b : i_head (m_s m) = false -> m_leave m = 0 -> Z.land (i_flags (m_s m)) 512 = 0 ->
  needbits 16 m = dh_mv m nx h b -> c_OS2 m = c_EXLEN2 (set_mode (initbits (dh_mv m nx h b)) EXLEN).
Proof.
  intros Hhd Hlv F1 E. unfold c_OS2. cbv zeta. rewrite E. dh_red. rewrite Hlv, Hhd. cbn [Z.eqb].
  unfold crc_if. dh_red. rewrite F1. cbn [Z.eqb negb andb]. reflexivity.
Qed.

Lemma dh_exlen m : i_head (m_s m) = false -> Z.land (i_flags (m_s m)) 1024 = 0 ->
  c_EXLEN2 m = c_EXTRA2 (set_mode m EXTRA).
Proof.
  intros Hhd F. unfold c_EXLEN2. rewrite F, Hhd. reflexivity.
Qed.

Lemma dh_extra m : Z.land (i_flags (m_s m)) 1024 = 0 ->
  c_EXTRA2 m = c_NAME2 (set_mode (upd_s m (fun s => set_i_length s 0)) NAME).
Proof.
  intros F. unfold c_EXTRA2. cbv zeta. rewrite F. reflexivity.
Qed.

Lemma dh_name m : i_head (m_s m) = false -> Z.land (i_flags (m_s m)) 2048 = 0 ->
  c_NAME2 m = c_COMMENT2 (set_mode (upd_s m (fun s => set_i_length s 0)) COMMENT).
Proof.
  intros Hhd F. unfold c_NAME2. cbv zeta. rewrite F, Hhd. reflexivity.
Qed.

Lemma dh_comment m : i_head (m_s m) = false -> Z.land (i_flags (m_s m)) 4096 = 0 ->
  c_COMMENT2 m = c_HCRC (set_mode m HCRC).
Proof.
  intros Hhd F. unfold c_COMMENT2. cbv zeta. rewrite F, Hhd. reflexivity.
Qed.

Lemma dh_hcrc m : i_head (m_s m) = false -> Z.land (i_flags (m_s m)) 512 = 0 ->
  c_HCRC m = IBrk (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 0)) 0) Zlib.proof.inflate.Model.TYPE).
Proof.
  intros Hhd F. unfold c_HCRC. cbv zeta. rewrite F, Hhd. reflexivity.
Qed.

Lemma dh_os_step m :
  i_head (m_s m) = false -> m_leave m = 0 -> dh_gzf (i_flags (m_s m)) ->
  (forall nx h b, needbits 16 m = set_leave (dh_mv m nx h b) -> c_OS2 m = IBrk (set_leave (dh_mv m nx h b))) /\
  (forall nx h b, needbits 16 m = dh_mv m nx h b ->
     exists m2, c_OS2 m = IBrk m2 /\ dh_same m m2 /\ m_leave m2 = 0 /\ m_nx m2 = nx /\
       m_hold m2 = 0 /\ m_bits m2 = 0 /\ i_mode (m_s m2) = Zlib.proof.inflate.Model.TYPE /\
       i_wbits (m_s m2) = i_wbits (m_s m) /\ i_flags (m_s m2) = i_flags (m_s m) /\ i_check (m_s m2) = 0).
Proof.
  intros Hhd Hlv Hf. destruct (dh_gzf_land _ Hf) as (F1 & F2 & F3 & F4 & _).
  split.
  - intros nx h b E. unfold c_OS2. cbv zeta. rewrite E. dh_red. cbn [Z.eqb Pos.eqb]. reflexivity.
  - intros nx h b E. rewrite (dh_os1 m nx h b Hhd Hlv F1 E).
    rewrite dh_exlen by (dh_red; auto). rewrite dh_extra by (dh_red; auto).
    rewrite dh_name by (dh_red; auto). rewrite dh_comment by (dh_red; auto). rewrite dh_hcrc by (dh_red; auto).
    eexists; split; [reflexivity|]. unfold dh_same, dh_keep. dh_red.
    repeat split; try reflexivity; auto.
Qed.

Lemma dh_time_step m :
  i_head (m_s m) = false -> m_leave m = 0 -> dh_gzf (i_flags (m_s m)) ->
  (forall nx h b, needbits 32 m = set_leave (dh_mv m nx h b) -> c_TIME2 m = IBrk (set_leave (dh_mv m nx h b))) /\
  (forall nx h b, needbits 32 m = dh_mv m nx h b -> c_TIME2 m = c_OS2 (set_mode (initbits (dh_mv m nx h b)) OS)).
Proof.
  intros Hhd Hlv Hf. destruct (dh_gzf_land _ Hf) as (F1 & F2 & F3 & F4 & _).
  split.
  - intros nx h b E. unfold c_TIME2. cbv zeta. rewrite E. dh_red. cbn [Z.eqb Pos.eqb]. reflexivity.
  - intros nx h b E. unfold c_TIME2. cbv zeta. rewrite E. dh_red. rewrite Hlv, Hhd. cbn [Z.eqb].
    unfold crc_if. dh_red. rewrite F1. cbn [Z.eqb negb andb]. reflexivity.
Qed.

Lemma dh_flags_step m :
  i_head (m_s m) = false -> m_leave m = 0 ->
  (forall nx h b, needbits 16 m = set_leave (dh_mv m nx h b) -> c_FLAGS2 m = IBrk (set_leave (dh_mv m nx h b))) /\
  (forall nx h b, needbits 16 m = dh_mv m nx h b -> dh_gzf h ->
     c_FLAGS2 m = c_TIME2 (set_mode (initbits (upd_s (dh_mv m nx h b) (fun s => set_i_flags s h))) TIME)).
Proof.
  intros Hhd Hlv.
  split.
  - intros nx h b E. unfold c_FLAGS2. cbv zeta. rewrite E. dh_red. cbn [Z.eqb Pos.eqb]. reflexivity.
  - intros nx h b E Hf. destruct (dh_gzf_land _ Hf) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    unfold c_FLAGS2. cbv zeta. rewrite E. dh_red. rewrite Hlv, F7, F5, F6. cbn [Z.eqb negb Pos.eqb].
    dh_red. rewrite Hhd.
    unfold crc_if. dh_red. rewrite F1. cbn [Z.eqb negb andb]. reflexivity.
Qed.

Lemma dh_step_md flush fx dx m :
  (m_mode m = FLAGS -> stepf2 flush fx dx m = c_FLAGS2 m) /\
  (m_mode m = TIME -> stepf2 flush fx dx m = c_TIME2 m) /\
  (m_mode m = OS -> stepf2 flush fx dx m = c_OS2 m).
Proof.
  unfold stepf2, step2. cbv zeta. repeat split; intros E; rewrite E; reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The invariant: reading and building at_mode, glob_ok, win_ok, chk_ok; the post-condition         *)

Ltac dh_modes_in H :=
  cbv [HEAD FLAGS TIME OS Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
       LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE] in H.

Lemma dh_at_head G s c h b out : at_mode G s c h b out -> i_mode s = HEAD ->
  hold_ok G c h b /\ at_head G s (8 * c - b) b out.
Proof.
  intros [Hh D] E. split; [exact Hh|]. cbv zeta in D. rewrite E in D.
  destruct D as [[_ A]|D]; [exact A|exfalso]. dh_modes_in D. intuition lia.
Qed.

Lemma dh_at_gz G s c h b out : at_mode G s c h b out -> i_mode s = FLAGS \/ i_mode s = TIME \/ i_mode s = OS ->
  hold_ok G c h b /\ at_gzhdr G s (8 * c - b) b out (i_mode s).
Proof.
  intros [Hh D] E. split; [exact Hh|]. cbv zeta in D.
  destruct D as [[M _]|[[_ A]|D]]; [|exact A|]; exfalso; rewrite ?M in E; dh_modes_in E; [lia|].
  destruct E as [E|[E|E]]; rewrite E in D; dh_modes_in D; intuition lia.
Qed.

Lemma dh_at_head_mk G s c h b out : hold_ok G c h b -> i_mode s = HEAD -> at_head G s (8 * c - b) b out ->
  at_mode G s c h b out.
Proof. intros Hh E A. split; [exact Hh|]. left. split; auto. Qed.

Lemma dh_at_gz_mk G s c h b out : hold_ok G c h b -> i_mode s = FLAGS \/ i_mode s = TIME \/ i_mode s = OS ->
  at_gzhdr G s (8 * c - b) b out (i_mode s) -> at_mode G s c h b out.
Proof. intros Hh E A. split; [exact Hh|]. right. left. split; auto. Qed.

Lemma dh_at_type_mk G s c h b out k : hold_ok G c h b ->
  i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO ->
  0 <= k <= nblk G -> 8 * c - b = bpos G k -> out = outk G k -> b < 8 ->
  i_last s = (if k =? 0 then 0 else lastflag G (k - 1)) -> at_mode G s c h b out.
Proof.
  intros Hh E Hk Hq Ho Hb Hl. split; [exact Hh|]. right. right. left. split; [exact E|].
  exists k. auto.
Qed.

Lemma dh_glob_mk G s s' : glob_ok G s -> i_wrap s' = i_wrap s -> i_head s' = false ->
  (i_mode s' = HEAD -> i_mode s = HEAD /\ i_wbits s' = i_wbits s) ->
  (i_mode s' <> HEAD -> dc_wb G <= i_wbits s' <= 15) ->
  (wrapped G = true -> i_mode s' <> HEAD -> i_mode s' <> FLAGS ->
     i_flags s' = match dc_w G with WGzip h => 8 + 256 * gz_flg h | _ => 0 end) ->
  glob_ok G s'.
Proof.
  intros ((wb0 & E & Hw) & _) Hwr Hhd Hm Hb Hf. split; [|split; [exact Hhd|split; [exact Hb|exact Hf]]].
  exists wb0. rewrite Hwr. split; [exact E|]. intros M. destruct (Hm M) as (M0 & W). rewrite W. auto.
Qed.

Lemma dh_win_mk G s s' ob : win_ok G s ob -> 0 <= i_wbits s ->
  i_wsize s' = i_wsize s -> i_whave s' = i_whave s -> i_wnext s' = i_wnext s -> i_wdata s' = i_wdata s ->
  (i_wbits s' = i_wbits s \/ i_wsize s = 0) -> win_ok G s' ob.
Proof.
  intros W Hb E1 E2 E3 E4 Hw. destruct W as [(W0 & Ob)|(Ws & Wh & Wf)].
  - left. rewrite E1. auto.
  - destruct Hw as [Hw|Hw].
    + right. rewrite E1, E2, Hw. split; [exact Ws|]. split; [exact Wh|].
      intros d Hd. unfold win_at. rewrite E1, E3, E4. apply Wf; auto.
    + exfalso. pose proof (Z.pow_pos_nonneg 2 (i_wbits s) ltac:(lia) Hb). lia.
Qed.

Lemma dh_chk_hdr G s ob ow : md_hdr (i_mode s) -> chk_ok G s ob ow.
Proof. unfold chk_ok, md_hdr. intros M _ A B C D. intuition. Qed.

Lemma dh_chkv_nil G : chkv G [] = match dc_w G with WZlib _ _ _ => 1 | _ => 0 end.
Proof. unfold chkv. destruct (dc_w G); reflexivity. Qed.

Lemma dh_chk_type G s ob ow : i_mode s = Zlib.proof.inflate.Model.TYPE -> ob = [] -> dc_hist G = [] ->
  i_check s = chkv G [] -> i_total s = 0 -> chk_ok G s ob ow.
Proof.
  intros M Ob Hh C T. unfold chk_ok. intros _ _ _ _ _. cbv zeta. rewrite M. cbn.
  subst ob. unfold produced. rewrite Hh. cbn. split; [exact C|]. split; [rewrite T; reflexivity|].
  exists []. reflexivity.
Qed.

Lemma dh_ac G md : md_hdr md \/ md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO -> after_check G md = false.
Proof.
  unfold after_check, md_hdr. intros H. destruct (wrapped G); [|reflexivity].
  repeat destruct H as [H|H]; subst md; reflexivity.
Qed.

Lemma dh_post G pos inp ob flush m m' :
  Kd G pos inp ob m -> md_hdr (m_mode m) -> dh_same m m' ->
  md_hdr (m_mode m') \/ m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = TYPEDO ->
  at_mode G (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m') ->
  glob_ok G (m_s m') -> win_ok G (m_s m') ob -> chk_ok G (m_s m') ob (m_ow m') ->
  (m_leave m' = 1 -> leave_why G pos inp ob flush m') ->
  dstep_post G pos inp ob flush m (IBrk m').
Proof.
  intros HK Hm (S1 & S2 & S3 & S4 & S5 & S6 & _) Hm' Ha Hg Hw Hc Hl.
  assert (A0 : after_check G (m_mode m) = false) by (apply dh_ac; auto).
  assert (A1 : after_check G (m_mode m') = false) by (apply dh_ac; auto).
  assert (D0 : (m_mode m =? DONE) = false).
  { apply Z.eqb_neq. unfold md_hdr in Hm. dh_modes_in Hm. unfold DONE. lia. }
  assert (D1 : (m_mode m' =? DONE) = false).
  { apply Z.eqb_neq. unfold md_hdr in Hm'. dh_modes_in Hm'. unfold DONE. lia. }
  cbn [dstep_post]. split; [|split; [exists []; rewrite app_nil_r; exact S2|exact Hl]].
  constructor.
  - rewrite S1. exact (kd_inp _ _ _ _ _ HK).
  - exact Ha.
  - exact Hg.
  - intros _. exact Hw.
  - exact Hc.
  - rewrite A1, S6. pose proof (kd_tout _ _ _ _ _ HK) as T. rewrite A0 in T. exact T.
  - rewrite A1, S3, S4. pose proof (kd_out _ _ _ _ _ HK) as T. rewrite A0 in T. exact T.
  - rewrite D1, S5. pose proof (kd_ret _ _ _ _ _ HK) as T. rewrite D0 in T. exact T.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The context of a pass                                                                          *)

Definition dh_ctx (G: dctx) (pos: Z) (inp ob: list Z) (m: mst) : Prop :=
  dctx_ok G /\ 0 <= pos /\ pos + Zlength inp <= Zlength (dc_src G) /\
  inp = sublist pos (pos + Zlength inp) (dc_src G) /\ Kd G pos inp ob m /\ mwf3 m /\ m_leave m = 0.

Lemma dh_in_of G pos inp ob m mx : dh_ctx G pos inp ob m -> m_inp mx = m_inp m ->
  0 <= m_nx mx <= Zlength (m_inp mx) -> dh_in G pos mx.
Proof.
  intros (Hok & Hp & Hl & Hi & HK & _) E N. pose proof (kd_inp _ _ _ _ _ HK) as I.
  unfold dh_in. rewrite E, I in *. destruct Hok as (_ & _ & _ & _ & _ & _ & Hb & _).
  repeat split; auto; lia.
Qed.

Lemma dh_same_mv x a b c : dh_same x (dh_mv x a b c).
Proof. unfold dh_same, dh_keep. dh_red. repeat split; reflexivity. Qed.

Lemma dh_same_lmv x a b c : dh_same x (set_leave (dh_mv x a b c)).
Proof. unfold dh_same, dh_keep. dh_red. repeat split; reflexivity. Qed.

Lemma dh_hold0 G c h b : hold_ok G c h b -> 0 <= c -> hold_ok G c 0 0.
Proof.
  intros (_ & Hc & _) H0. unfold hold_ok. split; [lia|]. split; [exact Hc|].
  rewrite Z.sub_0_r, sublist_nil. reflexivity.
Qed.

Lemma dh_gz_facts G h : dctx_ok G -> dc_w G = WGzip h ->
  gz_simple h /\ dc_hist G = [] /\ 8 <= dc_wb G <= 15 /\ D0 G = 80 /\ hdr_bytes (dc_w G) = gz_bytes h /\
  dh_gzf (8 + 256 * gz_flg h) /\ 10 <= slen G.
Proof.
  intros Hok E. pose proof (dh_hdr_slen G) as Sl.
  destruct Hok as ((Hwb & Hwo & _) & _ & Hs & _). rewrite E in Hwo. destruct Hwo as (_ & Hh).
  specialize (Hs h E). destruct (dh_gz_simple_bytes h Hs) as (_ & F).
  unfold D0. rewrite E in *. cbn [hdr_bytes] in *. rewrite (dh_gz_len h Hs) in *.
  split; [exact Hs|]. split; [exact Hh|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|lia]. unfold dh_gzf. rewrite F. destruct (gz_text h); auto.
Qed.

Lemma dh_win_same G m s' ob : mwf3 m -> win_ok G (m_s m) ob -> dh_keep (m_s m) s' ->
  (i_wbits s' = i_wbits (m_s m) \/ i_wsize (m_s m) = 0) -> win_ok G s' ob.
Proof.
  intros Hw W (_ & _ & _ & _ & E1 & E2 & E3 & E4) Wb.
  pose proof (sw_wbits _ (mw_s _ (proj1 Hw))).
  apply (dh_win_mk G (m_s m) s' ob W); auto; lia.
Qed.

Lemma dh_glob_gz G m s' h : glob_ok G (m_s m) -> m_mode m <> HEAD -> dc_w G = WGzip h ->
  i_wrap s' = i_wrap (m_s m) -> i_head s' = false -> i_mode s' <> HEAD -> i_wbits s' = i_wbits (m_s m) ->
  (i_mode s' <> FLAGS -> i_flags s' = 8 + 256 * gz_flg h) -> glob_ok G s'.
Proof.
  intros Hg Hm E Wr Hd Hm' Wb F. pose proof Hg as (_ & _ & Hb & _).
  apply (dh_glob_mk G (m_s m) s' Hg Wr Hd); [intros; contradiction| |].
  - intros _. rewrite Wb. apply Hb. exact Hm.
  - intros _ _ N. rewrite E. auto.
Qed.

Lemma dh_md_ne md : md_hdr md \/ md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO -> md < CHECK.
Proof. unfold md_hdr. intros H. dh_modes_in H. unfold CHECK. lia. Qed.

(* the gzip header from OS on: OS (16 bits) -> EXLEN .. HCRC (nothing, gz_simple) -> TYPE *)
Lemma dh_cont_os (K: dkit_stmt) G pos inp ob flush m mO h :
  dh_ctx G pos inp ob m -> md_hdr (m_mode m) -> m_mode m <> HEAD -> dc_w G = WGzip h ->
  dh_same m mO -> m_leave mO = 0 -> i_head (m_s mO) = false -> i_mode (m_s mO) = OS ->
  i_flags (m_s mO) = 8 + 256 * gz_flg h -> i_wbits (m_s mO) = i_wbits (m_s m) -> i_total (m_s m) = 0 ->
  0 <= m_nx mO <= Zlength (m_inp mO) -> hold_ok G (pos + m_nx mO) (m_hold mO) (m_bits mO) ->
  8 * (pos + m_nx mO) - m_bits mO = 64 -> 0 <= m_bits mO < 16 ->
  dstep_post G pos inp ob flush m (c_OS2 mO).
Proof.
  intros Hc Hm Hm0 Ew HS Hlv Hhd HmO Hfl Hwb Ht Hnx Hh Hq Hb.
  pose proof Hc as (Hok & Hp & Hl & Hi & HK & Hw & Hlv0).
  destruct (dh_gz_facts G h Hok Ew) as (Hs & Hhist & Hwbr & HD0 & Hhb & Hgzf & Hsl).
  pose proof HS as (S1 & S2 & S3 & S4 & S5 & S6 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  assert (Hmg : i_mode (m_s m) = FLAGS \/ i_mode (m_s m) = TIME \/ i_mode (m_s m) = OS).
  { unfold md_hdr, m_mode in Hm, Hm0. intuition. }
  destruct (dh_at_gz _ _ _ _ _ _ (kd_at _ _ _ _ _ HK) Hmg) as (_ & (h0 & _ & Hout & Hlast & _)).
  pose proof (kd_glob _ _ _ _ _ HK) as Hg.
  assert (Hwin : win_ok G (m_s m) ob) by (apply (kd_win _ _ _ _ _ HK); apply dh_md_ne; auto).
  assert (Ob : ob = []) by (rewrite Hhist in Hout; apply app_eq_nil in Hout; tauto).
  assert (Hin : dh_in G pos mO) by (apply (dh_in_of G pos inp ob m mO Hc S1 Hnx)).
  destruct (dh_nb K G pos 4 16 mO Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 16 mO) with (needbits 16 mO) in E.
  rewrite <- Hfl in Hgzf.
  destruct (dh_os_step mO Hhd Hlv Hgzf) as (L & Sx).
  destruct lv.
  - destruct R4 as (R4 & R5). rewrite (L _ _ _ E).
    apply (dh_post G pos inp ob flush m _ HK Hm).
    + apply (dh_same_trans _ mO); [exact HS|apply dh_same_lmv].
    + left. unfold m_mode. dh_red. rewrite HmO. unfold md_hdr. auto.
    + dh_red. apply dh_at_gz_mk; [exact R3|rewrite HmO; auto|]. rewrite HmO.
      exists h. split; [exact Ew|]. rewrite S2, Hout. split; [reflexivity|]. rewrite K1, Hlast.
      split; [reflexivity|]. split; [rewrite K2; exact Ht|]. right. right. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hfl.
    + dh_red. apply (dh_glob_gz G m (m_s mO) h Hg Hm0 Ew K3 Hhd);
        first [exact Hwb | intros _; exact Hfl | rewrite HmO; unfold OS, HEAD; lia].
    + dh_red. apply (dh_win_same G m (m_s mO) ob Hw Hwin); auto. repeat split; auto.
    + dh_red. apply dh_chk_hdr. rewrite HmO. unfold md_hdr. auto.
    + intros _. right. left. dh_red. split.
      * rewrite R4, S1. exact (f_equal (@Zlength Z) (kd_inp _ _ _ _ _ HK)).
      * rewrite <- (kd_inp _ _ _ _ _ HK), <- S1, <- R4. lia.
  - destruct R4 as (R4 & R5 & R6). specialize (R5 ltac:(lia)).
    assert (B16 : b' = 16) by lia. subst b'.
    destruct (Sx _ _ _ E) as (m2 & E2 & HS2 & L2 & N2 & H2 & B2 & M2 & W2 & F2 & C2).
    rewrite E2.
    pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
    apply (dh_post G pos inp ob flush m _ HK Hm).
    + apply (dh_same_trans _ mO); [exact HS|exact HS2].
    + right. left. exact M2.
    + rewrite H2, B2, N2. apply (dh_at_type_mk _ _ _ _ _ _ 0).
      * apply (dh_hold0 _ _ _ _ R3). lia.
      * left. exact M2.
      * pose proof (Zlength_nonneg (dc_bs G)). unfold nblk. lia.
      * rewrite (dk_bpos0 K), HD0. lia.
      * rewrite (dk_outk0 K), T2, S2. exact Hout.
      * lia.
      * rewrite J1, K1, Hlast. reflexivity.
    + apply (dh_glob_gz G m (m_s m2) h Hg Hm0 Ew);
        first [congruence | intros _; rewrite F2; exact Hfl | rewrite M2; unfold Zlib.proof.inflate.Model.TYPE, HEAD; lia].
    + apply (dh_win_same G m (m_s m2) ob Hw Hwin); [|left; congruence].
      repeat split; congruence.
    + apply dh_chk_type; [exact M2|exact Ob|exact Hhist|rewrite dh_chkv_nil, Ew; exact C2|].
      rewrite J2, K2. exact Ht.
    + intros X. rewrite L2 in X. discriminate.
Qed.


Lemma dh_same_os x a b : dh_same x (set_mode (initbits (dh_mv x a b 32)) OS).
Proof. unfold dh_same, dh_keep. dh_red. repeat split; reflexivity. Qed.

(* TIME (32 bits) -> OS *)
Lemma dh_cont_time (K: dkit_stmt) G pos inp ob flush m mT h :
  dh_ctx G pos inp ob m -> md_hdr (m_mode m) -> m_mode m <> HEAD -> dc_w G = WGzip h ->
  dh_same m mT -> m_leave mT = 0 -> i_head (m_s mT) = false -> i_mode (m_s mT) = TIME ->
  i_flags (m_s mT) = 8 + 256 * gz_flg h -> i_wbits (m_s mT) = i_wbits (m_s m) -> i_total (m_s m) = 0 ->
  0 <= m_nx mT <= Zlength (m_inp mT) -> hold_ok G (pos + m_nx mT) (m_hold mT) (m_bits mT) ->
  8 * (pos + m_nx mT) - m_bits mT = 32 -> 0 <= m_bits mT < 32 ->
  dstep_post G pos inp ob flush m (c_TIME2 mT).
Proof.
  intros Hc Hm Hm0 Ew HS Hlv Hhd HmT Hfl Hwb Ht Hnx Hh Hq Hb.
  pose proof Hc as (Hok & Hp & Hl & Hi & HK & Hw & Hlv0).
  destruct (dh_gz_facts G h Hok Ew) as (Hs & Hhist & Hwbr & HD0 & Hhb & Hgzf & Hsl).
  pose proof HS as (S1 & S2 & S3 & S4 & S5 & S6 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  assert (Hmg : i_mode (m_s m) = FLAGS \/ i_mode (m_s m) = TIME \/ i_mode (m_s m) = OS).
  { unfold md_hdr, m_mode in Hm, Hm0. intuition. }
  destruct (dh_at_gz _ _ _ _ _ _ (kd_at _ _ _ _ _ HK) Hmg) as (_ & (h0 & _ & Hout & Hlast & _)).
  pose proof (kd_glob _ _ _ _ _ HK) as Hg.
  assert (Hwin : win_ok G (m_s m) ob) by (apply (kd_win _ _ _ _ _ HK); apply dh_md_ne; auto).
  assert (Hin : dh_in G pos mT) by (apply (dh_in_of G pos inp ob m mT Hc S1 Hnx)).
  destruct (dh_nb K G pos 4 32 mT Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 32 mT) with (needbits 32 mT) in E.
  pose proof Hgzf as Hgzf'. rewrite <- Hfl in Hgzf'.
  destruct (dh_time_step mT Hhd Hlv Hgzf') as (L & Sx).
  destruct lv.
  - destruct R4 as (R4 & R5). rewrite (L _ _ _ E).
    apply (dh_post G pos inp ob flush m _ HK Hm).
    + apply (dh_same_trans _ mT); [exact HS|apply dh_same_lmv].
    + left. unfold m_mode. dh_red. rewrite HmT. unfold md_hdr. auto.
    + dh_red. apply dh_at_gz_mk; [exact R3|rewrite HmT; auto|]. rewrite HmT.
      exists h. split; [exact Ew|]. rewrite S2, Hout. split; [reflexivity|]. rewrite K1, Hlast.
      split; [reflexivity|]. split; [rewrite K2; exact Ht|]. right. left. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hfl.
    + dh_red. apply (dh_glob_gz G m (m_s mT) h Hg Hm0 Ew K3 Hhd);
        first [exact Hwb | intros _; exact Hfl | rewrite HmT; unfold TIME, HEAD; lia].
    + dh_red. apply (dh_win_same G m (m_s mT) ob Hw Hwin); auto. repeat split; auto.
    + dh_red. apply dh_chk_hdr. rewrite HmT. unfold md_hdr. auto.
    + intros _. right. left. dh_red. split.
      * rewrite R4, S1. exact (f_equal (@Zlength Z) (kd_inp _ _ _ _ _ HK)).
      * rewrite <- (kd_inp _ _ _ _ _ HK), <- S1, <- R4. lia.
  - destruct R4 as (R4 & R5 & R6). specialize (R5 ltac:(lia)).
    assert (B32 : b' = 32) by lia. rewrite B32 in E, R3.
    rewrite (Sx _ _ _ E).
    apply (dh_cont_os K G pos inp ob flush m _ h Hc Hm Hm0 Ew).
    + apply (dh_same_trans _ mT); [exact HS|apply dh_same_os].
    + dh_red. exact Hlv.
    + dh_red. exact Hhd.
    + dh_red. reflexivity.
    + dh_red. exact Hfl.
    + dh_red. exact Hwb.
    + exact Ht.
    + dh_red. lia.
    + dh_red. apply (dh_hold0 _ _ _ _ R3). lia.
    + dh_red. lia.
    + dh_red. lia.
Qed.

Lemma dh_same_time x a b f : dh_same x (set_mode (initbits (upd_s (dh_mv x a b 16) (fun s => set_i_flags s f))) TIME).
Proof. unfold dh_same, dh_keep. dh_red. repeat split; reflexivity. Qed.


Lemma dh_gz_hold_flags (K: dkit_stmt) G h : dctx_ok G -> dc_w G = WGzip h ->
  bval (sublist 16 32 (sbits G)) = 8 + 256 * gz_flg h.
Proof.
  intros Hok Ew. destruct (dh_gz_facts G h Hok Ew) as (Hs & _ & _ & HD0 & Hhb & _).
  rewrite (dh_hdr_bits K G 16 32 Hok) by lia. rewrite Hhb.
  destruct (dh_gz_simple_bytes h Hs) as (B & F). rewrite B, F.
  pose proof (dh_sub_bb [31; 139] [8; if gz_text h then 1 else 0] (le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h])) as X.
  cbn [Zlength] in X. change (8 * 2 + 8 * 2) with 32 in X. change (8 * 2) with 16 in X.
  replace (Zlength [31; 139]) with 2 in X by reflexivity.
  replace (Zlength [8; if gz_text h then 1 else 0]) with 2 in X by reflexivity.
  change (8 * 2 + 8 * 2) with 32 in X. change (8 * 2) with 16 in X. rewrite X.
  destruct (gz_text h); reflexivity.
Qed.

(* the gzip modes at a loop head; i_total = 0 there (see the note at dec_hdr_part) *)
Lemma dh_case_gz (K: dkit_stmt) G pos inp ob flush m :
  dh_ctx G pos inp ob m -> (m_mode m = FLAGS \/ m_mode m = TIME \/ m_mode m = OS) -> i_total (m_s m) = 0 ->
  dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros Hc Hmd Ht.
  pose proof Hc as (Hok & Hp & Hl & Hi & HK & Hw & Hlv).
  assert (Hm : md_hdr (m_mode m)) by (unfold md_hdr; tauto).
  assert (Hm0 : m_mode m <> HEAD) by (unfold m_mode in *; dh_modes_in Hmd; unfold HEAD; lia).
  destruct (dh_at_gz _ _ _ _ _ _ (kd_at _ _ _ _ _ HK) Hmd) as (Hh & (h & Ew & Hout & Hlast & Htot & D)).
  pose proof (kd_glob _ _ _ _ _ HK) as Hg. pose proof Hg as (_ & Hhd & _ & Hfl).
  assert (Hwin : win_ok G (m_s m) ob) by (apply (kd_win _ _ _ _ _ HK); apply dh_md_ne; auto).
  destruct (dh_gz_facts G h Hok Ew) as (Hs & Hhist & Hwbr & HD0 & Hhb & Hgzf & Hsl).
  pose proof (mw_nx _ (proj1 Hw)) as Hnx. pose proof (mw_bits _ (proj1 Hw)) as Hb.
  destruct (dh_step_md flush lenfix_list distfix_list m) as (SF & ST & SO).
  destruct Hmd as [Md|[Md|Md]]; unfold m_mode in Md; rewrite Md in D;
    destruct D as [(DM & Dq & Db)|[(DM & Dq & Db & Df)|(DM & Dq & Db & Df)]];
    try (dh_modes_in DM; lia).
  - (* FLAGS *)
    rewrite (SF Md).
    assert (Hin : dh_in G pos m) by (apply (dh_in_of G pos inp ob m m Hc eq_refl Hnx)).
    destruct (dh_nb K G pos 4 16 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
      as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
    change (needbits_f 4 16 m) with (needbits 16 m) in E.
    destruct (dh_flags_step m Hhd Hlv) as (L & Sx).
    destruct lv.
    + destruct R4 as (R4 & R5). rewrite (L _ _ _ E).
      apply (dh_post G pos inp ob flush m _ HK Hm).
      * apply dh_same_lmv.
      * left. unfold m_mode. dh_red. exact Hm.
      * dh_red. apply dh_at_gz_mk; [exact R3|rewrite Md; auto|]. rewrite Md.
        exists h. split; [exact Ew|]. split; [exact Hout|]. split; [exact Hlast|]. split; [exact Htot|].
        left. split; [reflexivity|]. lia.
      * dh_red. exact Hg.
      * dh_red. exact Hwin.
      * dh_red. apply dh_chk_hdr. exact Hm.
      * intros _. right. left. dh_red. split.
        -- rewrite R4. exact (f_equal (@Zlength Z) (kd_inp _ _ _ _ _ HK)).
        -- rewrite <- (kd_inp _ _ _ _ _ HK), <- R4. lia.
    + destruct R4 as (R4 & R5 & R6). specialize (R5 ltac:(lia)).
      assert (B16 : b' = 16) by lia. rewrite B16 in E, R3.
      assert (Hv : h' = 8 + 256 * gz_flg h).
      { destruct R3 as (_ & _ & R3). rewrite R3. replace (8 * (pos + nx') - 16) with 16 by lia.
        replace (8 * (pos + nx')) with 32 by lia. apply (dh_gz_hold_flags K G h Hok Ew). }
      rewrite Hv in E, R3. rewrite (Sx _ _ _ E Hgzf).
      apply (dh_cont_time K G pos inp ob flush m _ h Hc Hm Hm0 Ew).
      * apply dh_same_time.
      * dh_red. exact Hlv.
      * dh_red. exact Hhd.
      * dh_red. reflexivity.
      * dh_red. reflexivity.
      * dh_red. reflexivity.
      * exact Ht.
      * dh_red. lia.
      * dh_red. apply (dh_hold0 _ _ _ _ R3). lia.
      * dh_red. lia.
      * dh_red. lia.
  - (* TIME *)
    rewrite (ST Md).
    apply (dh_cont_time K G pos inp ob flush m m h Hc Hm Hm0 Ew (dh_same_refl m) Hlv Hhd Md Df eq_refl Ht Hnx Hh);
      lia.
  - (* OS *)
    rewrite (SO Md).
    apply (dh_cont_os K G pos inp ob flush m m h Hc Hm Hm0 Ew (dh_same_refl m) Hlv Hhd Md Df eq_refl Ht Hnx Hh);
      lia.
Qed.


Lemma dh_zlib_facts G wb fl did : dctx_ok G -> dc_w G = WZlib wb fl did -> did = None ->
  did = None /\ wb = dc_wb G /\ 8 <= wb <= 15 /\ 0 <= fl <= 3 /\ dc_hist G = [] /\ D0 G = 16 /\
  hdr_bytes (dc_w G) = zlib_hdr wb fl false /\ 2 <= slen G.
Proof.
  intros Hok E Hd. pose proof (dh_hdr_slen G) as Sl. pose proof Hok as ((Hwb & Hwo & Hww & _) & _).
  subst did. rewrite E in Hwo, Hww. destruct Hwo as (W1 & W2 & W3).
  unfold D0. rewrite E in *. cbn [hdr_bytes] in *. rewrite app_nil_r in *.
  rewrite dh_zlib_len in *. repeat split; auto; lia.
Qed.

Lemma dh_gz_hold_magic (K: dkit_stmt) G h : dctx_ok G -> dc_w G = WGzip h ->
  bval (sublist 0 16 (sbits G)) = 35615.
Proof.
  intros Hok Ew. destruct (dh_gz_facts G h Hok Ew) as (Hs & _ & _ & HD0 & Hhb & _).
  rewrite (dh_hdr_bits K G 0 16 Hok) by lia. rewrite Hhb.
  destruct (dh_gz_simple_bytes h Hs) as (B & _). rewrite B.
  pose proof (dh_sub_bb [] [31; 139] ([8; if gz_text h then 1 else 0] ++ (le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h]))) as X.
  replace (Zlength (@nil Z)) with 0 in X by reflexivity.
  replace (Zlength [31; 139]) with 2 in X by reflexivity.
  change (8 * 0) with 0 in X. change (0 + 8 * 2) with 16 in X. rewrite app_nil_l in X. rewrite X.
  reflexivity.
Qed.

Lemma dh_same_typedo x : dh_same x (set_mode x TYPEDO).
Proof. unfold dh_same, dh_keep. dh_red. repeat split; reflexivity. Qed.

(* HEAD at a loop head; i_total = 0 and, raw, bits < 8 there (see the note at dec_hdr_part) *)
Lemma dh_case_head (K: dkit_stmt) G pos inp ob flush m :
  dh_ctx G pos inp ob m -> m_mode m = HEAD -> i_total (m_s m) = 0 -> (wrapped G = false -> m_bits m < 8) ->
  dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros Hc Hmd Ht Hraw.
  pose proof Hc as (Hok & Hp & Hl & Hi & HK & Hw & Hlv).
  assert (Hm : md_hdr (m_mode m)) by (unfold md_hdr; tauto).
  destruct (dh_at_head _ _ _ _ _ _ (kd_at _ _ _ _ _ HK) Hmd) as (Hh & (Hout & Hq & Hb16 & Hlast & Htot0 & Hraw8 & Hfd)).
  pose proof (kd_glob _ _ _ _ _ HK) as Hg. pose proof Hg as ((wb0 & Er0 & Ewb) & Hhd & _ & _).
  destruct (init_wrap_wb_inv _ _ _ Er0) as (wrap & Er & Ewr).
  assert (Hwbg : 8 <= dc_wb G <= 15) by (destruct Hok as ((X & _) & _); exact X).
  specialize (Ewb Hmd).
  assert (Hwin : win_ok G (m_s m) ob) by (apply (kd_win _ _ _ _ _ HK); apply dh_md_ne; auto).
  pose proof (mw_nx _ (proj1 Hw)) as Hnx. pose proof (mw_bits _ (proj1 Hw)) as Hb.
  pose proof (sw_wbits _ (mw_s _ (proj1 Hw))) as Hwbr0.
  pose proof (dh_reset2 G _ _ Hok Er) as Hww.
  destruct (dh_head_step flush lenfix_list distfix_list m Hmd Hhd Hlv) as (Sraw & Sleave & Szlib & Sgz).
  assert (Hin : dh_in G pos m) by (apply (dh_in_of G pos inp ob m m Hc eq_refl Hnx)).
  unfold dh_wrapwb in Hww. destruct (dc_w G) as [|wb fl did|h] eqn:Ew.
  - (* raw *)
    destruct Hww as (W0' & Wb).
    assert (W0 : i_wrap (m_s m) = 0) by (rewrite Ewr, dh_rw by lia; exact W0').
    rewrite (Sraw W0).
    assert (Hb8 : m_bits m < 8) by (apply Hraw; unfold wrapped; rewrite Ew; reflexivity).
    apply (dh_post G pos inp ob flush m _ HK Hm).
    + apply dh_same_typedo.
    + right. right. reflexivity.
    + dh_red. apply (dh_at_type_mk _ _ _ _ _ _ 0).
      * exact Hh.
      * right. reflexivity.
      * pose proof (Zlength_nonneg (dc_bs G)). unfold nblk. lia.
      * rewrite (dk_bpos0 K). unfold D0. rewrite Ew. cbn. lia.
      * rewrite (dk_outk0 K). exact Hout.
      * exact Hb8.
      * dh_red. rewrite Hlast. reflexivity.
    + dh_red. assert (Hwbr : 8 <= dc_wb G <= 15) by (destruct Hok as ((X & _) & _); exact X).
      apply (dh_glob_mk G (m_s m) _ Hg); dh_red;
        first [reflexivity | exact Hhd | intros X; unfold TYPEDO, HEAD in X; lia | intros _; rewrite Ewb, Wb; lia
              | unfold wrapped; rewrite Ew; intros X; discriminate X].
    + dh_red. apply (dh_win_same G m _ ob Hw Hwin); [|left; reflexivity]. unfold dh_keep. dh_red. repeat split; reflexivity.
    + unfold chk_ok, wrapped. rewrite Ew. discriminate.
    + dh_red. rewrite Hlv. discriminate.
  - (* zlib *)
    assert (Hdn : did = None) by (destruct did as [i|]; [exfalso; exact (Hfd _ _ _ eq_refl)|reflexivity]).
    destruct (dh_zlib_facts G wb fl did Hok Ew Hdn) as (Hdid & Ewb' & Hwbr & Hfl & Hhist & HD0 & Hhb & Hsl).
    assert (Ob : ob = []) by (rewrite Hhist in Hout; apply app_eq_nil in Hout; tauto).
    assert (W57 : i_wrap (m_s m) = 5 \/ i_wrap (m_s m) = 7 \/ i_wrap (m_s m) = 13).
    { rewrite Ewr. destruct Hww as [(-> & [B|B])|(-> & B)];
        [left; apply dh_rw; lia|right; right; rewrite B; reflexivity|right; left; apply dh_rw; lia]. }
    assert (W0 : i_wrap (m_s m) <> 0) by lia.
    destruct (dh_nb K G pos 4 16 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
      as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
    change (needbits_f 4 16 m) with (needbits 16 m) in E.
    destruct lv.
    + destruct R4 as (R4 & R5). rewrite (Sleave _ _ _ W0 E).
      apply (dh_post G pos inp ob flush m _ HK Hm).
      * apply dh_same_lmv.
      * left. unfold m_mode. dh_red. exact Hm.
      * dh_red. apply dh_at_head_mk; [exact R3|exact Hmd|].
        split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [exact Hlast|]. split; [exact Htot0|].
        split; [intros X; unfold wrapped in X; rewrite Ew in X; discriminate|].
        intros a1 a2 a3 X; rewrite Ew in X; first [exact (Hfd _ _ _ X) | discriminate X].
      * dh_red. exact Hg.
      * dh_red. exact Hwin.
      * dh_red. apply dh_chk_hdr. exact Hm.
      * intros _. right. left. dh_red. split.
        -- rewrite R4. exact (f_equal (@Zlength Z) (kd_inp _ _ _ _ _ HK)).
        -- rewrite <- (kd_inp _ _ _ _ _ HK), <- R4. lia.
    + destruct R4 as (R4 & R5 & R6). specialize (R5 ltac:(lia)).
      assert (B16 : b' = 16) by lia. rewrite B16 in E, R3.
      assert (Hv : h' = bval (bytes_bits (zlib_hdr wb fl false))).
      { destruct R3 as (_ & _ & R3). rewrite R3. replace (8 * (pos + nx') - 16) with 0 by lia.
        replace (8 * (pos + nx')) with 16 by lia. rewrite <- Hhb, <- HD0. f_equal. apply (dk_hdr K G Hok). }
      destruct (dh_zhdr wb fl Hwbr Hfl) as (Z1 & Z2 & Z3 & Z4 & Z5). rewrite <- Hv in Z1, Z2, Z3, Z4, Z5.
      assert (Hwb0 : i_wbits (m_s m) = 0 \/ i_wbits (m_s m) = wb) by (rewrite Ewb; lia).
      destruct (Szlib nx' h' wb W57 E Z1 Z2 Z3 Z4 Z5 Hwbr Hwb0)
        as (m2 & E2 & HS2 & L2 & N2 & H2 & B2 & M2 & W2 & F2 & C2).
      rewrite E2.
      pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
      apply (dh_post G pos inp ob flush m _ HK Hm).
      * exact HS2.
      * right. left. exact M2.
      * rewrite H2, B2, N2. apply (dh_at_type_mk _ _ _ _ _ _ 0).
        -- apply (dh_hold0 _ _ _ _ R3). lia.
        -- left. exact M2.
        -- pose proof (Zlength_nonneg (dc_bs G)). unfold nblk. lia.
        -- rewrite (dk_bpos0 K), HD0. lia.
        -- rewrite (dk_outk0 K), T2. exact Hout.
        -- lia.
        -- rewrite J1, Hlast. reflexivity.
      * apply (dh_glob_mk G (m_s m) _ Hg); [exact J3|congruence| | |].
        -- intros X. rewrite M2 in X. unfold Zlib.proof.inflate.Model.TYPE, HEAD in X. lia.
        -- intros _. rewrite W2. lia.
        -- intros _ _ _. rewrite Ew. exact F2.
      * apply (dh_win_same G m _ ob Hw Hwin); [unfold dh_keep; repeat split; assumption|].
        destruct Hwb0 as [X|X]; [right|left; congruence].
        destruct (s3_head _ (proj2 Hw) Hmd X W0) as (Z & _). exact Z.
      * apply dh_chk_type; [exact M2|exact Ob|exact Hhist| |].
        -- rewrite dh_chkv_nil, Ew. exact C2.
        -- rewrite J2. exact Ht.
      * intros X. rewrite L2 in X. discriminate.
  - (* gzip *)
    destruct (dh_gz_facts G h Hok Ew) as (Hs & Hhist & Hwbr & HD0 & Hhb & Hgzf & Hsl).
    destruct Hww as (W67' & Wb).
    assert (W67 : i_wrap (m_s m) = 6 \/ i_wrap (m_s m) = 7) by (rewrite Ewr, dh_rw by lia; exact W67').
    assert (W0 : i_wrap (m_s m) <> 0) by lia.
    destruct (dh_nb K G pos 4 16 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
      as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
    change (needbits_f 4 16 m) with (needbits 16 m) in E.
    destruct lv.
    + destruct R4 as (R4 & R5). rewrite (Sleave _ _ _ W0 E).
      apply (dh_post G pos inp ob flush m _ HK Hm).
      * apply dh_same_lmv.
      * left. unfold m_mode. dh_red. exact Hm.
      * dh_red. apply dh_at_head_mk; [exact R3|exact Hmd|].
        split; [exact Hout|]. split; [lia|]. split; [lia|]. split; [exact Hlast|]. split; [exact Htot0|].
        split; [intros X; unfold wrapped in X; rewrite Ew in X; discriminate|].
        intros a1 a2 a3 X; rewrite Ew in X; first [exact (Hfd _ _ _ X) | discriminate X].
      * dh_red. exact Hg.
      * dh_red. exact Hwin.
      * dh_red. apply dh_chk_hdr. exact Hm.
      * intros _. right. left. dh_red. split.
        -- rewrite R4. exact (f_equal (@Zlength Z) (kd_inp _ _ _ _ _ HK)).
        -- rewrite <- (kd_inp _ _ _ _ _ HK), <- R4. lia.
    + destruct R4 as (R4 & R5 & R6). specialize (R5 ltac:(lia)).
      assert (B16 : b' = 16) by lia. rewrite B16 in E, R3.
      assert (Hv : h' = 35615).
      { destruct R3 as (_ & _ & R3). rewrite R3. replace (8 * (pos + nx') - 16) with 0 by lia.
        replace (8 * (pos + nx')) with 16 by lia. apply (dh_gz_hold_magic K G h Hok Ew). }
      rewrite Hv in E, R3.
      destruct (Sgz nx' W67 E ltac:(lia)) as (m2 & E2 & HS2 & L2 & N2 & H2 & B2 & M2 & W2).
      rewrite E2.
      pose proof HS2 as (T1 & T2 & T3 & T4 & T5 & T6 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8).
      apply (dh_post G pos inp ob flush m _ HK Hm).
      * exact HS2.
      * left. unfold md_hdr, m_mode. auto.
      * rewrite H2, B2, N2. apply dh_at_gz_mk; [apply (dh_hold0 _ _ _ _ R3); lia|rewrite M2; auto|].
        rewrite M2. exists h. split; [exact Ew|]. rewrite T2. split; [exact Hout|]. rewrite J1.
        split; [exact Hlast|]. split; [rewrite J2; exact Htot0|]. left. split; [reflexivity|]. lia.
      * apply (dh_glob_mk G (m_s m) _ Hg); [exact J3|congruence| | |].
        -- intros X. rewrite M2 in X. unfold FLAGS, HEAD in X. lia.
        -- intros _. rewrite W2, Ewb. lia.
        -- intros _ _ X. rewrite M2 in X. contradiction.
      * apply (dh_win_same G m _ ob Hw Hwin); [unfold dh_keep; repeat split; assumption|left; exact W2].
      * apply dh_chk_hdr. rewrite M2. unfold md_hdr. auto.
      * intros X. rewrite L2 in X. discriminate.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* (2) the group                                                                                  *)

(* what the header modes must also know (DecodeDefs' at_head / at_gzhdr do not state it): total = 0
   before the data, and a raw stream is at HEAD with no bits; proved below (dh_fix) *)
Definition dh_fix_stmt : Prop :=
  forall G pos inp ob m, dh_ctx G pos inp ob m -> md_hdr (m_mode m) ->
    i_total (m_s m) = 0 /\ (m_mode m = HEAD -> wrapped G = false -> m_bits m < 8).

Lemma dh_group (K: dkit_stmt) : dh_fix_stmt -> group_ok md_hdr.
Proof.
  intros FX G pos inp ob flush m Hok Hp Hl Hi HK Hw Hlv Hmd.
  assert (Hc : dh_ctx G pos inp ob m) by (unfold dh_ctx; tauto).
  destruct (FX G pos inp ob m Hc Hmd) as (Ht & Hr).
  destruct Hmd as [M|M].
  - exact (dh_case_head K G pos inp ob flush m Hc M Ht (Hr M)).
  - exact (dh_case_gz K G pos inp ob flush m Hc M Ht).
Qed.

Lemma dh_fix : dh_fix_stmt.
Proof.
  intros G pos inp ob m (_ & _ & _ & _ & HK & _) Hmd. pose proof (kd_at _ _ _ _ _ HK) as A.
  destruct Hmd as [M|M].
  - destruct (dh_at_head _ _ _ _ _ _ A M) as (_ & (_ & _ & _ & _ & T & R & _)). split; [exact T|]. intros _. exact R.
  - destruct (dh_at_gz _ _ _ _ _ _ A M) as (_ & (h & _ & _ & _ & T & _)). split; [exact T|].
    intros E. unfold m_mode in *. dh_modes_in M. dh_modes_in E. lia.
Qed.

Lemma dec_hdr_part : (dkit_stmt -> decode_init_stmt) /\ (dkit_stmt -> group_ok md_hdr).
Proof. split; intros K; [exact dh_init | exact (dh_group K dh_fix)]. Qed.

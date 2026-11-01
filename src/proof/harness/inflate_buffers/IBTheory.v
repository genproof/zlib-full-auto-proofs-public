(* Law inflate_buffers, theory: the facts of IBFacts.v (ib_facts) from the counters of run2 (IBRun.v) and the
   hypothesis ib_wbits_stmt (proved in IBWbits.v).  The API functions' facts are computations over
   ApiModel.v's model functions. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_buffers.IBFacts.
Require Import Zlib.proof.inflate_api.ResetKit5.
Require Import Zlib.proof.inflate_api.ResetFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* windowBits accepted by inflateInit2_ / inflateReset2                                           *)

Lemma ib_wb_range: forall w wrap wb, reset2_wb w = Some (wrap, wb) ->
  0 <= wrap <= 7 /\ (wb = 0 \/ 8 <= wb <= 15) /\ (wb = 0 -> 5 <= wrap).
Proof.
  intros w wrap wb H. unfold reset2_wb in H.
  destruct (Z.ltb_spec w 0).
  - destruct (Z.ltb_spec w (-15)); [discriminate | ].
    destruct (andb (8 <=? - w) (- w <=? 15)) eqn:E; [ | discriminate].
    inv H. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
  - destruct (Z.ltb_spec w 48).
    + destruct (orb (Z.land w 15 =? 0) (andb (8 <=? Z.land w 15) (Z.land w 15 <=? 15))) eqn:E; [ | discriminate].
      inv H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      assert (0 <= w / 16) by (apply Z.div_pos; lia).
      assert (w / 16 < 3) by (apply Z.div_lt_upper_bound; lia).
      split; [lia | ]. split; [ | lia].
      apply orb_prop in E. destruct E as [E | E]; [left; apply Z.eqb_eq in E; lia | right].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
    + destruct (orb (w =? 0) (andb (8 <=? w) (w <=? 15))) eqn:E; [ | discriminate].
      exfalso. apply orb_prop in E. destruct E as [E | E]; [apply Z.eqb_eq in E; lia | ].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

Ltac ib_s := cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was l_s set_l_s] in *.

Lemma ib_init (w: Z) (sp: val) : wbits_ok w = true -> ib_inv (init_live sp w).
Proof.
  unfold wbits_ok, ib_inv, ib_inv_s, init_live. destruct (reset2_wb w) as [[wrap wb]|] eqn:E; [|discriminate].
  intros _. destruct (ib_wb_range w wrap wb E) as (R & B & _). cbn [l_s].
  destruct (init_s_fields wrap wb R) as (_ & -> & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
  split; [reflexivity | lia].
Qed.

Lemma ib_bytes_sublist (l: list Z) (i j: Z) : bytes_ok l -> bytes_ok (sublist i j l).
Proof. intros H. unfold bytes_ok in *. apply Forall_sublist. exact H. Qed.

Lemma ib_getdict (L: live) : live_ok L -> ib_inv L ->
  0 <= i_whave (l_s L) <= 32768 /\ Zlength (dict_bytes (l_s L)) = i_whave (l_s L) /\ bytes_ok (dict_bytes (l_s L)).
Proof.
  intros (_ & W & _) (_ & WB).
  destruct (sw_wdata _ W) as [WL WO]. pose proof (sw_wsize _ W) as sw_wsize0. pose proof (sw_whave _ W) as sw_whave0.
  pose proof (sw_wvalid _ W) as sw_wvalid0. pose proof (sw_wnext _ W) as sw_wnext0.
  assert (Hws: i_wsize (l_s L) <= 32768).
  { destruct sw_wsize0 as [-> | [_ ->]]; [lia | ].
    change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hn: 0 <= i_wnext (l_s L) <= i_whave (l_s L)).
  { destruct (Z.lt_ge_cases (i_whave (l_s L)) (i_wsize (l_s L))) as [Lt | Ge].
    - rewrite (sw_wvalid0 Lt). lia.
    - destruct sw_wnext0 as [N1 N2]. lia. }
  split; [lia | ]. unfold dict_bytes. split.
  - rewrite Zlength_app, !Zlength_sublist by lia. lia.
  - unfold bytes_ok. apply Forall_app. split; apply ib_bytes_sublist; exact WO.
Qed.

(* ssearch looks at no more bytes than offered *)
Lemma ib_ssearch_len (got: Z) (l: list Z) : 0 <= snd (ssearch got l) <= Zlength l.
Proof.
  revert got. induction l as [|b r IH]; intros got; simpl; [rewrite Zlength_nil; lia | ].
  rewrite Zlength_cons.
  destruct (got <? 4); simpl; [ | pose proof (Zlength_nonneg r); lia].
  destruct (ssearch _ r) as [g n] eqn:E. simpl.
  specialize (IH (if b =? (if got <? 2 then 0 else 255) then got + 1 else if negb (b =? 0) then 0 else 4 - got)).
  rewrite E in IH. simpl in IH. lia.
Qed.

Lemma ib_sync (s: istate) (inp: list Z) (s': istate) (len: Z) : swf s -> ib_inv_s s ->
  (sync_s s inp = SyncData s' len \/ sync_s s inp = SyncOk s' len) ->
  0 <= len <= Zlength inp /\ ib_inv_s s'.
Proof.
  intros _ (H & WB) E. unfold sync_s in E.
  destruct ((Zlength inp =? 0) && (i_bits s <? 8))%bool; [destruct E; discriminate | ].
  set (s1 := if i_mode s =? SYNC then s else sync_start s) in E.
  assert (I1: ib_inv_s s1).
  { subst s1. destruct (i_mode s =? SYNC); [split; auto | ].
    unfold sync_start. ib_s. split; auto. }
  pose proof (ib_ssearch_len (i_have s1) inp) as SL.
  destruct (ssearch (i_have s1) inp) as [got n] eqn:SE. simpl in SL.
  destruct I1 as [H1 W1].
  destruct (negb (got =? 4)).
  - destruct E as [E | E]; inv E. split; [lia | ]. split; ib_s; auto.
  - destruct E as [E | E]; [discriminate | ]. inv E. split; [lia | ].
    unfold reset_s, reset_keep_s.
    ib_s. destruct (i_flags s1 =? -1); [destruct (i_wbits s1 =? 0) | ];
      unfold ib_inv_s; ib_s; split; auto; lia.
Qed.

Lemma ib_setdict (s: istate) (dict: list Z) : ib_inv_s s -> ib_inv_s (setdict_s s dict) /\ ib_inv_s (set_i_mode s MEM).
Proof.
  intros [H W]. unfold setdict_s, updatewindow. split; [ | ib_s; split; auto].
  destruct (i_wsize s =? 0);
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; ib_s; split; auto.
Qed.

Lemma ib_prime (bits value: Z) (s s': istate) : ib_inv_s s -> prime_s bits value s = Some s' -> ib_inv_s s'.
Proof.
  intros [H W] E. unfold prime_s in E.
  repeat match type of E with context [if ?c then _ else _] => destruct c end; inv E; ib_s; split; auto.
Qed.

Lemma ib_validate (check: Z) (s: istate) : ib_inv_s s -> ib_inv_s (validate_s check s).
Proof. intros [H W]. unfold validate_s. destruct (_ && _)%bool; ib_s; split; auto. Qed.

Lemma ib_reset (L: live) : live_ok L -> ib_inv L ->
  live_ok (set_l_s L (reset_s (l_s L))) /\ ib_inv (set_l_s L (reset_s (l_s L))).
Proof.
  intros H [_ W]. split; [apply live_reset_ok; exact H | ].
  unfold ib_inv, ib_inv_s, reset_s, reset_keep_s. ib_s. split; auto.
Qed.

Lemma ib_land3 (wrap: Z) : 5 <= wrap <= 7 -> Z.land wrap 3 <> 0.
Proof. intros H. assert (wrap = 5 \/ wrap = 6 \/ wrap = 7) as [-> | [-> | ->]] by lia; discriminate. Qed.

Lemma ib_reset2 (L: live) (w wrap wb: Z) : live_ok L -> ib_inv L -> reset2_wb w = Some (wrap, wb) ->
  live_ok (set_l_s L (reset2_s wrap wb (l_s L))) /\ ib_inv (set_l_s L (reset2_s wrap wb (l_s L))).
Proof.
  intros HL [_ WB] E. destruct (ib_wb_range w wrap wb E) as (R1 & R2 & R3).
  destruct (reset2_wrap_ok w wrap wb E) as (RW & _ & _ & _).
  rewrite (reset2_s_eq wrap wb (l_s L) R1).
  split.
  2: { unfold ib_inv, ib_inv_s. rs_simpl. split; [reflexivity | lia]. }
  destruct L as [sp winp s h headp hsh xb nb cb].
  destruct HL as (P & W & M & HW & W3 & HS & WB0 & HD & WF).
  cbn [l_s l_sp l_h l_hsh l_xb l_nb l_cb set_l_s] in *.
  set (s0 := if ((i_win s && negb (i_wbits s =? wb)) || (wb =? 0))%bool then set_i_win s false else s) in *.
  assert (Win: wb = 0 -> i_win s0 = false).
  { intros ->. subst s0. rewrite orb_true_r. reflexivity. }
  split; [exact P | ]. split; [ | split; [ | split; [exact HW | split; [ | split; [exact HS | ]]]]].
  - destruct W. constructor; rs_simpl; auto;
      try (unfold HEAD, SYNC, srange, urange, lrange, tref_ok, ENOUGH_CODES in *; rep_lia).
    all: try (subst s0; destruct (_ || _)%bool; ib_s; auto; fail).
    all: try (split; [reflexivity | constructor]).
  - constructor; rs_simpl; repeat split; intros; exfalso;
      try (apply head_not_decode; assumption);
      unfold HEAD, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST in *; lia.
  - destruct W3. constructor; rs_simpl; auto; intros HM;
      try (exfalso; apply head_not_decode; exact HM);
      try (unfold HEAD, LENEXT, DISTEXT in *; lia).
  - rs_simpl. split; [ | split; [intro; discriminate | ]].
    + intros HB. split; [ | apply Win; exact HB].
      subst wb. unfold reset2_wrap. cbn [Z.eqb].
      assert (C: wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
      destruct C as [-> | [-> | ->]]; discriminate.
    + intros _ _. split; [reflexivity | left; reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate(): Spec5's inflate_rel and the counters of run2                                        *)

Lemma ib_u64_id (x: Z) : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros H. unfold u64. apply Z.mod_small. unfold Int64.max_unsigned in H. change Int64.modulus with (2 ^ 64) in H. lia. Qed.

Lemma ib_inflate : ib_run_stmt -> ib_wbits_stmt -> ib_inflate_stmt.
Proof.
  intros RUN WBS flush strmp z L ib inp ob r z' st' ow LOK ZOK [HH WB] Ps Bi Li Ao Ni Ai No REL.
  destruct ZOK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct REL as [(BAD & -> & -> & -> & ->) | (NB & L0 & o & res & winp & EL & EO & RUN2 & SNX & -> & -> & -> & _ & ->)].
  - exists L. split; [reflexivity | ]. split; [split; auto | ].
    rewrite !Z.sub_diag, Zlength_nil. split; [lia | ]. split; [lia | ]. split; [exact Ni | ].
    split; [auto | ]. split; [destruct ob; auto | ]. split; [auto | ]. split; [reflexivity | ].
    intros _. rewrite !Z.add_0_r, !ib_u64_id by (unfold Int64.max_unsigned in *; lia). auto.
  - inv EL.
    assert (Hai: zf_ai z = Zlength inp).
    { destruct ib; [ | exact Ai]. subst inp. unfold inflate_bad in NB.
      destruct (Z.eq_dec (zf_ai z) 0) as [E0 | E0]; [rewrite E0; reflexivity | ].
      exfalso. apply NB. right. right. auto. }
    destruct (RUN flush z L0 inp res LOK (conj Z1 (conj Z2 (conj Z3 (conj Z4 (conj Z5 Z6))))) Bi Li Ao RUN2)
      as (MI & MA & MS & MO & MH & MT).
    pose proof (WBS flush z L0 inp res LOK (conj Z1 (conj Z2 (conj Z3 (conj Z4 (conj Z5 Z6))))) WB RUN2) as W'.
    set (m := r_m res) in *.
    eexists. split; [reflexivity | ]. split.
    { unfold ib_inv, ib_inv_s. cbn [l_s]. fold m. split; [congruence | exact W']. }
    unfold z_after. cbn [zf_ai zf_ao zf_ni zf_no zf_tin zf_tout]. fold m. rewrite MI, MA.
    pose proof (Zlength_nonneg (m_ow m)).
    replace (zf_ai z - (Zlength inp - m_snx m)) with (m_snx m) by lia.
    replace (zf_ao z - (zf_ao z - m_sow m)) with (m_sow m) by lia.
    split; [lia | ]. split; [lia | ]. split; [reflexivity | ].
    split.
    { intros ->. subst inp. rewrite Zlength_nil in SNX. lia. }
    split; [reflexivity | ]. split; [discriminate | ]. split; [lia | ].
    exact MT.
Qed.

Lemma ib_facts_of : ib_run_stmt -> ib_wbits_stmt -> ib_facts.
Proof.
  intros RUN WBS. constructor.
  - exact ib_init.
  - exact (ib_inflate RUN WBS).
  - exact ib_sync.
  - exact ib_getdict.
  - exact ib_setdict.
  - exact ib_prime.
  - exact ib_validate.
  - exact ib_reset.
  - intros L w wrap wb A B C. exact (ib_reset2 L w wrap wb A B C).
Qed.

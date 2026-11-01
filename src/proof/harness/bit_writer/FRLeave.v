(* The fixed-block run theory (FRDefs.v): the exit of a call (inf_leave: the window update, Z_MEM_ERROR, the
   return code) gives FRFacts.fr_post with the invariant fr_inv. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* fr_at reads only these fields of the state *)
Definition frl_same (s s': istate) : Prop :=
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\
  i_lencode s' = i_lencode s /\ i_lenbits s' = i_lenbits s /\ i_distcode s' = i_distcode s /\
  i_distbits s' = i_distbits s /\ i_length s' = i_length s /\ i_extra s' = i_extra s /\
  i_offset s' = i_offset s.

Lemma frl_at_ext C s s' c hold bits out :
  frl_same s s' -> fr_at C s c hold bits out -> fr_at C s' c hold bits out.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) A.
  unfold fr_at, fr_fixed in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. exact A.
Qed.

(* updatewindow writes only the window fields *)
Lemma frl_uw_same (s: istate) (d: list Z) : frl_same s (updatewindow s d).
Proof.
  unfold updatewindow, frl_same. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
Qed.

(* the window never holds more than the output before the update and the bytes it is given *)
Lemma frl_uw_whave (s: istate) (d: list Z) (N: Z) :
  0 <= i_whave s <= N ->
  (i_wsize s <> 0 -> i_whave s <= i_wsize s /\ (i_whave s < i_wsize s -> i_wnext s = i_whave s)) ->
  i_whave (updatewindow s d) <= N + Zlength d.
Proof.
  intros H W. unfold updatewindow. cbv zeta.
  set (s0 := if i_wsize s =? 0 then _ else s).
  assert (H0: 0 <= i_whave s0 <= N /\ (i_whave s0 < i_wsize s0 -> i_wnext s0 = i_whave s0)).
  { unfold s0. destruct (Z.eqb_spec (i_wsize s) 0); cbn; [lia|].
    destruct (W n) as [W1 W2]. split; auto. }
  clearbody s0. destruct H0 as [H0 V]. pose proof (Zlength_nonneg d).
  destruct (Z.leb_spec (i_wsize s0) (Zlength d)); [cbn; lia|].
  destruct (negb _) eqn:E; cbn.
  - apply negb_true_iff, Z.eqb_neq in E.
    destruct (Z.ltb_spec (i_whave s0) (i_wsize s0)) as [L|L].
    + specialize (V L). lia.
    + lia.
  - destruct (i_whave s0 <? i_wsize s0); lia.
Qed.

(* the state after RESTORE, and the bytes updatewindow is given at the exit *)
Definition frl_s1 (m: mst) : istate := set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m).
Definition frl_wd (m: mst) : list Z :=
  sublist (Zlength (m_ow m) - u32 (m_out m - m_left m)) (Zlength (m_ow m)) (m_ow m).

(* what leave_fin keeps: the stream positions, the fields fr_at reads, the bit buffer; the window is updated
   when leave_ok; the return code is the loop's, or Z_BUF_ERROR instead of Z_OK *)
(* the state after the window update (if any) *)
Definition frl_s2 (flush: Z) (m: mst) : istate :=
  if leave_ok flush m then set_i_win (updatewindow (frl_s1 m) (frl_wd m)) true else frl_s1 m.

Lemma frl_s2_facts flush m :
  frl_same (m_s m) (frl_s2 flush m) /\ i_hold (frl_s2 flush m) = m_hold m /\ i_bits (frl_s2 flush m) = m_bits m.
Proof.
  assert (S1: frl_same (m_s m) (frl_s1 m) /\ i_hold (frl_s1 m) = m_hold m /\ i_bits (frl_s1 m) = m_bits m).
  { unfold frl_s1, frl_same. cbn. repeat split. }
  unfold frl_s2. destruct (leave_ok flush m); [|exact S1].
  destruct S1 as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) & H1 & B1).
  pose proof (frl_uw_same (frl_s1 m) (frl_wd m)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  assert (Hh: i_hold (updatewindow (frl_s1 m) (frl_wd m)) = i_hold (frl_s1 m) /\
              i_bits (updatewindow (frl_s1 m) (frl_wd m)) = i_bits (frl_s1 m)).
  { unfold updatewindow. cbv zeta.
    destruct (i_wsize (frl_s1 m) =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; split; reflexivity. }
  destruct Hh as [Hh Hb].
  unfold frl_same; cbn [i_mode i_last i_wrap i_lencode i_lenbits i_distcode i_distbits i_length i_extra i_offset
    i_hold i_bits set_i_win].
  repeat split; congruence.
Qed.

(* what leave_fin keeps: the stream positions, the state frl_s2 up to the counters and the check value; the
   return code is the loop's, or Z_BUF_ERROR instead of Z_OK *)
Lemma frl_fin flush m :
  let res := leave_fin flush m in let mF := r_m res in let sF := m_s mF in
  m_ow mF = m_ow m /\ m_snx mF = m_nx m /\ m_sow mF = Zlength (m_ow m) /\
  frl_same (frl_s2 flush m) sF /\ i_hold sF = i_hold (frl_s2 flush m) /\ i_bits sF = i_bits (frl_s2 flush m) /\
  i_whave sF = i_whave (frl_s2 flush m) /\ i_wsize sF = i_wsize (frl_s2 flush m) /\
  (r_ret res = m_ret m \/ (r_ret res = Z_BUF_ERROR /\ m_ret m = Z_OK)).
Proof.
  cbv zeta. unfold leave_fin. cbv zeta.
  set (m2 := if leave_ok flush m then _ else restore m).
  assert (A: m_s m2 = frl_s2 flush m /\ m_ow m2 = m_ow m /\ m_snx m2 = m_nx m /\ m_sow m2 = Zlength (m_ow m) /\
             m_ret m2 = m_ret m /\ m_in m2 = m_in m /\ m_inp m2 = m_inp m /\ m_nx m2 = m_nx m /\
             m_out m2 = m_out m /\ m_aout m2 = m_aout m).
  { unfold m2, frl_s2. destruct (leave_ok flush m); repeat split. }
  clearbody m2. destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  set (m3 := upd_s (set_m_tout _ _) _).
  assert (B: frl_same (m_s m2) (m_s m3) /\ i_hold (m_s m3) = i_hold (m_s m2) /\
             i_bits (m_s m3) = i_bits (m_s m2) /\ i_whave (m_s m3) = i_whave (m_s m2) /\
             i_wsize (m_s m3) = i_wsize (m_s m2) /\ m_ow m3 = m_ow m2 /\ m_snx m3 = m_snx m2 /\
             m_sow m3 = m_sow m2 /\ m_ret m3 = m_ret m2).
  { unfold m3, upd_s, frl_same. cbn. repeat split. }
  clearbody m3. destruct B as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) & B1 & B2 & B3 & B4 & B5 & B6 &
    B7 & B8).
  destruct (andb (negb (Z.land _ 4 =? 0)) (negb (_ =? 0))).
  - cbn [r_m r_ret]. unfold upd_s, frl_same.
    cbn [m_s set_m_adler set_m_s m_ow m_snx m_sow m_ret i_mode i_last i_wrap i_lencode i_lenbits i_distcode
      i_distbits i_length i_extra i_offset i_hold i_bits i_whave i_wsize set_i_check].
    repeat split; try congruence.
    destruct (andb _ _) eqn:R; [right; split; auto | left; congruence].
    apply andb_true_iff in R. destruct R as [_ R]. apply Z.eqb_eq in R. congruence.
  - cbn [r_m r_ret]. unfold frl_same.
    repeat split; try congruence.
    destruct (andb _ _) eqn:R; [right; split; auto | left; congruence].
    apply andb_true_iff in R. destruct R as [_ R]. apply Z.eqb_eq in R. congruence.
Qed.

Lemma frl_same_trans s1 s2 s3 : frl_same s1 s2 -> frl_same s2 s3 -> frl_same s1 s3.
Proof. unfold frl_same. intuition congruence. Qed.

(* the output space of the call is its whole output: the exit gives updatewindow all of it *)
Lemma frl_wd_ow m : m_out m = m_aout m -> Zlength (m_ow m) <= Int.max_unsigned -> frl_wd m = m_ow m.
Proof.
  intros O W. unfold frl_wd, m_left. rewrite O.
  replace (m_aout m - (m_aout m - Zlength (m_ow m))) with (Zlength (m_ow m)) by lia.
  unfold u32. rewrite Z.mod_small by (pose proof (Zlength_nonneg (m_ow m)); rep_lia).
  rewrite Z.sub_diag. apply sublist_same; reflexivity.
Qed.

(* no output and no window before: no window after *)
Lemma frl_s2_wsize flush m :
  m_out m = m_aout m -> m_ow m = [] -> i_wsize (m_s m) = 0 -> i_wsize (frl_s2 flush m) = 0.
Proof.
  intros O W Z0. unfold frl_s2.
  replace (leave_ok flush m) with false.
  - unfold frl_s1. cbn. exact Z0.
  - unfold leave_ok, m_left. rewrite Z0, O, W, Zlength_nil, Z.sub_0_r, !Z.eqb_refl. reflexivity.
Qed.

(* the window after the exit holds no more than the output *)
Lemma frl_s2_whave flush m (L: live) (ob: list Z) :
  swf (l_s L) -> fr_wsame (l_s L) (m_s m) -> i_whave (l_s L) <= Zlength ob ->
  m_out m = m_aout m -> Zlength (m_ow m) <= Int.max_unsigned ->
  i_whave (frl_s2 flush m) <= Zlength (ob ++ m_ow m).
Proof.
  intros SW (W1 & W2 & W3 & _) H O OW.
  pose proof (sw_whave _ SW) as Hwh. pose proof (sw_wvalid _ SW) as Hwv.
  rewrite Zlength_app. pose proof (Zlength_nonneg (m_ow m)).
  unfold frl_s2. destruct (leave_ok flush m).
  - cbn [i_whave set_i_win]. replace (Zlength (m_ow m)) with (Zlength (frl_wd m)) by (rewrite frl_wd_ow; auto).
    apply frl_uw_whave; unfold frl_s1; cbn [i_whave i_wsize i_wnext set_i_bits set_i_hold];
      rewrite ?W1, ?W2, ?W3; [lia|]. intros _. split; auto. lia.
  - unfold frl_s1. cbn. lia.
Qed.

Lemma fr_leave : fr_leave_stmt.
Proof.
  intros C pos inp ob L z flush m res X E IL.
  destruct X as (OK & P0 & Pin & Inp & Imax & LO & ZO).
  destruct LO as (_ & SW & _).
  destruct E as [M LV WHY]. destruct M as [Mi Mn Ma Mo Mnx Mow Mw Mwh Mat].
  pose proof (proj1 (proj2 ZO)) as Hao.
  assert (OA: m_out m = m_aout m) by congruence.
  assert (OW: Zlength (m_ow m) <= Int.max_unsigned) by lia.
  pose proof Mw as (Ws & _).
  destruct IL as [LK WF |].
  - (* the window allocation fails: only when the window is used, so a stop *)
    unfold fr_post. cbv zeta. cbn [r_m r_ret m_snx m_sow m_ow m_s set_mode upd_s restore set_m_s set_m_sow
      set_m_snx i_wsize set_i_mode set_i_bits set_i_hold].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [intros _ Z0; congruence|].
    right; left. split; [reflexivity|].
    destruct (Z.eq_dec (i_wsize (l_s L)) 0) as [Z0|Z0]; [left|right; exact Z0].
    unfold leave_ok in LK. rewrite Ws, Z0 in LK. cbn in LK.
    apply andb_true_iff in LK. destruct LK as [LK _]. apply andb_true_iff in LK. destruct LK as [_ LK].
    apply Z.ltb_lt in LK.
    destruct WHY as [(Bd & _) | (_ & _ & St)]; [rewrite Bd in LK; lia | exact St].
  - (* the normal exit *)
    destruct (frl_fin flush m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    destruct (frl_s2_facts flush m) as (G1 & G2 & G3).
    set (mF := r_m (leave_fin flush m)) in *.
    assert (I: fr_inv C (pos + m_snx mF) (ob ++ m_ow mF) (m_s mF)).
    { rewrite F1, F2. split.
      - rewrite F5, F6, G2, G3. apply (frl_at_ext C (m_s m)); [|exact Mat].
        apply (frl_same_trans _ (frl_s2 flush m)); assumption.
      - rewrite F7. apply (frl_s2_whave flush m L ob); auto. }
    unfold fr_post. cbv zeta. fold mF. rewrite F1, F2, F3.
    split; [lia|]. split; [reflexivity|]. split; [lia|].
    split.
    { intros W0 Z0. rewrite F8. apply frl_s2_wsize; auto. congruence. }
    rewrite F1, F2 in I.
    destruct WHY as [(Bd & Rd) | (Bd & Ro & St)].
    + left. split; [|exact I].
      destruct F9 as [R | (_ & R)]; rewrite Rd in R; [exact R | discriminate].
    + right; right. split; [|split; [exact St | exact I]].
      destruct F9 as [R | (R & _)]; [left; congruence | right; exact R].
Qed.

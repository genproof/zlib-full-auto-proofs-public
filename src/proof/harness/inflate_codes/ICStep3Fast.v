(* LEN's fast path (ICStep3Stmts.v fast_stmt): inflate_fast's model (Model.v fast / fast_loop / fast_iter /
   fwalk_f / copy_bytes) preserves mwf3x.  Facts used: each iteration starts with >= 6 input bytes and
   >= 258 bytes of output space, reads at most 6 bytes and writes at most 258 (lvalid: len_ok);
   8 * nx - bits never decreases (so bits >> 3 <= nx - nx at entry, bits < 8 at entry). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_codes.ICStep3Stmts.
Import ListNotations.
Local Open Scope Z_scope.


(* ---------------------------------------------------------------------------------------------- *)
(* small facts                                                                                   *)

Lemma bytes_ok_Znth: forall l i, bytes_ok l -> 0 <= Znth i l <= 255.
Proof.
  intros l i H. unfold bytes_ok in H.
  destruct (zlt i 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia|].
  destruct (zlt i (Zlength l)); [|rewrite Znth_overflow by lia; unfold Inhabitant_Z; lia].
  rewrite Forall_forall in H. specialize (H (Znth i l) ltac:(apply Znth_In; lia)). simpl in H. rep_lia.
Qed.

Lemma bytes_ok_app1: forall l x, bytes_ok l -> 0 <= x <= 255 -> bytes_ok (l ++ [x]).
Proof. intros l x H X. unfold bytes_ok in *. apply Forall_app; split; auto. Qed.

Lemma copy_f_ok: forall n w sr ow ow' sr',
  copy_f n w sr ow = (ow', sr') -> bytes_ok w -> bytes_ok ow ->
  Zlength ow' = Zlength ow + Z.of_nat n /\ bytes_ok ow'.
Proof.
  induction n; intros w sr ow ow' sr' E Bw Bo; simpl in E.
  - inversion E; subst. split; [lia|auto].
  - destruct sr as [i|i].
    + apply IHn in E; auto.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil in E. destruct E; split; auto; lia.
      * apply bytes_ok_app1; auto. apply bytes_ok_Znth; auto.
    + apply IHn in E; auto.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil in E. destruct E; split; auto; lia.
      * apply bytes_ok_app1; auto. apply bytes_ok_Znth; auto.
Qed.

Lemma copy_bytes_ok: forall w sr n ow ow' sr',
  copy_bytes w sr n ow = (ow', sr') -> bytes_ok w -> bytes_ok ow ->
  Zlength ow' = Zlength ow + Z.max 0 n /\ bytes_ok ow'.
Proof.
  intros w sr n ow ow' sr' E Bw Bo. unfold copy_bytes in E. apply copy_f_ok in E; auto.
  destruct E as [E1 E2]. split; auto. rewrite E1. destruct (zlt n 0).
  - rewrite Z_to_nat_neg by lia. lia.
  - rewrite Z2Nat.id by lia. lia.
Qed.

Lemma len_link_true: forall op, 1 <= op <= 14 -> len_link op = true.
Proof.
  intros op H. assert (op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/
    op = 9 \/ op = 10 \/ op = 11 \/ op = 12 \/ op = 13 \/ op = 14) by lia.
  repeat (destruct H0 as [H0|H0]; [subst; reflexivity|]). subst; reflexivity.
Qed.

Lemma dist_link_true: forall op, 1 <= op <= 14 -> dist_link op = true.
Proof.
  intros op H. assert (op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5 \/ op = 6 \/ op = 7 \/ op = 8 \/
    op = 9 \/ op = 10 \/ op = 11 \/ op = 12 \/ op = 13 \/ op = 14) by lia.
  repeat (destruct H0 as [H0|H0]; [subst; reflexivity|]). subst; reflexivity.
Qed.

Lemma land16_cases: forall op, 16 <= op <= 29 -> Z.land op 16 <> 0 /\ Z.land op 15 = op - 16.
Proof.
  intros op H. assert (op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21 \/ op = 22 \/
    op = 23 \/ op = 24 \/ op = 25 \/ op = 26 \/ op = 27 \/ op = 28 \/ op = 29) by lia.
  repeat (destruct H0 as [H0|H0]; [subst; split; [discriminate|reflexivity]|]). subst; split; [discriminate|reflexivity].
Qed.

Lemma land_48_16: forall op, Z.land op 48 = 0 -> Z.land op 16 = 0.
Proof.
  intros op H. change 16 with (Z.land 48 16). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma len_link_final: forall e, final_ok LENS e -> len_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. simpl in H. unfold len_link.
  destruct H as [[H _] | [[H _] | [H | [H _]]]].
  - rewrite H. reflexivity.
  - destruct (land16_cases (e_op e) ltac:(lia)) as [A _].
    apply Z.eqb_neq in A. rewrite A. rewrite orb_true_r. reflexivity.
  - rewrite H. reflexivity.
  - apply Z.eqb_neq in H. rewrite H. rewrite orb_true_r. reflexivity.
Qed.

Lemma dist_link_final: forall e, final_ok DISTS e -> dist_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. simpl in H. unfold dist_link.
  destruct H as [[H _] | [H _]].
  - destruct (land16_cases (e_op e) ltac:(lia)) as [A _].
    apply Z.eqb_neq in A. rewrite A. reflexivity.
  - apply Z.eqb_neq in H. rewrite H. rewrite orb_true_r. reflexivity.
Qed.


Lemma final_len16: forall e, final_ok LENS e -> Z.land (e_op e) 16 <> 0 -> 16 <= e_op e <= 21.
Proof.
  intros e H L. unfold final_ok in H. simpl in H.
  destruct H as [[H _] | [[H _] | [H | [_ H]]]]; auto.
  - rewrite H in L. contradiction.
  - rewrite H in L. contradiction.
  - apply land_48_16 in H. contradiction.
Qed.

Lemma final_dist16: forall e, final_ok DISTS e -> Z.land (e_op e) 16 <> 0 -> 16 <= e_op e <= 29.
Proof.
  intros e H L. unfold final_ok in H. simpl in H.
  destruct H as [[H _] | [_ H]]; auto.
  apply land_48_16 in H. contradiction.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* frames: a machine that differs from another only in nx, hold, bits, ow                        *)

Definition mbuf (m: mst) (n h b: Z) (o: list Z) : mst :=
  set_m_ow (set_m_bits (set_m_hold (set_m_nx m n) h) b) o.

Definition frame (m m': mst) : Prop := m' = mbuf m (m_nx m') (m_hold m') (m_bits m') (m_ow m').

Lemma frame_refl: forall m, frame m m.
Proof. intros m. destruct m; reflexivity. Qed.

Lemma frame_trans: forall m1 m2 m3, frame m1 m2 -> frame m2 m3 -> frame m1 m3.
Proof.
  unfold frame. intros m1 m2 m3 E1 E2. rewrite E2 at 1. rewrite E1. reflexivity.
Qed.

Lemma frame_pull: forall m, frame m (pull m).
Proof. intros m. destruct m; reflexivity. Qed.

Lemma frame_drop: forall m k, frame m (dropbits k m).
Proof. intros m k. destruct m; reflexivity. Qed.

Lemma frame_ow: forall m o, frame m (set_m_ow m o).
Proof. intros m o. destruct m; reflexivity. Qed.

Lemma frame_s: forall m m', frame m m' -> m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\
  m_sow m' = m_sow m /\ m_out m' = m_out m.
Proof. intros m m' E. rewrite E. repeat split. Qed.

Lemma mwf_set_ow: forall m o, mwf m -> Zlength o <= m_aout m -> bytes_ok o -> m_sow m <= Zlength o ->
  mwf (set_m_ow m o).
Proof.
  intros m o W A B C. pose proof (mw_sow _ W). destruct W. constructor; simpl; auto; try lia.
Qed.

Definition avail (m: mst) : Z := 8 * (Zlength (m_inp m) - m_nx m) + m_bits m.
Definition qv (m: mst) : Z := 8 * m_nx m - m_bits m.

Lemma qv_ow: forall m o, qv (set_m_ow m o) = qv m.
Proof. reflexivity. Qed.

Lemma bits_ow: forall m o, m_bits (set_m_ow m o) = m_bits m.
Proof. reflexivity. Qed.

Lemma pull_facts: forall m, mwf m -> m_nx m < Zlength (m_inp m) -> 0 <= m_bits m <= 31 ->
  mwf (pull m) /\ frame m (pull m) /\ m_bits (pull m) = m_bits m + 8 /\ avail (pull m) = avail m /\
  qv (pull m) = qv m /\ m_ow (pull m) = m_ow m /\ m_nx (pull m) = m_nx m + 1.
Proof.
  intros m W N B.
  assert (Bp: m_bits (pull m) = m_bits m + 8) by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; lia).
  split; [apply mwf_pull; auto; unfold m_have; lia|].
  split; [apply frame_pull|]. split; [auto|].
  unfold avail, qv. rewrite Bp. unfold pull; simpl. repeat split; lia.
Qed.

Lemma drop_facts: forall m k, mwf m -> 0 <= k <= m_bits m ->
  mwf (dropbits k m) /\ frame m (dropbits k m) /\ m_bits (dropbits k m) = m_bits m - k /\
  avail (dropbits k m) = avail m - k /\ qv (dropbits k m) = qv m + k /\ m_ow (dropbits k m) = m_ow m /\
  m_nx (dropbits k m) = m_nx m.
Proof.
  intros m k W K.
  assert (Bp: m_bits (dropbits k m) = m_bits m - k)
    by (unfold dropbits; simpl; unfold u32; rewrite Z.mod_small; pose proof (mw_bits _ W); lia).
  split; [apply mwf_dropbits; auto|]. split; [apply frame_drop|]. split; [auto|].
  unfold avail, qv. rewrite Bp. unfold dropbits; simpl. repeat split; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* fast_iter cut into segments                                                                   *)

Definition s_fill2 (m: mst) : mst := if m_bits m <? 15 then fpull (fpull m) else m.

Definition s_lext (here: entry) (m: mst) : Z * mst :=
    let len := e_val here in
    let opx := Z.land (e_op here) 15 in
      if negb (opx =? 0) then
        let m := if m_bits m <? opx then fpull m else m in
        (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
      else (len, m).

Definition s_dext (opx: Z) (m: mst) : mst :=
  if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m.

Definition s_copy (s: istate) (m: mst) (dist len: Z) : bool * mst :=
      let op := Zlength (m_ow m) in        (* out - beg *)
      if op <? dist then
        let op := dist - op in
        if andb (i_whave s <? op) (negb (i_sane s =? 0)) then (false, set_bad m F_far) else
        let w := i_wdata s in
        let wsz := i_wsize s in let wnx := i_wnext s in
        let '(ow, sr, len) :=
          if wnx =? 0 then
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wsz - op), len)
          else if wnx <? op then
            let op2 := op - wnx in
            if op2 <? len then
              let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 (m_ow m) in
              let len := len - op2 in
              if wnx <? len then
                let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
                (ow, SOut (Zlength ow - dist), len - wnx)
              else (ow, SWin 0, len)
            else (m_ow m, SWin (wsz + wnx - op), len)
          else
            if op <? len then
              let '(ow, _) := copy_bytes w (SWin (wnx - op)) op (m_ow m) in
              (ow, SOut (Zlength ow - dist), len - op)
            else (m_ow m, SWin (wnx - op), len) in
        let '(ow, _) := copy_bytes w sr len ow in
        (true, set_m_ow m ow)
      else
        let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m) in
        (true, set_m_ow m ow).

Definition fast_iter' (m: mst) : bool * mst :=
  let s := m_s m in
  let m := s_fill2 m in
  let '(here, m) := fwalk_f lenfix_list distfix_list 2 len_link (i_lencode s)
                      (tab_entry lenfix_list distfix_list s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m in
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ [e_val here mod 256]))
  else if negb (Z.land op 16 =? 0) then
    let '(len, m) := s_lext here m in
    let m := s_fill2 m in
    let '(here, m) := fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode s)
                        (tab_entry lenfix_list distfix_list s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m in
    let op := e_op here in
    if negb (Z.land op 16 =? 0) then
      let opx := Z.land op 15 in
      let m := s_dext opx m in
      let dist := u32 (e_val here + m_hold m mod 2 ^ opx) in
      let m := dropbits opx m in
      s_copy s m dist len
    else (false, set_bad m F_d_code)
  else if negb (Z.land op 32 =? 0) then (false, set_mode m Model.TYPE)
  else (false, set_bad m F_ll_code).

Lemma fast_iter_eq: forall m, fast_iter lenfix_list distfix_list m = fast_iter' m.
Proof. intros m. reflexivity. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the segments                                                                                  *)

Lemma fill2_ok: forall m, mwf m -> 0 <= m_bits m <= 31 ->
  (m_bits m < 15 -> 16 <= 8 * (Zlength (m_inp m) - m_nx m)) ->
  mwf (s_fill2 m) /\ frame m (s_fill2 m) /\ 15 <= m_bits (s_fill2 m) <= 31 /\
  avail (s_fill2 m) = avail m /\ qv (s_fill2 m) = qv m /\ m_ow (s_fill2 m) = m_ow m.
Proof.
  intros m W B N. unfold s_fill2, fpull. destruct (Z.ltb_spec (m_bits m) 15).
  - specialize (N H).
    destruct (pull_facts m W ltac:(lia) B) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    destruct (pull_facts (pull m) W1 ltac:(rewrite N1; unfold pull; simpl; lia) ltac:(lia))
      as (W2 & F2 & B2 & A2 & Q2 & O2 & N2).
    split; [auto|]. split; [eapply frame_trans; eauto|]. split; [lia|]. split; [congruence|].
    split; congruence.
  - split; [auto|]. split; [apply frame_refl|]. split; [lia|]. auto.
Qed.

Lemma fwalk_S: forall k lf t e m, fwalk_f lenfix_list distfix_list (S k) lf t e m =
  let m1 := dropbits (e_bits e) m in
  if lf (e_op e) then fwalk_f lenfix_list distfix_list k lf t
                        (tab_entry lenfix_list distfix_list (m_s m1) t (e_val e + m_hold m1 mod 2 ^ e_op e)) m1
  else (e, m1).
Proof. reflexivity. Qed.

Lemma fwalk_ok: forall kind lf t rb sz s m here m',
  tvalid_g kind (tab_entry lenfix_list distfix_list s t) rb sz ->
  (forall op, 1 <= op <= 14 -> lf op = true) ->
  (forall e, final_ok kind e -> lf (e_op e) = false) ->
  mwf m -> m_s m = s -> 15 <= m_bits m ->
  fwalk_f lenfix_list distfix_list 2 lf t (tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)) m = (here, m') ->
  mwf m' /\ frame m m' /\ m_bits m - 15 <= m_bits m' <= m_bits m /\ avail m - 15 <= avail m' /\ qv m <= qv m' /\
  m_ow m' = m_ow m /\
  final_ok kind here /\ (exists i, 0 <= i < sz /\ here = tab_entry lenfix_list distfix_list s t i).
Proof.
  intros kind lf t rb sz s m here m' TV LT LF W Es Bm E.
  pose proof (tv_rb _ _ _ _ TV) as RB. pose proof (tv_size _ _ _ _ TV) as SZ.
  assert (Hi: 0 <= m_hold m mod 2 ^ rb < 2 ^ rb) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  set (i := m_hold m mod 2 ^ rb) in *.
  pose proof (tv_root _ _ _ _ TV i Hi) as R. cbv zeta in R. destruct R as [Eok R].
  set (e := tab_entry lenfix_list distfix_list s t i) in *.
  rewrite fwalk_S in E. cbv zeta in E.
  destruct (islink kind (e_op e)) eqn:IL.
  - destruct R as (R1 & R2 & R3 & R4).
    rewrite (LT (e_op e) ltac:(lia)) in E.
    destruct (drop_facts m (e_bits e) W ltac:(lia)) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    set (m1 := dropbits (e_bits e) m) in *.
    assert (Hj: 0 <= m_hold m1 mod 2 ^ e_op e < 2 ^ e_op e) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    destruct (R4 _ Hj) as (S1 & S2 & S3 & S4 & S5). cbv zeta in S1, S2, S3, S4, S5.
    assert (Es1: m_s m1 = s) by (unfold m1, dropbits; simpl; auto).
    rewrite Es1 in E.
    set (e2 := tab_entry lenfix_list distfix_list s t (e_val e + m_hold m1 mod 2 ^ e_op e)) in *.
    rewrite fwalk_S in E. cbv zeta in E. rewrite (LF _ S5) in E.
    inversion E; subst here m'. destruct S2 as (_ & S2 & _).
    destruct (drop_facts m1 (e_bits e2) W1 ltac:(lia)) as (W2 & F2 & B2 & A2 & Q2 & O2 & N2).
    split; [auto|]. split; [eapply frame_trans; eauto|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [congruence|]. split; [auto|]. exists (e_val e + m_hold m1 mod 2 ^ e_op e). split; [lia|reflexivity].
  - destruct R as [R1 R2]. rewrite (LF _ R2) in E. inversion E; subst here m'.
    destruct Eok as (_ & Eb & _).
    destruct (drop_facts m (e_bits e) W ltac:(lia)) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [auto|]. split; [auto|]. exists i. split; [lia|reflexivity].
Qed.


Lemma final_len_val: forall e, final_ok LENS e -> 16 <= e_op e <= 21 -> 3 <= e_val e <= 258.
Proof.
  intros e H R. unfold final_ok in H. simpl in H.
  destruct H as [[H _] | [[_ H] | [H | [H _]]]]; try lia.
  exfalso. apply H. assert (e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21) by lia.
  repeat (destruct H0 as [H0|H0]; [rewrite H0; reflexivity|]). rewrite H0; reflexivity.
Qed.

Lemma lext_ok: forall here m len m',
  mwf m -> 0 <= m_bits m <= 31 -> 16 <= e_op here <= 21 -> final_ok LENS here -> len_ok here ->
  (m_bits m < 5 -> m_nx m < Zlength (m_inp m)) ->
  s_lext here m = (len, m') ->
  mwf m' /\ frame m m' /\ 0 <= m_bits m' <= 31 /\ avail m - 5 <= avail m' /\ qv m <= qv m' /\
  m_ow m' = m_ow m /\ 0 <= len <= 258.
Proof.
  intros here m len m' W B Op F L N E. unfold s_lext in E. cbv zeta in E.
  destruct (land16_cases (e_op here) ltac:(lia)) as [_ Lx].
  pose proof (final_len_val here F Op) as V. unfold len_ok in L. specialize (L Op).
  set (opx := Z.land (e_op here) 15) in *.
  destruct (Z.eqb_spec opx 0) as [Z0|Z0].
  - simpl in E. inversion E; subst len m'.
    split; [auto|]. split; [apply frame_refl|]. repeat split; try lia.
  - simpl in E.
    assert (P: exists m1, (if m_bits m <? opx then fpull m else m) = m1 /\ mwf m1 /\ frame m m1 /\
               opx <= m_bits m1 <= 31 /\ avail m1 = avail m /\ qv m1 = qv m /\ m_ow m1 = m_ow m).
    { destruct (Z.ltb_spec (m_bits m) opx).
      - destruct (pull_facts m W ltac:(apply N; lia) B) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
        exists (pull m). split; [reflexivity|]. split; [auto|]. split; [auto|]. split; [lia|].
        split; [lia|]. split; congruence.
      - exists m. split; [reflexivity|]. split; [auto|]. split; [apply frame_refl|]. repeat split; lia. }
    destruct P as (m1 & E1 & W1 & F1 & B1 & A1 & Q1 & O1). rewrite E1 in E.
    inversion E; subst len m'. fold (dropbits opx m1).
    destruct (drop_facts m1 opx W1 ltac:(lia)) as (W2 & F2 & B2 & A2 & Q2 & O2 & N2).
    split; [auto|]. split; [eapply frame_trans; eauto|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [congruence|].
    assert (0 <= m_hold m1 mod 2 ^ opx < 2 ^ opx) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    rewrite Lx in *. unfold u32. rewrite Z.mod_small; lia.
Qed.

Lemma dext_ok: forall opx m, mwf m -> 0 <= opx <= 13 -> 0 <= m_bits m <= 31 -> 13 <= avail m ->
  mwf (s_dext opx m) /\ frame m (s_dext opx m) /\ opx <= m_bits (s_dext opx m) <= 31 /\
  qv (s_dext opx m) = qv m /\ m_ow (s_dext opx m) = m_ow m.
Proof.
  intros opx m W X B A. unfold s_dext, fpull, avail in *.
  destruct (Z.ltb_spec (m_bits m) opx).
  - destruct (pull_facts m W ltac:(lia) B) as (W1 & F1 & B1 & A1 & Q1 & O1 & N1).
    unfold avail in A1. rewrite B1.
    destruct (Z.ltb_spec (m_bits m + 8) opx).
    + destruct (pull_facts (pull m) W1 ltac:(lia) ltac:(lia)) as (W2 & F2 & B2 & A2 & Q2 & O2 & N2).
      split; [auto|]. split; [eapply frame_trans; eauto|]. split; [lia|]. split; congruence.
    + split; [auto|]. split; [auto|]. split; [lia|]. split; congruence.
  - split; [auto|]. split; [apply frame_refl|]. split; [lia|]. split; auto.
Qed.

Lemma copy_ok: forall s m dist len go m',
  bytes_ok (i_wdata s) -> bytes_ok (m_ow m) -> 0 <= len -> 0 <= i_wnext s ->
  s_copy s m dist len = (go, m') ->
  (go = true /\ exists o, m' = set_m_ow m o /\ Zlength o = Zlength (m_ow m) + len /\ bytes_ok o) \/
  (go = false /\ m' = set_bad m F_far).
Proof.
  intros s m dist len go m' Bw Bo Hl Hw E. unfold s_copy in E. cbv zeta in E.
  repeat match type of E with
  | context [if ?c then _ else _] => destruct c eqn:?; cbv beta iota in E
  | context [copy_bytes ?w ?sr ?n ?o] =>
      let H := fresh "C" in destruct (copy_bytes w sr n o) as [? ?] eqn:H;
      apply copy_bytes_ok in H; [destruct H as [? ?] | auto | auto]; cbv beta iota in E
  end.
  all: inversion E; subst.
  all: try (right; split; reflexivity).
  all: left; split; [reflexivity|]; eexists; split; [reflexivity|]; split; [|auto].
  all: repeat match goal with H: (_ <? _) = _ |- _ => first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end.
  all: repeat match goal with H: (_ =? _) = _ |- _ => first [apply Z.eqb_eq in H | apply Z.eqb_neq in H] end.
  all: lia.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* one iteration                                                                                 *)

Definition iter_post (m: mst) (r: bool * mst) : Prop :=
  let '(go, m') := r in
  exists mb, frame m mb /\ mwf mb /\ qv m <= qv mb /\ 0 <= m_bits mb <= 31 /\
    ((go = true /\ m' = mb) \/
     (go = false /\ (m' = set_mode mb Model.TYPE \/ exists e, m' = set_bad mb e))).

Lemma iter_ok: forall m, mwf3x m -> m_mode m = LEN -> m_nx m + 6 <= Zlength (m_inp m) ->
  Zlength (m_ow m) + 258 <= m_aout m -> m_bits m <= 31 -> iter_post m (fast_iter' m).
Proof.
  intros m [W X] Hmd Hnx How Hb.
  assert (DM: decode_mode (m_mode m)) by (unfold decode_mode; right; left; exact Hmd).
  destruct (x3_lens _ X DM) as (lsz & Lsz & LV & LOK).
  destruct (md_tables _ (mw_md _ W) DM) as [_ (dsz & Dsz & DV)].
  pose proof (mw_bits _ W) as B0.
  pose proof (sw_wdata _ (mw_s _ W)) as [_ BW].
  pose proof (sw_wnext _ (mw_s _ W)) as [[WN _] _].
  pose proof (mw_ow _ W) as [_ BO].
  assert (A0: 48 <= avail m) by (unfold avail; lia).
  unfold fast_iter'. cbv zeta.
  destruct (fill2_ok m W ltac:(lia) ltac:(intros; lia)) as (W1 & F1 & B1 & A1 & Q1 & O1).
  destruct (frame_s _ _ F1) as (S1 & I1 & AO1 & SO1 & _).
  match goal with |- context [fwalk_f ?a ?b ?c ?d ?e ?f ?g] => destruct (fwalk_f a b c d e f g) as [h1 m2] eqn:E2 end.
  destruct (fwalk_ok LENS len_link _ _ _ _ _ h1 m2 LV len_link_true len_link_final W1 S1 ltac:(lia) E2)
    as (W2 & F2 & B2 & A2 & Q2 & O2 & FO2 & (i2 & I2 & H2)).
  destruct (frame_s _ _ F2) as (S2 & I2' & AO2 & SO2 & _).
  cbv beta iota.
  destruct (e_op h1 =? 0) eqn:Op0; cbv beta iota.
  - (* literal *)
    exists (set_m_ow m2 (m_ow m2 ++ [e_val h1 mod 256])).
    pose proof (Z.mod_pos_bound (e_val h1) 256 ltac:(lia)).
    split; [eapply frame_trans; [exact F1|]; eapply frame_trans; [exact F2|]; apply frame_ow|].
    split.
    { apply mwf_set_ow; auto.
      - rewrite Zlength_app, Zlength_cons, Zlength_nil. rewrite O2, O1, AO2, AO1. lia.
      - apply bytes_ok_app1; [congruence|lia].
      - pose proof (mw_sow _ W2). rewrite Zlength_app. pose proof (Zlength_nonneg [e_val h1 mod 256]). lia. }
    split; [unfold qv in *; simpl; lia|]. split; [simpl; lia|]. left; auto.
  - destruct (Z.land (e_op h1) 16 =? 0) eqn:L16; cbv beta iota.
    + destruct (Z.land (e_op h1) 32 =? 0); cbv beta iota;
      exists m2; (split; [eapply frame_trans; eauto|]); (split; [auto|]); (split; [lia|]); (split; [lia|]);
      right; (split; [reflexivity|]); [right; eexists; reflexivity | left; reflexivity].
    + apply Z.eqb_neq in L16. pose proof (final_len16 _ FO2 L16) as OpR.
      assert (LO: len_ok h1) by (rewrite H2; apply LOK; auto).
      destruct (s_lext h1 m2) as [len m3] eqn:E3.
      unfold avail in A0, A1, A2.
      destruct (lext_ok h1 m2 len m3 W2 ltac:(lia) OpR FO2 LO ltac:(intros; lia) E3)
        as (W3 & F3 & B3 & A3 & Q3 & O3 & Len).
      destruct (frame_s _ _ F3) as (S3 & I3 & AO3 & SO3 & _).
      unfold avail in A3.
      cbv beta iota.
      destruct (fill2_ok m3 W3 ltac:(lia) ltac:(intros; lia)) as (W4 & F4 & B4 & A4 & Q4 & O4).
      destruct (frame_s _ _ F4) as (S4 & I4 & AO4 & SO4 & _).
      match goal with |- context [fwalk_f ?a ?b ?c ?d ?e ?f ?g] => destruct (fwalk_f a b c d e f g) as [h5 m5] eqn:E5 end.
      destruct (fwalk_ok DISTS dist_link _ _ _ _ _ h5 m5 DV dist_link_true dist_link_final W4
                  ltac:(congruence) ltac:(lia) E5)
        as (W5 & F5 & B5 & A5 & Q5 & O5 & FO5 & _).
      destruct (frame_s _ _ F5) as (S5 & I5 & AO5 & SO5 & _).
      cbv beta iota.
      destruct (Z.land (e_op h5) 16 =? 0) eqn:D16; cbv beta iota.
      * exists m5.
        split; [repeat (eapply frame_trans; [eassumption|]); apply frame_refl|].
        split; [auto|]. split; [lia|]. split; [lia|].
        right. split; [reflexivity|]. right; eexists; reflexivity.
      * apply Z.eqb_neq in D16. pose proof (final_dist16 _ FO5 D16) as DR.
        destruct (land16_cases (e_op h5) DR) as [_ DX].
        unfold avail in A4, A5.
        destruct (dext_ok (Z.land (e_op h5) 15) m5 W5 ltac:(lia) ltac:(lia) ltac:(unfold avail; lia))
          as (W6 & F6 & B6 & Q6 & O6).
        destruct (drop_facts _ (Z.land (e_op h5) 15) W6 ltac:(lia)) as (W7 & F7 & B7 & A7 & Q7 & O7 & N7).
        destruct (frame_s _ _ F6) as (S6 & I6 & AO6 & SO6 & _).
        destruct (frame_s _ _ F7) as (S7 & I7 & AO7 & SO7 & _).
        match goal with |- context [s_copy ?a ?b ?c ?d] => destruct (s_copy a b c d) as [go m8] eqn:E8 end.
        assert (OW7: m_ow (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)) = m_ow m) by congruence.
        apply copy_ok in E8; [| auto | rewrite OW7; auto | lia | auto].
        destruct E8 as [(G & o & E8 & Lo & Bo8) | (G & E8)]; subst go m8.
        -- exists (set_m_ow (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)) o).
           split; [repeat (eapply frame_trans; [eassumption|]); apply frame_ow|].
           split.
           { apply mwf_set_ow; auto; rewrite ?AO7, ?AO6, ?AO5, ?AO4, ?AO3, ?AO2.
             - rewrite AO1. rewrite OW7 in Lo. lia.
             - pose proof (mw_sow _ W7). lia. }
           rewrite qv_ow, bits_ow. split; [lia|]. split; [lia|]. left; auto.
        -- exists (dropbits (Z.land (e_op h5) 15) (s_dext (Z.land (e_op h5) 15) m5)).
           split; [repeat (eapply frame_trans; [eassumption|]); apply frame_refl|].
           split; [auto|]. split; [lia|]. split; [lia|].
           right. split; [reflexivity|]. right; eexists; reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the loop                                                                                      *)

Lemma mwf3x_of_frame: forall m mb, mwf3x m -> frame m mb -> mwf mb -> mwf3x mb.
Proof.
  intros m mb [W X] F Wb. destruct (frame_s _ _ F) as (S & _).
  apply mwf3x_intro with m; auto.
Qed.

Lemma fast_loop_S: forall k m, fast_loop lenfix_list distfix_list (S k) m =
  let '(go, m) := fast_iter lenfix_list distfix_list m in
  if andb (andb go (m_nx m <? Zlength (m_inp m) - 5)) (Zlength (m_ow m) <? m_aout m - 257)
  then fast_loop lenfix_list distfix_list k m else m.
Proof. reflexivity. Qed.

Lemma loop_ok: forall k m, mwf3x m -> m_mode m = LEN -> m_nx m + 6 <= Zlength (m_inp m) ->
  Zlength (m_ow m) + 258 <= m_aout m -> 0 <= m_bits m <= 31 ->
  exists mb, frame m mb /\ mwf3x mb /\ qv m <= qv mb /\ 0 <= m_bits mb <= 31 /\
    (fast_loop lenfix_list distfix_list k m = mb \/
     fast_loop lenfix_list distfix_list k m = set_mode mb Model.TYPE \/
     exists e, fast_loop lenfix_list distfix_list k m = set_bad mb e).
Proof.
  induction k; intros m W Hmd Hnx How Hb.
  - exists m. split; [apply frame_refl|]. split; [auto|]. split; [lia|]. split; [lia|]. left; reflexivity.
  - rewrite fast_loop_S, fast_iter_eq.
    pose proof (iter_ok m W Hmd Hnx How ltac:(lia)) as IT.
    destruct (fast_iter' m) as [go m1]. destruct IT as (mb & F & Wb & Q & B & C).
    assert (W2: mwf3x mb) by (eapply mwf3x_of_frame; eauto).
    destruct (frame_s _ _ F) as (S & I & AO & _).
    destruct C as [(G & E) | (G & E)]; subst go.
    + subst m1. simpl andb.
      destruct (andb (m_nx mb <? Zlength (m_inp mb) - 5) (Zlength (m_ow mb) <? m_aout mb - 257)) eqn:Cnd.
      * apply andb_prop in Cnd. destruct Cnd as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
        assert (Md: m_mode mb = LEN) by (unfold m_mode; rewrite S; exact Hmd).
        destruct (IHk mb W2 Md ltac:(lia) ltac:(lia) B) as (mb' & F' & W' & Q' & B' & C').
        exists mb'. split; [eapply frame_trans; eauto|]. split; [auto|]. split; [lia|]. split; [lia|]. exact C'.
      * exists mb. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. left; reflexivity.
    + simpl andb. exists mb. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. right.
      destruct E as [E|[e E]]; [left; exact E | right; exists e; exact E].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* after the loop                                                                                *)

Definition post (m: mst) : mst :=
  let len := Z.shiftr (m_bits m) 3 in
  let m := set_m_nx m (m_nx m - len) in
  let bits := m_bits m - len * 8 in
  set_m_bits (set_m_hold m (m_hold m mod 2 ^ bits)) bits.

Lemma fast_eq: forall m, fast lenfix_list distfix_list m =
  restore (post (fast_loop lenfix_list distfix_list (Z.to_nat (m_aout m) + 1) m)).
Proof. reflexivity. Qed.

Lemma tab_entry_codes: forall s s' t i, i_codes s' = i_codes s ->
  tab_entry lenfix_list distfix_list s' t i = tab_entry lenfix_list distfix_list s t i.
Proof. intros s s' t i E. destruct t; simpl; congruence. Qed.

Lemma tvalid_codes: forall kind s s' t rb, i_codes s' = i_codes s ->
  tvalid kind lenfix_list distfix_list s t rb -> tvalid kind lenfix_list distfix_list s' t rb.
Proof.
  intros kind s s' t rb E (sz & A & B). exists sz. split; auto.
  unfold tvalid_b in *. eapply tvalid_g_ext; [|exact B]. intros. symmetry; apply tab_entry_codes; auto.
Qed.

Lemma lvalid_codes: forall s s' t rb, i_codes s' = i_codes s ->
  lvalid lenfix_list distfix_list s t rb -> lvalid lenfix_list distfix_list s' t rb.
Proof.
  intros s s' t rb E (sz & A & B & C). exists sz. split; auto. split.
  - unfold tvalid_b in *. eapply tvalid_g_ext; [|exact B]. intros. symmetry; apply tab_entry_codes; auto.
  - intros i Hi. rewrite (tab_entry_codes s s'); auto.
Qed.

(* the state with other hold / bits / back: the same facts *)
Lemma mwf3x_upd_s: forall m f,
  mwf3x m ->
  (forall s, swf s -> swf (f s)) ->
  (forall s, i_mode (f s) = i_mode s /\ i_codes (f s) = i_codes s /\ i_lencode (f s) = i_lencode s /\
             i_distcode (f s) = i_distcode s /\ i_lenbits (f s) = i_lenbits s /\
             i_distbits (f s) = i_distbits s /\ i_ncode (f s) = i_ncode s /\ i_nlen (f s) = i_nlen s /\
             i_ndist (f s) = i_ndist s /\ i_have (f s) = i_have s /\ i_lens (f s) = i_lens s /\
             i_extra (f s) = i_extra s /\ i_length (f s) = i_length s /\ i_offset (f s) = i_offset s /\
             i_wbits (f s) = i_wbits s /\ i_wsize (f s) = i_wsize s /\
             i_wrap (f s) = i_wrap s /\ i_win (f s) = i_win s) ->
  (i_mode (m_s m) = LENEXT \/ i_mode (m_s m) = DIST \/ i_mode (m_s m) = DISTEXT -> i_back (f (m_s m)) = i_back (m_s m)) ->
  mwf3x (upd_s m f).
Proof.
  intros m f [W X] SW FE BK.
  destruct (FE (m_s m)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18).
  constructor.
  - destruct W. constructor; simpl; auto.
    + destruct mw_md as [L1 L2 L3 L4 L5 L6 L7 L8 L9].
      constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9, ?E10, ?E11, ?E12, ?E13, ?E14.
      * exact L1.
      * intros H. destruct (L2 H) as (A1 & A2 & A3 & A4 & A5 & A6).
        split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [|auto].
        apply tvalid_codes with (s := m_s m); auto.
      * intros H. destruct (L3 H) as [A1 A2]. split; apply tvalid_codes with (s := m_s m); auto.
      * exact L4.
      * exact L5.
      * exact L6.
      * exact L7.
      * exact L8.
      * destruct L9 as (B1 & B2 & B3).
        split; [intros H; rewrite BK by (left; exact H); auto|].
        split; [intros H; rewrite BK by (right; left; exact H); auto|].
        intros H; rewrite BK by (right; right; exact H); auto.
    + unfold m_mode in *; simpl. rewrite E1. auto.
  - destruct X. constructor; unfold m_mode; simpl; rewrite ?E1, ?E3, ?E5, ?E13, ?E14, ?E15, ?E16, ?E17, ?E18; auto.
    intros D. apply lvalid_codes with (s := m_s m); auto.
Qed.


Lemma mwf3x_restore: forall m, mwf3x m -> mwf3x (restore m).
Proof.
  intros m [W X]. unfold restore.
  pose proof (mw_hold _ W) as WH. pose proof (mw_bits _ W) as WB.
  apply mwf3x_upd_s.
  - constructor.
    + pose proof (mw_nx _ W). pose proof (Zlength_nonneg (m_ow m)).
      destruct W; constructor; simpl; auto; lia.
    + apply xwf3_ext with m; auto.
  - intros s' Hs. destruct Hs; constructor; simpl; auto.
  - intros s'. simpl. repeat split.
  - intros _. reflexivity.
Qed.

Lemma mwf_post: forall m, mwf m -> 0 <= m_bits m <= 31 -> -8 < qv m -> mwf (post m).
Proof.
  intros m W B Q. unfold qv in Q.
  assert (S: Z.shiftr (m_bits m) 3 = m_bits m / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  pose proof (Z.div_mod (m_bits m) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)).
  pose proof (mw_hold _ W) as WH.
  assert (Pw: 0 < 2 ^ (m_bits m - m_bits m / 8 * 8)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound (m_hold m) (2 ^ (m_bits m - m_bits m / 8 * 8)) Pw).
  pose proof (Z.mod_le (m_hold m) (2 ^ (m_bits m - m_bits m / 8 * 8)) ltac:(unfold lrange in WH; lia) Pw).
  unfold post. rewrite S. remember (m_bits m / 8) as q eqn:Hq. clear Hq.
  destruct W; constructor; simpl; auto.
  - lia.
  - unfold lrange in *. lia.
  - lia.
Qed.

Lemma mwf3x_post: forall m, mwf3x m -> 0 <= m_bits m <= 31 -> -8 < qv m -> mwf3x (post m).
Proof.
  intros m W B Q. apply mwf3x_of_frame with m; auto.
  - destruct m; reflexivity.
  - apply mwf_post; auto. apply W.
Qed.

Lemma mwf3x_set_msg: forall m e, mwf3x m -> mwf3x (set_m_msg m e).
Proof.
  intros m e [W X]. constructor.
  - destruct W; constructor; simpl; auto.
  - apply xwf3_ext with m; auto.
Qed.

Lemma post_set_mode: forall m md, restore (post (set_mode m md)) = set_mode (restore (post m)) md.
Proof. reflexivity. Qed.

Lemma post_set_bad: forall m e, restore (post (set_bad m e)) = set_bad (restore (post m)) e.
Proof. reflexivity. Qed.

Lemma mode_restore_post: forall m, m_mode (restore (post m)) = m_mode m.
Proof. reflexivity. Qed.

Lemma TYPE_range: HEAD <= Model.TYPE <= SYNC /\ Model.TYPE <> LENLENS /\ Model.TYPE <> CODELENS /\
  ~ decode_mode Model.TYPE.
Proof. unfold HEAD, Model.TYPE, SYNC, LENLENS, CODELENS, decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT. lia. Qed.

Lemma BAD_range: HEAD <= BAD <= SYNC /\ BAD <> LENLENS /\ BAD <> CODELENS /\ ~ decode_mode BAD.
Proof. unfold HEAD, BAD, SYNC, LENLENS, CODELENS, decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT. lia. Qed.

Lemma mode_neq: LEN <> Model.TYPE /\ BAD <> Model.TYPE /\ Model.TYPE <> LENEXT /\ Model.TYPE <> DIST /\
  Model.TYPE <> DISTEXT.
Proof. unfold LEN, BAD, Model.TYPE, LENEXT, DIST, DISTEXT. lia. Qed.

Lemma fast_ok : fast_stmt.
Proof.
  intros m W L Md Hh Hl Hb.
  pose proof (mwf3x_restore m W) as W0.
  set (m0 := restore m) in *.
  assert (Md0: m_mode m0 = LEN) by exact Md.
  assert (N0: m_nx m0 + 6 <= Zlength (m_inp m0)) by (unfold m_have in Hh; exact (ltac:(simpl; lia))).
  assert (O0: Zlength (m_ow m0) + 258 <= m_aout m0) by (unfold m_left in Hl; exact (ltac:(simpl; lia))).
  assert (B0: 0 <= m_bits m0 <= 31) by (pose proof (mw_bits _ (m3_w _ W)); exact (ltac:(simpl; lia))).
  assert (Q0: -8 < qv m0) by (pose proof (mw_nx _ (m3_w _ W)); unfold qv; exact (ltac:(simpl; lia))).
  destruct (loop_ok (Z.to_nat (m_aout m0) + 1) m0 W0 Md0 N0 O0 B0) as (mb & F & Wb & Q & B & C).
  destruct (frame_s _ _ F) as (S & _).
  assert (Mb: m_mode mb = LEN) by (unfold m_mode; rewrite S; exact Md0).
  assert (Wp: mwf3x (restore (post mb))) by (apply mwf3x_restore; apply mwf3x_post; auto; lia).
  assert (Mp: m_mode (restore (post mb)) = LEN) by (rewrite mode_restore_post; exact Mb).
  assert (Op: m_out (restore (post mb)) = m_aout (restore (post mb))).
  { apply mwf_out_eq; [apply Wp | rewrite Mp; unfold LEN, LENGTH; lia
                     | rewrite Mp; unfold LEN, DONE; lia | rewrite Mp; unfold LEN, BAD; lia]. }
  destruct mode_neq as (N1 & N2 & N3 & N4 & N5).
  rewrite fast_eq. cbv zeta.
  destruct C as [E | [E | [e E]]]; rewrite E.
  - rewrite Mp. apply Z.eqb_neq in N1. rewrite N1. exact Wp.
  - rewrite post_set_mode.
    destruct TYPE_range as (R1 & R2 & R3 & R4).
    assert (Wt: mwf3x (set_mode (restore (post mb)) Model.TYPE)) by (apply mwf3x_set_mode_plain; auto; unfold HEAD, Model.TYPE, SYNC; lia).
    replace (m_mode (set_mode (restore (post mb)) Model.TYPE) =? Model.TYPE) with true
      by (symmetry; apply Z.eqb_eq; reflexivity).
    apply mwf3x_upd_s; auto.
    + intros s' Hs. destruct Hs; constructor; simpl; auto. lia.
    + intros s'. simpl. repeat split.
    + intros [H|[H|H]]; simpl in H; congruence.
  - rewrite post_set_bad. unfold set_bad.
    destruct BAD_range as (R1 & R2 & R3 & R4).
    assert (Wt: mwf3x (set_mode (set_m_msg (restore (post mb)) (Some e)) BAD)).
    { apply mwf3x_set_mode_plain; auto; first [apply mwf3x_set_msg; auto | unfold HEAD, BAD, SYNC; lia]. }
    replace (m_mode (set_mode (set_m_msg (restore (post mb)) (Some e)) BAD) =? Model.TYPE) with false
      by (symmetry; apply Z.eqb_neq; exact N2).
    exact Wt.
Qed.

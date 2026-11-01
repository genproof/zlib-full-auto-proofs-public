(* MATCH: the copy of up to min(length, left) bytes of a match, from the window (the bytes of O0, the output
   of the earlier calls) or from the output of this call, is as many abstract steps, one byte each; a
   distance past the start of the whole output is refused by both machines (the window test whave < copy is
   the abstract |output| < offset because whave = min(|O0|, 32768) and offset <= 32768). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimDecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract side: k steps of a_MATCH                                                          *)

(* the abstract state after k bytes of a match: the length decreased by k, LEN when it reaches 0 *)
Definition mstate (s: istate) (k: Z) : istate :=
  if i_length s - k =? 0 then set_i_mode (set_i_length s (i_length s - k)) LEN
  else set_i_length s (i_length s - k).

Lemma set_i_length_twice s v v' : set_i_length (set_i_length s v) v' = set_i_length s v'.
Proof. destruct s; reflexivity. Qed.

Lemma set_i_length_same s : set_i_length s (i_length s) = s.
Proof. destruct s; reflexivity. Qed.

(* n bytes of a match that does not go past the start of the output O, within the limits, are n steps;
   the bytes written are those of a copy from |O| - offset in the output itself *)
Lemma amatch_steps src I R : forall n s q O,
  i_mode s = MATCH -> 1 <= i_length s -> Z.of_nat n <= i_length s -> i_offset s <= Zlength O ->
  q <= 8 * I -> Zlength O + Z.of_nat n <= R ->
  areach src I R (AS s q O)
    (AS (mstate s (Z.of_nat n)) q (fst (copy_f n [] (SOut (Zlength O - i_offset s)) O))).
Proof.
  induction n as [|n IH]; intros s q O Md L1 Ln Off Q Rn.
  - cbn [copy_f fst]. unfold mstate. replace (i_length s - Z.of_nat 0) with (i_length s) by lia.
    destruct (Z.eqb_spec (i_length s) 0); [lia|]. rewrite set_i_length_same. constructor.
  - assert (Hs: astep lenfix_list distfix_list src (AS s q O) =
      AGo q true (AS (if i_length s - 1 =? 0 then set_i_mode (set_i_length s (i_length s - 1)) LEN
                      else set_i_length s (i_length s - 1)) q (O ++ [Znth (Zlength O - i_offset s) O]))).
    { rewrite astep_MATCH by exact Md. unfold a_MATCH. cbn [a_s a_O a_q].
      destruct (Z.ltb_spec (Zlength O) (i_offset s)); [lia|]. reflexivity. }
    eapply ar_step; [exact Hs| |].
    { cbn [blocked a_O]. intros [B|[_ B]]; lia. }
    cbn [copy_f].
    destruct (Z.eqb_spec (i_length s - 1) 0) as [E|E].
    + assert (n = 0%nat) by lia. subst n. cbn [copy_f fst].
      unfold mstate. replace (i_length s - Z.of_nat 1) with (i_length s - 1) by lia. rewrite E. constructor.
    + assert (A := IH (set_i_length s (i_length s - 1)) q (O ++ [Znth (Zlength O - i_offset s) O])
                    Md ltac:(cbn; lia) ltac:(cbn; lia)
                    ltac:(cbn; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia) Q
                    ltac:(rewrite Zlength_app, Zlength_cons, Zlength_nil; lia)).
      replace (mstate s (Z.of_nat (S n))) with (mstate (set_i_length s (i_length s - 1)) (Z.of_nat n)).
      2:{ unfold mstate. cbn [i_length set_i_length]. rewrite !set_i_length_twice.
          replace (i_length s - 1 - Z.of_nat n) with (i_length s - Z.of_nat (S n)) by lia. reflexivity. }
      replace (Zlength O - i_offset s + 1) with
        (Zlength (O ++ [Znth (Zlength O - i_offset s) O]) - i_offset (set_i_length s (i_length s - 1))).
      2:{ cbn [i_offset set_i_length]. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
      exact A.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The concrete copies as copies of the whole output                                              *)

Lemma copy_f_length n : forall w sr ow, Zlength (fst (copy_f n w sr ow)) = Zlength ow + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros w sr ow; cbn [copy_f fst]; [lia|].
  destruct sr; rewrite IH, Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

(* a copy from the output of this call is the copy from the whole output O0 ++ ow *)
Lemma copy_out_app w w' O0 : forall n i ow, Zlength O0 <= i ->
  O0 ++ fst (copy_f n w (SOut (i - Zlength O0)) ow) = fst (copy_f n w' (SOut i) (O0 ++ ow)).
Proof.
  induction n as [|n IH]; intros i ow Hi; cbn [copy_f fst]; [reflexivity|].
  rewrite Znth_app2 by lia. rewrite <- app_assoc.
  replace (i - Zlength O0 + 1) with (i + 1 - Zlength O0) by lia. apply IH. lia.
Qed.

(* a copy from the window, whose bytes are those of O0 from i' on, is the copy from the whole output *)
Lemma copy_win_app w w' O0 : forall n i i' ow, 0 <= i' -> i' + Z.of_nat n <= Zlength O0 ->
  (forall j, 0 <= j < Z.of_nat n -> Znth (i + j) w = Znth (i' + j) O0) ->
  O0 ++ fst (copy_f n w (SWin i) ow) = fst (copy_f n w' (SOut i') (O0 ++ ow)).
Proof.
  induction n as [|n IH]; intros i i' ow H0 Hn Hw; cbn [copy_f fst]; [reflexivity|].
  rewrite Znth_app1 by lia. rewrite <- app_assoc.
  replace (Znth i' O0) with (Znth i w) by (rewrite <- (Z.add_0_r i), <- (Z.add_0_r i'); apply Hw; lia).
  apply IH; [lia|lia|]. intros j Hj.
  replace (i + 1 + j) with (i + (j + 1)) by lia. replace (i' + 1 + j) with (i' + (j + 1)) by lia.
  apply Hw. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The end of a MATCH pass                                                                        *)

Lemma mstate_z s k : i_length s - k = 0 -> mstate s k = set_i_mode (set_i_length s (i_length s - k)) LEN.
Proof. intros E. unfold mstate. rewrite E. reflexivity. Qed.

Lemma mstate_nz s k : i_length s - k <> 0 -> mstate s k = set_i_length s (i_length s - k).
Proof. intros E. unfold mstate. destruct (Z.eqb_spec (i_length s - k) 0); [lia|reflexivity]. Qed.

Lemma mstate_flags s k : i_flags (mstate s k) = i_flags s.
Proof. unfold mstate. destruct (_ =? 0); reflexivity. Qed.

Lemma mstate_check s k : i_check (mstate s k) = i_check s.
Proof. unfold mstate. destruct (_ =? 0); reflexivity. Qed.

(* the pass copied k >= 1 bytes, the bytes of the abstract copy: k abstract steps, and the relation holds *)
Lemma match_fin flush src P0 O0 m a ow' k :
  rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = MATCH ->
  1 <= k <= m_left m -> k <= i_length (m_s m) -> i_offset (a_s a) <= Zlength (a_O a) ->
  O0 ++ ow' = fst (copy_f (Z.to_nat k) [] (SOut (Zlength (a_O a) - i_offset (a_s a))) (a_O a)) ->
  dgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (IBrk (if i_length (m_s m) - k =? 0
           then set_mode (upd_s (set_m_ow m ow') (fun s => set_i_length s (i_length (m_s m) - k))) LEN
           else upd_s (set_m_ow m ow') (fun s => set_i_length s (i_length (m_s m) - k)))).
Proof.
  intros Rl Aw L Hm Hk Hl Off Eo.
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (Ha: a_mode a = MATCH) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  pose proof (rl_s _ _ _ _ _ Rl NB) as Se.
  assert (Hlen: i_length (m_s m) = i_length (a_s a)) by (apply (se_length _ _ Se); change (len_live (a_mode a)); rewrite Ha; unfold len_live; auto).
  assert (L1: 1 <= i_length (a_s a)) by exact (md_match _ (aw_md _ _ Aw) Ha).
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  pose proof (rl_O _ _ _ _ _ Rl) as RO.
  assert (Lw: Zlength ow' = Zlength (m_ow m) + k).
  { apply (f_equal (@Zlength Z)) in Eo. rewrite copy_f_length, Zlength_app, RO, Zlength_app in Eo.
    rewrite Z2Nat.id in Eo by lia. lia. }
  assert (Q: a_q a <= 8 * (P0 + Zlength (m_inp m))).
  { rewrite (rl_q _ _ _ _ _ Rl NB). apply (mq_le src), (rl_bb _ _ _ _ _ Rl). }
  assert (A := amatch_steps src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (Z.to_nat k) (a_s a) (a_q a)
                 (a_O a) Ha L1 ltac:(lia) Off Q
                 ltac:(rewrite RO, Zlength_app; unfold m_left in Hk; lia)).
  rewrite Z2Nat.id in A by lia. rewrite <- Eo in A.
  rewrite Hlen.
  set (a' := AS (mstate (a_s a) k) (a_q a) (O0 ++ ow')) in A.
  assert (Ea: a = AS (a_s a) (a_q a) (a_O a)) by (destruct a; reflexivity).
  rewrite <- Ea in A.
  exists a'. split; [exact A|].
  destruct (Z.eqb_spec (i_length (a_s a) - k) 0) as [E|E].
  - split; [|cbn; intros Hx; rewrite L in Hx; discriminate].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    + rewrite Hm. unfold decode_mode; auto 7.
    + apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
    + unfold m_left in Hk. lia.
    + subst a'. cbn. rewrite mstate_z by exact E. reflexivity.
    + unfold decode_mode; auto.
    + exact (rl_q _ _ _ _ _ Rl NB).
    + subst a'. cbn. rewrite mstate_z by exact E. rewrite <- Hlen.
      apply seq_mode; [apply seq_length; exact Se| | |]; intros P; exfalso; dmd.
    + subst a'. cbn. apply mstate_flags.
    + subst a'. cbn. apply mstate_check.
    + unfold win_eq; cbn; auto.
    + exact (rl_head _ _ _ _ _ Rl).
  - split; [|cbn; intros Hx; rewrite L in Hx; discriminate].
    eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
    + rewrite Hm. unfold decode_mode; auto 7.
    + apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
    + unfold m_left in Hk. lia.
    + subst a'. cbn. rewrite mstate_nz by exact E. exact (rl_mode _ _ _ _ _ Rl).
    + left. change (decode_mode (m_mode m)). rewrite Hm. unfold decode_mode; auto 7.
    + exact (rl_q _ _ _ _ _ Rl NB).
    + subst a'. cbn. rewrite mstate_nz by exact E. rewrite <- Hlen. apply seq_length; exact Se.
    + subst a'. cbn. apply mstate_flags.
    + subst a'. cbn. apply mstate_check.
    + unfold win_eq; cbn; auto.
    + exact (rl_head _ _ _ _ _ Rl).
Qed.

(* the end of a MATCH pass by match_fin, leaving the equality of the copies *)
Ltac match_fin_tac :=
  match goal with
  | Rl: rel ?src ?P0 ?O0 ?m ?a, Aw: awf _ _, L: m_leave _ = 0, Hm: m_mode _ = MATCH, NFa: _ <= Zlength (a_O _)
    |- context [copy_bytes ?w ?sr ?k ?ow] =>
    let Ec := fresh "Ec" in
    assert (Ec: O0 ++ fst (copy_bytes w sr k ow) =
                fst (copy_f (Z.to_nat k) [] (SOut (Zlength (a_O a) - i_offset (a_s a))) (a_O a)));
    [| let ow' := fresh "ow'" in let x := fresh "x" in
       destruct (copy_bytes w sr k ow) as [ow' x]; cbn [fst] in Ec;
       apply match_fin; [exact Rl|exact Aw|exact L|exact Hm|lia|lia|exact NFa|exact Ec]]
  end.

Lemma sd_match : kit_stmt -> awf_stmt -> sim_ok (fun md => md = MATCH).
Proof.
  intros KIT AW. apply sim_ok_dgoal. intros flush src P0 O0 m a Rl Aw L Hm.
  rewrite stepf2_MATCH by exact Hm. unfold c_MATCH.
  assert (NB: m_mode m <> BAD) by (rewrite Hm; discriminate).
  assert (Ha: a_mode a = MATCH) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Hm).
  pose proof (rl_s _ _ _ _ _ Rl NB) as Se.
  pose proof (rl_aout _ _ _ _ _ Rl) as Ao.
  pose proof (rl_O _ _ _ _ _ Rl) as RO.
  pose proof (Zlength_nonneg (m_ow m)) as Zow.
  assert (Hout: m_out m = m_aout m).
  { apply (proj2 (proj2 (rl_out _ _ _ _ _ Rl))). right; left. rewrite Hm. unfold data_mode, decode_mode; auto 20. }
  assert (Q: a_q a <= 8 * (P0 + Zlength (m_inp m))).
  { rewrite (rl_q _ _ _ _ _ Rl NB). apply (mq_le src), (rl_bb _ _ _ _ _ Rl). }
  destruct (Z.eqb_spec (m_left m) 0) as [L0|L0].
  - (* no output space: the call stops before the next byte *)
    apply dgoal_here.
    + eapply rel_dec_next with (m := m) (a := a); try exact Rl; cbn; try reflexivity.
      * rewrite Hm. unfold decode_mode; auto 7.
      * apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
      * lia.
      * exact (rl_mode _ _ _ _ _ Rl).
      * left. change (decode_mode (m_mode m)). rewrite Hm. unfold decode_mode; auto 7.
      * exact (rl_q _ _ _ _ _ Rl NB).
      * exact RO.
      * exact Se.
      * unfold win_eq; cbn; auto.
      * exact (rl_head _ _ _ _ _ Rl).
    + intros _. destruct (Zlength (a_O a) <? i_offset (a_s a)) eqn:Ef; eapply stop_full;
        try (rewrite astep_MATCH by exact Ha; unfold a_MATCH; rewrite Ef; reflexivity).
      all: first [rewrite RO, Zlength_app; unfold m_left in L0; lia
                 |cbn; apply (rl_ret _ _ _ _ _ Rl NB); rewrite Hm; discriminate].
  - assert (C0: u32 (m_out m - m_left m) = Zlength (m_ow m)).
    { unfold m_left. rewrite Hout. unfold u32. change Int.max_unsigned with 4294967295 in Ao. change (2 ^ 32) with 4294967296.
      rewrite Z.mod_small; lia. }
    pose proof (Zlength_nonneg O0) as ZO0.
    rewrite C0.
    assert (Hoff: i_offset (m_s m) = i_offset (a_s a))
      by (apply (se_offset _ _ Se); change (off_live (a_mode a)); rewrite Ha; unfold off_live; auto).
    assert (Hlen: i_length (m_s m) = i_length (a_s a))
      by (apply (se_length _ _ Se); change (len_live (a_mode a)); rewrite Ha; unfold len_live; auto).
    assert (L1: 1 <= i_length (a_s a)) by exact (md_match _ (aw_md _ _ Aw) Ha).
    assert (O32: i_offset (a_s a) <= 32768) by exact (aw_offset _ _ Aw Ha).
    assert (Hsane: i_sane (m_s m) = 1) by (rewrite (se_sane _ _ Se); exact (sw_sane _ (aw_swf _ _ Aw))).
    assert (Hwin: swin_ok (m_s m) O0).
    { apply (rl_win _ _ _ _ _ Rl). unfold win_mode. right. split; [rewrite Hm; unfold data_mode, decode_mode; auto 20|].
      rewrite Hm. discriminate. }
    assert (Lp: 1 <= m_left m) by (unfold m_left in *; lia).
    rewrite Hsane, Hoff. change (negb (1 =? 0)) with true. rewrite andb_true_r.
    destruct (Z.ltb_spec (Zlength (m_ow m)) (i_offset (a_s a))) as [Lo|Lo].
    + destruct (Z.ltb_spec (i_whave (m_s m)) (i_offset (a_s a) - Zlength (m_ow m))) as [Far|NFar].
      * (* a distance past the start of the whole output: both machines go to BAD *)
        assert (Fa: Zlength (a_O a) < i_offset (a_s a)).
        { rewrite RO, Zlength_app.
          destruct Hwin as [(W1 & W2 & W3)|(W1 & W2 & W3 & W4)]; [subst O0; rewrite Zlength_nil; lia|].
          rewrite W3 in Far. lia. }
        set (a1 := AS (set_i_mode (a_s a) BAD) (a_q a) (a_O a)).
        assert (S1: astep lenfix_list distfix_list src a = AGo (a_q a) true a1).
        { rewrite astep_MATCH by exact Ha. unfold a_MATCH.
          destruct (Z.ltb_spec (Zlength (a_O a)) (i_offset (a_s a))); [reflexivity|lia]. }
        eapply dgoal_write; [exact S1|exact Q|rewrite RO, Zlength_app; unfold m_left in Lp; lia|].
        apply dgoal_here.
        { eapply rel_dec_bad; try exact Rl; cbn; try reflexivity.
          - apply bitbuf_ext with m; try reflexivity. exact (rl_bb _ _ _ _ _ Rl).
          - exact (rl_head _ _ _ _ _ Rl). }
        cbn. intros Hx. rewrite L in Hx. discriminate.
      * (* a copy from the window: the bytes of O0 from |O0 ++ ow| - offset on *)
        destruct Hwin as [(W1 & W2 & W3)|(W1 & W2 & W3 & W4 & W5 & W6 & W7)]; [lia|].
        assert (NFa: i_offset (a_s a) <= Zlength (a_O a)) by (rewrite RO, Zlength_app; lia).
        destruct (Z.ltb_spec (i_wnext (m_s m)) (i_offset (a_s a) - Zlength (m_ow m))) as [Wr|Wr];
          cbv beta iota; match_fin_tac.
        -- unfold copy_bytes. rewrite RO. apply copy_win_app.
           ++ rewrite Zlength_app. lia.
           ++ rewrite Zlength_app, Z2Nat.id by lia. lia.
           ++ intros j Hj. rewrite Z2Nat.id in Hj by lia. rewrite Zlength_app.
              assert (Hw: i_whave (m_s m) = 32768)
                by (destruct (Z_lt_le_dec (i_whave (m_s m)) 32768) as [H|H]; [specialize (W5 H)|]; lia).
              replace (Zlength O0 + Zlength (m_ow m) - i_offset (a_s a) + j)
                with (Zlength O0 - (i_offset (a_s a) - Zlength (m_ow m) - j)) by lia.
              rewrite <- W7 by lia. unfold swin_at.
              destruct (Z.leb_spec (i_offset (a_s a) - Zlength (m_ow m) - j) (i_wnext (m_s m))); [lia|].
              f_equal. lia.
        -- unfold copy_bytes. rewrite RO. apply copy_win_app.
           ++ rewrite Zlength_app. lia.
           ++ rewrite Zlength_app, Z2Nat.id by lia. lia.
           ++ intros j Hj. rewrite Z2Nat.id in Hj by lia. rewrite Zlength_app.
              replace (Zlength O0 + Zlength (m_ow m) - i_offset (a_s a) + j)
                with (Zlength O0 - (i_offset (a_s a) - Zlength (m_ow m) - j)) by lia.
              rewrite <- W7 by lia. unfold swin_at.
              destruct (Z.leb_spec (i_offset (a_s a) - Zlength (m_ow m) - j) (i_wnext (m_s m))); [|lia].
              f_equal. lia.
    + (* a copy from the output of this call *)
      assert (NFa: i_offset (a_s a) <= Zlength (a_O a)) by (rewrite RO, Zlength_app; lia).
      match_fin_tac.
      unfold copy_bytes. rewrite RO.
      replace (Zlength (m_ow m) - i_offset (a_s a))
        with (Zlength (O0 ++ m_ow m) - i_offset (a_s a) - Zlength O0) by (rewrite Zlength_app; lia).
      apply copy_out_app. rewrite Zlength_app. lia.
Qed.

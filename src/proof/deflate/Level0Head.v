(** * The output of deflate at level 0: [l0_head_stmt] (see Level0Stmts.v) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Stmts.
Require Import Zlib.proof.deflate.LTHdrStages Zlib.proof.deflate.LTApiEntry.
Import ListNotations.
Local Open Scope Z_scope.

(** deflate()'s entry stage with Z_FINISH, nothing pending, room in the output and a status other than
    FINISH only records the flush in [last_flush] (when no input is offered: the previous flush -2 ranks
    below Z_FINISH, and Z_FINISH is never refused). *)
Lemma l0_entry : forall s z,
  d_status s <> FINISH_STATE -> d_pending s = 0 -> 0 < z_avail_out z -> d_last_flush s = -2 ->
  c_deflate_entry s z Z_FINISH = Some (set_d_last_flush s Z_FINISH, z, None).
Proof.
  intros s z Hst P0 Hav Hlf. unfold c_deflate_entry.
  apply Z.eqb_neq in Hst. rewrite Hst. cbn [andb].
  replace (z_avail_out z =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (d_pending (set_d_last_flush s Z_FINISH)) with (d_pending s). rewrite P0. cbn [Z.eqb negb].
  rewrite Hlf. change (d_status (set_d_last_flush s Z_FINISH)) with (d_status s).
  destruct (z_avail_in z =? 0) eqn:Ein.
  - cbn. rewrite Hst. reflexivity.
  - cbn. rewrite Hst. reflexivity.
Qed.

(** The end of the header stages started at the beginning of the header [H] ([k = 0]) with more room in
    the output than [H] needs: the stages cannot stop with a full output, so the header is done, the state
    is BUSY with nothing pending and the stream got exactly the bytes of [H]. *)
Lemma l0_post : forall s z H s' z' r,
  hdr_post hinv s z H 0 s' z' r -> Zlength H < z_avail_out z ->
  r = None /\ core_eq s s' /\ outok s' /\ d_wrap s' = d_wrap s /\ d_bi_valid s' = d_bi_valid s /\
  d_status s' = BUSY_STATE /\ d_pending s' = 0 /\ d_po s' = 0 /\ zout_step z z' H (z_adler z').
Proof.
  intros s z H s' z' r [Hc [Ho [Hw [Hg [Hbv [x [k' [Hk [Hx [Hz Hr]]]]]]]]]] Hlt.
  destruct r as [c|].
  - exfalso. destruct Hr as [_ [Hav _]].
    assert (Lx : Zlength x <= k').
    { pose proof (f_equal (@Zlength Z) Hx) as L.
      rewrite Zlength_app, Zlength_sublist in L by lia. pose proof (Zlength_nonneg (pend s')). lia. }
    destruct Hz as [_ [_ [_ [_ [_ [Ha _]]]]]]. lia.
  - destruct Hr as [Ek [Hst [P0 [Po _]]]].
    assert (Hpe : pend s' = []) by (unfold pend; rewrite P0, Z.add_0_r; apply sublist_nil).
    rewrite Hpe, app_nil_r, Ek, sublist_same in Hx by lia. subst x.
    split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(** The counters of the stream after the header: total_out does not wrap (it stays below 2^41). *)
Lemma l0_zout : forall z z' H a,
  zout_step z z' H a -> 0 <= z_total_out z <= 1099511627776 -> Zlength H <= 10 ->
  z_out z' = z_out z ++ H /\ z_in z' = z_in z /\ z_next_in z' = z_next_in z /\
  z_avail_in z' = z_avail_in z /\ z_total_in z' = z_total_in z /\ z_msg z' = z_msg z /\
  z_avail_out z' = z_avail_out z - Zlength H /\ z_total_out z' = z_total_out z + Zlength H.
Proof.
  intros z z' H a [Ei [En [Ea [Et [Eo [Eao [Eto [_ Em]]]]]]]] Ht LH.
  pose proof (Zlength_nonneg H).
  repeat split; try assumption.
  rewrite Eto. unfold u64. apply Z.mod_small. lia.
Qed.

Theorem l0_head : l0_head_stmt.
Proof.
  intros s z Hp Ho P0 Po Hbv Hsn Hss Hgz Hlf Hw Hst Hav Ht.
  assert (Hhl : 0 <= hdr_len (d_wrap s) <= 10)
    by (unfold hdr_len; destruct (d_wrap s =? 0); [lia|destruct (d_wrap s =? 1); lia]).
  assert (Hnf : d_status s <> FINISH_STATE)
    by (rewrite Hst; destruct (d_wrap s =? 2); discriminate).
  rewrite (l0_entry s z Hnf P0 ltac:(lia) Hlf). cbn [then_stage bind].
  set (s1 := set_d_last_flush s Z_FINISH).
  assert (Hc1 : core_eq s s1) by apply ent_core_eq_lf.
  rewrite hdr_stages_eq.
  destruct (Z.eq_dec (d_wrap s) 2) as [W2|W2].
  - (* gzip, no user header: 10 bytes *)
    rewrite W2 in Hst. cbn [Z.eqb Pos.eqb] in Hst.
    rewrite zlib_id by (change (d_status s1) with (d_status s); rewrite Hst; discriminate).
    cbn [then_stage bind].
    destruct (gzip_stage s1 z Hp Ho P0 Hsn Hbv ltac:(lia) Ht Hst W2
                ltac:(intros h E; change (d_gzhead s1) with (d_gzhead s) in E; congruence))
      as [s' [z' [r [E [[_ Hge]|[Es Hpost]]]]]].
    + exfalso. destruct Hge as [_ [_ [h [xfl [Eh [_ [_ [_ [Hm _]]]]]]]]].
      destruct Hm as [[_ [_ [_ [_ [_ [_ [_ [Hg0 _]]]]]]]] _].
      change (d_gzhead s1) with (d_gzhead s) in Hg0. congruence.
    + change (d_gzhead s1) with (d_gzhead s) in Hpost. rewrite Hgz in Hpost.
      assert (LH : Zlength (gz_hdr_bytes None (xfl_byte s1)) = 10) by reflexivity.
      assert (Hhl2 : hdr_len (d_wrap s) = 10) by (rewrite W2; reflexivity).
      destruct (l0_post _ _ _ _ _ _ Hpost ltac:(lia))
        as [-> [Hc [Ho' [Hw' [Hbv' [Hs' [P0' [Po' Hz]]]]]]]].
      rewrite E. cbn [then_stage bind].
      destruct (busy_rest s' z' Hs') as [_ B]. rewrite B.
      destruct (l0_zout _ _ _ _ Hz Ht ltac:(lia)) as [Eo [Ei [En [Ea [Eti [Em [Eao Eto]]]]]]].
      exists s', z', (gz_hdr_bytes None (xfl_byte s1)).
      split; [reflexivity|].
      split; [eapply ent_core_eq_trans; [exact Hc1|exact Hc]|].
      split; [exact Ho'|]. split; [exact P0'|]. split; [exact Po'|].
      split; [rewrite Hbv'; exact Hbv|]. split; [exact Hs'|]. split; [exact Hw'|].
      rewrite LH, Hhl2. repeat split; assumption.
  - (* raw (no header) or zlib (2 bytes, no dictionary) *)
    assert (W2' : (d_wrap s =? 2) = false) by (apply Z.eqb_neq; exact W2).
    rewrite W2' in Hst.
    destruct (zlib_stage s1 z Hp Ho P0 Hsn Hbv ltac:(lia) Ht Hst ltac:(change (d_wrap s1) with (d_wrap s); lia))
      as [s' [z' [r [E [Es Hpost]]]]].
    set (H := hdr_bytes s1 (z_adler z)) in Hpost.
    assert (LH : Zlength H = hdr_len (d_wrap s)).
    { unfold H, hdr_bytes, zlib_hdr_bytes. change (d_wrap s1) with (d_wrap s).
      change (d_strstart s1) with (d_strstart s). rewrite Hss.
      destruct (Z.eq_dec (d_wrap s) 0) as [W0|W0].
      - rewrite W0. reflexivity.
      - replace (d_wrap s) with 1 by lia. reflexivity. }
    destruct (l0_post _ _ _ _ _ _ Hpost ltac:(lia))
      as [-> [Hc [Ho' [Hw' [Hbv' [Hs' [P0' [Po' Hz]]]]]]]].
    rewrite E. cbn [then_stage bind].
    destruct (busy_rest s' z' Hs') as [B _]. rewrite B.
    destruct (l0_zout _ _ _ _ Hz Ht ltac:(lia)) as [Eo [Ei [En [Ea [Eti [Em [Eao Eto]]]]]]].
    exists s', z', H.
    split; [reflexivity|].
    split; [eapply ent_core_eq_trans; [exact Hc1|exact Hc]|].
    split; [exact Ho'|]. split; [exact P0'|]. split; [exact Po'|].
    split; [rewrite Hbv'; exact Hbv|]. split; [exact Hs'|]. split; [exact Hw'|].
    rewrite LH in *. repeat split; assumption.
Qed.

(** * deflateSetDictionary, fragment S_loop (DictKit.v): while (s->lookahead >= MIN_MATCH) { ...; fill_window(s); },
    given the triple of the inner do-while loop (DictInner.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.DictKit.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The two fields the loop writes (strstart, lookahead), and the rest of the stream *)
Definition sl_rest (s : dstate) (z : strm) (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    : mpred :=
  (trees_at (d_trm s) (p_s p) (p_pbuf p) (p_strm p) gv * win_at s p * hash_at s p *
   @field_at DCS.CS Ews t_ds (DOT _block_start) (vl (d_block_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_length) (vi (d_match_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_match) (vi (d_prev_match s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_available) (vi (d_match_available s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _match_start) (vi (d_match_start s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _prev_length) (vi (d_prev_length s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _insert) (vi (d_insert s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _slid) (vi (d_slid s)) (p_s p) *
   cfg_at s p * stat_at s p * strm_in_at z (p_s p) (p_strm p) pin msgv gv * in_obj ish z pin)%logic.

Definition sl_pure (s : dstate) (z : strm) (ish : share) (msgv : val) : Prop :=
  strm_ranges z /\ msg_ok (z_msg z) msgv /\ readable_share ish /\ dstate_ranges s.

Lemma sl_open s z p pin ish msgv gv :
  dfull_in s z p pin ish msgv gv |--
  !! sl_pure s z ish msgv &&
  (@field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
   @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
   sl_rest s z p pin ish msgv gv).
Proof.
  unfold dfull_in, dstate_at, match_at, sl_rest, sl_pure. Intros.
  apply andp_right; [apply prop_right; tauto|]. cancel.
Qed.

Lemma sl_ranges s a b : dstate_ranges s -> u32_ok a -> u32_ok b ->
  dstate_ranges (set_d_lookahead (set_d_strstart s a) b).
Proof. unfold dstate_ranges. intros. tauto. Qed.

Lemma sl_close s z p pin ish msgv gv a b :
  sl_pure s z ish msgv -> u32_ok a -> u32_ok b ->
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi a) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi b) (p_s p) *
  sl_rest s z p pin ish msgv gv |--
  dfull_in (set_d_lookahead (set_d_strstart s a) b) z p pin ish msgv gv.
Proof.
  intros (H1 & H2 & H3 & H4) Ha Hb.
  pose proof (sl_ranges s a b H4 Ha Hb) as H5.
  unfold dfull_in, dstate_at. apply andp_right; [apply prop_right; tauto|]. rewrite (prop_true_andp _ _ H5).
  unfold match_at, sl_rest. cancel. apply derives_refl.
Qed.

Lemma sl_close' s z p pin ish msgv gv :
  sl_pure s z ish msgv ->
  @field_at DCS.CS Ews t_ds (DOT _strstart) (vi (d_strstart s)) (p_s p) *
  @field_at DCS.CS Ews t_ds (DOT _lookahead) (vi (d_lookahead s)) (p_s p) *
  sl_rest s z p pin ish msgv gv |-- dfull_in s z p pin ish msgv gv.
Proof.
  intros (H1 & H2 & H3 & H4).
  unfold dfull_in, dstate_at, match_at, sl_rest. entailer!.
Qed.

Lemma sl_u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296). rep_lia. Qed.

Lemma sd_insert_runs_str a r : runs sd_insert_body a r -> u32_ok (snd r).
Proof.
  induction 1 as [a r H|a a' r H _ IH]; [|exact IH].
  destruct a as [[s str] n]. unfold sd_insert_body in H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  destruct (_ =? 0); inversion H; subst. apply sl_u32_range.
Qed.

Lemma sd_insert_str s str n s1 str' : loop FUEL sd_insert_body (s, str, n) = Some (s1, str') -> u32_ok str'.
Proof. intros H. apply loop_runs in H. exact (sd_insert_runs_str _ _ H). Qed.

Lemma runs_inv'' {A B} (body : A -> option (A + B)) a r :
  runs body a r -> exists res, body a = Some res /\
    match res with inl a' => runs body a' r | inr r' => r' = r end.
Proof.
  intros H. destruct (runs_inv _ _ _ H) as [E|[a' [E R]]]; eexists; split; eauto; reflexivity.
Qed.

(** One iteration of the model, when the test passes. *)
Lemma sd_body_step t zt r : runs sd_body (t, zt) r -> d_lookahead t >= MIN_MATCH ->
  exists s1 str' s2 z2,
    loop FUEL sd_insert_body (t, d_strstart t, u32 (d_lookahead t - (MIN_MATCH - 1))) = Some (s1, str') /\
    c_fill_window (set_d_lookahead (set_d_strstart s1 str') (MIN_MATCH - 1)) zt = Some (s2, z2) /\
    runs sd_body (s2, z2) r.
Proof.
  intros H Hl. destruct (runs_inv'' _ _ _ H) as [res [E R]].
  unfold sd_body in E. rewrite (proj2 (Z.geb_le _ _)) in E by lia.
  inv_bind E. destruct x as [s1 str']. inv_bind E. destruct x as [s2 z2]. inversion E; subst.
  exists s1, str', s2, z2. auto.
Qed.

Lemma sd_body_exit t zt r : runs sd_body (t, zt) r -> d_lookahead t < MIN_MATCH -> r = (t, zt).
Proof.
  intros H Hl. destruct (runs_inv'' _ _ _ H) as [res [E R]].
  unfold sd_body in E. destruct (d_lookahead t >=? MIN_MATCH) eqn:G; [apply Z.geb_le in G; lia|].
  inversion E; subst. auto.
Qed.

Lemma sd_loop_of : sd_inner_triple -> sd_loop_triple.
Proof.
  intros HI. unfold sd_loop_triple. intros.
  apply loop_runs in H.
  unfold S_loop. show_sd_stmt. abbreviate_semax.
  forward_loop (EX t : dstate, EX zt : strm, EX msgv1 : val,
      PROP (runs sd_body (t, zt) (s', z'))
      LOCAL (temp _s (p_s p); temp _strm strmp; temp _wrap (vi wrap); temp _avail (vi avail);
             temp _next next; gvars gv)
      SEP (dfull_in t zt p pin ish msgv1 gv; deflate_globals gv; Fr))
    break: (PROP () LOCAL (temp _s (p_s p); temp _strm strmp; temp _wrap (vi wrap); temp _avail (vi avail);
                    temp _next next; gvars gv)
       SEP (EX msgv' : val, dfull_in s' z' p pin ish msgv' gv; deflate_globals gv; Fr)).
  { Exists s z msgv. entailer!. }
  Intros t zt msgv1. rename H0 into Hrun.
  sep_apply sl_open. Intros. rename H0 into Hp.
  pose proof Hp as (_ & _ & _ & Hr). unfold dstate_ranges, u32_ok in Hr.
  forward.
  forward_if.
  2: { assert (Hl : d_lookahead t < MIN_MATCH) by (unfold MIN_MATCH; lia).
    pose proof (sd_body_exit _ _ _ Hrun Hl) as E. inversion E; subst s' z'.
    forward. sep_apply (sl_close' t zt p pin ish msgv1 gv Hp). Exists msgv1. entailer!. }
  assert (Hl : d_lookahead t >= MIN_MATCH) by (unfold MIN_MATCH; lia).
  destruct (sd_body_step _ _ _ Hrun Hl) as (s1 & str' & s2 & z2 & Hins & Hfw & Hrun2).
  forward. forward. forward.
  assert (En : u32 (d_lookahead t - (MIN_MATCH - 1)) = d_lookahead t - 2)
    by (unfold u32, MIN_MATCH; apply Z.mod_small; rep_lia).
  rewrite En in Hins. change (MIN_MATCH - 1) with 2 in Hfw.
  sep_apply (sl_close' t zt p pin ish msgv1 gv Hp).
  apply seq_assoc.
  eapply semax_seq'.
  { eapply semax_pre; [| exact (HI Espec p pin ish msgv1 gv t zt (d_strstart t) (d_lookahead t - 2) s1 str'
                                  strmp next wrap avail (deflate_globals gv * Fr)%logic ltac:(rep_lia) ltac:(rep_lia) Hins)].
    rewrite !sub_repr. entailer!. }
  abbreviate_semax.
  pose proof (sd_insert_str _ _ _ _ _ Hins) as Hstr.
  Intros. sep_apply sl_open. Intros. rename H1 into Hp1.
  forward. forward.
  change (Int.sub (Int.repr 3) (Int.repr 1)) with (Int.repr 2).
  sep_apply (sl_close s1 zt p pin ish msgv1 gv str' 2 Hp1 Hstr ltac:(unfold u32_ok; rep_lia)).
  forward_call (set_d_lookahead (set_d_strstart s1 str') 2, zt, p, pin, ish, msgv1, (s2, z2), gv).
  Intros msgv2. Exists s2 z2 msgv2. entailer!. apply derives_refl.
Qed.

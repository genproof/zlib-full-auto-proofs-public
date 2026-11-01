(** * str_stage under [0 <= base]: the NAME_STATE / COMMENT_STATE string loop of deflate().

    [str_stage] of LTHdrStr.v lacks [0 <= base] and is false without it (VST sublist clamps a negative lower
    bound).  [str_stage_nn] is the same statement with [0 <= base] after [cstr_ok o].
    Proof: [loop_measure] with the invariant [sP] (hmid at base + gzindex, adler = hadler at
    base + gzindex - pending + beg), measure |l| - gzindex; [str_put] the byte step, [str_body_ok] one iteration. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTHdrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma hmid_pbs_pos : forall s0 z0 H k0 s z kk, hmid s0 z0 H k0 s z kk -> 0 < d_pending_buf_size s.
Proof.
  intros s0 z0 H k0 s z kk [[_ [Hp _]] _].
  destruct Hp as [_ [_ [_ [Hb [_ [_ [_ [HL [Hpb _]]]]]]]]].
  rewrite Hpb, HL. assert (0 < 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Section StrLoop.
Variables (s0 : dstate) (z0 : strm) (H : list Z) (k0 : Z) (h : gzh) (l l0 : list Z) (base st w : Z)
          (gh : option gzh).
Hypothesis HB : bytes H.
Hypothesis Hl : l = l0 ++ [0].
Hypothesis Hl0len : Zlength l0 <= 4096.
Hypothesis Hl0 : Forall (fun b => 0 < b < 256) l0.
Hypothesis Hlen : base + Zlength l <= Zlength H.
Hypothesis Hsub : sublist base (base + Zlength l) H = l.
Hypothesis Hbase : 0 <= base.

Definition sP (a : dstate * strm * Z) : Prop :=
  let '(s, z, beg) := a in
  hmid s0 z0 H k0 s z (base + d_gzindex s) /\ d_status s = st /\ d_gzhead s = gh /\ d_wrap s = w /\
  0 <= d_gzindex s < Zlength l /\ 0 <= beg <= d_pending s /\
  z_adler z = hadler h H (base + d_gzindex s - d_pending s + beg).

Definition sQ (b : (dstate * strm * Z) + (dstate * strm)) : Prop :=
  match b with
  | inl (s, z, beg) =>
    hmid s0 z0 H k0 s z (base + Zlength l) /\ d_status s = st /\ d_gzhead s = gh /\ d_wrap s = w /\
    0 <= beg <= d_pending s /\ z_adler z = hadler h H (base + Zlength l - d_pending s + beg)
  | inr (s, z) =>
    d_status s = st /\ d_gzhead s = gh /\ d_wrap s = w /\ 0 <= d_gzindex s < Zlength l /\
    hret s0 z0 H k0 s z (base + d_gzindex s) /\ z_adler z = hadler h H (base + d_gzindex s)
  end.

Definition sM (a : dstate * strm * Z) : Z := let '(s, _, _) := a in Zlength l - d_gzindex s.

(** The byte part of one iteration, from a state with room in pending_buf. *)
Lemma str_put : forall s z beg,
  sP (s, z, beg) -> d_pending s < d_pending_buf_size s ->
  exists r : (dstate * strm * Z) + ((dstate * strm * Z) + (dstate * strm)), (let* v := rd l (d_gzindex s) in
             let s := set_d_gzindex s (u64 (d_gzindex s + 1)) in
             let* s := c_dput_byte s v in
             if v =? 0 then Some (inr (inl (s, z, beg))) else Some (inl (s, z, beg))) = Some r /\
    match r with inl a' => sP a' /\ sM a' < sM (s, z, beg) | inr b => sQ b end.
Proof.
  intros s z beg [Hm [Hst [Hgh [Hw [Hg [Hbeg Ha]]]]]] Hlt.
  assert (Ll : Zlength l = Zlength l0 + 1) by (rewrite Hl, Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Rd : rd l (d_gzindex s) = Some (Znth (d_gzindex s) l)).
  { unfold rd, in_range. replace ((0 <=? d_gzindex s) && (d_gzindex s <? Zlength l)) with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. }
  rewrite Rd. cbn [bind].
  set (g := d_gzindex s) in *. set (v := Znth g l).
  assert (Hv : 0 <= v < 256 /\ (v = 0 <-> g = Zlength l0)).
  { subst v. rewrite Hl. destruct (Z.eq_dec g (Zlength l0)) as [E|E].
    - rewrite app_Znth2 by lia. rewrite E, Z.sub_diag. cbn. split; [lia|tauto].
    - rewrite app_Znth1 by lia. assert (F := proj1 (Forall_forall _ l0) Hl0 (Znth g l0) ltac:(apply Znth_In; lia)). cbn beta in F.
      split; [lia|]. split; intro; lia. }
  assert (HZ : Znth (base + g) H = u8 v).
  { unfold u8. rewrite Z.mod_small by lia. subst v. rewrite <- Hsub.
    rewrite Znth_sublist by lia. f_equal; lia. }
  assert (U : u64 (g + 1) = g + 1) by (unfold u64; apply Z.mod_small; lia).
  assert (Hm1 := hmid_gzindex _ _ _ _ _ _ _ (u64 (g + 1)) Hm).
  destruct (dput_byte_mid _ _ _ _ _ _ _ v Hm1 Hlt ltac:(lia) HZ) as [o [Ep [Hm2 Hp2]]].
  rewrite Ep. cbn [bind].
  change (d_pending (set_d_out (set_d_gzindex s (u64 (g + 1))) o) = d_pending s + 1) in Hp2.
  change (d_gzindex (set_d_out (set_d_gzindex s (u64 (g + 1))) o)) with (u64 (g + 1)).
  destruct (v =? 0) eqn:Ev.
  - apply Z.eqb_eq in Ev. assert (Eg : g = Zlength l0) by (apply Hv; exact Ev).
    eexists. split; [reflexivity|]. cbn [sQ].
    replace (base + Zlength l) with (base + g + 1) by lia.
    split; [exact Hm2|]. split; [exact Hst|]. split; [exact Hgh|]. split; [exact Hw|].
    rewrite Hp2. split; [lia|]. rewrite Ha. f_equal. lia.
  - apply Z.eqb_neq in Ev. assert (Eg : g <> Zlength l0) by (intro E; apply Ev, Hv, E).
    eexists. split; [reflexivity|]. cbn [sP sM].
    change (d_gzindex (set_d_out (set_d_gzindex s (u64 (g + 1))) o)) with (u64 (g + 1)). rewrite U. rewrite U in Hm2, Hp2.
    split; [|lia].
    replace (base + (g + 1)) with (base + g + 1) by lia.
    split; [exact Hm2|]. split; [exact Hst|]. split; [exact Hgh|]. split; [exact Hw|].
    rewrite Hp2. split; [lia|]. split; [lia|]. rewrite Ha. f_equal. lia.
Qed.

Lemma str_body_ok : forall a, sP a -> 0 <= sM a /\ exists r, str_body h l a = Some r /\
  match r with inl a' => sP a' /\ sM a' < sM a | inr b => sQ b end.
Proof.
  intros [[s z] beg] HP.
  split; [destruct HP as [_ [_ [_ [_ [Hg _]]]]]; cbn [sM]; lia|].
  pose proof HP as [Hm [Hst [Hgh [Hw [Hg [Hbeg Ha]]]]]].
  destruct (hmid_buf_len _ _ _ _ _ _ _ Hm) as [_ [_ [_ Hpb]]].
  unfold str_body. destruct (d_pending s =? d_pending_buf_size s) eqn:EP.
  - apply Z.eqb_eq in EP.
    rewrite (hcrc_update_mid _ _ _ _ _ _ _ h beg Hm HB Hbeg Ha). cbn [bind].
    destruct (flush_mid _ _ _ _ _ _ _ (hmid_adler _ _ _ _ _ _ _ (hadler h H (base + d_gzindex s)) Hm))
      as [s' [z' [Ef [E1 [E2 [E3 [E4 Hc]]]]]]].
    rewrite Ef. cbn [bind].
    assert (GW : forall s1 z1 kk, hacc s0 z0 H k0 s1 z1 kk -> d_gzhead s1 = gh /\ d_wrap s1 = w).
    { intros s1 z1 kk A1. destruct Hm as [[_ [_ [_ [_ [_ [_ [Wr [Gz _]]]]]]]] _].
      destruct A1 as [_ [_ [_ [_ [_ [_ [Wr1 [Gz1 _]]]]]]]]. split; congruence. }
    destruct Hc as [[P0 Hm'] | [P0 [Av Ha']]].
    + rewrite P0. cbn [Z.eqb negb].
      assert (HP' : sP (s', z', 0)).
      { cbn [sP]. rewrite E2. destruct (GW _ _ _ (proj1 Hm')) as [G1 W1].
        split; [exact Hm'|]. split; [congruence|]. split; [exact G1|]. split; [exact W1|].
        split; [lia|]. rewrite P0. split; [lia|]. rewrite E4. cbn. f_equal; lia. }
      destruct (str_put s' z' 0 HP' ltac:(rewrite P0; pose proof (hmid_pbs_pos _ _ _ _ _ _ _ Hm'); lia))
        as [r [E Hr]].
      exists r. split; [exact E|]. destruct r as [a'|b]; [|exact Hr].
      destruct Hr as [Hr1 Hr2]. split; [exact Hr1|]. cbn [sM] in *. rewrite E2 in Hr2. exact Hr2.
    + destruct (d_pending s' =? 0) eqn:EP'; [apply Z.eqb_eq in EP'; contradiction|]. cbn [negb].
      eexists. split; [reflexivity|]. cbn [sQ].
      destruct (GW _ _ _ Ha') as [G1 W1].
      split; [cbn; congruence|]. split; [exact G1|]. split; [exact W1|].
      change (d_gzindex (set_d_last_flush s' (-1))) with (d_gzindex s'). rewrite E2.
      split; [exact Hg|]. split; [|rewrite E4; reflexivity].
      split; [exact Ha'|]. split; [reflexivity|]. split; [exact Av|exact P0].
  - apply Z.eqb_neq in EP. cbn [bind].
    destruct (str_put s z beg HP ltac:(lia)) as [r [E Hr]].
    exists r. split; [exact E|exact Hr].
Qed.

End StrLoop.

Lemma str_stage_nn : forall s0 z0 H k0 s z h o reset base,
  hmid s0 z0 H k0 s z (base + d_gzindex s) -> d_gzhead s = Some h -> bytes H -> cstr_ok o -> 0 <= base ->
  (match o with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end) ->
  base + Zlength (cstr_bytes o) <= Zlength H ->
  sublist base (base + Zlength (cstr_bytes o)) H = cstr_bytes o ->
  z_adler z = hadler h H (base + d_gzindex s) ->
  exists s' z' r, c_deflate_str h o reset s z = Some (s', z', r) /\
    d_status s' = d_status s /\ d_gzhead s' = d_gzhead s /\ d_wrap s' = d_wrap s /\
    match r with
    | None => hmid s0 z0 H k0 s' z' (base + Zlength (cstr_bytes o)) /\
              (reset = true -> d_gzindex s' = 0) /\
              z_adler z' = hadler h H (base + Zlength (cstr_bytes o))
    | Some c => c = Z_OK /\ o <> None /\ 0 <= d_gzindex s' < Zlength (cstr_bytes o) /\
                hret s0 z0 H k0 s' z' (base + d_gzindex s') /\ z_adler z' = hadler h H (base + d_gzindex s')
    end.
Proof.
  intros s0 z0 H k0 s z h o reset base Hm Eh HB Hc Hnn Hidx Hlen Hsub Ha.
  destruct o as [l|].
  2:{ cbn [cstr_bytes Zlength] in *. cbn. exists s, z, None.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite Hidx in Hm, Ha. rewrite Z.add_0_r in *. split; [exact Hm|]. split; [intros _; exact Hidx|exact Ha]. }
  destruct (Hc l eq_refl) as [l0 [Hl [Hl0len Hl0]]]. cbn [cstr_bytes] in *.
  assert (Ll : Zlength l = Zlength l0 + 1) by (rewrite Hl, Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (HP0 : sP s0 z0 H k0 h l base (d_status s) (d_wrap s) (d_gzhead s) (s, z, d_pending s)).
  { cbn [sP]. pose proof (hmid_pending_le _ _ _ _ _ _ _ Hm).
    split; [exact Hm|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. split; [lia|]. rewrite Ha. f_equal; lia. }
  destruct (loop_measure _ _ _ _ (str_body_ok s0 z0 H k0 h l l0 base (d_status s) (d_wrap s) (d_gzhead s)
              HB Hl Hl0len Hl0 Hlen Hsub Hnn) _ HP0 ltac:(cbn [sM]; destruct Hidx; lia)) as [b [Eb Qb]].
  unfold c_deflate_str. rewrite Eb. cbn [bind].
  destruct b as [[[s1 z1] beg]|[s1 z1]].
  - destruct Qb as [Hm1 [Hs1 [Hg1 [Hw1 [Hb1 Ha1]]]]].
    replace (base + Zlength l - d_pending s1 + beg) with (base + Zlength l - d_pending s1 + beg) in Ha1 by lia.
    rewrite (hcrc_update_mid _ _ _ _ _ _ _ h beg Hm1 HB Hb1 Ha1). cbn [bind].
    eexists _, _, None. split; [reflexivity|].
    destruct reset; cbn [set_d_gzindex d_status d_gzhead d_wrap d_gzindex].
    + split; [exact Hs1|]. split; [exact Hg1|]. split; [exact Hw1|].
      split; [apply hmid_adler, hmid_gzindex, Hm1|]. split; [reflexivity|reflexivity].
    + split; [exact Hs1|]. split; [exact Hg1|]. split; [exact Hw1|].
      split; [apply hmid_adler, Hm1|]. split; [discriminate|reflexivity].
  - destruct Qb as [Hs1 [Hg1 [Hw1 [Hi1 [Hr1 Ha1]]]]].
    exists s1, z1, (Some Z_OK). split; [reflexivity|].
    split; [exact Hs1|]. split; [exact Hg1|]. split; [exact Hw1|].
    split; [reflexivity|]. split; [discriminate|]. split; [exact Hi1|]. split; [exact Hr1|exact Ha1].
Qed.


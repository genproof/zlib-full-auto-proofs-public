(* inflate_fast (BodyF5.v): what the model's table walks find (F5Kit lwalk/dwalk). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Import Zlib.proof.inffast.F5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the walk on a valid table, generic in the kind                                                  *)

Lemma f5w_link_sub: forall op, Z.land op 240 = 0 -> Z.land op 16 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H. split.
  - change 16 with (Z.land 240 16). rewrite Z.land_assoc, H. reflexivity.
  - change 64 with (Z.land 240 64). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma f5w_len_link_true: forall op, islink LENS op = true -> len_link op = true.
Proof.
  intros op H. unfold islink in H. cbn in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H2. destruct (f5w_link_sub op H2) as [A B].
  unfold len_link. rewrite A, B. destruct (op =? 0); reflexivity || discriminate.
Qed.

Lemma f5w_dist_link_true: forall op, islink DISTS op = true -> dist_link op = true.
Proof.
  intros op H. unfold islink in H. cbn in H.
  apply Z.eqb_eq in H. destruct (f5w_link_sub op H) as [A B].
  unfold dist_link. rewrite A, B. reflexivity.
Qed.

Lemma f5w_len_final: forall e, final_ok LENS e -> len_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. cbn in H. unfold len_link.
  destruct H as [[H _] | [[H _] | [H | [H _]]]].
  - rewrite H. reflexivity.
  - assert (E: e_op e = 16 \/ e_op e = 17 \/ e_op e = 18 \/ e_op e = 19 \/ e_op e = 20 \/ e_op e = 21) by lia.
    destruct E as [E|[E|[E|[E|[E|E]]]]]; rewrite E; reflexivity.
  - rewrite H. reflexivity.
  - destruct (Z.land (e_op e) 64 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    rewrite !orb_true_r. reflexivity.
Qed.

Lemma f5w_dist_final: forall e, final_ok DISTS e -> dist_link (e_op e) = false.
Proof.
  intros e H. unfold final_ok in H. cbn in H. unfold dist_link.
  destruct H as [[H _] | [H _]].
  - assert (E: exists k, 0 <= k <= 13 /\ e_op e = 16 + k) by (exists (e_op e - 16); lia).
    destruct E as (k & K & E). rewrite E.
    assert (Z.land (16 + k) 16 = 16).
    { assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
              k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
      repeat (destruct H0 as [H0|H0]; [subst k; reflexivity|]); subst k; reflexivity. }
    rewrite H0. reflexivity.
  - destruct (Z.land (e_op e) 64 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    rewrite orb_true_r. reflexivity.
Qed.

Lemma f5w_mod_range: forall x n, 0 <= n -> 0 <= x mod 2 ^ n < 2 ^ n.
Proof. intros x n H. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma f5w_u32: forall x, 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros x H. unfold u32. apply Z.mod_small; auto. Qed.

Lemma f5w_walk: forall kind (islk: Z -> bool) (P: entry -> Prop) s t rb sz m,
  tvalid_b kind lenfix_list distfix_list s t rb sz ->
  (forall i, 0 <= i < sz -> P (tab_entry lenfix_list distfix_list s t i)) ->
  (forall op, islink kind op = true -> islk op = true) ->
  (forall e, final_ok kind e -> islk (e_op e) = false) ->
  m_s m = s -> 15 <= m_bits m <= 39 ->
  let '(e, m') := fwalk_f lenfix_list distfix_list 2 islk t
                    (tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)) m in
  entry_ok e /\ final_ok kind e /\ P e /\ islk (e_op e) = false /\
  m_bits m - 15 <= m_bits m' <= m_bits m /\
  m' = set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m - m_bits m'))) (m_bits m').
Proof.
  intros kind islk P s t rb sz m [R S T] HP HL HF Hs Hb.
  set (i := m_hold m mod 2 ^ rb).
  assert (Hi: 0 <= i < 2 ^ rb) by (apply f5w_mod_range; lia).
  assert (Hisz: 0 <= i < sz) by lia.
  destruct (T i Hi) as [Eok Hroot]. cbv zeta in Hroot.
  set (e := tab_entry lenfix_list distfix_list s t i) in *.
  destruct Eok as (Eo & Eb & Ev).
  cbn [fwalk_f]. cbn [m_s m_bits m_hold set_m_bits set_m_hold].
  destruct (islink kind (e_op e)) eqn:LK.
  - rewrite (HL _ LK).
    destruct Hroot as (B1 & B2 & B3 & B4).
    set (j := Z.shiftr (m_hold m) (e_bits e) mod 2 ^ e_op e).
    assert (Hj: 0 <= j < 2 ^ e_op e) by (apply f5w_mod_range; lia).
    destruct (B4 j Hj) as (C1 & C2 & C3 & C4 & C5). cbv zeta in *.
    rewrite Hs.
    set (e2 := tab_entry lenfix_list distfix_list s t (e_val e + j)) in *.
    rewrite (HF _ C5).
    destruct C2 as (D1 & D2 & D3).
    rewrite (f5w_u32 (m_bits m - e_bits e)) by lia.
    rewrite (f5w_u32 (m_bits m - e_bits e - e_bits e2)) by lia.
    split; [split; auto|]. split; [auto|]. split; [apply HP; auto|]. split; [apply HF; auto|].
    unfold set_m_bits, set_m_hold; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret
      m_leave m_adler m_msg m_tin m_tout m_snx m_sow].
    split; [lia|]. rewrite Z.shiftr_shiftr by lia.
    f_equal; f_equal; lia.
  - destruct Hroot as [B1 B2].
    rewrite (HF _ B2).
    rewrite (f5w_u32 (m_bits m - e_bits e)) by lia.
    split; [split; auto|]. split; [auto|]. split; [apply HP; auto|]. split; [apply HF; auto|].
    unfold set_m_bits, set_m_hold; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret
      m_leave m_adler m_msg m_tin m_tout m_snx m_sow].
    split; [lia|].
    f_equal; f_equal; lia.
Qed.

Lemma f5_walk_facts : lwalk_facts_stmt /\ dwalk_facts_stmt.
Proof.
  split.
  - intros m [W TL] Hmd Hb. destruct TL as (sz & Hsz & TV & LO).
    pose proof (mw_bits _ W) as Hb'.
    unfold lwalk.
    pose proof (f5w_walk LENS len_link len_ok (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) sz m
                  TV LO f5w_len_link_true f5w_len_final eq_refl ltac:(lia)) as H.
    destruct (fwalk_f _ _ _ _ _ _ _) as [e m'].
    destruct H as (A & B & C & D & E). auto.
  - intros m [W TL] Hmd Hb.
    destruct (md_tables _ (mw_md _ W)) as [_ (sz & Hsz & TV)].
    { unfold decode_mode. right; left. exact Hmd. }
    pose proof (mw_bits _ W) as Hb'.
    unfold dwalk.
    pose proof (f5w_walk DISTS dist_link (fun _ => True) (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m)) sz m
                  TV (fun _ _ => I) f5w_dist_link_true f5w_dist_final eq_refl ltac:(lia)) as H.
    destruct (fwalk_f _ _ _ _ _ _ _) as [e m'].
    destruct H as (A & B & C & D & E). auto.
Qed.

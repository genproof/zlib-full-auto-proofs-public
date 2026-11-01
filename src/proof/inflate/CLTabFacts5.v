(* case CODELENS: the pure facts of the two inflate_table calls (CLKit5.cl_tab_facts_stmt), as TLFacts.v over mwf / mwf3 with cover3_stmt *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.inftrees.ref Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma ctf_fact_result : facts.fact_result.
Proof.
  exact (part_result.fact_result_ok part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2
           part_subbits.subbits_ok2
           (part_size.size_ok2 part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2)).
Qed.

Local Open Scope Z_scope.

Ltac ctf_md_neq := cbv [HEAD TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT LENGTH DONE BAD SYNC] in *;
  lia.

Lemma ctf_call_table: forall type lo n req s r codes nxt b,
  cover3_stmt -> swf s -> 0 <= lo -> 0 <= n -> lo + n <= 320 ->
  inputs_ok type (sublist lo (lo + n) (i_lens s)) req ->
  cap_ok type (sublist lo (lo + n) (i_lens s)) req (ENOUGH_CODES - i_next s) ->
  (type = CODES -> n <= 19) ->
  call_table type lo n req s = (r, codes, nxt, b) ->
  Zlength codes = ENOUGH_CODES /\ Forall entry_ok codes /\ -1 <= r <= 1 /\
  (r <> 0 -> nxt = i_next s /\ b = req) /\
  (r = 0 -> exists used t,
     inflate_table_model type (sublist lo (lo + n) (i_lens s)) req
       (sublist (i_next s) ENOUGH_CODES (i_codes s)) = ROk b used t /\
     nxt = i_next s + used /\ codes = sublist 0 (i_next s) (i_codes s) ++ t /\
     Zlength t = ENOUGH_CODES - i_next s /\ tab_ok type t b used /\ 1 <= used <= ENOUGH_CODES - i_next s /\
     (type = LENS -> used <= ENOUGH_LENS) /\
     (type = LENS -> forall i, 0 <= i < used -> len_ok (Znth i t))).
Proof.
  intros type lo n req s r codes nxt b C3 S Hlo Hn Hhi IN CAP C19 E.
  unfold call_table in E.
  set (old := sublist (i_next s) ENOUGH_CODES (i_codes s)) in *.
  set (L := sublist lo (lo + n) (i_lens s)) in *.
  destruct (sw_codes _ S) as [ZC FC]. pose proof (sw_next _ S) as NX.
  assert (ZO: Zlength old = ENOUGH_CODES - i_next s)
    by (unfold old; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  assert (FO: Forall entry_ok old) by (apply Forall_sublist; auto).
  assert (ZL: Zlength L = n) by (unfold L; rewrite Zlength_sublist; destruct (sw_lens _ S); lia).
  assert (Zpre: Zlength (sublist 0 (i_next s) (i_codes s)) = i_next s)
    by (rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  assert (Fpre: Forall entry_ok (sublist 0 (i_next s) (i_codes s))) by (apply Forall_sublist; auto).
  rewrite <- ZO in CAP.
  pose proof (ctf_fact_result type L req old IN CAP FO) as FR.
  unfold ref.expected_call in FR.
  destruct (inflate_table_model type L req old) as [ | t | root used t] eqn:M;
    cbn [it_ret it_tab it_adv it_bits] in E; inversion E; subst r codes nxt b; clear E.
  - split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|].
    split; [lia|]. split; [intros; split; [lia | auto]|]. intros; lia.
  - destruct FR as (_ & FR1 & FR2).
    split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|].
    split; [lia|]. split; [intros; split; [lia | auto]|]. intros; lia.
  - destruct FR as (W0 & Rt & Us & U1 & _ & ZT & FT & _).
    destruct (C3 type L req old root used t IN ltac:(intros; lia) CAP FO M) as (TO & UO & LO).
    split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|].
    split; [lia|]. split; [intros; lia|]. intros _.
    exists used, t. split; [auto|]. split; [auto|]. split; [auto|]. split; [lia|]. split; [auto|].
    split; [lia|]. split; [|exact LO]. intros TL. subst type.
    destruct (negb (ref.expected_valid LENS L =? 0)); [discriminate|].
    cbn [Z.eqb andb LENS] in W0. destruct (Z.ltb_spec ENOUGH_LENS (ref.two_level_size L (ref.expected_root req L)));
      [discriminate|]. lia.
Qed.

Lemma ctf_forall_sublist: forall (P: Z -> Prop) lo hi l, 0 <= lo <= hi -> hi <= Zlength l ->
  (forall k, lo <= k < hi -> P (Znth k l)) -> Forall P (sublist lo hi l).
Proof.
  intros P lo hi l H1 H2 H. rewrite Forall_forall. intros x IN.
  apply In_Znth in IN. destruct IN as (i & Hi & E). subst x.
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply H; lia.
Qed.

(* a table built at codes[k ..) *)
Lemma ctf_tvalid_at: forall kind fx dx s k rb used t,
  0 <= k -> used <= ENOUGH_CODES - k ->
  (forall i, 0 <= i < used -> Znth (k + i) (i_codes s) = Znth i t) ->
  tab_ok kind t rb used -> tvalid kind fx dx s (TCodes k) rb.
Proof.
  intros kind fx dx s k rb used t Hk Hu E T. exists used. split; [simpl; lia|].
  unfold tvalid_b. apply tvalid_g_ext with (fun i => Znth i t); auto.
  intros i Hi. simpl. symmetry. apply E; auto.
Qed.

Lemma ctf_tvalid_len_at: forall fx dx s k rb used t,
  0 <= k -> used <= ENOUGH_CODES - k ->
  (forall i, 0 <= i < used -> Znth (k + i) (i_codes s) = Znth i t) ->
  tab_ok LENS t rb used -> (forall i, 0 <= i < used -> len_ok (Znth i t)) ->
  tvalid_len fx dx s (TCodes k) rb.
Proof.
  intros fx dx s k rb used t Hk Hu E T L. exists used. split; [simpl; lia|]. split.
  - unfold tvalid_b. apply tvalid_g_ext with (fun i => Znth i t); auto.
    intros i Hi. simpl. symmetry. apply E; auto.
  - intros i Hi. simpl. rewrite E; auto.
Qed.

Lemma cl_tab_facts : cl_tab_facts_stmt.
Proof.
  intros C3 m1 W1 Md1 L1 Hfull mA EA.
  pose proof (mw_md _ W1) as MD. pose proof (mw_s _ W1) as S.
  destruct (md_codelens _ MD Md1) as (H0 & Hnl & Hnd & LC & TV & LE).
  assert (Hh: i_have (m_s m1) = i_nlen (m_s m1) + i_ndist (m_s m1)) by lia.
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  unfold cl_lens_m in EA.
  set (s1 := set_i_lenbits (set_i_lencode (set_i_next (m_s m1) 0) (TCodes 0)) 9) in EA.
  assert (S1: swf s1) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  assert (IN1: inputs_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9).
  { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold LENS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply ctf_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (CAP1: cap_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9 (ENOUGH_CODES - i_next s1)).
  { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intros; lia|].
    split; intros; lia. }
  destruct (call_table LENS 0 (i_nlen s1) 9 s1) as [[[r1 c1] n1] b1] eqn:CT1.
  destruct (ctf_call_table LENS 0 (i_nlen s1) 9 s1 r1 c1 n1 b1 C3 S1 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia)
              IN1 CAP1 ltac:(unfold LENS, CODES; lia) CT1) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  inversion EA; subst r1 mA; clear EA.
  destruct (Ry1 eq_refl) as (used1 & t1 & M1 & En1 & Ec1 & Zt1 & T1 & U1 & U1L & LO1).
  specialize (U1L eq_refl). specialize (LO1 eq_refl). change (i_next s1) with 0 in *.
  rewrite sublist_nil in Ec1. simpl app in Ec1. subst c1 n1.
  pose proof (tv_rb _ _ _ _ T1) as RB1.
  set (s2 := set_i_lenbits (set_i_next (set_i_codes s1 t1) (0 + used1)) b1).
  assert (S2: swf s2) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES, ENOUGH_LENS in *; try lia).
  split.
  { unfold cl_dists_pre. cbn [m_s set_m_ret set_m_s m_mode m_leave]. unfold m_mode in Md1. simpl.
    split; [exact S2|]. split; [exact Md1|]. split; [exact L1|]. split; [lia|]. split; [lia|].
    split; [unfold ENOUGH_CODES, ENOUGH_LENS in *; lia|].
    intros k Hk. split; [rewrite Forall_forall in FL; apply FL; apply Znth_In; lia | apply LE; lia]. }
  intros R2. unfold cl_dists_m in *. cbn [m_s set_m_ret set_m_s] in *.
  set (s3 := set_i_distbits (set_i_distcode s2 (TCodes (i_next s2))) 6) in *.
  assert (S3: swf s3).
  { destruct S2; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES, ENOUGH_LENS in *; try lia. }
  assert (IN2: inputs_ok DISTS (sublist (i_nlen s3) (i_nlen s3 + i_ndist s3) (i_lens s3)) 6).
  { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold DISTS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply ctf_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (CAP2: cap_ok DISTS (sublist (i_nlen s3) (i_nlen s3 + i_ndist s3) (i_lens s3)) 6 (ENOUGH_CODES - i_next s3)).
  { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_DISTS, ENOUGH_CODES in *.
    split; [intros; lia|]. split; intros; lia. }
  destruct (call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3) as [[[r2 c2] n2] d2] eqn:CT2.
  cbn [fst snd] in *. subst r2.
  destruct (ctf_call_table DISTS (i_nlen s3) (i_ndist s3) 6 s3 0 c2 n2 d2 C3 S3 ltac:(simpl; lia) ltac:(simpl; lia)
              ltac:(simpl; lia) IN2 CAP2 ltac:(unfold DISTS, CODES; lia) CT2) as (ZC2 & FC2 & R2 & Rn2 & Ry2).
  destruct (Ry2 eq_refl) as (used2 & t2 & M2 & En2 & Ec2 & Zt2 & T2 & U2 & _ & _).
  change (i_next s3) with (0 + used1) in *. change (i_codes s3) with t1 in *. subst c2 n2.
  pose proof (tv_rb _ _ _ _ T2) as RB2.
  set (s4 := set_i_mode (set_i_distbits (set_i_next (set_i_codes s3 (sublist 0 (0 + used1) t1 ++ t2))
                                          (0 + used1 + used2)) d2) LEN_).
  assert (EQ: set_mode (set_m_ret (set_m_s (set_m_ret (set_m_s m1 s2) 0)
           (set_i_distbits (set_i_next (set_i_codes s3 (sublist 0 (0 + used1) t1 ++ t2)) (0 + used1 + used2)) d2)) 0) LEN_
     = set_m_s (set_m_ret m1 0) s4) by reflexivity.
  rewrite EQ. clear EQ.
  unfold ENOUGH_CODES, ENOUGH_LENS in *.
  assert (G1: forall i, 0 <= i < used1 -> Znth (0 + i) (sublist 0 (0 + used1) t1 ++ t2) = Znth i t1).
  { intros i Hi. rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
    f_equal; lia. }
  assert (G2: forall i, 0 <= i < used2 -> Znth (0 + used1 + i) (sublist 0 (0 + used1) t1 ++ t2) = Znth i t2).
  { intros i Hi. rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
    f_equal; lia. }
  assert (WR: mwf (set_m_ret m1 0)) by (destruct W1; constructor; simpl; auto; lia).
  assert (O1: m_out m1 = m_aout m1) by (apply mwf_out_eq; auto; rewrite Md1; ctf_md_neq).
  split.
  - destruct WR; constructor; simpl; auto.
    + unfold s4. constructor; simpl; intros; try ctf_md_neq.
      split.
      * apply ctf_tvalid_at with used1 t1; simpl; auto; unfold ENOUGH_CODES; lia.
      * apply ctf_tvalid_at with used2 t2; simpl; auto; unfold ENOUGH_CODES; lia.
    + unfold s4. destruct S3; constructor; simpl; auto; unfold ENOUGH_CODES; try lia; ctf_md_neq.
  - unfold s4. constructor; simpl; intros; try ctf_md_neq.
    apply ctf_tvalid_len_at with used1 t1; simpl; auto; unfold ENOUGH_CODES; lia.
Qed.

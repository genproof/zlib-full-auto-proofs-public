(* Law inflate_reset, TABLE / LENLENS / CODELENS: CODELENS after its loop, the LENS and DISTS tables
   (IRTabKit.irt_clpost_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRTabKit.
Require Import Zlib.proof.inflate.Step3Tables.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* irt_clpost with the two inflate_table calls made explicit                                     *)

Definition irc_s1 (s: istate) : istate := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9.
Definition irc_F (s: istate) (c: list entry) (n b: Z) : istate :=
  set_i_lenbits (set_i_next (set_i_codes (irc_s1 s) c) n) b.
Definition irc_s3 (s: istate) (c: list entry) (n b: Z) : istate :=
  set_i_distbits (set_i_distcode (irc_F s c n b) (TCodes n)) 6.
Definition irc_G (s: istate) (c: list entry) (n b: Z) (c2: list entry) (n2 d2: Z) : istate :=
  set_i_distbits (set_i_next (set_i_codes (irc_s3 s c n b) c2) n2) d2.

Definition irc_L1 (s: istate) := sublist 0 (0 + i_nlen s) (i_lens s).
Definition irc_o1 (s: istate) := sublist 0 ENOUGH_CODES (i_codes s).
Definition irc_L2 (s: istate) := sublist (i_nlen s) (i_nlen s + i_ndist s) (i_lens s).

Definition irc_rhs (m: mst) : irt_res :=
  let s := m_s m in
  if Znth 256 (i_lens s) =? 0 then ITDone (IBrk (set_bad m M_eob)) else
  let r1 := inflate_table_model LENS (irc_L1 s) 9 (irc_o1 s) in
  let c1 := sublist 0 0 (i_codes s) ++ it_tab (irc_o1 s) r1 in
  let n1 := 0 + it_adv r1 in let b1 := it_bits 9 r1 in
  if negb (it_ret r1 =? 0) then ITDone (IBrk (set_bad (set_m_ret (set_m_s m (irc_F s c1 n1 b1)) (it_ret r1)) M_ll_set)) else
  let o2 := sublist n1 ENOUGH_CODES c1 in
  let r2 := inflate_table_model DISTS (irc_L2 s) 6 o2 in
  let c2 := sublist 0 n1 c1 ++ it_tab o2 r2 in
  let G := irc_G s c1 n1 b1 c2 (n1 + it_adv r2) (it_bits 6 r2) in
  if negb (it_ret r2 =? 0) then ITDone (IBrk (set_bad (set_m_ret (set_m_s m G) (it_ret r2)) M_d_set)) else
  ITLen (set_mode (set_m_ret (set_m_s m G) (it_ret r2)) LEN_).

Lemma irc_eq m : irt_clpost m = irc_rhs m.
Proof.
  unfold irt_clpost, irc_rhs, call_table, irc_G, irc_s3, irc_F, irc_s1, irc_L1, irc_L2, irc_o1.
  cbv beta iota zeta.
  cbn [i_mode i_next i_lens i_codes i_nlen i_ndist set_i_lenbits set_i_lencode set_i_next set_i_codes
       set_i_distbits set_i_distcode].
  rewrite !tb_ret_ret. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One stream: the preconditions of the two inflate_table calls and the facts of their tables     *)

Lemma irc_side (C3: Zlib.proof.inflate.Cover3.cover3_stmt) m :
  mwf3x m -> m_mode m = CODELENS -> i_nlen (m_s m) + i_ndist (m_s m) <= i_have (m_s m) ->
  inputs_ok LENS (irc_L1 (m_s m)) 9 /\ cap_ok LENS (irc_L1 (m_s m)) 9 (Zlength (irc_o1 (m_s m))) /\
  Forall entry_ok (irc_o1 (m_s m)) /\ Zlength (irc_o1 (m_s m)) = ENOUGH_CODES /\
  inputs_ok DISTS (irc_L2 (m_s m)) 6 /\
  (forall root used t, inflate_table_model LENS (irc_L1 (m_s m)) 9 (irc_o1 (m_s m)) = ROk root used t ->
     Zlength t = ENOUGH_CODES /\ Forall entry_ok t /\ tab_ok LENS t root used /\ 1 <= used <= ENOUGH_LENS /\
     cap_ok DISTS (irc_L2 (m_s m)) 6 (Zlength (sublist used ENOUGH_CODES t)) /\
     Forall entry_ok (sublist used ENOUGH_CODES t) /\
     Zlength (sublist used ENOUGH_CODES t) = ENOUGH_CODES - used /\
     (forall root2 used2 u,
        inflate_table_model DISTS (irc_L2 (m_s m)) 6 (sublist used ENOUGH_CODES t) = ROk root2 used2 u ->
        tab_ok DISTS u root2 used2 /\ used2 <= ENOUGH_CODES - used)).
Proof.
  intros W1 Md1 Hh0.
  pose proof (irk_cover2 C3) as C2.
  pose proof (mw_md _ (m3_w _ W1)) as MD. pose proof (mw_s _ (m3_w _ W1)) as S.
  destruct (md_codelens _ MD Md1) as (H0 & Hnl & Hnd & LC & TV & LE).
  destruct (sw_lens _ S) as [ZL FL]. destruct (sw_codes _ S) as [ZC FC].
  set (s1 := irc_s1 (m_s m)).
  assert (S1: swf s1) by (destruct S; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  assert (IN1: inputs_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9).
  { unfold inputs_ok. simpl. rewrite Zlength_sublist by lia. split; [unfold LENS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply tb_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (CAP1: cap_ok LENS (sublist 0 (0 + i_nlen s1) (i_lens s1)) 9 (ENOUGH_CODES - i_next s1)).
  { unfold cap_ok. simpl. unfold LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_CODES. split; [intros; lia|].
    split; intros; lia. }
  assert (IN2: inputs_ok DISTS (irc_L2 (m_s m)) 6).
  { unfold inputs_ok, irc_L2. rewrite Zlength_sublist by lia. split; [unfold DISTS; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    apply tb_forall_sublist; try lia. intros k Hk. split.
    - rewrite Forall_forall in FL. apply FL. apply Znth_In; lia.
    - apply LE; lia. }
  assert (ZO: Zlength (irc_o1 (m_s m)) = ENOUGH_CODES)
    by (unfold irc_o1; rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia).
  assert (FO: Forall entry_ok (irc_o1 (m_s m))) by (unfold irc_o1; apply Forall_sublist; auto).
  split; [exact IN1|]. split; [unfold cap_ok, LENS, CODES, DISTS, ENOUGH_LENS; rewrite ZO; unfold ENOUGH_CODES; split; [intros; lia|]; split; intros; lia|].
  split; [exact FO|]. split; [exact ZO|]. split; [exact IN2|].
  intros root used t M.
  destruct (call_table LENS 0 (i_nlen s1) 9 s1) as [[[r1 c1] n1] b1] eqn:CT1.
  destruct (tb_call_table LENS 0 (i_nlen s1) 9 s1 r1 c1 n1 b1 C2 S1 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia)
              IN1 CAP1 ltac:(unfold LENS, CODES; lia) CT1) as (ZC1 & FC1 & R1 & Rn1 & Ry1).
  unfold call_table in CT1. change (i_next s1) with 0 in CT1.
  change (sublist 0 (0 + i_nlen s1) (i_lens s1)) with (irc_L1 (m_s m)) in CT1.
  change (sublist 0 ENOUGH_CODES (i_codes s1)) with (irc_o1 (m_s m)) in CT1.
  rewrite M in CT1. cbn [it_ret it_tab it_adv it_bits] in CT1. inversion CT1; subst r1 c1 n1 b1; clear CT1.
  destruct (Ry1 eq_refl) as (used1 & t1 & M1 & En1 & Ec1 & Zt1 & T1 & U1 & U1L).
  change (sublist 0 (0 + i_nlen s1) (i_lens s1)) with (irc_L1 (m_s m)) in M1.
  change (sublist (i_next s1) ENOUGH_CODES (i_codes s1)) with (irc_o1 (m_s m)) in M1.
  rewrite M in M1. inversion M1; subst used1 t1; clear M1.
  specialize (U1L eq_refl). change (i_next s1) with 0 in *.
  assert (Ft: Forall entry_ok t).
  { exact FC1. }
  split; [lia|]. split; [exact Ft|]. split; [exact T1|]. split; [lia|].
  assert (ZO2: Zlength (sublist used ENOUGH_CODES t) = ENOUGH_CODES - used)
    by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (CAP2: cap_ok DISTS (irc_L2 (m_s m)) 6 (Zlength (sublist used ENOUGH_CODES t))).
  { rewrite ZO2. unfold cap_ok, LENS, CODES, DISTS, ENOUGH_LENS, ENOUGH_DISTS, ENOUGH_CODES in *.
    split; [intros; lia|]. split; intros; lia. }
  assert (FO2: Forall entry_ok (sublist used ENOUGH_CODES t)) by (apply Forall_sublist; auto).
  split; [exact CAP2|]. split; [exact FO2|]. split; [exact ZO2|].
  intros root2 used2 u M2.
  destruct (C3 DISTS (irc_L2 (m_s m)) 6 _ root2 used2 u IN2 ltac:(unfold DISTS, CODES; lia) CAP2 FO2 M2)
    as (T2 & U2 & _).
  split; [exact T2|]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The tables in the final code space                                                             *)

(* treach_eq on the code space at offset k, as lists *)
Definition irc_tl (kind: Z) (c1 c2: list entry) (k rb: Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb ->
    let e := Znth (k + i) c1 in
    e = Znth (k + i) c2 /\
    (islink kind (e_op e) = true -> forall j, 0 <= j < 2 ^ e_op e ->
       Znth (k + (e_val e + j)) c1 = Znth (k + (e_val e + j)) c2).

Lemma irc_tl_treach kind sa sb k rb :
  irc_tl kind (i_codes sa) (i_codes sb) k rb -> treach_eq kind sa sb (TCodes k) rb.
Proof. intros H. exact H. Qed.

(* the LENS table at 0, kept below used by the DISTS build *)
Lemma irc_tl_lens kind t1 t2 u1 u2 root used :
  treach_l kind t1 t2 root -> tab_ok kind t1 root used -> used <= Zlength t1 -> used <= Zlength t2 ->
  irc_tl kind (sublist 0 used t1 ++ u1) (sublist 0 used t2 ++ u2) 0 root.
Proof.
  intros TL T Z1 Z2 i Hi. destruct T as [RB SZ RT].
  assert (G1: forall x, 0 <= x < used -> Znth x (sublist 0 used t1 ++ u1) = Znth x t1).
  { intros x Hx. rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia. }
  assert (G2: forall x, 0 <= x < used -> Znth x (sublist 0 used t2 ++ u2) = Znth x t2).
  { intros x Hx. rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia. }
  specialize (RT i Hi). cbv zeta in RT |- *. rewrite !Z.add_0_l.
  assert (Iu: 0 <= i < used) by lia.
  rewrite (G1 i Iu), (G2 i Iu). destruct (TL i Hi) as [E1 E2].
  split; [exact E1|]. intros LK j Hj.
  rewrite LK in RT. destruct RT as [_ (_ & _ & _ & SB)]. destruct (SB j Hj) as [Rj _].
  rewrite !Z.add_0_l. rewrite (G1 _ Rj), (G2 _ Rj). apply E2; auto.
Qed.

(* the DISTS table at used *)
Lemma irc_tl_dists kind t1 t2 u1 u2 root2 used2 used :
  treach_l kind u1 u2 root2 -> tab_ok kind u1 root2 used2 ->
  Zlength (sublist 0 used t1) = used -> Zlength (sublist 0 used t2) = used ->
  irc_tl kind (sublist 0 used t1 ++ u1) (sublist 0 used t2 ++ u2) used root2.
Proof.
  intros TL T Z1 Z2 i Hi. destruct T as [RB SZ RT].
  assert (G1: forall x, 0 <= x -> Znth (used + x) (sublist 0 used t1 ++ u1) = Znth x u1).
  { intros x Hx. rewrite Znth_app2 by lia. rewrite Z1. f_equal; lia. }
  assert (G2: forall x, 0 <= x -> Znth (used + x) (sublist 0 used t2 ++ u2) = Znth x u2).
  { intros x Hx. rewrite Znth_app2 by lia. rewrite Z2. f_equal; lia. }
  specialize (RT i Hi). cbv zeta in RT |- *.
  rewrite G1, G2 by lia. destruct (TL i Hi) as [E1 E2].
  split; [exact E1|]. intros LK j Hj.
  rewrite LK in RT. destruct RT as [_ (_ & _ & _ & SB)]. destruct (SB j Hj) as [Rj _].
  rewrite G1, G2 by lia. apply E2; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The new states are related                                                                    *)

Ltac irc_cst := unfold HEAD, TABLE, LENLENS, CODELENS, BAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, COPY_,
  COPY, EXTRA in *.

Lemma irc_srel_badF no sa sb ca cb n b :
  srel no sa sb -> i_mode sb = CODELENS ->
  srel no (set_i_mode (irc_F sa ca n b) BAD) (set_i_mode (irc_F sb cb n b) BAD).
Proof.
  intros S Md. destruct sa, sb. destruct S; cbn in *. subst.
  unfold irc_F, irc_s1. constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irc_cst; lia).
  all: destruct sr_check as [?|[?|[_ ?]]]; auto.
Qed.

Lemma irc_srel_badG no sa sb ca cb n b c2a c2b n2 d2 :
  srel no sa sb -> i_mode sb = CODELENS ->
  srel no (set_i_mode (irc_G sa ca n b c2a n2 d2) BAD) (set_i_mode (irc_G sb cb n b c2b n2 d2) BAD).
Proof.
  intros S Md. destruct sa, sb. destruct S; cbn in *. subst.
  unfold irc_G, irc_s3, irc_F, irc_s1. constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irc_cst; lia).
  all: destruct sr_check as [?|[?|[_ ?]]]; auto.
Qed.

Lemma irc_srel_len no sa sb ca cb n b c2a c2b n2 d2 :
  srel no sa sb -> i_mode sb = CODELENS ->
  irc_tl LENS c2a c2b 0 b -> irc_tl DISTS c2a c2b n d2 ->
  srel no (set_i_mode (irc_G sa ca n b c2a n2 d2) LEN_) (set_i_mode (irc_G sb cb n b c2b n2 d2) LEN_).
Proof.
  intros S Md T1 T2. destruct sa, sb. destruct S; cbn in *. subst.
  unfold irc_G, irc_s3, irc_F, irc_s1. constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irc_cst; lia).
  all: first [destruct sr_wbits as [?|[?|?]]; auto; exfalso; irc_cst; lia
             | destruct sr_check as [?|[?|[[?|?] _]]]; auto; exfalso; irc_cst; lia
             | split; [exact T1 | exact T2] ].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kr of the results                                                                              *)

Lemma irc_bad_eq m s r e :
  set_bad (set_m_ret (set_m_s m s) r) e = set_m_s (set_m_msg (set_m_ret m r) (Some e)) (set_i_mode s BAD).
Proof. destruct m; reflexivity. Qed.

Lemma irc_len_eq m s r :
  set_mode (set_m_ret (set_m_s m s) r) LEN_ = set_m_s (set_m_ret m r) (set_i_mode s LEN_).
Proof. destruct m; reflexivity. Qed.

Lemma irc_kr_new W0 wrap src pos inp aout ma mb sa sb r e md :
  Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD -> md <> HEAD ->
  srel (m_ow mb = []) (set_i_mode sa md) (set_i_mode sb md) ->
  i_wrap sb = i_wrap (m_s mb) -> i_head sb = i_head (m_s mb) ->
  i_wbits sa = i_wbits (m_s ma) -> i_wbits sb = i_wbits (m_s mb) ->
  Kr W0 wrap src pos inp aout (set_m_s (set_m_msg (set_m_ret ma r) e) (set_i_mode sa md))
    (set_m_s (set_m_msg (set_m_ret mb r) e) (set_i_mode sb md)).
Proof.
  intros K Hh Hmd S Ew Ed Ea Eb.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K) as Kw. pose proof (kr_head _ _ _ _ _ _ _ _ K) as Kh.
  assert (K1: Kr W0 wrap src pos inp aout (set_m_msg (set_m_ret ma r) e) (set_m_msg (set_m_ret mb r) e)).
  { apply irk_mach with ma mb; auto. pose proof (irk_mf_of_Kr _ _ _ _ _ _ _ _ K) as E.
    unfold irk_mf in *. destruct ma, mb; cbn in *. injection E; intros; subst; reflexivity. }
  apply irk_state; auto; cbn [set_i_mode i_mode i_wrap i_head i_wbits m_s set_m_msg set_m_ret m_ow] in *; auto.
  all: first [congruence | destruct ma; exact Ea | destruct mb; exact Eb].
Qed.

Lemma irc_srel_bad0 no sa sb :
  srel no sa sb -> srel no (set_i_mode sa BAD) (set_i_mode sb BAD).
Proof.
  intros S. destruct sa, sb. destruct S; cbn in *. subst.
  constructor; cbn; auto; intros;
    try (exfalso; unfold lenlive, decode_mode in *; cbn in *; irc_cst; lia).
  all: destruct sr_check as [?|[?|[_ ?]]]; auto.
Qed.

Lemma irc_bad0 W0 wrap src pos inp aout ma mb e :
  Kr W0 wrap src pos inp aout ma mb -> m_mode mb <> HEAD ->
  Kr W0 wrap src pos inp aout (set_bad ma e) (set_bad mb e).
Proof.
  intros K Hh. pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  pose proof (kr_wrap _ _ _ _ _ _ _ _ K) as Kw. pose proof (kr_head _ _ _ _ _ _ _ _ K) as Kh.
  assert (K1: Kr W0 wrap src pos inp aout (set_m_msg ma (Some e)) (set_m_msg mb (Some e))).
  { apply irk_mach with ma mb; auto. pose proof (irk_mf_of_Kr _ _ _ _ _ _ _ _ K) as E.
    unfold irk_mf in *. destruct ma, mb; cbn in *. injection E; intros; subst; reflexivity. }
  unfold set_bad, set_mode, upd_s.
  apply irk_state; cbn [m_s set_m_msg m_ow] in *; auto.
  - apply irc_srel_bad0; auto.
  - unfold BAD, HEAD; cbn. lia.
Qed.

Lemma irc_sub_eq (l1 l2: list Z) lo hi :
  0 <= lo <= hi -> hi <= Zlength l1 -> hi <= Zlength l2 ->
  (forall k, lo <= k < hi -> Znth k l1 = Znth k l2) -> sublist lo hi l1 = sublist lo hi l2.
Proof.
  intros H1 H2 H3 E. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia. apply E; lia.
Qed.

Lemma irt_clpost_ok : Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt -> irt_clpost_stmt.
Proof.
  intros C3 TD W0 wrap src pos inp aout ma mb K Wa Wb L Md Hh.
  pose proof (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K)) as S.
  assert (Mdb: i_mode (m_s mb) = CODELENS) by exact Md.
  assert (Hhd: m_mode mb <> HEAD) by (rewrite Md; unfold CODELENS, HEAD; lia).
  assert (Ma: m_mode ma = CODELENS) by (unfold m_mode in *; rewrite (sr_mode _ _ _ S); exact Md).
  destruct (sr_nlen _ _ _ S (or_intror Mdb)) as (En & Ed & Ehv).
  assert (Ha: i_nlen (m_s ma) + i_ndist (m_s ma) <= i_have (m_s ma)) by lia.
  destruct (irc_side C3 ma Wa Ma Ha) as (INa & CAPa & FOa & ZOa & IN2a & Ra).
  destruct (irc_side C3 mb Wb Md Hh) as (INb & CAPb & FOb & ZOb & IN2b & Rb).
  pose proof (mw_md _ (m3_w _ Wb)) as MD. destruct (md_codelens _ MD Mdb) as (_ & Hnl & Hnd & _).
  pose proof (sw_lens _ (mw_s _ (m3_w _ Wa))) as [ZLa _].
  pose proof (sw_lens _ (mw_s _ (m3_w _ Wb))) as [ZLb _].
  pose proof (sr_codelens _ _ _ S Mdb) as CL.
  assert (EL1: irc_L1 (m_s ma) = irc_L1 (m_s mb)).
  { unfold irc_L1. rewrite En. apply irc_sub_eq; try lia. intros k Hk. apply CL; lia. }
  assert (EL2: irc_L2 (m_s ma) = irc_L2 (m_s mb)).
  { unfold irc_L2. rewrite En, Ed. apply irc_sub_eq; try lia. intros k Hk. apply CL; lia. }
  assert (E256: Znth 256 (i_lens (m_s ma)) = Znth 256 (i_lens (m_s mb))) by (apply CL; lia).
  rewrite (irc_eq ma), (irc_eq mb). unfold irc_rhs. cbv zeta.
  rewrite E256. destruct (Znth 256 (i_lens (m_s mb)) =? 0).
  { cbn [irt_rr]. apply irc_bad0; auto. }
  rewrite EL1 in *. rewrite EL2 in *.
  destruct (TD LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s ma)) (irc_o1 (m_s mb)) INb
              ltac:(unfold LENS, CODES; lia) CAPa FOa ltac:(lia) FOb) as (Er & Eadv & Eb & Ok).
  rewrite Er, Eadv, Eb.
  destruct (Z.eqb_spec (it_ret (inflate_table_model LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s mb)))) 0) as [R0|R0].
  2:{ cbn [negb irt_rr]. rewrite irc_bad_eq, irc_bad_eq.
      apply irc_kr_new; auto; [unfold BAD, HEAD; lia | apply irc_srel_badF; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model LENS (irc_L1 (m_s mb)) 9 (irc_o1 (m_s ma))) as [ | ta | root used t1] eqn:MA;
    cbn [it_ret] in Er; [rewrite <- Er in R0; discriminate .. |].
  destruct (Ok root used t1 eq_refl) as (t2 & MB & TL1).
  rewrite MB. cbn [it_ret it_tab it_adv it_bits].
  rewrite !sublist_nil, !app_nil_l, !Z.add_0_l.
  destruct (Ra root used t1 eq_refl) as (Zt1 & Ft1 & T1 & U1 & CAP2a & FO2a & ZO2a & Da).
  destruct (Rb root used t2 MB) as (Zt2 & Ft2 & T2 & U2 & CAP2b & FO2b & ZO2b & Db).
  destruct (TD DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t1) (sublist used ENOUGH_CODES t2) IN2b
              ltac:(unfold DISTS, CODES; lia) CAP2a FO2a ltac:(lia) FO2b) as (Er2 & Eadv2 & Eb2 & Ok2).
  rewrite Er2, Eadv2, Eb2.
  destruct (Z.eqb_spec (it_ret (inflate_table_model DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t2))) 0)
    as [R2|R2].
  2:{ cbn [negb irt_rr]. rewrite irc_bad_eq, irc_bad_eq.
      apply irc_kr_new; auto; [unfold BAD, HEAD; lia | apply irc_srel_badG; auto | reflexivity ..]. }
  cbn [negb].
  destruct (inflate_table_model DISTS (irc_L2 (m_s mb)) 6 (sublist used ENOUGH_CODES t1))
    as [ | ua | root2 used2 u1] eqn:MA2; cbn [it_ret] in Er2; [rewrite <- Er2 in R2; discriminate .. |].
  destruct (Ok2 root2 used2 u1 eq_refl) as (u2 & MB2 & TL2).
  rewrite MB2. cbn [it_ret it_tab it_adv it_bits irt_rr].
  destruct (Da root2 used2 u1 eq_refl) as [TD2 UD2].
  assert (Zs1: Zlength (sublist 0 used t1) = used) by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  assert (Zs2: Zlength (sublist 0 used t2) = used) by (rewrite Zlength_sublist; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia).
  split; [|split; [exact L | reflexivity]].
  rewrite irc_len_eq, irc_len_eq.
  change (set_m_ret ma 0) with (set_m_msg (set_m_ret ma 0) (m_msg ma)).
  change (set_m_ret mb 0) with (set_m_msg (set_m_ret mb 0) (m_msg mb)).
  rewrite (mr_msg _ _ (kr_rel _ _ _ _ _ _ _ _ K)).
  apply irc_kr_new; auto; [unfold LEN_, HEAD; lia | | reflexivity ..].
  apply irc_srel_len; [exact S | exact Mdb | |].
  - apply irc_tl_lens; auto; unfold ENOUGH_CODES, ENOUGH_LENS in *; lia.
  - apply irc_tl_dists with used2; auto.
Qed.

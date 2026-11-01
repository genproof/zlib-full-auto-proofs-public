(* Law inflate_check, theory part: the decoding cases LEN_ .. LIT keep Kx. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Zlib.proof.inflate.MwfLemmas.
Import ListNotations.
Local Open Scope Z_scope.

(* The explicit forms of NEEDBITS and the lookups and the table facts: inflate_codes/TheoryDec.v's (dc_* there). *)
Definition ikc_md (x: Z) : Prop := decode_mode x \/ x = Zlib.proof.inflate.Model.TYPE \/ x = BAD.

Lemma ikc_md_ne x : ikc_md x -> x <> SYNC /\ x <> HEAD /\ x <> DICTID /\ x <> DICT.
Proof.
  unfold ikc_md, decode_mode. intros H.
  repeat match type of H with _ \/ _ => destruct H as [H|H] end; subst x;
  unfold LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, BAD, Zlib.proof.inflate.Model.TYPE,
    SYNC, HEAD, DICTID, DICT; repeat split; lia.
Qed.

Lemma ikc_Kc wrap src pos inp aout m m' :
  Kc wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) ->
  ikc_md (m_mode m') ->
  (m_mode m' <> BAD -> m_mode m' <> DONE -> m_ret m' = Z_OK) ->
  (m_leave m' = 1 ->
     (m_mode m' = DONE -> m_ret m' = Z_STREAM_END) /\ (m_mode m' = BAD -> m_ret m' = Z_DATA_ERROR)) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> m_mode m' <> MEM -> 0 <= m_bits m' <= 31) ->
  (m_out m' <> m_aout m' -> 0 < m_nx m') ->
  Kc wrap src pos inp aout m'.
Proof.
  intros K Hi Ha Hw Hhd Hmd Hr Hrx Hmsg Hb Ho.
  destruct (ikc_md_ne _ Hmd) as (N1 & N2 & N3 & N4).
  constructor; auto.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hhd; apply (kc_head _ _ _ _ _ _ K).
  - intros _ E; contradiction.
  - intros E; contradiction.
  - intros E; contradiction.
Qed.

Lemma ikc_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small; lia. Qed.

Lemma ikc_land15 x : 0 <= Z.land x 15 <= 15.
Proof.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 4) ltac:(lia)). change (Z.ones 4) with 15. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tables                                                                                          *)

Definition ikc_get (codes: list entry) (t: tref) (i: Z) : entry :=
  match t with
  | TLenfix => Znth i lenfix_list
  | TDistfix => Znth i distfix_list
  | TCodes k => Znth (k + i) codes
  end.

Lemma ikc_get_eq s t i : tab_entry lenfix_list distfix_list s t i = ikc_get (i_codes s) t i.
Proof. destruct t; reflexivity. Qed.

(* what the lookups need of a valid table *)
Definition ikc_tab (kind: Z) (codes: list entry) (t: tref) (rb: Z) : Prop :=
  1 <= rb <= 15 /\
  forall i, 0 <= i < 2 ^ rb ->
    0 <= e_bits (ikc_get codes t i) <= 15 /\ 0 <= e_op (ikc_get codes t i) /\
    (islink kind (e_op (ikc_get codes t i)) = true ->
       e_bits (ikc_get codes t i) = rb /\
       forall j, 0 <= j < 2 ^ e_op (ikc_get codes t i) ->
         0 <= e_bits (ikc_get codes t (e_val (ikc_get codes t i) + j)) /\
         rb + e_bits (ikc_get codes t (e_val (ikc_get codes t i) + j)) <= 15).

Lemma ikc_tab_of kind s t rb :
  tvalid kind lenfix_list distfix_list s t rb -> ikc_tab kind (i_codes s) t rb.
Proof.
  intros (sz & _ & [R S T]). split; [exact R|]. intros i Hi.
  destruct (T i Hi) as [E F]. cbv zeta in F. rewrite ikc_get_eq in E, F.
  destruct E as (E1 & E2 & E3).
  destruct (islink kind (e_op (ikc_get (i_codes s) t i))) eqn:L.
  - destruct F as (F1 & F2 & F3 & F4). split; [lia|]. split; [lia|]. intros _. split; [exact F1|].
    intros j Hj. destruct (F4 j Hj) as (G1 & G2 & G3 & G4 & G5). rewrite ikc_get_eq in G2, G4.
    destruct G2 as (_ & G2 & _). split; lia.
  - destruct F as (F1 & _). split; [lia|]. split; [lia|]. intros D; discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS and the lookups, in explicit form                                                      *)

Lemma ikc_pull_bits m : 0 <= m_bits m <= 39 -> m_bits (pull m) = m_bits m + 8.
Proof. intros H. cbn [pull m_bits set_m_bits]. apply ikc_u32. lia. Qed.

Lemma ikc_nbf n k m :
  n <= 32 -> 0 <= m_bits m <= 39 -> n <= m_bits m + 8 * Z.of_nat k ->
  exists nx h b lv,
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) (n + 7) /\ (lv = 1 \/ (lv = m_leave m /\ n <= b)).
Proof.
  intros Hn. revert m. induction k as [|k IH]; intros m Hb Hk.
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|]. lia.
  - cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|]. lia.
      * pose proof (ikc_pull_bits m Hb) as Hb'.
        destruct (IH (pull m) ltac:(lia) ltac:(lia)) as (nx' & h' & b' & lv' & E & R & C).
        rewrite E. exists nx', h', b', lv'. split; [destruct m; reflexivity|].
        cbn [pull m_leave set_m_nx set_m_hold set_m_bits] in C. lia.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|]. lia.
Qed.

Lemma ikc_nb n m :
  0 <= n <= 15 -> 0 <= m_bits m <= 31 ->
  exists nx h b lv,
    needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\ (lv = 1 \/ (lv = m_leave m /\ n <= b)).
Proof.
  intros Hn Hb. destruct (ikc_nbf n 4 m ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx & h & b & lv & E & R & C).
  exists nx, h, b, lv. split; [exact E|]. lia.
Qed.

Lemma ikc_lk1f k t nb m :
  0 <= nb -> 0 <= m_bits m <= 31 ->
  (forall i, 0 <= i < 2 ^ nb -> 0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t i) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k lenfix_list distfix_list t nb m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ e_bits here <= b /\
       exists i, 0 <= i < 2 ^ nb /\ here = tab_entry lenfix_list distfix_list (m_s m) t i) /\
    (ok = false -> lv = 1).
Proof.
  revert m. induction k as [|k IH]; intros m Hnb Hb F Hk.
  - cbn [lookup1_f]. pose proof (Z.mod_pos_bound (m_hold m) (2 ^ nb) ltac:(lia)) as BR.
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [|discriminate]. intros _. split; [reflexivity|].
    specialize (F _ BR). split; [unfold bitsn; lia|]. eexists; split; [exact BR|reflexivity].
  - cbn [lookup1_f]. pose proof (Z.mod_pos_bound (m_hold m) (2 ^ nb) ltac:(lia)) as BR.
    pose proof (F _ BR) as Fb. unfold bitsn in *.
    destruct (Z.leb_spec (e_bits (tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ nb)))
                (m_bits m)) as [L|L].
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. split; [|discriminate]. intros _. split; [reflexivity|]. split; [lia|].
      eexists; split; [exact BR|reflexivity].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. split; [discriminate|]. auto.
      * pose proof (ikc_pull_bits m ltac:(lia)) as Hb'.
        specialize (IH (pull m) Hnb ltac:(lia) F ltac:(lia)).
        destruct (lookup1_f k lenfix_list distfix_list t nb (pull m)) as [[h m'] ok].
        destruct IH as (nx' & h' & b' & lv' & E & R & C1 & C2).
        exists nx', h', b', lv'. split; [rewrite E; destruct m; reflexivity|].
        cbn [pull m_leave m_s set_m_nx set_m_hold set_m_bits] in C1. split; [lia|]. split; [|exact C2].
        intros T. destruct (C1 T) as (C3 & C4 & C5). split; [exact C3|]. split; [lia|exact C5].
Qed.

Lemma ikc_lk1 t nb m :
  0 <= nb -> 0 <= m_bits m <= 31 ->
  (forall i, 0 <= i < 2 ^ nb -> 0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t i) <= 15) ->
  let '(here, m', ok) := lookup1 lenfix_list distfix_list t nb m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ e_bits here <= b /\
       exists i, 0 <= i < 2 ^ nb /\ here = tab_entry lenfix_list distfix_list (m_s m) t i) /\
    (ok = false -> lv = 1).
Proof. intros. apply ikc_lk1f; auto. cbn. lia. Qed.

Lemma ikc_subrange x b o : 0 <= b -> 0 <= o -> 0 <= Z.shiftr (x mod 2 ^ (b + o)) b < 2 ^ o.
Proof.
  intros Hb Ho. rewrite Z.shiftr_div_pow2 by lia.
  assert (P: 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (Q: 0 <= x mod 2 ^ (b + o) < 2 ^ (b + o)) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r in Q |- * by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; nia.
Qed.

Lemma ikc_lk2f k t last m :
  0 <= e_bits last <= m_bits m -> m_bits m <= 31 -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) /\
     e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup2_f k lenfix_list distfix_list t last m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ 0 <= e_bits here /\ e_bits last + e_bits here <= b) /\
    (ok = false -> lv = 1).
Proof.
  revert m. induction k as [|k IH]; intros m Hl Hb Ho F Hk.
  - cbn [lookup2_f]. pose proof (ikc_subrange (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    unfold bitsn. specialize (F _ BR).
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [|discriminate]. intros _. lia.
  - cbn [lookup2_f]. pose proof (ikc_subrange (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    pose proof (F _ BR) as Fb. unfold bitsn in *.
    destruct (Z.leb_spec (e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t
                (e_val last + Z.shiftr (m_hold m mod 2 ^ (e_bits last + e_op last)) (e_bits last)))) (m_bits m))
      as [L|L].
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. split; [|discriminate]. intros _. lia.
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. split; [discriminate|]. auto.
      * pose proof (ikc_pull_bits m ltac:(lia)) as Hb'.
        specialize (IH (pull m) ltac:(lia) ltac:(lia) Ho F ltac:(lia)).
        destruct (lookup2_f k lenfix_list distfix_list t last (pull m)) as [[h m'] ok].
        destruct IH as (nx' & h' & b' & lv' & E & R & C1 & C2).
        exists nx', h', b', lv'. split; [rewrite E; destruct m; reflexivity|].
        cbn [pull m_leave m_s set_m_nx set_m_hold set_m_bits] in C1. split; [lia|]. split; [exact C1|exact C2].
Qed.

Lemma ikc_lk2 t last m :
  0 <= e_bits last <= m_bits m -> m_bits m <= 31 -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) /\
     e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) <= 15) ->
  let '(here, m', ok) := lookup2 lenfix_list distfix_list t last m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ 0 <= e_bits here /\ e_bits last + e_bits here <= b) /\
    (ok = false -> lv = 1).
Proof. intros. apply ikc_lk2f; auto. cbn. lia. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS and the lookups with the bit buffer (the kit)                                        *)

Lemma ikc_nbk (KIT: ik_kit) src pos inp n m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp ->
  ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
  0 <= n <= 15 -> 0 <= m_bits m <= 31 ->
  exists nx h b lv,
    needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\ (lv = 1 \/ (lv = m_leave m /\ n <= b)) /\
    ik_bitbuf src (pos + nx) h b /\ m_nx m <= nx <= Zlength inp /\ b - m_bits m = 8 * (nx - m_nx m).
Proof.
  intros Hc Hi Hn Bf Hnn Hb.
  destruct (ikc_nb n m Hnn Hb) as (nx & h & b & lv & E & R & C).
  pose proof (kk_needbits KIT src pos inp n m Hc Hi Hn ltac:(lia) ltac:(lia) Bf) as NB. cbv zeta in NB.
  rewrite E in NB. cbn [m_nx m_hold m_bits set_m_leave set_m_bits set_m_hold set_m_nx] in NB.
  destruct NB as (B & _ & N & D & _).
  exists nx, h, b, lv. tauto.
Qed.

Lemma ikc_lk1k (KIT: ik_kit) src pos inp t nb m here m1 ok :
  lookup1 lenfix_list distfix_list t nb m = (here, m1, ok) ->
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp ->
  ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
  0 <= nb -> 0 <= m_bits m <= 31 ->
  (forall i, 0 <= i < 2 ^ nb -> 0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t i) <= 15) ->
  exists nx h b lv, m1 = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ e_bits here <= b /\
       exists i, 0 <= i < 2 ^ nb /\ here = tab_entry lenfix_list distfix_list (m_s m) t i) /\
    (ok = false -> lv = 1) /\
    ik_bitbuf src (pos + nx) h b /\ m_nx m <= nx <= Zlength inp /\ b - m_bits m = 8 * (nx - m_nx m).
Proof.
  intros L Hc Hi Hn Bf Hnb Hb T.
  pose proof (ikc_lk1 t nb m Hnb Hb T) as D. rewrite L in D. cbv beta iota in D.
  destruct D as (nx & h & b & lv & E & R & C1 & C2).
  pose proof (kk_lookup1 KIT src pos inp lenfix_list distfix_list t nb m here m1 ok Hc Hi Hn ltac:(lia) Bf L)
    as K.
  subst m1. cbn [m_nx m_hold m_bits set_m_leave set_m_bits set_m_hold set_m_nx] in K.
  destruct K as (B & _ & N & Dd & _).
  exists nx, h, b, lv. tauto.
Qed.

Lemma ikc_lk2k (KIT: ik_kit) src pos inp t last m here m2 ok :
  lookup2 lenfix_list distfix_list t last m = (here, m2, ok) ->
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp ->
  ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
  0 <= e_bits last <= m_bits m -> m_bits m <= 31 -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) /\
     e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) <= 15) ->
  exists nx h b lv, m2 = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ 0 <= e_bits here /\ e_bits last + e_bits here <= b) /\
    (ok = false -> lv = 1) /\
    ik_bitbuf src (pos + nx) h b /\ m_nx m <= nx <= Zlength inp /\ b - m_bits m = 8 * (nx - m_nx m).
Proof.
  intros L Hc Hi Hn Bf Hl Hb Ho T.
  pose proof (ikc_lk2 t last m Hl Hb Ho T) as D. rewrite L in D. cbv beta iota in D.
  destruct D as (nx & h & b & lv & E & R & C1 & C2).
  pose proof (kk_lookup2 KIT src pos inp lenfix_list distfix_list t last m here m2 ok Hc Hi Hn ltac:(lia) Bf L)
    as K.
  subst m2. cbn [m_nx m_hold m_bits set_m_leave set_m_bits set_m_hold set_m_nx] in K.
  destruct K as (B & _ & N & Dd & _).
  exists nx, h, b, lv. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx after a decoding step                                                                       *)

Lemma ikc_Kx wrap src pos out a0 m :
  Kx wrap src pos out a0 m -> decode_mode (m_mode m) -> m_out m = m_aout m ->
  forall m',
  m_out m' = m_out m -> m_aout m' = m_aout m -> m_tout m' = m_tout m ->
  i_total (m_s m') = i_total (m_s m) -> i_flags (m_s m') = i_flags (m_s m) ->
  i_check (m_s m') = i_check (m_s m) -> m_adler m' = m_adler m ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  ikc_md (m_mode m') ->
  Kx wrap src pos out a0 m'.
Proof.
  intros X Hd Ho m' Eo Ea Et Etot Ef Eck Ead Hb Hc Hmd.
  assert (Nm : forall P : Prop, (m_mode m' = EXTRA \/ m_mode m' = NAME \/ m_mode m' = COMMENT \/
                 m_mode m' = COPY_ \/ m_mode m' = COPY \/ m_mode m' = EXLEN \/ ik_pre_mode (m_mode m') \/
                 m_mode m' = CHECK \/ m_mode m' = LENGTH \/ m_mode m' = DONE \/ m_mode m' = MEM) -> P).
  { intros P H. exfalso. unfold ikc_md, decode_mode, ik_pre_mode, ik_gzhdr_mode in *.
    unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
      Zlib.proof.inflate.Model.TYPE, COPY_, COPY, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT,
      CHECK, LENGTH, DONE, BAD, MEM in *. lia. }
  assert (Hpost : wrap <> 0 -> ik_post wrap src pos out m').
  { intros W. assert (PM : ik_post_mode (m_mode m)) by (unfold ik_post_mode; tauto).
    pose proof (kx_post _ _ _ _ _ _ X W PM) as P. unfold ik_post in *.
    rewrite Ef, Eck, Ead, Eo, Ea, Ho, Z.sub_diag, sublist_nil.
    rewrite Ho, Z.sub_diag, sublist_nil in P.
    destruct P as [P1 [P2 P3]]. split; [|split; auto]. destruct P1 as [P1|P1]; [left|right]; intuition lia. }
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - exact Hb.
  - split; intros; apply Nm; tauto.
  - left. congruence.
  - rewrite Etot, Eo, Ea. exact (kx_total _ _ _ _ _ _ X).
  - rewrite Et, Eo, Ea. exact (kx_tout _ _ _ _ _ _ X).
  - intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (A & _). split; [congruence|].
    split; [intros P; apply Nm; unfold ik_pre_mode; tauto|].
    split; intros P; apply Nm; unfold ik_pre_mode; tauto.
  - intros _ P. apply Nm; tauto.
  - intros _ P. apply Nm; unfold ik_pre_mode; tauto.
  - intros _ P. apply Nm; unfold ik_pre_mode; tauto.
  - intros W _. apply Hpost; auto.
  - intros W _. right. apply Hpost; auto.
  - intros W. unfold ik_trail. split; [|split]; intros E; apply Nm; tauto.
Qed.

(* LEN_ -> LEN keeps mwf3 *)
Lemma ikc_mwf3_len m : mwf3 m -> m_mode m = LEN_ -> mwf3 (set_mode m LEN).
Proof.
  intros [W S] Hm.
  assert (D : decode_mode (m_mode m)) by (unfold decode_mode; left; exact Hm).
  assert (Hr: HEAD <= LEN <= SYNC) by (unfold HEAD, SYNC, LEN; lia).
  pose proof (Inv.md_tables _ (Inv.mw_md _ W) D) as T.
  assert (Hne: forall P: Prop,
    LEN = LENLENS \/ LEN = CODELENS \/ LEN = LENEXT \/ LEN = DIST \/ LEN = DISTEXT \/ LEN = MATCH -> P).
  { intros P H. exfalso. unfold LENLENS, CODELENS, LENEXT, DIST, DISTEXT, MATCH, LEN in *. lia. }
  assert (O: m_out m = m_aout m).
  { apply Inv.mwf_out_eq; [exact W | | | ]; rewrite Hm; unfold LENGTH, DONE, BAD, LEN_; lia. }
  split.
  - apply (MwfLemmas.mwf_set_mode m LEN W Hr);
      [ intro; apply Hne; tauto | intro; apply Hne; tauto | intros _; exact T
      | intro; apply Hne; tauto | intro; apply Hne; tauto | intro; apply Hne; tauto
      | intro; apply Hne; tauto | intro; apply Hne; tauto | intro; apply Hne; tauto
      | intro; apply Hne; tauto | intro; apply Hne; tauto | left; exact O ].
  - destruct S as [A B C E]. cbn [set_mode upd_s m_s set_m_s].
    constructor; cbn [i_mode i_wbits i_wsize i_wrap i_win i_length i_offset i_lencode i_lenbits set_i_mode].
    + intro F. exfalso. unfold HEAD, LEN in *. lia.
    + intros _. destruct (B D) as (sz & S1 & S2 & S3). exists sz. split; [exact S1|]. split; [exact S2|].
      exact S3.
    + intro F. exfalso. unfold LENEXT, LEN in *. lia.
    + intro F. exfalso. unfold DISTEXT, LEN in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Ltac ikc_red :=
  unfold m_mode, m_have, m_left in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       set_m_ret set_m_out set_m_tout set_m_ow
       upd_s upd_h set_mode set_leave set_bad dropbits andb negb
       i_mode i_wrap i_head i_length i_offset i_extra i_back i_was i_codes i_lencode i_distcode
       i_lenbits i_distbits i_flags i_total i_check
       set_i_mode set_i_length set_i_offset set_i_extra set_i_back set_i_was] in *.

Ltac ikc_u32s :=
  repeat match goal with
  | |- context [u32 ?x] => lazymatch x with context [u32 _] => fail | _ => rewrite (ikc_u32 x) by lia end
  end.

Ltac ikc_side :=
  ikc_red;
  unfold ikc_md, decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, BAD, DONE, MEM,
    Zlib.proof.inflate.Model.TYPE, Z_OK, Z_STREAM_END, Z_DATA_ERROR in *;
  intros;
  repeat match goal with H: ?A -> _, H2: ?A |- _ =>
    lazymatch type of A with Prop => specialize (H H2) end end;
  ikc_u32s;
  first [assumption | reflexivity | discriminate | lia | (exfalso; lia) | congruence | idtac].

Ltac ikc_fin KX := cbn [stepx_post]; apply KX; ikc_side.
Ltac ikc_go KX := lazymatch goal with |- Kx _ _ _ _ _ _ => apply KX; ikc_side | _ => ikc_side end.

Lemma ikc_01 : (0 =? 1) = false.
Proof. reflexivity. Qed.

Lemma ikc_lit (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = LIT ->
  stepx_post wrap src pos out a0 (c_LIT m).
Proof.
  intros Hc Hi Hn Hb Hl Ho X Hmd.
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_LIT. destruct (m_left m =? 0); ikc_fin KX.
Qed.

Lemma ikc_match (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = MATCH ->
  stepx_post wrap src pos out a0 (c_MATCH m).
Proof.
  intros Hc Hi Hn Hb Hl Ho X Hmd.
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_MATCH. cbv beta zeta.
  destruct (m_left m =? 0); [ikc_fin KX|].
  repeat (cbv beta iota zeta;
    match goal with
    | |- stepx_post _ _ _ _ _ (IBrk (if ?c then _ else _)) => destruct c; ikc_fin KX
    | |- stepx_post _ _ _ _ _ (IBrk _) => ikc_fin KX
    | |- context [copy_bytes ?a ?b ?c ?d] => destruct (copy_bytes a b c d)
    | |- stepx_post _ _ _ _ _ (if ?c then _ else _) => destruct c
    | |- stepx_post _ _ _ _ _ (match (if ?c then _ else _) with _ => _ end) => destruct c
    end).
Qed.

Lemma ikc_distext (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = DISTEXT ->
  0 <= i_extra (m_s m) <= 15 ->
  stepx_post wrap src pos out a0 (c_DISTEXT m).
Proof.
  intros Hc Hi Hn Hb Hl Ho X Hmd Hx.
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_DISTEXT. cbv beta zeta.
  destruct (negb (i_extra (m_s m) =? 0)).
  - destruct (ikc_nbk KIT src pos inp (i_extra (m_s m)) m Hc Hi Hn Bf Hx Hb)
      as (nx & h & b & lv & E & R & C & B & N & D).
    rewrite E.
    destruct C as [->|[-> C]].
    + ikc_red. rewrite Z.eqb_refl. ikc_fin KX.
    + assert (BD: ik_bitbuf src (pos + nx) (Z.shiftr h (i_extra (m_s m))) (b - i_extra (m_s m)))
        by (apply (kk_bb_drop KIT); [lia|exact B]).
      ikc_red. rewrite Hl, ikc_01. apply (ikc_match KIT wrap src pos out a0 inp); ikc_go KX.
  - apply (ikc_match KIT wrap src pos out a0 inp); ikc_go KX.
Qed.

Lemma ikc_dist (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = DIST ->
  ikc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  stepx_post wrap src pos out a0 (c_DIST lenfix_list distfix_list m).
Proof.
  intros Hc Hi Hn Hb Hl Ho X Hmd [Hrb T].
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  assert (T1 : forall i, 0 <= i < 2 ^ i_distbits (m_s m) ->
    0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) i) <= 15).
  { intros i Hi'. rewrite ikc_get_eq. apply (T i Hi'). }
  unfold c_DIST. cbv beta zeta.
  destruct (lookup1 _ _ _ _ m) as [[here m1] ok] eqn:L1.
  destruct (ikc_lk1k KIT src pos inp _ _ m here m1 ok L1 Hc Hi Hn Bf ltac:(lia) Hb T1)
    as (nx1 & h1 & b1 & lv1 & -> & B1 & OK1 & NOK1 & BB1 & N1 & D1).
  destruct ok; [|rewrite (NOK1 eq_refl); cbv beta iota zeta delta [negb]; ikc_fin KX].
  destruct (OK1 eq_refl) as (-> & Hh & i & Hi' & Eh). rewrite ikc_get_eq in Eh.
  destruct (T i Hi') as (Tb & To & Tl). rewrite <- Eh in Tb, To, Tl.
  cbv beta iota zeta.
  destruct (Z.land (e_op here) 240 =? 0) eqn:EL.
  - assert (Lk : islink DISTS (e_op here) = true) by (unfold islink; rewrite EL; reflexivity).
    destruct (Tl Lk) as (Te & Tj).
    destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2] eqn:L2.
    pose proof (ikc_lk2k KIT src pos inp _ _ _ _ _ _ L2 Hc) as LK2.
    cbn [m_bits m_s m_inp m_nx m_hold m_leave set_m_leave set_m_bits set_m_hold set_m_nx] in LK2.
    spec LK2; [assumption|]. spec LK2; [lia|]. spec LK2; [assumption|]. spec LK2; [lia|].
    spec LK2; [lia|]. spec LK2; [lia|].
    spec LK2. { intros j Hj. rewrite ikc_get_eq. rewrite Te. apply (Tj j Hj). }
    destruct LK2 as (nx2 & h2' & b2 & lv2 & -> & B2 & OK2 & NOK2 & BB2 & N2 & D2).
    destruct ok2; [|rewrite (NOK2 eq_refl); cbv beta iota zeta delta [negb]; ikc_fin KX].
    destruct (OK2 eq_refl) as (-> & Hh2a & Hh2b).
    cbv beta iota zeta delta [negb].
    assert (BD: ik_bitbuf src (pos + nx2) (Z.shiftr (Z.shiftr h2' (e_bits here)) (e_bits h2))
                  (b2 - e_bits here - e_bits h2))
      by (apply (kk_bb_drop KIT); [lia|]; apply (kk_bb_drop KIT); [lia|exact BB2]).
    destruct (Z.land (e_op h2) 64 =? 0); [|ikc_fin KX].
    apply (ikc_distext KIT wrap src pos out a0 inp); ikc_go KX. apply ikc_land15.
  - cbv beta iota zeta delta [negb].
    assert (BD: ik_bitbuf src (pos + nx1) (Z.shiftr h1 (e_bits here)) (b1 - e_bits here))
      by (apply (kk_bb_drop KIT); [lia|exact BB1]).
    destruct (Z.land (e_op here) 64 =? 0); [|ikc_fin KX].
    apply (ikc_distext KIT wrap src pos out a0 inp); ikc_go KX. apply ikc_land15.
Qed.

Lemma ikc_lenext (KIT: ik_kit) wrap src pos out a0 inp m :
  ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = LENEXT ->
  0 <= i_extra (m_s m) <= 15 ->
  ikc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  stepx_post wrap src pos out a0 (c_LENEXT lenfix_list distfix_list m).
Proof.
  intros Hc Hi Hn Hb Hl Ho X Hmd Hx Td.
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  unfold c_LENEXT. cbv beta zeta.
  destruct (negb (i_extra (m_s m) =? 0)).
  - destruct (ikc_nbk KIT src pos inp (i_extra (m_s m)) m Hc Hi Hn Bf Hx Hb)
      as (nx & h & b & lv & E & R & C & B & N & D).
    rewrite E.
    destruct C as [->|[-> C]].
    + ikc_red. rewrite Z.eqb_refl. ikc_fin KX.
    + assert (BD: ik_bitbuf src (pos + nx) (Z.shiftr h (i_extra (m_s m))) (b - i_extra (m_s m)))
        by (apply (kk_bb_drop KIT); [lia|exact B]).
      ikc_red. rewrite Hl, ikc_01. apply (ikc_dist KIT wrap src pos out a0 inp); ikc_go KX.
  - apply (ikc_dist KIT wrap src pos out a0 inp); ikc_go KX.
Qed.

Lemma ikc_len (KIT: ik_kit) (F: fastx_stmt) wrap src pos out a0 inp aout m :
  ctx_ok src pos inp -> Kc wrap src pos inp aout m -> mwf3 m ->
  m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = LEN ->
  ikc_tab LENS (i_codes (m_s m)) (i_lencode (m_s m)) (i_lenbits (m_s m)) ->
  ikc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  stepx_post wrap src pos out a0 (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros Hc K Hw Hi Hn Hb Hl Ho X Hmd [Hrb T] Td.
  unfold c_LEN.
  destruct (andb (andb (6 <=? m_have m) (258 <=? m_left m)) (m_bits m <? 8)) eqn:EF.
  { apply andb_prop in EF as [EF E3]. apply andb_prop in EF as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
    cbn [stepx_post]. exact (F wrap src pos out a0 inp aout m Hc K X Hw Hl Hmd Ho E1 E2 E3). }
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  assert (T1 : forall i, 0 <= i < 2 ^ i_lenbits (m_s m) ->
    0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) i) <= 15).
  { intros i Hi'. rewrite ikc_get_eq. apply (T i Hi'). }
  cbv beta zeta.
  destruct (lookup1 _ _ _ _ _) as [[here m1] ok] eqn:L1.
  pose proof (ikc_lk1k KIT src pos inp _ _ _ here m1 ok L1 Hc) as LK1.
  cbn [m_bits m_s m_inp m_nx m_hold m_leave upd_s set_m_s i_codes i_lencode i_lenbits set_i_back] in LK1.
  specialize (LK1 Hi Hn Bf ltac:(lia) Hb T1).
  destruct LK1 as (nx1 & h1 & b1 & lv1 & -> & B1 & OK1 & NOK1 & BB1 & N1 & D1).
  destruct ok; [|rewrite (NOK1 eq_refl); cbv beta iota zeta delta [negb]; ikc_fin KX].
  destruct (OK1 eq_refl) as (-> & Hh & i & Hi' & Eh). rewrite ikc_get_eq in Eh.
  cbn [m_s upd_s set_m_s i_codes set_i_back] in Eh.
  destruct (T i Hi') as (Tb & To & Tl). rewrite <- Eh in Tb, To, Tl.
  cbv beta iota zeta.
  destruct (andb (negb (e_op here =? 0)) (Z.land (e_op here) 240 =? 0)) eqn:EL.
  - assert (Lk : islink LENS (e_op here) = true) by (unfold islink; rewrite <- EL; reflexivity).
    destruct (Tl Lk) as (Te & Tj).
    destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2] eqn:L2.
    pose proof (ikc_lk2k KIT src pos inp _ _ _ _ _ _ L2 Hc) as LK2.
    cbn [m_bits m_s m_inp m_nx m_hold m_leave upd_s set_m_s set_m_leave set_m_bits set_m_hold set_m_nx
         i_codes i_lencode set_i_back] in LK2.
    spec LK2; [assumption|]. spec LK2; [lia|]. spec LK2; [assumption|]. spec LK2; [lia|].
    spec LK2; [lia|]. spec LK2; [lia|].
    spec LK2. { intros j Hj. rewrite ikc_get_eq. rewrite Te. apply (Tj j Hj). }
    destruct LK2 as (nx2 & h2' & b2 & lv2 & -> & B2 & OK2 & NOK2 & BB2 & N2 & D2).
    destruct ok2; [|rewrite (NOK2 eq_refl); cbv beta iota zeta delta [negb]; ikc_fin KX].
    destruct (OK2 eq_refl) as (-> & Hh2a & Hh2b).
    cbv beta iota zeta delta [negb].
    assert (BD: ik_bitbuf src (pos + nx2) (Z.shiftr (Z.shiftr h2' (e_bits here)) (e_bits h2))
                  (b2 - e_bits here - e_bits h2))
      by (apply (kk_bb_drop KIT); [lia|]; apply (kk_bb_drop KIT); [lia|exact BB2]).
    destruct (e_op h2 =? 0); [ikc_fin KX|].
    destruct (Z.land (e_op h2) 32 =? 0); [|ikc_fin KX].
    destruct (Z.land (e_op h2) 64 =? 0); [|ikc_fin KX].
    apply (ikc_lenext KIT wrap src pos out a0 inp); ikc_go KX. apply ikc_land15.
  - cbv beta iota zeta delta [negb].
    assert (BD: ik_bitbuf src (pos + nx1) (Z.shiftr h1 (e_bits here)) (b1 - e_bits here))
      by (apply (kk_bb_drop KIT); [lia|exact BB1]).
    destruct (e_op here =? 0); [ikc_fin KX|].
    destruct (Z.land (e_op here) 32 =? 0); [|ikc_fin KX].
    destruct (Z.land (e_op here) 64 =? 0); [|ikc_fin KX].
    apply (ikc_lenext KIT wrap src pos out a0 inp); ikc_go KX. apply ikc_land15.
Qed.

Lemma ikc_len_ (KIT: ik_kit) (F: fastx_stmt) wrap src pos out a0 inp aout m :
  ctx_ok src pos inp -> Kc wrap src pos inp aout m -> mwf3 m ->
  m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 ->
  m_leave m = 0 -> m_out m = m_aout m -> Kx wrap src pos out a0 m -> m_mode m = LEN_ ->
  m_ret m = Z_OK ->
  ikc_tab LENS (i_codes (m_s m)) (i_lencode (m_s m)) (i_lenbits (m_s m)) ->
  ikc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  stepx_post wrap src pos out a0 (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros Hc K Hw Hi Hn Hb Hl Ho X Hmd Hret Tl Td.
  assert (Hd: decode_mode (m_mode m)) by (rewrite Hmd; unfold decode_mode; tauto).
  pose proof (ikc_Kx wrap src pos out a0 m X Hd Ho) as KX.
  pose proof (kx_buf _ _ _ _ _ _ X) as Bf.
  pose proof (ikc_mwf3_len m Hw Hmd) as Hw'.
  unfold c_LEN_.
  apply (ikc_len KIT F wrap src pos out a0 inp aout); try exact Hw'.
  all: try (eapply ikc_Kc; [exact K|..]; ikc_side; fail).
  all: ikc_go KX.
Qed.

Lemma ikx_dec : decx_stmt.
Proof.
  intros KIT F wrap src pos out a0 inp aout flush m Hc K X Hw Hl Hmd.
  pose proof (proj1 Hw) as W.
  destruct (Inv.md_tables _ (Inv.mw_md _ W) Hmd) as [TL TD].
  apply ikc_tab_of in TL. apply ikc_tab_of in TD.
  pose proof (Inv.sw_extra _ (Inv.mw_s _ W)) as Hx.
  assert (Hne : m_mode m <> LENGTH /\ m_mode m <> DONE /\ m_mode m <> BAD /\ m_mode m <> MEM).
  { unfold decode_mode in Hmd.
    repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end; rewrite Hmd;
    unfold LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, LENGTH, DONE, BAD, MEM; repeat split; lia. }
  destruct Hne as (N1 & N2 & N3 & N4).
  pose proof (Inv.mwf_out_eq m W N1 N2 N3) as Ho.
  pose proof (kc_ret _ _ _ _ _ _ K N3 N2) as Hret.
  pose proof (kc_bits _ _ _ _ _ _ K N3 N4) as Hb.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hi.
  pose proof (Inv.mw_nx _ W) as Hn. rewrite Hi in Hn.
  unfold decode_mode in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 _ _ _ m) with (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_len_ KIT F wrap src pos out a0 inp aout); auto.
  - replace (stepf2 _ _ _ m) with (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_len KIT F wrap src pos out a0 inp aout); auto.
  - replace (stepf2 _ _ _ m) with (c_LENEXT lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_lenext KIT wrap src pos out a0 inp); auto.
  - replace (stepf2 _ _ _ m) with (c_DIST lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_dist KIT wrap src pos out a0 inp); auto.
  - replace (stepf2 _ _ _ m) with (c_DISTEXT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_distext KIT wrap src pos out a0 inp); auto.
  - replace (stepf2 _ _ _ m) with (c_MATCH m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_match KIT wrap src pos out a0 inp); auto.
  - replace (stepf2 _ _ _ m) with (c_LIT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (ikc_lit KIT wrap src pos out a0 inp); auto.
Qed.

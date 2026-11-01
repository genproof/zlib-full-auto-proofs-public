(* Law inflate_codes, theory part: the decoding cases LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the modes the cases of this group reach *)
Definition dc_md (x: Z) : Prop := decode_mode x \/ x = Zlib.proof.inflate.Model.TYPE \/ x = BAD.

Definition dc_P (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kc wrap src pos inp aout m' /\ (m_leave m' = 0 -> m_mode m' <> DICT)
  | IRet _ _ => False
  end.

Lemma dc_md_ne x : dc_md x -> x <> SYNC /\ x <> HEAD /\ x <> DICTID /\ x <> DICT.
Proof.
  unfold dc_md, decode_mode. intros H.
  repeat match type of H with _ \/ _ => destruct H as [H|H] end; subst x;
  unfold LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, BAD, Zlib.proof.inflate.Model.TYPE,
    SYNC, HEAD, DICTID, DICT; repeat split; lia.
Qed.

Lemma dc_Kc wrap src pos inp aout m m' :
  Kc wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) ->
  dc_md (m_mode m') ->
  (m_mode m' <> BAD -> m_mode m' <> DONE -> m_ret m' = Z_OK) ->
  (m_leave m' = 1 ->
     (m_mode m' = DONE -> m_ret m' = Z_STREAM_END) /\ (m_mode m' = BAD -> m_ret m' = Z_DATA_ERROR)) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> m_mode m' <> MEM -> 0 <= m_bits m' <= 31) ->
  (m_out m' <> m_aout m' -> 0 < m_nx m') ->
  Kc wrap src pos inp aout m'.
Proof.
  intros K Hi Ha Hw Hhd Hmd Hr Hrx Hmsg Hb Ho.
  destruct (dc_md_ne _ Hmd) as (N1 & N2 & N3 & N4).
  constructor; auto.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hhd; apply (kc_head _ _ _ _ _ _ K).
  - intros _ E; contradiction.
  - intros E; contradiction.
  - intros E; contradiction.
Qed.

Lemma dc_brk wrap src pos inp aout m' :
  Kc wrap src pos inp aout m' -> dc_md (m_mode m') -> dc_P wrap src pos inp aout (IBrk m').
Proof.
  intros K Hmd. destruct (dc_md_ne _ Hmd) as (_ & _ & _ & N). cbn [dc_P]. split; auto.
Qed.

Lemma dc_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small; lia. Qed.

Lemma dc_land15 x : 0 <= Z.land x 15 <= 15.
Proof.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 4) ltac:(lia)). change (Z.ones 4) with 15. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tables                                                                                          *)

Definition dc_get (codes: list entry) (t: tref) (i: Z) : entry :=
  match t with
  | TLenfix => Znth i lenfix_list
  | TDistfix => Znth i distfix_list
  | TCodes k => Znth (k + i) codes
  end.

Lemma dc_get_eq s t i : tab_entry lenfix_list distfix_list s t i = dc_get (i_codes s) t i.
Proof. destruct t; reflexivity. Qed.

(* what the lookups need of a valid table *)
Definition dc_tab (kind: Z) (codes: list entry) (t: tref) (rb: Z) : Prop :=
  1 <= rb <= 15 /\
  forall i, 0 <= i < 2 ^ rb ->
    0 <= e_bits (dc_get codes t i) <= 15 /\ 0 <= e_op (dc_get codes t i) /\
    (islink kind (e_op (dc_get codes t i)) = true ->
       e_bits (dc_get codes t i) = rb /\
       forall j, 0 <= j < 2 ^ e_op (dc_get codes t i) ->
         0 <= e_bits (dc_get codes t (e_val (dc_get codes t i) + j)) /\
         rb + e_bits (dc_get codes t (e_val (dc_get codes t i) + j)) <= 15).

Lemma dc_tab_of kind s t rb :
  tvalid kind lenfix_list distfix_list s t rb -> dc_tab kind (i_codes s) t rb.
Proof.
  intros (sz & _ & [R S T]). split; [exact R|]. intros i Hi.
  destruct (T i Hi) as [E F]. cbv zeta in F. rewrite dc_get_eq in E, F.
  destruct E as (E1 & E2 & E3).
  destruct (islink kind (e_op (dc_get (i_codes s) t i))) eqn:L.
  - destruct F as (F1 & F2 & F3 & F4). split; [lia|]. split; [lia|]. intros _. split; [exact F1|].
    intros j Hj. destruct (F4 j Hj) as (G1 & G2 & G3 & G4 & G5). rewrite dc_get_eq in G2, G4.
    destruct G2 as (_ & G2 & _). split; lia.
  - destruct F as (F1 & _). split; [lia|]. split; [lia|]. intros D; discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS and the lookups, in explicit form                                                      *)

Lemma dc_pull_bits m : 0 <= m_bits m <= 39 -> m_bits (pull m) = m_bits m + 8.
Proof. intros H. cbn [pull m_bits set_m_bits]. apply dc_u32. lia. Qed.

Lemma dc_nbf n k m :
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
      * pose proof (dc_pull_bits m Hb) as Hb'.
        destruct (IH (pull m) ltac:(lia) ltac:(lia)) as (nx' & h' & b' & lv' & E & R & C).
        rewrite E. exists nx', h', b', lv'. split; [destruct m; reflexivity|].
        cbn [pull m_leave set_m_nx set_m_hold set_m_bits] in C. lia.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|]. lia.
Qed.

Lemma dc_nb n m :
  0 <= n <= 15 -> 0 <= m_bits m <= 31 ->
  exists nx h b lv,
    needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\ (lv = 1 \/ (lv = m_leave m /\ n <= b)).
Proof.
  intros Hn Hb. destruct (dc_nbf n 4 m ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx & h & b & lv & E & R & C).
  exists nx, h, b, lv. split; [exact E|]. lia.
Qed.

Lemma dc_lk1f k t nb m :
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
      * pose proof (dc_pull_bits m ltac:(lia)) as Hb'.
        specialize (IH (pull m) Hnb ltac:(lia) F ltac:(lia)).
        destruct (lookup1_f k lenfix_list distfix_list t nb (pull m)) as [[h m'] ok].
        destruct IH as (nx' & h' & b' & lv' & E & R & C1 & C2).
        exists nx', h', b', lv'. split; [rewrite E; destruct m; reflexivity|].
        cbn [pull m_leave m_s set_m_nx set_m_hold set_m_bits] in C1. split; [lia|]. split; [|exact C2].
        intros T. destruct (C1 T) as (C3 & C4 & C5). split; [exact C3|]. split; [lia|exact C5].
Qed.

Lemma dc_lk1 t nb m :
  0 <= nb -> 0 <= m_bits m <= 31 ->
  (forall i, 0 <= i < 2 ^ nb -> 0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t i) <= 15) ->
  let '(here, m', ok) := lookup1 lenfix_list distfix_list t nb m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ e_bits here <= b /\
       exists i, 0 <= i < 2 ^ nb /\ here = tab_entry lenfix_list distfix_list (m_s m) t i) /\
    (ok = false -> lv = 1).
Proof. intros. apply dc_lk1f; auto. cbn. lia. Qed.

Lemma dc_subrange x b o : 0 <= b -> 0 <= o -> 0 <= Z.shiftr (x mod 2 ^ (b + o)) b < 2 ^ o.
Proof.
  intros Hb Ho. rewrite Z.shiftr_div_pow2 by lia.
  assert (P: 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (Q: 0 <= x mod 2 ^ (b + o) < 2 ^ (b + o)) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r in Q |- * by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; nia.
Qed.

Lemma dc_lk2f k t last m :
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
  - cbn [lookup2_f]. pose proof (dc_subrange (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    unfold bitsn. specialize (F _ BR).
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [|discriminate]. intros _. lia.
  - cbn [lookup2_f]. pose proof (dc_subrange (m_hold m) (e_bits last) (e_op last) ltac:(lia) Ho) as BR.
    pose proof (F _ BR) as Fb. unfold bitsn in *.
    destruct (Z.leb_spec (e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t
                (e_val last + Z.shiftr (m_hold m mod 2 ^ (e_bits last + e_op last)) (e_bits last)))) (m_bits m))
      as [L|L].
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. split; [|discriminate]. intros _. lia.
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. split; [discriminate|]. auto.
      * pose proof (dc_pull_bits m ltac:(lia)) as Hb'.
        specialize (IH (pull m) ltac:(lia) ltac:(lia) Ho F ltac:(lia)).
        destruct (lookup2_f k lenfix_list distfix_list t last (pull m)) as [[h m'] ok].
        destruct IH as (nx' & h' & b' & lv' & E & R & C1 & C2).
        exists nx', h', b', lv'. split; [rewrite E; destruct m; reflexivity|].
        cbn [pull m_leave m_s set_m_nx set_m_hold set_m_bits] in C1. split; [lia|]. split; [exact C1|exact C2].
Qed.

Lemma dc_lk2 t last m :
  0 <= e_bits last <= m_bits m -> m_bits m <= 31 -> 0 <= e_op last ->
  (forall j, 0 <= j < 2 ^ e_op last ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) /\
     e_bits last + e_bits (tab_entry lenfix_list distfix_list (m_s m) t (e_val last + j)) <= 15) ->
  let '(here, m', ok) := lookup2 lenfix_list distfix_list t last m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_bits m <= b <= Z.max (m_bits m) 22 /\
    (ok = true -> lv = m_leave m /\ 0 <= e_bits here /\ e_bits last + e_bits here <= b) /\
    (ok = false -> lv = 1).
Proof. intros. apply dc_lk2f; auto. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                       *)

Ltac dc_red :=
  unfold m_mode, m_have, m_left in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       set_m_ret set_m_out set_m_tout set_m_ow
       upd_s upd_h set_mode set_leave set_bad dropbits andb negb
       i_mode i_wrap i_head i_length i_offset i_extra i_back i_was i_codes i_lencode i_distcode
       i_lenbits i_distbits
       set_i_mode set_i_length set_i_offset set_i_extra set_i_back set_i_was] in *.

Ltac dc_u32s :=
  repeat match goal with
  | |- context [u32 ?x] => lazymatch x with context [u32 _] => fail | _ => rewrite (dc_u32 x) by lia end
  end.

Ltac dc_side :=
  dc_red;
  unfold dc_md, decode_mode, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, BAD, DONE, MEM,
    Zlib.proof.inflate.Model.TYPE, Z_OK, Z_STREAM_END, Z_DATA_ERROR in *;
  intros;
  repeat match goal with H: ?A -> _, H2: ?A |- _ => specialize (H H2) end;
  dc_u32s;
  first [assumption | reflexivity | discriminate | lia | (exfalso; lia) | congruence | idtac].

Ltac dc_kc := eapply dc_Kc; [eassumption|..]; dc_side.
Ltac dc_fin := apply dc_brk; [dc_kc|]; dc_side.

Lemma dc_01 : (0 =? 1) = false.
Proof. reflexivity. Qed.

Lemma dc_lit wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = LIT -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m ->
  dc_P wrap src pos inp aout (c_LIT m).
Proof.
  intros K Hmd Hl Hret Hb Ho. unfold c_LIT. destruct (m_left m =? 0); dc_fin.
Qed.

Lemma dc_match wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = MATCH -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m ->
  dc_P wrap src pos inp aout (c_MATCH m).
Proof.
  intros K Hmd Hl Hret Hb Ho. unfold c_MATCH. cbv beta zeta.
  destruct (m_left m =? 0); [dc_fin|].
  repeat (cbv beta iota zeta;
    match goal with
    | |- dc_P _ _ _ _ _ (IBrk (if ?c then _ else _)) => destruct c; dc_fin
    | |- dc_P _ _ _ _ _ (IBrk _) => dc_fin
    | |- context [copy_bytes ?a ?b ?c ?d] => destruct (copy_bytes a b c d)
    | |- dc_P _ _ _ _ _ (if ?c then _ else _) => destruct c
    | |- dc_P _ _ _ _ _ (match (if ?c then _ else _) with _ => _ end) => destruct c
    end).
Qed.

Lemma dc_distext wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = DISTEXT -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m -> 0 <= i_extra (m_s m) <= 15 ->
  dc_P wrap src pos inp aout (c_DISTEXT m).
Proof.
  intros K Hmd Hl Hret Hb Ho Hx. unfold c_DISTEXT. cbv beta zeta.
  destruct (negb (i_extra (m_s m) =? 0)).
  - destruct (dc_nb (i_extra (m_s m)) m Hx Hb) as (nx & h & b & lv & E & R & C). rewrite E.
    destruct C as [->|[-> C]].
    + dc_red. rewrite Z.eqb_refl. dc_fin.
    + dc_red. rewrite Hl, dc_01. apply dc_match; [dc_kc|..]; dc_side.
  - apply dc_match; [dc_kc|..]; dc_side.
Qed.

Lemma dc_dist wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = DIST -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m ->
  dc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  dc_P wrap src pos inp aout (c_DIST lenfix_list distfix_list m).
Proof.
  intros K Hmd Hl Hret Hb Ho [Hrb T]. unfold c_DIST. cbv beta zeta.
  pose proof (dc_lk1 (i_distcode (m_s m)) (i_distbits (m_s m)) m ltac:(lia) Hb) as L1.
  spec L1. { intros i Hi. rewrite dc_get_eq. apply (T i Hi). }
  revert L1. destruct (lookup1 _ _ _ _ m) as [[here m1] ok].
  intros (nx1 & h1 & b1 & lv1 & -> & B1 & OK1 & NOK1).
  destruct ok; [|rewrite (NOK1 eq_refl); cbv beta iota zeta delta [negb]; dc_fin].
  destruct (OK1 eq_refl) as (-> & Hh & i & Hi & Eh). rewrite dc_get_eq in Eh.
  destruct (T i Hi) as (Tb & To & Tl). rewrite <- Eh in Tb, To, Tl.
  cbv beta iota zeta.
  destruct (Z.land (e_op here) 240 =? 0) eqn:EL.
  - assert (Lk : islink DISTS (e_op here) = true) by (unfold islink; rewrite EL; reflexivity).
    destruct (Tl Lk) as (Te & Tj).
    pose proof (dc_lk2 (i_distcode (m_s m)) here
      (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx1) h1) b1) (m_leave m))) as L2.
    cbn [m_bits m_s set_m_leave set_m_bits set_m_hold set_m_nx] in L2.
    spec L2; [lia|]. spec L2; [lia|]. spec L2; [lia|].
    spec L2. { intros j Hj. rewrite dc_get_eq. rewrite Te. apply (Tj j Hj). }
    revert L2. destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2].
    intros (nx2 & h2' & b2 & lv2 & -> & B2 & OK2 & NOK2).
    destruct ok2; [|rewrite (NOK2 eq_refl); cbv beta iota zeta delta [negb]; dc_fin].
    destruct (OK2 eq_refl) as (-> & Hh2a & Hh2b).
    cbv beta iota zeta delta [negb].
    destruct (Z.land (e_op h2) 64 =? 0); [|dc_fin].
    apply dc_distext; [dc_kc|..]; dc_side. apply dc_land15.
  - cbv beta iota zeta delta [negb].
    destruct (Z.land (e_op here) 64 =? 0); [|dc_fin].
    apply dc_distext; [dc_kc|..]; dc_side. apply dc_land15.
Qed.

Lemma dc_lenext wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> m_mode m = LENEXT -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m -> 0 <= i_extra (m_s m) <= 15 ->
  dc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  dc_P wrap src pos inp aout (c_LENEXT lenfix_list distfix_list m).
Proof.
  intros K Hmd Hl Hret Hb Ho Hx Td. unfold c_LENEXT. cbv beta zeta.
  destruct (negb (i_extra (m_s m) =? 0)).
  - destruct (dc_nb (i_extra (m_s m)) m Hx Hb) as (nx & h & b & lv & E & R & C). rewrite E.
    destruct C as [->|[-> C]].
    + dc_red. rewrite Z.eqb_refl. dc_fin.
    + dc_red. rewrite Hl, dc_01. apply dc_dist; [dc_kc|..]; dc_side.
  - apply dc_dist; [dc_kc|..]; dc_side.
Qed.

Lemma dc_len wrap src pos inp aout m :
  fast_kc_stmt ->
  Kc wrap src pos inp aout m -> m_mode m = LEN -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m ->
  dc_tab LENS (i_codes (m_s m)) (i_lencode (m_s m)) (i_lenbits (m_s m)) ->
  dc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  dc_P wrap src pos inp aout (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros F K Hmd Hl Hret Hb Ho [Hrb T] Td. unfold c_LEN.
  destruct ((6 <=? m_have m) && (258 <=? m_left m) && (m_bits m <? 8))%bool.
  { destruct (F wrap src pos inp aout m K Hl Hmd Ho) as (K' & L' & M'). cbv zeta in K', L', M' |- *.
    apply dc_brk; [exact K'|]. unfold dc_md, decode_mode. clear -M'. tauto. }
  cbv beta zeta.
  pose proof (dc_lk1 (i_lencode (m_s m)) (i_lenbits (m_s m)) (upd_s m (fun s => set_i_back s 0))
    ltac:(lia) Hb) as L1.
  spec L1. { intros i Hi. rewrite dc_get_eq. apply (T i Hi). }
  revert L1. destruct (lookup1 _ _ _ _ _) as [[here m1] ok].
  intros (nx1 & h1 & b1 & lv1 & -> & B1 & OK1 & NOK1).
  destruct ok; [|rewrite (NOK1 eq_refl); cbv beta iota zeta delta [negb]; dc_fin].
  destruct (OK1 eq_refl) as (-> & Hh & i & Hi & Eh). rewrite dc_get_eq in Eh. cbn [m_s upd_s set_m_s i_codes set_i_back] in Eh.
  destruct (T i Hi) as (Tb & To & Tl). rewrite <- Eh in Tb, To, Tl.
  cbv beta iota zeta.
  destruct (negb (e_op here =? 0) && (Z.land (e_op here) 240 =? 0))%bool eqn:EL.
  - assert (Lk : islink LENS (e_op here) = true) by (unfold islink; rewrite <- EL; reflexivity).
    destruct (Tl Lk) as (Te & Tj).
    pose proof (dc_lk2 (i_lencode (m_s m)) here
      (set_m_leave (set_m_bits (set_m_hold (set_m_nx (upd_s m (fun s => set_i_back s 0)) nx1) h1) b1)
         (m_leave (upd_s m (fun s => set_i_back s 0))))) as L2.
    cbn [m_bits m_s m_leave upd_s set_m_s set_m_leave set_m_bits set_m_hold set_m_nx i_lencode set_i_back] in L2, B1 |- *.
    spec L2; [lia|]. spec L2; [lia|]. spec L2; [lia|].
    spec L2. { intros j Hj. rewrite dc_get_eq. rewrite Te. apply (Tj j Hj). }
    revert L2. destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2].
    intros (nx2 & h2' & b2 & lv2 & -> & B2 & OK2 & NOK2).
    destruct ok2; [|rewrite (NOK2 eq_refl); cbv beta iota zeta delta [negb]; dc_fin].
    destruct (OK2 eq_refl) as (-> & Hh2a & Hh2b).
    cbv beta iota zeta delta [negb].
    destruct (e_op h2 =? 0); [dc_fin|].
    destruct (Z.land (e_op h2) 32 =? 0); [|dc_fin].
    destruct (Z.land (e_op h2) 64 =? 0); [|dc_fin].
    apply dc_lenext; [dc_kc|..]; dc_side. apply dc_land15.
  - cbv beta iota zeta delta [negb].
    destruct (e_op here =? 0); [dc_fin|].
    destruct (Z.land (e_op here) 32 =? 0); [|dc_fin].
    destruct (Z.land (e_op here) 64 =? 0); [|dc_fin].
    apply dc_lenext; [dc_kc|..]; dc_side. apply dc_land15.
Qed.

Lemma dc_len_ wrap src pos inp aout m :
  fast_kc_stmt ->
  Kc wrap src pos inp aout m -> m_mode m = LEN_ -> m_leave m = 0 -> m_ret m = Z_OK ->
  0 <= m_bits m <= 31 -> m_out m = m_aout m ->
  dc_tab LENS (i_codes (m_s m)) (i_lencode (m_s m)) (i_lenbits (m_s m)) ->
  dc_tab DISTS (i_codes (m_s m)) (i_distcode (m_s m)) (i_distbits (m_s m)) ->
  dc_P wrap src pos inp aout (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros F K Hmd Hl Hret Hb Ho Tl Td. unfold c_LEN_.
  apply dc_len; [exact F|dc_kc|..]; dc_side.
Qed.

Lemma dc_post wrap src pos inp aout m o :
  dc_P wrap src pos inp aout o -> step_post wrap src pos inp aout m o.
Proof. destruct o; cbn; tauto. Qed.

Lemma th_dec : dec_stmt.
Proof.
  intros F wrap src pos inp aout flush m Hc K Hw Hl Hmd.
  pose proof (proj1 Hw) as W.
  destruct (Inv.md_tables _ (Inv.mw_md _ W) Hmd) as [TL TD].
  apply dc_tab_of in TL. apply dc_tab_of in TD.
  pose proof (Inv.sw_extra _ (Inv.mw_s _ W)) as Hx.
  assert (Hne : m_mode m <> LENGTH /\ m_mode m <> DONE /\ m_mode m <> BAD /\ m_mode m <> MEM).
  { unfold decode_mode in Hmd.
    repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end; rewrite Hmd;
    unfold LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, LENGTH, DONE, BAD, MEM; repeat split; lia. }
  destruct Hne as (N1 & N2 & N3 & N4).
  pose proof (Inv.mwf_out_eq m W N1 N2 N3) as Ho.
  pose proof (kc_ret _ _ _ _ _ _ K N3 N2) as Hret.
  pose proof (kc_bits _ _ _ _ _ _ K N3 N4) as Hb.
  unfold decode_mode in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 _ _ _ m) with (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_len_; auto.
  - replace (stepf2 _ _ _ m) with (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_len; auto.
  - replace (stepf2 _ _ _ m) with (c_LENEXT lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_lenext; auto.
  - replace (stepf2 _ _ _ m) with (c_DIST lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_dist; auto.
  - replace (stepf2 _ _ _ m) with (c_DISTEXT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_distext; auto.
  - replace (stepf2 _ _ _ m) with (c_MATCH m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_match; auto.
  - replace (stepf2 _ _ _ m) with (c_LIT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply dc_post, dc_lit; auto.
Qed.

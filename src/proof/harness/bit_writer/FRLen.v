(* The fixed-block run theory (FRDefs.v): the passes of LEN (the fast path, or one fixed code: a literal to LIT,
   the tail's first code into LENEXT or BAD) and LIT. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the projections and setters of the machine and of the state that the passes of LEN and LIT use *)
Ltac fr_simp :=
  unfold m_mode, upd_s, set_mode, set_leave, set_bad, dropbits;
  cbn [m_s m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
       set_m_s set_m_nx set_m_ow set_m_hold set_m_bits set_m_ret set_m_leave set_m_msg
       upd_s set_mode set_leave set_bad dropbits m_mode
       i_mode i_wsize i_whave i_wnext i_win i_wdata i_wbits i_sane i_lencode i_lenbits i_distcode i_distbits
       i_length i_extra i_back set_i_back set_i_length set_i_mode set_i_extra].

Lemma fr_u32_small : forall x, 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

(* the window fields are kept by the setters of mode, length, extra and back *)
Lemma fr_wsame_set : forall s s0 md ln ex bk,
  fr_wsame s s0 ->
  fr_wsame s (set_i_mode s0 md) /\ fr_wsame s (set_i_length s0 ln) /\ fr_wsame s (set_i_extra s0 ex) /\
  fr_wsame s (set_i_back s0 bk).
Proof. intros. unfold fr_wsame in *. fr_simp. tauto. Qed.

Lemma fr_fixed_set : forall s md ln ex bk,
  fr_fixed s ->
  fr_fixed (set_i_mode s md) /\ fr_fixed (set_i_length s ln) /\ fr_fixed (set_i_extra s ex) /\
  fr_fixed (set_i_back s bk).
Proof. intros. unfold fr_fixed in *. fr_simp. tauto. Qed.

(* the bits of a table entry's op that LEN tests: an invalid code (op & 112 = 64), a length (op = 16 + extra) *)
Lemma fr_op_bad : forall op, Z.land op 112 = 64 ->
  (op =? 0) = false /\ (Z.land op 240 =? 0) = false /\ (Z.land op 32 =? 0) = true /\ (Z.land op 64 =? 0) = false.
Proof.
  intros op H.
  assert (A : forall k, Z.land k 112 = k -> Z.land op k = Z.land (Z.land op 112) k).
  { intros k Hk. rewrite <- Z.land_assoc, (Z.land_comm 112 k), Hk. reflexivity. }
  assert (H240 : Z.land (Z.land op 240) 112 = 64) by (rewrite <- Z.land_assoc; exact H).
  rewrite (A 32 eq_refl), (A 64 eq_refl), H.
  split; [apply Z.eqb_neq; intro E; subst op; discriminate H|].
  split; [apply Z.eqb_neq; intro E; rewrite E in H240; discriminate H240|].
  split; reflexivity.
Qed.

Lemma fr_op_len : forall e, 0 <= e <= 5 -> let op := 16 + e in
  (op =? 0) = false /\ (Z.land op 240 =? 0) = false /\ (Z.land op 32 =? 0) = true /\ (Z.land op 64 =? 0) = true /\
  Z.land op 15 = e.
Proof.
  intros e He. assert (e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) as Hc by lia.
  repeat destruct Hc as [Hc | Hc]; subst e; repeat split; reflexivity.
Qed.

Lemma fr_len_extra0 : Znth 0 len_extra = 0.
Proof. reflexivity. Qed.

(* reading fr_at at LEN and at LIT *)
Lemma fr_at_len : forall C s c h b out, fr_at C s c h b out -> i_mode s = LEN ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ b <= 8 /\
  exists j, 0 <= j <= fr_n C /\ 8 * c - b = fr_lpos C j /\ out = fr_lit C j.
Proof.
  intros C s c h b out H HM. unfold fr_at in H. cbv zeta in H. rewrite HM in H.
  destruct H as [[H _] | [Hh H]]; [discriminate H|].
  destruct H as [(H & _) | [(H & _) | (Hf & H)]]; try discriminate H.
  destruct H as [(Hm & Hb & Hj) | H].
  - exact (conj Hh (conj Hf (conj Hb Hj))).
  - exfalso. repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [H ?]
    end; discriminate H.
Qed.

Lemma fr_at_lit : forall C s c h b out, fr_at C s c h b out -> i_mode s = LIT ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ b < 8 /\
  exists j, 0 <= j < fr_n C /\ 8 * c - b = fr_lpos C (j + 1) /\ out = fr_lit C j /\
            i_length s = Znth j (fr_lits C).
Proof.
  intros C s c h b out H HM. unfold fr_at in H. cbv zeta in H. rewrite HM in H.
  destruct H as [[H _] | [Hh H]]; [discriminate H|].
  destruct H as [(H & _) | [(H & _) | (Hf & H)]]; try discriminate H.
  destruct H as [([H|H] & _) | [(Hm & Hb & Hj) | H]]; try discriminate H.
  - exact (conj Hh (conj Hf (conj Hb Hj))).
  - exfalso. repeat match goal with
    | H : _ \/ _ |- _ => destruct H as [H | H]
    | H : _ /\ _ |- _ => destruct H as [H ?]
    end; discriminate H.
Qed.

(* building fr_at at LEN, LIT, LENEXT and BAD *)
Lemma fr_at_mk_len : forall C s c h b out j,
  hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = LEN -> b <= 8 -> 0 <= j <= fr_n C ->
  8 * c - b = fr_lpos C j -> out = fr_lit C j -> fr_at C s c h b out.
Proof.
  intros. unfold fr_at. cbv zeta. right. split; [assumption|]. right. right. split; [assumption|].
  left. split; [right; assumption|]. split; [assumption|]. exists j. auto.
Qed.

Lemma fr_at_mk_lit : forall C s c h b out j,
  hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = LIT -> b < 8 -> 0 <= j < fr_n C ->
  8 * c - b = fr_lpos C (j + 1) -> out = fr_lit C j -> i_length s = Znth j (fr_lits C) -> fr_at C s c h b out.
Proof.
  intros. unfold fr_at. cbv zeta. right. split; [assumption|]. right. right. split; [assumption|].
  right. left. split; [assumption|]. split; [assumption|]. exists j. auto.
Qed.

Lemma fr_at_mk_lenext : forall C s c h b out,
  hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = LENEXT -> b < 8 -> out = fr_lits C ->
  ((exists w, fr_tail C = TDCode w /\ 8 * c - b = fr_tpos C + Znth 257 fixed_ll /\ i_extra s = 0) \/
   (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ 8 * c - b = fr_tpos C + Znth lc fixed_ll /\
      i_extra s = Znth (lc - 257) len_extra)) ->
  fr_at C s c h b out.
Proof.
  intros. unfold fr_at. cbv zeta. right. split; [assumption|]. right. right. split; [assumption|].
  right. right. left. auto.
Qed.

Lemma fr_at_mk_bad : forall C s c h b out,
  i_mode s = BAD -> Zlength out <= fr_n C -> fr_at C s c h b out.
Proof. intros. unfold fr_at. cbv zeta. left. auto. Qed.

(* LIT: the output full leaves (a literal still to write), otherwise the literal is written and LEN follows *)
Lemma fr_lit_pass : fr_layout_stmt -> fr_pass (fun md => md = LIT) (fun _ m => c_LIT m).
Proof.
  intros LAY C pos inp ob L z flush m CTX K HM.
  destruct K as [[Hinp Hin Hao Hout Hnx How Hwin Hwh Hat] LV RT].
  pose proof CTX as [OK _].
  destruct (LAY C OK) as (LJ & L0 & LB & LL & LN & _).
  unfold m_mode in HM.
  destruct (fr_at_lit _ _ _ _ _ _ Hat HM) as (Hh & Hf & Hb & j & Hj & Hq & Ho & Hl).
  unfold c_LIT, m_left.
  destruct (Z.eqb_spec (m_aout m - Zlength (m_ow m)) 0) as [E|E].
  - right. constructor; [constructor|..]; fr_simp; auto.
    right. split; [rewrite HM; discriminate|]. split; [auto|].
    right. left. split; [lia|]. left.
    rewrite <- Zlength_app, Ho, LL by lia. unfold fr_n in Hj. lia.
  - left. destruct (LJ j ltac:(lia)) as (Hlj & Hp1 & _ & Hl1).
    constructor; [constructor|..]; fr_simp; auto.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + unfold fr_at. cbv zeta. right. split; [exact Hh|]. right. right. split; [apply fr_fixed_set; auto|].
      left. fr_simp. split; [right; reflexivity|]. split; [lia|].
      exists (j + 1). split; [lia|]. split; [lia|].
      rewrite app_assoc, Ho, Hl1, Hl, Z.mod_small by lia. reflexivity.
Qed.

(* the code at the bit position of literal j: literal j itself (j < |lits|), or the first code of the tail
   (j = |lits|: 286 or 287, the length code 257, or the far length code lc); it ends by fr_end *)
Lemma fr_sym_at : fr_layout_stmt -> forall C j, fr_ok C -> 0 <= j <= fr_n C ->
  exists sy, 0 <= sy < 288 /\ fr_lpos C j + Znth sy fixed_ll <= fr_end C /\
    sublist (fr_lpos C j) (fr_lpos C j + Znth sy fixed_ll) (bytes_bits (fr_src C)) = send_sym fixed_ll sy /\
    ((j < fr_n C /\ sy = Znth j (fr_lits C)) \/
     (j = fr_n C /\ ((sy = 286 \/ sy = 287) \/
                     (exists w, fr_tail C = TDCode w /\ sy = 257) \/
                     (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ sy = lc /\ 257 <= lc <= 285)))).
Proof.
  intros LAY C j OK Hj.
  pose proof (LAY C OK) as (LJ & L0 & LB & LL & LN & LE & LT & Lll & Ldl & Lfl & Lfd & Lle & Lde).
  destruct (Z_lt_le_dec j (fr_n C)) as [Hlt|Hge].
  - destruct (LJ j ltac:(lia)) as (Hl & Hp & Hs & _).
    exists (Znth j (fr_lits C)). split; [lia|]. rewrite <- Hp.
    split; [pose proof (LB (j + 1) ltac:(lia)); lia|]. split; [exact Hs|]. left. auto.
  - assert (Ej : j = fr_n C) by lia. subst j. fold (fr_tpos C) in *.
    destruct OK as (_ & _ & _ & Htl & _).
    destruct (fr_tail C) as [w|w|lc lx dc dx] eqn:T; cbv zeta in LT; cbn [tail_ok] in Htl.
    + destruct LT as (Le & Ls). exists (286 + w). split; [lia|]. split; [lia|]. split; [rewrite <- Le; exact Ls|].
      right. split; [auto|]. left. lia.
    + destruct LT as (Le & Ls & _). exists 257. split; [lia|].
      split; [pose proof (Lfd (30 + w) ltac:(lia)); lia|]. split; [exact Ls|].
      right. split; [auto|]. right. left. exists w. auto.
    + destruct LT as (Le & Ls & _). exists lc. split; [lia|].
      split; [pose proof (Lfd dc ltac:(lia)); pose proof (Lle (lc - 257) ltac:(lia));
              pose proof (Lde dc ltac:(lia)); lia|].
      split; [exact Ls|]. right. split; [auto|]. right. right. exists lc, lx, dc, dx. split; [auto|]. lia.
Qed.

(* LEN: the fast path is inflate_fast (fr_fast_stmt); otherwise one fixed code is looked up at literal j: out of
   input leaves (the code ends after the input), a literal goes to LIT, 286/287 to BAD, and the tail's length
   code (257, or the far code lc) sets its extra bits and falls through into LENEXT *)
Lemma fr_len_pass : fr_layout_stmt -> fr_bits_stmt -> fr_fast_stmt ->
  fr_pass (fun md => md = LENEXT) (fun _ m => c_LENEXT lenfix_list distfix_list m) ->
  fr_pass (fun md => md = LEN) (fun _ m => c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m).
Proof.
  intros LAY FB FAST HLE C pos inp ob L z flush m CTX K HM.
  unfold c_LEN.
  destruct (andb (andb (6 <=? m_have m) (258 <=? m_left m)) (m_bits m <? 8)) eqn:F.
  { apply andb_true_iff in F as [F F3]. apply andb_true_iff in F as [F1 F2].
    apply Z.leb_le in F1. apply Z.leb_le in F2. apply Z.ltb_lt in F3.
    left. exact (FAST C pos inp ob L z m CTX K HM F1 F2 F3). }
  clear F.
  pose proof K as [[Hinp Hin Hao Hout Hnx How Hwin Hwh Hat] LV RT].
  pose proof CTX as (OK & Hpos & Hlen & Heq & _).
  pose proof (LAY C OK) as (LJ & L0 & LB & LL & LN & LE & _ & Lll & Ldl & Lfl & Lfd & Lle & Lde).
  unfold m_mode in HM.
  destruct (fr_at_len _ _ _ _ _ _ Hat HM) as (Hh & Hf & Hb & j & Hj & Hq & Ho).
  pose proof Hf as (Hlc & Hlb & _ & _).
  destruct (fr_sym_at LAY C j OK Hj) as (sy & Hsy & Hend & Hsub & Hcase).
  remember (upd_s m (fun s => set_i_back s 0)) as m0 eqn:Em0.
  assert (E0 : m_s m0 = set_i_back (m_s m) 0 /\ m_inp m0 = inp /\ m_in m0 = m_in m /\ m_aout m0 = m_aout m /\
               m_out m0 = m_out m /\ m_nx m0 = m_nx m /\ m_ow m0 = m_ow m /\ m_hold m0 = m_hold m /\
               m_bits m0 = m_bits m /\ m_ret m0 = m_ret m /\ m_leave m0 = m_leave m)
    by (subst m0; repeat split; auto).
  destruct E0 as (Es0 & Ei0 & Ein0 & Eao0 & Eo0 & Enx0 & Eow0 & Eh0 & Eb0 & Er0 & El0).
  clear Em0.
  assert (Hlc0 : i_lencode (m_s m0) = TLenfix) by (rewrite Es0; exact Hlc).
  assert (Hlb0 : i_lenbits (m_s m0) = 9) by (rewrite Es0; exact Hlb).
  rewrite Hlc0, Hlb0.
  pose proof (fb_lookup FB C pos inp m0 TLenfix 9 LENS fixed_ll sy) as LK.
  assert (Hin' : fr_in C pos inp) by (destruct OK as [Hbo _]; unfold fr_in; auto).
  assert (Hbuf : fr_buf C pos inp m0) by (unfold fr_buf; rewrite Ei0, Enx0, Eh0, Eb0; auto).
  specialize (LK Hin' Hbuf (or_introl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) ltac:(lia)
                 ltac:(lia)).
  cbv zeta in LK. rewrite Enx0, Eb0, Hq in LK.
  specialize (LK ltac:(lia) Hsub).
  destruct (lookup1 lenfix_list distfix_list TLenfix 9 m0) as [[here m1] ok] eqn:LKe.
  destruct LK as (nx & h & b & lv & Em1 & Hnx1 & Hh1 & Hq1 & Htrue & Hfalse).
  subst m1.
  destruct ok.
  2: {
    specialize (Hfalse eq_refl) as (Hlv & Hnxe & Hbl). subst lv.
    change (negb false) with true. cbv beta iota.
    right. constructor; [constructor|..]; fr_simp; rewrite ?Es0, ?Ei0, ?Ein0, ?Eao0, ?Eo0, ?Eow0, ?Er0;
      fr_simp; auto; try lia.
    - pose proof (Lfl sy Hsy).
      apply (fr_at_mk_len _ _ _ _ _ _ j); [exact Hh1 | apply fr_fixed_set; auto | fr_simp; exact HM | lia | exact Hj | exact Hq1 | exact Ho].
    - right. split; [rewrite HM; discriminate|]. split; [exact RT|].
      right. right. lia. }
  specialize (Htrue eq_refl) as (Hlv & Heb & Hbb & Hms). rewrite El0, LV in Hlv. subst lv.
  change (negb true) with false. cbv beta iota.
  pose proof (Lfl sy Hsy) as Hlsy.
  assert (Hu : u32 (b - e_bits here) = b - e_bits here) by (apply fr_u32_small; lia).
  assert (Hd : hold_ok (fr_g C) (pos + nx) (Z.shiftr h (e_bits here)) (b - e_bits here))
    by (apply (dk_drop dkit); [exact Hh1 | lia]).
  destruct Hcase as [(Hjn & Esy) | (Ejn & Hcase)].
  - (* a literal: to LIT *)
    destruct (LJ j ltac:(lia)) as (Hl8 & Hp1 & _ & _).
    destruct (fb_ms_lit FB sy (e_op here) (e_val here) ltac:(lia) Hms) as (Hop & Hval).
    assert (E1 : (e_op here =? 0) = true) by (rewrite Hop; reflexivity).
    do 2 (rewrite ?E1; cbn [negb andb]).
    left. constructor; [constructor|..]; fr_simp; rewrite ?Es0, ?Ei0, ?Ein0, ?Eao0, ?Eo0, ?Eow0, ?Er0;
      fr_simp; auto; try lia.
    subst sy. apply (fr_at_mk_lit _ _ _ _ _ _ j); rewrite ?Hu; auto; try lia.
    all: try (unfold fr_fixed; fr_simp; exact Hf).
    all: fr_simp; congruence.
  - subst j. fold (fr_tpos C) in *.
    destruct Hcase as [Hbad | [(w & Tw & Esy) | (lc & lx & dc & dx & Tf & Esy & Hlc')]].
    + (* 286, 287: an invalid literal/length code, to BAD *)
      pose proof (fb_ms_bad FB LENS sy (e_op here) (e_val here) (or_introl (conj eq_refl Hbad)) Hms) as H112.
      destruct (fr_op_bad _ H112) as (E1 & E2 & E3 & E4).
      do 4 (rewrite ?E1, ?E2, ?E3, ?E4; cbn [negb andb]).
      left. constructor; [constructor|..]; fr_simp; rewrite ?Es0, ?Ei0, ?Ein0, ?Eao0, ?Eo0, ?Eow0, ?Er0;
        fr_simp; auto; try lia.
      apply fr_at_mk_bad; [fr_simp; reflexivity | rewrite Ho, LL; lia].
    + (* 257 (length 3, no extra bits), to LENEXT *)
      subst sy.
      destruct (fb_ms_len FB 0 (e_op here) (e_val here) ltac:(lia) Hms) as (Hop & Hval).
      rewrite fr_len_extra0 in Hop.
      pose proof (fr_op_len 0 ltac:(lia)) as X. cbv zeta in X. rewrite <- Hop in X.
      destruct X as (E1 & E2 & E3 & E4 & E5).
      do 4 (rewrite ?E1, ?E2, ?E3, ?E4; cbn [negb andb]).
      apply (HLE C pos inp ob L z flush); [exact CTX | | fr_simp; reflexivity].
      constructor; [constructor|..]; fr_simp; rewrite ?Es0, ?Ei0, ?Ein0, ?Eao0, ?Eo0, ?Eow0, ?Er0;
        fr_simp; auto; try lia.
      apply fr_at_mk_lenext; rewrite ?Hu; auto; try lia.
      all: try (unfold fr_fixed; fr_simp; exact Hf).
      all: try (fr_simp; reflexivity).
      all: try (rewrite Ho; exact LN).
      left. exists w. split; [exact Tw|]. split; [lia|]. fr_simp. exact E5.
    + (* the far length code lc, to LENEXT with its extra bits *)
      subst sy.
      assert (Hms' : ref.means_symbol LENS (257 + (lc - 257)) (e_op here) (e_val here) = true)
        by (replace (257 + (lc - 257)) with lc by lia; exact Hms).
      destruct (fb_ms_len FB (lc - 257) (e_op here) (e_val here) ltac:(lia) Hms') as (Hop & Hval).
      destruct (Lle (lc - 257) ltac:(lia)) as (Hx & _).
      pose proof (fr_op_len _ Hx) as X. cbv zeta in X. rewrite <- Hop in X.
      destruct X as (E1 & E2 & E3 & E4 & E5).
      do 4 (rewrite ?E1, ?E2, ?E3, ?E4; cbn [negb andb]).
      apply (HLE C pos inp ob L z flush); [exact CTX | | fr_simp; reflexivity].
      constructor; [constructor|..]; fr_simp; rewrite ?Es0, ?Ei0, ?Ein0, ?Eao0, ?Eo0, ?Eow0, ?Er0;
        fr_simp; auto; try lia.
      apply fr_at_mk_lenext; rewrite ?Hu; auto; try lia.
      all: try (unfold fr_fixed; fr_simp; exact Hf).
      all: try (fr_simp; reflexivity).
      all: try (rewrite Ho; exact LN).
      right. exists lc, lx, dc, dx. split; [exact Tf|]. split; [lia|]. fr_simp. exact E5.
Qed.

Lemma fr_len : fr_layout_stmt -> fr_bits_stmt -> fr_fast_stmt ->
  fr_pass (fun md => md = LENEXT) (fun _ m => c_LENEXT lenfix_list distfix_list m) -> fr_len_stmt.
Proof.
  intros LAY FB FAST HLE. split; [exact (fr_len_pass LAY FB FAST HLE) | exact (fr_lit_pass LAY)].
Qed.

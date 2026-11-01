(** * Lemma (i): the static-tree call of _tr_flush_block, and facts common to both calls *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The static tables *)

Definition stl_ok (c : Z) : bool :=
  (1 <=? Znth c static_ltree_len) && (Znth c static_ltree_len <=? 9) &&
  (0 <=? Znth c static_ltree_code) && (Znth c static_ltree_code <? 2 ^ Znth c static_ltree_len) &&
  ((c <? 256) || (Znth c static_ltree_len <=? 8)).
Definition std_ok (c : Z) : bool :=
  (Znth c static_dtree_len =? 5) && (0 <=? Znth c static_dtree_code) && (Znth c static_dtree_code <? 32).

Lemma stl_all : check_from stl_ok 0 288 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma std_all : check_from std_ok 0 30 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma static_l : forall c, 0 <= c <= 287 ->
  code_ok static_ltree_code static_ltree_len c /\ Znth c static_ltree_len <= 9 /\
  (256 <= c -> Znth c static_ltree_len <= 8).
Proof.
  intros c Hc. assert (H := check_from_spec _ _ _ stl_all c ltac:(simpl; lia)). unfold stl_ok in H.
  repeat rewrite andb_true_iff in H. rewrite orb_true_iff in H. rewrite !Z.leb_le, !Z.ltb_lt in H. unfold code_ok. lia.
Qed.

Lemma static_d : forall c, 0 <= c <= 29 ->
  code_ok static_dtree_code static_dtree_len c /\ Znth c static_dtree_len = 5.
Proof.
  intros c Hc. assert (H := check_from_spec _ _ _ std_all c ltac:(simpl; lia)). unfold std_ok in H.
  repeat rewrite andb_true_iff in H. rewrite Z.eqb_eq, Z.leb_le, Z.ltb_lt in H. unfold code_ok.
  destruct H as [[H1 H2] H3]. rewrite H1. change (2 ^ 5) with 32. lia.
Qed.

(** Codes and cost of one symbol under any code tables. *)
Lemma sym_parts : forall dist lc, valid_sym dist lc -> dist <> 0 ->
  0 <= Znth lc length_code_tab <= 28 /\ 0 <= Znth (Znth lc length_code_tab) extra_lbits <= 5 /\
  0 <= d_code (dist - 1) <= 29 /\ 0 <= Znth (d_code (dist - 1)) extra_dbits <= 13.
Proof.
  intros dist lc [Hl Hd] Hne.
  destruct (length_code_facts lc Hl) as [A [B _]]. destruct (dist_code_facts (dist - 1) ltac:(lia)) as [C [D _]].
  lia.
Qed.

Lemma static_sym : forall dist lc, valid_sym dist lc ->
  sym_codes_ok static_ltree_code static_ltree_len static_dtree_code static_dtree_len dist lc /\
  sym_cost static_ltree_len static_dtree_len dist lc <= 31.
Proof.
  intros dist lc Hv. unfold sym_codes_ok, sym_cost. destruct (Z.eqb_spec dist 0) as [E|E].
  - destruct Hv as [Hl _]. destruct (static_l lc ltac:(lia)) as [A [B _]]. split; [exact A|lia].
  - destruct (sym_parts dist lc Hv E) as [A [B [C D]]].
    assert (G1 : 0 <= Znth lc length_code_tab + 257 <= 287) by lia.
    assert (G2 : 0 <= d_code (dist - 1) <= 29) by lia.
    destruct (static_l _ G1) as [A1 [_ B1]]. specialize (B1 ltac:(lia)). destruct (static_d _ G2) as [A2 B2].
    split; [split; auto|]. lia.
Qed.

Lemma cost_sum_le : forall llens dlens (l : list (Z * Z)) c,
  (forall x, In x l -> sym_cost llens dlens (fst x) (snd x) <= c) -> cost_sum llens dlens l <= c * Z.of_nat (length l).
Proof.
  intros llens dlens l c H. induction l as [|[d x] l IH]; [simpl; lia|].
  cbn [cost_sum length]. assert (H1 := H (d, x) (in_eq _ _)). simpl in H1.
  assert (IH' := IH ltac:(intros; apply H; right; auto)). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma length_firstn_le : forall {A} (l : list A) k, (k <= length l)%nat -> length (firstn k l) = k.
Proof. intros. rewrite length_firstn. lia. Qed.

(** ** flush_prep keeps the output, lit_bufsize and sym_next *)

Lemma flush_prep_keeps : forall s stored_len,
  let s' := fst (fst (fst (flush_prep s stored_len))) in
  tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s /\ tr_sym_next s' = tr_sym_next s.
Proof.
  intros s stored_len. unfold flush_prep.
  destruct (tr_level s >? 0); [|cbn [fst]; auto].
  set (s0 := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s).
  assert (E0 : tr_out s0 = tr_out s /\ tr_lit_bufsize s0 = tr_lit_bufsize s /\ tr_sym_next s0 = tr_sym_next s)
    by (unfold s0; destruct (tr_data_type s =? Z_UNKNOWN); auto).
  destruct (build_tree static_l_desc (tr_ltree s0) (tr_wk s0)) as [[lt lmax] w1].
  destruct (build_tree static_d_desc (tr_dtree (set_wk (set_lmax (set_ltree s0 lt) lmax) w1))
                       (tr_wk (set_wk (set_lmax (set_ltree s0 lt) lmax) w1))) as [[dt dmax] w2].
  unfold build_bl_tree.
  destruct (scan_tree _ _ _) as [lt' bl1].
  destruct (scan_tree _ _ bl1) as [dt' bl2].
  destruct (build_tree static_bl_desc bl2 _) as [[bl3 blmax] w3].
  cbn [fst]. exact E0.
Qed.

(** ** The static call *)

Theorem static_overlay : forall L syms o0 last,
  bits_ok o0 -> o_pending o0 = 0 -> o_bi_valid o0 <= 7 -> Zlength (o_buf o0) = 4 * L -> 128 <= L ->
  Zlength syms <= L - 1 -> (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  (forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) (o_buf o0) = Znth i (sym_bytes syms)) ->
  0 <= last <= 1 ->
  overlay_ok L syms (send_bits o0 (Z.shiftl STATIC_TREES 1 + last) 3,
                     static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len).
Proof.
  intros L syms o0 last Hok Hp Hv Hlen HL Hn Hval Hsy Hlast.
  assert (Hval3 : 0 <= Z.shiftl STATIC_TREES 1 + last < 2 ^ 3) by (change (Z.shiftl STATIC_TREES 1) with 2; change (2 ^ 3) with 8; lia).
  destruct (send_bits_spec o0 (Z.shiftl STATIC_TREES 1 + last) 3 Hok ltac:(lia) Hval3) as [B1 [V1 [Ok1 [P1 W1]]]].
  set (o := send_bits o0 (Z.shiftl STATIC_TREES 1 + last) 3) in *.
  destruct W1 as [W1a [W1b [W1c W1d]]].
  unfold overlay_ok. split; [exact Ok1|]. split; [lia|]. split.
  { intros i Hi. rewrite W1d by lia. apply Hsy; auto. }
  split; [intros x Hx; apply static_sym, Hval, Hx|].
  split; [apply (static_l END_BLOCK); unfold END_BLOCK; lia|].
  intros k Hk.
  assert (Hs : forall x, In x (firstn k syms) -> valid_sym (fst x) (snd x) /\
               sym_codes_ok static_ltree_code static_ltree_len static_dtree_code static_dtree_len (fst x) (snd x))
    by (intros x Hx; apply firstn_In in Hx; split; [apply Hval, Hx|apply static_sym, Hval, Hx]).
  destruct (compress_sep_spec (firstn k syms) o _ _ _ _ Ok1 Hs) as [_ [Hb _]].
  rewrite Hb.
  assert (Hc := cost_sum_le static_ltree_len static_dtree_len (firstn k syms) 31
                  ltac:(intros x Hx; apply static_sym, Hval; eapply firstn_In; eauto)).
  rewrite length_firstn_le in Hc by exact Hk.
  assert (Hb0 : bitpos o0 <= 7) by (unfold bitpos; lia).
  rewrite Zlength_correct in Hn. lia.
Qed.

(* RT-D part FLUSH: compress_sep + END_BLOCK sends Format.send_syms; Format.syms_ok of the block's symbols (interface: RTDFlushDefs.v, RTDFlushDefs2.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs2.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtdc_bits_le_0 : forall v, F.bits_le v 0 = [].
Proof. reflexivity. Qed.

Lemma rtdc_wcode : wsend_stmt -> forall o codes lens fl c,
  bits_ok o -> o_pending o + 2 <= Zlength (o_buf o) -> cimpl codes lens fl c ->
  bits_ok (send_code o c codes lens) /\ obits (send_code o c codes lens) = obits o ++ F.send_sym fl c.
Proof.
  intros W o codes lens fl c Ho Hp [_ [Hl [Hc Hb]]]. unfold send_code.
  destruct (W o (Znth c codes) (Znth c lens)) as [W1 W2]; auto; try lia.
  { destruct Ho as [_ [_ ?]]; auto. }
  rewrite W2, Hb. auto.
Qed.

Lemma rtdc_wextra : wsend_stmt -> forall o v n v',
  bits_ok o -> o_pending o + 2 <= Zlength (o_buf o) -> 0 <= n <= 16 -> (n <> 0 -> 0 <= v < 2 ^ n /\ v = v') ->
  let o' := if negb (n =? 0) then send_bits o v n else o in
  bits_ok o' /\ obits o' = obits o ++ F.bits_le v' n.
Proof.
  intros W o v n v' Ho Hp Hn Hv o'. subst o'.
  destruct (Z.eqb_spec n 0); simpl.
  - subst n. rewrite rtdc_bits_le_0, app_nil_r. auto.
  - destruct (Hv n0) as [Hv1 <-]. apply W; auto; try lia. destruct Ho as [_ [_ ?]]; auto.
Qed.

Lemma rtdc_wlen : forall o o', writes o o' -> o_pending o <= o_pending o' /\ Zlength (o_buf o') = Zlength (o_buf o).
Proof. intros o o' [A [B _]]. auto. Qed.

Lemma rtdc_wif : forall (b : bool) o v n, writes o (if b then send_bits o v n else o).
Proof. intros [|] o v n; [apply send_bits_writes|apply writes_refl]. Qed.

Lemma rtdc_sym : wsend_stmt -> tabs2_stmt -> forall o lcodes llens dcodes dlens ll dl d l,
  bits_ok o ->
  (if d =? 0 then 0 <= l < 256 else 0 <= l <= 255 /\ 1 <= d <= 32768) ->
  (if d =? 0 then cimpl lcodes llens ll l
   else cimpl lcodes llens ll (257 + F.len_code (l + 3)) /\ cimpl dcodes dlens dl (F.dist_code d)) ->
  o_pending (send_symbol o lcodes llens dcodes dlens d l) + 2 <= Zlength (o_buf o) ->
  let o' := send_symbol o lcodes llens dcodes dlens d l in
  bits_ok o' /\ obits o' = obits o ++ F.send_one ll dl (fsym (d, l)).
Proof.
  intros W T o lcodes llens dcodes dlens ll dl d l Ho Hr Hc Hp o'. subst o'.
  unfold fsym; cbn [fst snd].
  revert Hp. unfold send_symbol.
  destruct (Z.eqb_spec d 0) as [Hd|Hd].
  - intros Hp. pose proof (rtdc_wlen _ _ (send_code_writes o l lcodes llens)) as [P0 L0].
    eapply rtdc_wcode; eauto. lia.
  - destruct Hr as [Hl Hdist]. destruct Hc as [Cl Cd].
    destruct T as [_ [_ [TL TD]]].
    destruct (TL l Hl) as [L1 [L2 [L3 [L4 [L5 L6]]]]].
    destruct (TD d Hdist) as [D1 [D2 [D3 [D4 [D5 D6]]]]].
    unfold LITERALS.
    set (code := Znth l length_code_tab) in *.
    set (dcode := d_code (d - 1)) in *.
    set (o1 := send_code o (code + 256 + 1) lcodes llens).
    set (o2 := if negb (Znth code extra_lbits =? 0) then send_bits o1 (l - Znth code base_length_tab) (Znth code extra_lbits) else o1).
    set (o3 := send_code o2 dcode dcodes dlens).
    set (o4 := if negb (Znth dcode extra_dbits =? 0) then send_bits o3 (d - 1 - Znth dcode base_dist_tab) (Znth dcode extra_dbits) else o3).
    intros Hp.
    assert (W12 : writes o1 o2).
    { apply rtdc_wif. }
    assert (W01 : writes o o1) by apply send_code_writes.
    assert (W23 : writes o2 o3) by apply send_code_writes.
    assert (W34 : writes o3 o4).
    { apply rtdc_wif. }
    apply rtdc_wlen in W01, W12, W23, W34.
    assert (E1 : code + 256 + 1 = 257 + F.len_code (l + 3)) by (rewrite <- L1; lia).
    destruct (rtdc_wcode W o lcodes llens ll (code + 256 + 1)) as [B1 O1]; auto; try lia.
    { rewrite E1; auto. }
    fold o1 in B1, O1. rewrite E1 in O1.
    destruct (rtdc_wextra W o1 (l - Znth code base_length_tab) (Znth code extra_lbits) (l + 3 - Znth code F.len_base)) as [B2 O2]; auto; try lia.
    { rewrite L3. intros Hn. rewrite (L4 Hn). split; lia. }
    fold o2 in B2, O2.
    destruct (rtdc_wcode W o2 dcodes dlens dl dcode) as [B3 O3]; auto; try lia.
    { subst dcode. rewrite D1; auto. }
    fold o3 in B3, O3.
    destruct (rtdc_wextra W o3 (d - 1 - Znth dcode base_dist_tab) (Znth dcode extra_dbits) (d - Znth dcode F.dist_base)) as [B4 O4]; auto; try lia.
    { rewrite D3, D4. intros _. split; lia. }
    fold o4 in B4, O4.
    split; auto.
    rewrite O4, O3, O2, O1. unfold F.send_one.
    rewrite L3, D3. subst dcode. rewrite D1. rewrite <- L1.
    rewrite !app_assoc. reflexivity.
Qed.

Lemma rtdc_sep : wsend_stmt -> tabs2_stmt -> forall syms o lcodes llens dcodes dlens ll dl,
  bits_ok o -> zsyms_ok syms -> syms_cimpl lcodes llens dcodes dlens ll dl syms ->
  o_pending (compress_sep o lcodes llens dcodes dlens syms) + 2 <= Zlength (o_buf o) ->
  let o' := compress_sep o lcodes llens dcodes dlens syms in
  bits_ok o' /\ obits o' = obits o ++ flat_map (F.send_one ll dl) (map fsym syms).
Proof.
  intros W T. induction syms as [|[d l] r IH]; intros o lcodes llens dcodes dlens ll dl Ho Hz Hc Hp o'; subst o'.
  - simpl. rewrite app_nil_r. auto.
  - cbn [compress_sep] in *.
    pose proof (rtdc_wlen _ _ (compress_sep_writes r (send_symbol o lcodes llens dcodes dlens d l) lcodes llens dcodes dlens)) as [P1 L1].
    pose proof (rtdc_wlen _ _ (send_symbol_writes o lcodes llens dcodes dlens d l)) as [P0 L0].
    destruct (rtdc_sym W T o lcodes llens dcodes dlens ll dl d l) as [B1 O1]; auto.
    { apply (Hz (d, l)); left; auto. }
    { apply (Hc (d, l)); left; auto. }
    { lia. }
    destruct (IH (send_symbol o lcodes llens dcodes dlens d l) lcodes llens dcodes dlens ll dl) as [B2 O2]; auto.
    { intros x Hx; apply Hz; right; auto. }
    { intros x Hx; apply Hc; right; auto. }
    { lia. }
    split; auto. rewrite O2, O1. cbn [map flat_map]. rewrite app_assoc. reflexivity.
Qed.

Lemma rtdc_comp : wsend_stmt -> tabs2_stmt -> comp_stmt.
Proof.
  intros W T o lcodes llens dcodes dlens ll dl syms Ho Hz Hc He Hp0 Hp o'. subst o'.
  pose proof (rtdc_wlen _ _ (compress_sep_writes syms o lcodes llens dcodes dlens)) as [P1 L1].
  destruct (rtdc_sep W T syms o lcodes llens dcodes dlens ll dl) as [B1 O1]; auto.
  destruct (rtdc_wcode W (compress_sep o lcodes llens dcodes dlens syms) lcodes llens ll END_BLOCK) as [B2 O2]; auto; try lia.
  split; auto. rewrite O2, O1. unfold F.send_syms. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rtdc_symsok : symsok_stmt.
Proof.
  intros wmax out syms. revert out.
  induction syms as [|[d l] r IH]; intros out ll dl Hr Hn; simpl; auto.
  simpl in Hr. destruct Hr as [Hx Hr].
  assert (Hn0 := Hn (d, l) (or_introl eq_refl)). cbn [fst snd] in Hn0, Hx.
  unfold fsym in *; cbn [fst snd] in *.
  destruct (Z.eqb_spec d 0).
  - split; [split; [unfold F.byte_ok; lia|auto]|].
    apply IH; auto. intros x Hi; apply Hn; right; auto.
  - split; [repeat split; tauto || lia|].
    apply IH; auto. intros x Hi; apply Hn; right; auto.
Qed.

Theorem rtd_comp2_ok : wsend_stmt -> tabs2_stmt -> comp_stmt /\ symsok_stmt.
Proof.
  intros W T. split; [apply rtdc_comp; auto|apply rtdc_symsok].
Qed.

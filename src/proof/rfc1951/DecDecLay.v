(* Part of DecDec.group_dec: the layout of a Huffman block in the input.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lay_blocks_ok_nth : forall w bs out n, blocks_ok w out bs -> (n < length bs)%nat ->
  block_ok w (fold_left block_data (firstn n bs) out) (nth n bs (Stored [])).
Proof.
  intros w bs; induction bs as [|b r IH]; intros out n H Hn; simpl in Hn; [lia|].
  destruct H as [H1 H2]. destruct n as [|n]; simpl; auto.
  apply IH; auto; lia.
Qed.

Lemma lay_syms_ok_nth : forall w ll dl syms out n, syms_ok w ll dl out syms -> (n < length syms)%nat ->
  sym_ok w ll dl (syms_data out (firstn n syms)) (nth n syms (Lit 0)).
Proof.
  intros w ll dl syms; induction syms as [|b r IH]; intros out n H Hn; simpl in Hn; [lia|].
  destruct H as [H1 H2]. destruct n as [|n]; simpl; auto.
  apply IH; auto; lia.
Qed.

Lemma lay_firstn_S : forall {A} (l: list A) n d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l; induction l as [|a r IH]; intros n d Hn; simpl in Hn; [lia|].
  destruct n as [|n]; [reflexivity|].
  change (a :: firstn (S n) r = a :: firstn n r ++ [nth n r d]). rewrite (IH n d) by (simpl in Hn; lia). reflexivity.
Qed.

Lemma lay_flat_map_split : forall {A B} (f: A -> list B) l n d, (n < length l)%nat ->
  flat_map f l = flat_map f (firstn n l) ++ f (nth n l d) ++ flat_map f (skipn (S n) l).
Proof.
  intros A B f l; induction l as [|a r IH]; intros n d Hn; simpl in Hn; [lia|].
  destruct n as [|n]; simpl; auto. rewrite (IH n d) by lia. rewrite app_assoc. reflexivity.
Qed.

Lemma lay_lz_copy_prefix : forall n dist out, exists d, lz_copy n dist out = out ++ d.
Proof.
  induction n as [|n IH]; intros dist out; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (IH dist (out ++ [Znth (Zlength out - dist) out])) as [d Hd]. rewrite Hd.
    eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma lay_syms_data_prefix : forall syms out, exists d, syms_data out syms = out ++ d.
Proof.
  unfold syms_data. induction syms as [|s r IH]; intros out; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (IH (sym_data out s)) as [d Hd]. rewrite Hd.
    destruct s; simpl.
    + eexists. rewrite <- app_assoc. reflexivity.
    + destruct (lay_lz_copy_prefix (Z.to_nat len) dist out) as [d' Hd']. rewrite Hd'.
      eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma lay_Zlength_bits_le : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma lay_Zlength_bits3 : forall cl, Zlength (flat_map (fun c => bits_le c 3) cl) = 3 * Zlength cl.
Proof.
  induction cl as [|c r IH]; cbn [flat_map]; [reflexivity|].
  rewrite Zlength_app, IH, lay_Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma lay_enc_huff : forall p f b ll dl syms,
  ((b = Fixed syms /\ ll = fixed_ll /\ dl = fixed_dl) \/
   (exists nlen ndist clsent toks, b = Dynamic nlen ndist clsent toks syms /\
      ll = dyn_ll nlen toks /\ dl = dyn_dl nlen ndist toks)) ->
  exists H, enc_block p f b = H ++ flat_map (send_one ll dl) syms ++ send_sym ll 256 /\
    Zlength H = hb_hdr b.
Proof.
  intros p f b ll dl syms [[-> [-> ->]] | [nlen [ndist [clsent [toks [-> [-> ->]]]]]]].
  - exists [f; true; false]. split; reflexivity.
  - exists (f :: [false; true] ++ bits_le (nlen - 257) 5 ++ bits_le (ndist - 1) 5 ++
       bits_le (Zlength clsent - 4) 4 ++ flat_map (fun c => bits_le c 3) clsent ++
       flat_map (send_tok (cl_lens clsent)) toks).
    split.
    + unfold enc_block, send_syms. cbn [app]. rewrite <- !app_assoc. reflexivity.
    + unfold hb_hdr. cbn [app].
      rewrite !Zlength_cons, !Zlength_app, !lay_Zlength_bits_le, lay_Zlength_bits3 by lia.
      lia.
Qed.

Lemma lay_sublist_mid : forall (L A B C: list bool) a,
  0 <= a -> sublist a (a + Zlength (A ++ B ++ C)) L = A ++ B ++ C ->
  sublist (a + Zlength A) (a + Zlength A + Zlength B) L = B.
Proof.
  intros L A B C a Ha H.
  rewrite !Zlength_app in H.
  pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B). pose proof (Zlength_nonneg C).
  replace (a + Zlength A) with (Zlength A + a) by lia.
  replace (Zlength A + a + Zlength B) with (Zlength A + Zlength B + a) by lia.
  rewrite <- (sublist_sublist (Zlength A + Zlength B) (a + (Zlength A + (Zlength B + Zlength C))) (Zlength A) a L) by lia.
  rewrite H. rewrite sublist_app2 by lia. rewrite Z.sub_diag.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
  rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

Lemma lay_Zlength_pack : forall bs, Zlength (pack bs) = (Zlength bs + 7) / 8.
Proof.
  intros. unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  pose proof (Zlength_nonneg bs). rewrite Z2Nat.id; [lia|]. apply Z.div_pos; lia.
Qed.

Lemma lay_endpos_le : forall G, endpos G <= 8 * slen G.
Proof.
  intros G. unfold endpos, slen, D0.
  assert (Hd: Zlength (deflate_bits (dc_bs G)) <= 8 * Zlength (deflate_bytes (dc_bs G))).
  { unfold deflate_bytes. rewrite lay_Zlength_pack.
    set (L := Zlength (deflate_bits (dc_bs G))).
    pose proof (Z_div_mod_eq_full (L + 7) 8). pose proof (Z.mod_pos_bound (L + 7) 8). lia. }
  assert (exists tr, stream_bytes (dc_w G) (dc_hist G) (dc_bs G) =
            hdr_bytes (dc_w G) ++ deflate_bytes (dc_bs G) ++ tr) as [tr Htr].
  { unfold stream_bytes, hdr_bytes. destruct (dc_w G) as [| wb fl did | h].
    - exists []. rewrite app_nil_r. reflexivity.
    - eexists. rewrite <- !app_assoc. reflexivity.
    - eexists. reflexivity. }
  rewrite Htr, !Zlength_app. pose proof (Zlength_nonneg tr). lia.
Qed.

Lemma lay_pad8_nonneg : forall p, 0 <= pad8 p.
Proof. intros. unfold pad8. apply Z.mod_pos_bound. lia. Qed.

Lemma lay_bpos_mono : forall (K: dkit_stmt) G, dctx_ok G -> forall n k, 0 <= k -> k + Z.of_nat n <= nblk G ->
  bpos G k <= bpos G (k + Z.of_nat n).
Proof.
  intros K G HG n; induction n as [|n IH]; intros k Hk Hn.
  - rewrite Z.add_0_r. lia.
  - replace (k + Z.of_nat (S n)) with (k + Z.of_nat n + 1) by lia.
    destruct (dk_blk K G (k + Z.of_nat n) HG ltac:(lia)) as [E _].
    rewrite E. pose proof (Zlength_nonneg (enc_block (bpos G (k + Z.of_nat n) - D0 G)
      (lastflag G (k + Z.of_nat n) =? 1) (blk G (k + Z.of_nat n)))).
    specialize (IH k Hk ltac:(lia)). lia.
Qed.

Lemma lay_bpos_range : forall (K: dkit_stmt) G k, dctx_ok G -> 0 <= k <= nblk G ->
  0 <= bpos G k /\ bpos G k <= 8 * slen G.
Proof.
  intros K G k HG Hk.
  pose proof (lay_bpos_mono K G HG (Z.to_nat k) 0 ltac:(lia) ltac:(lia)) as H1.
  pose proof (lay_bpos_mono K G HG (Z.to_nat (nblk G - k)) k ltac:(lia) ltac:(lia)) as H2.
  rewrite dk_bpos0 in H1 by exact K. replace (0 + Z.of_nat (Z.to_nat k)) with k in H1 by lia.
  replace (k + Z.of_nat (Z.to_nat (nblk G - k))) with (nblk G) in H2 by lia.
  destruct (dk_end K G HG) as [E _].
  pose proof (lay_endpos_le G). pose proof (lay_pad8_nonneg (bpos G (nblk G))).
  assert (0 <= D0 G) by (unfold D0; pose proof (Zlength_nonneg (hdr_bytes (dc_w G))); lia).
  lia.
Qed.

Lemma lay_Znth_nz : forall i (l: list Z), Znth i l <> 0 -> 0 <= i < Zlength l.
Proof.
  intros i l H. destruct (Z_lt_le_dec i 0). { rewrite Znth_underflow in H by lia. easy. }
  destruct (Z_lt_le_dec i (Zlength l)). lia. rewrite Znth_overflow in H by lia. easy.
Qed.

Lemma lay_fixed_codes :
  lens_ok fixed_ll /\ complete fixed_ll /\ used fixed_ll 256 /\ lens_ok fixed_dl /\ complete fixed_dl.
Proof.
  unfold lens_ok, complete, used. repeat split.
  all: try lia.
  all: try (vm_compute; reflexivity).
  - apply Forall_forall; intros x Hx; unfold fixed_ll in Hx; rewrite !in_app_iff in Hx.
    destruct Hx as [Hx|[Hx|[Hx|Hx]]]; apply repeat_spec in Hx; subst; unfold MAXLEN; lia.
  - vm_compute. intro H; discriminate H.
  - apply Forall_forall; intros x Hx; unfold fixed_dl in Hx; apply repeat_spec in Hx; subst; unfold MAXLEN; lia.
Qed.

Lemma lay_syms_data_app : forall out a b, syms_data out (a ++ b) = syms_data (syms_data out a) b.
Proof. intros. unfold syms_data. apply fold_left_app. Qed.

Lemma lay_ok : dkit_stmt -> lay_stmt.
Proof.
  intros K G s k j ll dl syms p0 HG Hh.
  pose proof Hh as Hh0.
  destruct Hh as [[Hk Hlast] [Hcase [Hj [Htl [Htd Hp0]]]]].
  pose proof HG as HG0.
  destruct HG as [[Hwb [_ [_ [_ [_ Hbks]]]]] _].
  assert (Hn: (Z.to_nat k < length (dc_bs G))%nat).
  { unfold nblk in Hk. rewrite Zlength_correct in Hk. lia. }
  pose proof (lay_blocks_ok_nth _ _ _ _ Hbks Hn) as Hb.
  change (fold_left block_data (firstn (Z.to_nat k) (dc_bs G)) (dc_hist G)) with (outk G k) in Hb.
  change (nth (Z.to_nat k) (dc_bs G) (Stored [])) with (blk G k) in Hb.
  (* the codes, the symbols, the data of the block *)
  assert (Hc: lens_ok ll /\ (complete ll \/ single ll) /\ used ll 256 /\
              lens_ok dl /\ (complete dl \/ single dl \/ empty_code dl) /\
              syms_ok (2 ^ dc_wb G) ll dl (outk G k) syms /\
              block_data (outk G k) (blk G k) = syms_data (outk G k) syms).
  { destruct Hcase as [[Hbk [-> ->]] | [nlen [ndist [clsent [toks [Hbk [-> ->]]]]]]];
      rewrite Hbk in Hb |- *.
    - destruct lay_fixed_codes as [F1 [F2 [F3 [F4 F5]]]]. simpl in Hb. tauto.
    - destruct Hb as [_ [_ [_ [_ [_ [_ [_ [[L1 [L2 L3]] [[D1 D2] Hs]]]]]]]]].
      repeat split; auto; apply lay_Znth_nz in L2; lia. }
  destruct Hc as [Hll [Hllc [Hu [Hdl [Hdlc [Hsyms Hbd]]]]]].
  destruct (lay_enc_huff (bpos G k - D0 G) (lastflag G k =? 1) _ _ _ _ Hcase) as [H [HE HH]].
  destruct (dk_blk K G k HG0 Hk) as [Hb1 Hb2].
  rewrite HE in Hb1, Hb2.
  destruct (lay_bpos_range K G k HG0 ltac:(lia)) as [Hr0 _].
  destruct (lay_bpos_range K G (k + 1) HG0 ltac:(lia)) as [_ Hr1].
  assert (Houtk: outk G (k + 1) = syms_data (outk G k) syms).
  { rewrite dk_outk by (exact K || lia). exact Hbd. }
  set (nj := Z.to_nat j) in *.
  assert (Hnj: (nj <= length syms)%nat) by (unfold nj; rewrite Zlength_correct in Hj; lia).
  pose proof (Zlength_nonneg H) as HH0.
  pose proof (Zlength_nonneg (send_sym ll 256)) as Hss0.
  split; [exact Hll|]. split; [exact Hllc|]. split; [exact Hu|].
  split; [exact Hdl|]. split; [exact Hdlc|].
  split; [|split].
  - destruct (dk_full_len K G (k + 1) ltac:(lia)) as [_ [rest Hrest]].
    destruct (lay_syms_data_prefix (skipn nj syms) (outj G k syms j)) as [d Hd].
    exists (d ++ rest). rewrite Hrest, Houtk, app_assoc, <- Hd.
    unfold outj. fold nj. rewrite <- lay_syms_data_app, firstn_skipn. reflexivity.
  - intros Hjl. cbv zeta.
    assert (Hnj': (nj < length syms)%nat) by (unfold nj; rewrite Zlength_correct in Hjl; lia).
    unfold sym_at. fold nj.
    set (sy := nth nj syms (Lit 0)).
    pose proof (lay_flat_map_split (send_one ll dl) syms nj (Lit 0) Hnj') as Hsplit.
    fold sy in Hsplit.
    set (F1 := flat_map (send_one ll dl) (firstn nj syms)) in *.
    set (F2 := flat_map (send_one ll dl) (skipn (S nj) syms)) in *.
    assert (Hoff: sym_off ll dl syms j = Zlength F1) by reflexivity.
    pose proof (Zlength_nonneg F1). pose proof (Zlength_nonneg F2).
    pose proof (Zlength_nonneg (send_one ll dl sy)).
    rewrite Hsplit in Hb1, Hb2.
    rewrite !Zlength_app in Hb1.
    split; [|split; [|split; [|split]]].
    + apply lay_syms_ok_nth; auto.
    + rewrite Hp0, Hoff.
      replace (bpos G k + hb_hdr (blk G k) + Zlength F1) with (bpos G k + Zlength (H ++ F1))
        by (rewrite Zlength_app; lia).
      apply (lay_sublist_mid _ _ _ (F2 ++ send_sym ll 256)); [lia|].
      rewrite <- !app_assoc. rewrite !Zlength_app.
      replace (bpos G k + (Zlength H + (Zlength F1 + (Zlength (send_one ll dl sy) +
                (Zlength F2 + Zlength (send_sym ll 256))))))
        with (bpos G (k + 1)) by lia.
      rewrite Hb2. rewrite <- !app_assoc. reflexivity.
    + rewrite Hp0, Hoff. lia.
    + unfold outj. replace (Z.to_nat (j + 1)) with (S nj) by (unfold nj; lia).
      rewrite (lay_firstn_S syms nj (Lit 0) Hnj'), lay_syms_data_app. reflexivity.
    + destruct Hh0 as [Hi [Hc2 [_ [Ht1 [Ht2 _]]]]].
      split; [exact Hi|]. split; [exact Hc2|]. split; [lia|]. split; [exact Ht1|]. split; [exact Ht2|].
      unfold sym_off. replace (Z.to_nat (j + 1)) with (S nj) by (unfold nj; lia).
      rewrite (lay_firstn_S syms nj (Lit 0) Hnj'), flat_map_app. cbn [flat_map]. rewrite app_nil_r.
      rewrite Zlength_app. fold F1. fold sy. rewrite Hp0, Hoff. lia.
  - intros Hjl.
    assert (Hfa: firstn nj syms = syms).
    { apply firstn_all2. unfold nj. rewrite Hjl, Zlength_correct. lia. }
    assert (Hoff: sym_off ll dl syms j = Zlength (flat_map (send_one ll dl) syms)).
    { unfold sym_off. fold nj. rewrite Hfa. reflexivity. }
    pose proof (Zlength_nonneg (flat_map (send_one ll dl) syms)).
    rewrite !Zlength_app in Hb1.
    split; [|split; [|split]].
    + rewrite Hp0, Hoff.
      replace (bpos G k + hb_hdr (blk G k) + Zlength (flat_map (send_one ll dl) syms))
        with (bpos G k + Zlength (H ++ flat_map (send_one ll dl) syms)) by (rewrite Zlength_app; lia).
      apply (lay_sublist_mid _ _ _ []); [lia|].
      rewrite app_nil_r, <- !app_assoc, !Zlength_app.
      replace (bpos G k + (Zlength H + (Zlength (flat_map (send_one ll dl) syms) +
                Zlength (send_sym ll 256)))) with (bpos G (k + 1)) by lia.
      rewrite Hb2. reflexivity.
    + rewrite Hp0, Hoff. lia.
    + exact Hr1.
    + rewrite Houtk. unfold outj. fold nj. rewrite Hfa. reflexivity.
Qed.

(* Part of inflate_fast's decode theory (DecFastKit.v): the facts of a Huffman block at a symbol. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecFastKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dfb_epos_ge : forall bs k p, p <= epos p bs k.
Proof.
  induction bs as [|b r IH]; intros k p; destruct k; simpl; try lia.
  specialize (IH k (p + Zlength (enc_block p false b))).
  pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

Lemma dfb_bpos_nonneg : forall G k, 0 <= bpos G k.
Proof.
  intros. unfold bpos, D0. pose proof (dfb_epos_ge (dc_bs G) (Z.to_nat k) 0).
  pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). lia.
Qed.

Lemma dfb_sublist_len : forall {A} i j (l: list A), i < j -> Zlength (sublist i j l) = j - i -> j <= Zlength l.
Proof.
  intros A i j l Hij H. unfold sublist in H.
  rewrite Zlength_correct, length_skipn, length_firstn in H.
  rewrite Zlength_correct. lia.
Qed.

Lemma dfb_blocks_ok_nth : forall w bs hist k, blocks_ok w hist bs -> (k < length bs)%nat ->
  block_ok w (expand hist (firstn k bs)) (nth k bs (Stored [])).
Proof.
  induction bs as [|b r IH]; intros hist k H Hk; simpl in Hk; [lia|].
  destruct H as [H1 H2]. destruct k; simpl; [exact H1|].
  apply (IH (block_data hist b) k H2). lia.
Qed.

Lemma dfb_syms_ok_app : forall w ll dl a b out, syms_ok w ll dl out (a ++ b) ->
  syms_ok w ll dl (syms_data out a) b.
Proof.
  induction a as [|x r IH]; intros b out H; simpl in *; [exact H|].
  destruct H as [_ H]. apply IH. exact H.
Qed.

Lemma dfb_Zlength_bits_le : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma dfb_Zlength_flat3 : forall l, Zlength (flat_map (fun c => bits_le c 3) l) = 3 * Zlength l.
Proof.
  induction l as [|x r IH]; [reflexivity|].
  change (flat_map (fun c => bits_le c 3) (x :: r)) with (bits_le x 3 ++ flat_map (fun c => bits_le c 3) r).
  rewrite Zlength_app, IH, dfb_Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma dfb_fixed_ll : Forall (fun l => 0 <= l <= 15) fixed_ll.
Proof.
  apply Forall_forall. intros x Hx. unfold fixed_ll in Hx.
  repeat (apply in_app_or in Hx; destruct Hx as [Hx|Hx]); apply repeat_spec in Hx; lia.
Qed.

Lemma dfb_fixed_dl : Forall (fun l => 0 <= l <= 15) fixed_dl.
Proof.
  apply Forall_forall. intros x Hx. unfold fixed_dl in Hx. apply repeat_spec in Hx; lia.
Qed.

Lemma dfb_firstn_S : forall {A} (l: list A) j d, (j < length l)%nat ->
  firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  induction l as [|x r IH]; intros j d Hj; simpl in Hj; [lia|].
  destruct j; simpl; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma dfb : dkit_stmt -> hblk_stmt.
Proof.
  intros DK G s k j ll dl syms p0 HG Hin.
  destruct Hin as [[Hk Hlast] [Hcase [Hj [Htl [Htd Hp0]]]]].
  pose proof HG as HG'.
  destruct HG' as [[_ [_ [_ [_ [_ Hbo]]]]] _].
  assert (Hk' : (Z.to_nat k < length (dc_bs G))%nat).
  { unfold nblk in Hk. rewrite Zlength_correct in Hk. lia. }
  pose proof (dfb_blocks_ok_nth _ _ _ _ Hbo Hk') as Hbk.
  change (expand (dc_hist G) (firstn (Z.to_nat k) (dc_bs G))) with (outk G k) in Hbk.
  change (nth (Z.to_nat k) (dc_bs G) (Stored [])) with (blk G k) in Hbk.
  destruct (dk_blk DK G k HG Hk) as [Hbp Hsub].
  pose proof (dk_outk DK G k Hk) as Hout.
  set (fin := lastflag G k =? 1) in *.
  (* the common facts of both kinds of block *)
  assert (Hc : Forall (fun l => 0 <= l <= 15) ll /\ Forall (fun l => 0 <= l <= 15) dl /\
               Znth 256 ll <> 0 /\ 256 < Zlength ll /\
               syms_ok (2 ^ dc_wb G) ll dl (outk G k) syms /\
               block_data (outk G k) (blk G k) = syms_data (outk G k) syms /\
               exists P, enc_block (bpos G k - D0 G) fin (blk G k) = P ++ send_syms ll dl syms /\
                         Zlength P = hb_hdr (blk G k)).
  { destruct Hcase as [[Hb [-> ->]] | [nlen [ndist [clsent [toks [Hb [-> ->]]]]]]];
      rewrite Hb in *; simpl in Hbk.
    - split; [exact dfb_fixed_ll|]. split; [exact dfb_fixed_dl|].
      split; [vm_compute; discriminate|]. split; [reflexivity|].
      split; [exact Hbk|]. split; [reflexivity|].
      exists [fin; true; false]. split; reflexivity.
    - destruct Hbk as (Hnl & Hnd & Hcl & _ & _ & _ & Hlen & [Hll1 [Hll2 _]] & [Hdl1 _] & Hso).
      assert (Hzl : Zlength (dyn_ll nlen toks) = nlen).
      { unfold dyn_ll. rewrite Zlength_sublist; lia. }
      split; [exact Hll1|]. split; [exact Hdl1|]. split; [exact Hll2|]. split; [lia|].
      split; [exact Hso|]. split; [reflexivity|].
      eexists. split.
      + unfold enc_block. rewrite app_comm_cons. rewrite !app_assoc. reflexivity.
      + rewrite !Zlength_app, Zlength_cons, !dfb_Zlength_bits_le, dfb_Zlength_flat3 by lia.
        simpl. lia. }
  destruct Hc as (Hll & Hdl & H256 & Hzll & Hso & Hbd & P & Henc & HP).
  assert (Hpos : 0 < Zlength (enc_block (bpos G k - D0 G) fin (blk G k))).
  { unfold enc_block. rewrite Zlength_cons.
    match goal with |- 0 < Z.succ (Zlength ?l) => pose proof (Zlength_nonneg l) end. lia. }
  rewrite Henc in Hbp, Hsub, Hpos.
  unfold send_syms in Hbp, Hsub, Hpos.
  rewrite <- (firstn_skipn (Z.to_nat j) syms) in Hbp, Hsub, Hpos.
  rewrite flat_map_app in Hbp, Hsub, Hpos.
  set (A := flat_map (send_one ll dl) (firstn (Z.to_nat j) syms)) in *.
  set (B := flat_map (send_one ll dl) (skipn (Z.to_nat j) syms) ++ send_sym ll 256).
  assert (HA : sym_off ll dl syms j = Zlength A) by reflexivity.
  rewrite <- app_assoc in Hbp, Hsub, Hpos. fold B in Hbp, Hsub, Hpos.
  rewrite !Zlength_app in Hbp, Hpos.
  pose proof (dfb_bpos_nonneg G k) as Hb0.
  pose proof (Zlength_nonneg P). pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B).
  assert (HlenB : p0 + Zlength B = bpos G (k + 1)) by lia.
  assert (Hsbits : bpos G (k + 1) <= Zlength (sbits G)).
  { destruct (Z.lt_ge_cases (bpos G k) (bpos G (k + 1))) as [Hlt|Hge].
    - apply (dfb_sublist_len (bpos G k)); [exact Hlt|]. rewrite Hsub, !Zlength_app. lia.
    - (* the block has at least its BFINAL bit *)
      lia. }
  assert (HB : sublist p0 (bpos G (k + 1)) (sbits G) = B).
  { assert (E : sublist (Zlength P + Zlength A) (Zlength P + Zlength A + Zlength B) (P ++ A ++ B) = B).
    { rewrite sublist_app2 by lia. rewrite sublist_app2 by lia.
      apply sublist_same; lia. }
    rewrite <- Hsub in E. rewrite sublist_sublist in E by lia.
    rewrite <- E. f_equal; lia. }
  split; [exact Hll|]. split; [exact Hdl|]. split; [exact H256|]. split; [exact Hzll|].
  split; [exact Hsbits|]. split; [exact HlenB|]. split; [exact HB|].
  split.
  - intros Hjl.
    assert (Hjn : (Z.to_nat j < length syms)%nat) by (rewrite Zlength_correct in Hjl; lia).
    assert (Hfs : firstn (Z.to_nat (j + 1)) syms = firstn (Z.to_nat j) syms ++ [sym_at syms j]).
    { replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. apply dfb_firstn_S. exact Hjn. }
    assert (Hout1 : outj G k syms (j + 1) = sym_data (outj G k syms j) (sym_at syms j)).
    { unfold outj, syms_data. rewrite Hfs, fold_left_app. reflexivity. }
    split; [|split; [exact Hout1|]].
    + rewrite <- (firstn_skipn (Z.to_nat j) syms) in Hso.
      apply dfb_syms_ok_app in Hso.
      unfold sym_at. destruct (skipn (Z.to_nat j) syms) eqn:Es.
      * exfalso. apply (f_equal (@length sym)) in Es. rewrite skipn_length in Es. simpl in Es. lia.
      * assert (nth (Z.to_nat j) syms (Lit 0) = s0).
        { rewrite <- (firstn_skipn (Z.to_nat j) syms), app_nth2, Es; rewrite firstn_length; [|lia].
          replace (Z.to_nat j - Init.Nat.min (Z.to_nat j) (length syms))%nat with 0%nat by lia. reflexivity. }
        rewrite H2. destruct Hso as [Hso _]. exact Hso.
    + split; [split; assumption|]. split; [exact Hcase|]. split; [lia|].
      split; [exact Htl|]. split; [exact Htd|].
      rewrite Hp0. unfold sym_off. rewrite Hfs, flat_map_app, Zlength_app. simpl flat_map.
      rewrite app_nil_r. fold A. lia.
  - intros ->. unfold outj. rewrite firstn_all2 by (rewrite Zlength_correct; lia).
    rewrite Hout, <- Hbd. reflexivity.
Qed.

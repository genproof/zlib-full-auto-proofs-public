(* RT-I: copy of rfc1951/DecCallOut.v over the generalized definitions RTIGDefs.v. *)
(* Part of dec_call: what at_mode (DecodeDefs.v) says about the output o (history included):
   it starts with the history, it is a prefix of the full data, it is bytes, and where it is relative to the
   last block (for data_type's bit 64). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition dco_concl (G: dctx) (s: istate) (o: list Z) : Prop :=
  (exists d, o = dc_hist G ++ d) /\ (exists r, full G = o ++ r) /\ bytes_ok o /\
  (i_last s <> 0 -> Zlength (outk G (nblk G - 1)) <= Zlength o) /\
  (i_last s = 0 -> Zlength o <= Zlength (outk G (nblk G - 1))).

Lemma dco_len_prefix : forall (a b: list Z), (exists e, a = b ++ e) -> Zlength b <= Zlength a.
Proof. intros a b [e ->]. rewrite Zlength_app. pose proof (Zlength_nonneg e). lia. Qed.

Lemma dco_lz_add : forall a b d o, lz_copy (a + b) d o = lz_copy b d (lz_copy a d o).
Proof. induction a; intros; simpl; auto. Qed.

Lemma dco_lz_ext : forall n d o, exists e, lz_copy n d o = o ++ e.
Proof.
  induction n; intros; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (IHn d (o ++ [Znth (Zlength o - d) o])) as [e He]. rewrite He, <- app_assoc. eauto.
Qed.

Lemma dco_lz_le : forall a b d o, (a <= b)%nat -> exists e, lz_copy b d o = lz_copy a d o ++ e.
Proof.
  intros. replace b with (a + (b - a))%nat by lia. rewrite dco_lz_add. apply dco_lz_ext.
Qed.

Lemma dco_sym_ext : forall o s, exists e, sym_data o s = o ++ e.
Proof. intros o []; simpl. - eauto. - apply dco_lz_ext. Qed.

Lemma dco_syms_ext : forall l o, exists e, syms_data o l = o ++ e.
Proof.
  induction l; intros; unfold syms_data; simpl.
  - exists []. rewrite app_nil_r. auto.
  - destruct (dco_sym_ext o a) as [e1 He1]. destruct (IHl (sym_data o a)) as [e2 He2].
    unfold syms_data in He2. rewrite He2, He1, <- app_assoc. eauto.
Qed.

Lemma dco_syms_app : forall o l1 l2, syms_data o (l1 ++ l2) = syms_data (syms_data o l1) l2.
Proof. intros. unfold syms_data. apply fold_left_app. Qed.

Lemma dco_block_ext : forall o b, exists e, block_data o b = o ++ e.
Proof. intros o []; simpl; eauto using dco_syms_ext. Qed.

Lemma dco_outk_prefix : dkit_stmt -> forall G i n, 0 <= i -> i + Z.of_nat n <= nblk G ->
  exists e, outk G (i + Z.of_nat n) = outk G i ++ e.
Proof.
  intros K G i n Hi. induction n; intros Hn.
  - exists []. rewrite Z.add_0_r, app_nil_r. auto.
  - destruct IHn as [e He]; [lia|].
    replace (i + Z.of_nat (S n)) with ((i + Z.of_nat n) + 1) by lia.
    rewrite (dk_outk K) by lia.
    destruct (dco_block_ext (outk G (i + Z.of_nat n)) (blk G (i + Z.of_nat n))) as [e2 He2].
    rewrite He2, He, <- app_assoc. eauto.
Qed.

Lemma dco_outk_le : dkit_stmt -> forall G i j, 0 <= i <= j -> j <= nblk G ->
  exists e, outk G j = outk G i ++ e.
Proof.
  intros K G i j Hij Hj. replace j with (i + Z.of_nat (Z.to_nat (j - i))) by lia.
  apply dco_outk_prefix; auto; lia.
Qed.

Lemma dco_lz_bytes : forall n d o, Forall byte_ok o -> Forall byte_ok (lz_copy n d o).
Proof.
  induction n; intros; simpl; auto. apply IHn. apply Forall_app; split; auto. constructor; auto.
  destruct (Z_le_gt_dec 0 (Zlength o - d)); [destruct (Z_lt_ge_dec (Zlength o - d) (Zlength o))|].
  - apply Forall_Znth; auto; lia.
  - rewrite Znth_outofbounds by lia. unfold byte_ok, default, Inhabitant_Z; lia.
  - rewrite Znth_outofbounds by lia. unfold byte_ok, default, Inhabitant_Z; lia.
Qed.

Lemma dco_syms_bytes : forall w ll dl l o, syms_ok w ll dl o l -> Forall byte_ok o ->
  Forall byte_ok (syms_data o l).
Proof.
  induction l; intros o H Ho; unfold syms_data; simpl in *; auto.
  destruct H as [H1 H2]. apply IHl; auto.
  destruct a; simpl in *.
  - apply Forall_app; split; auto. constructor; [tauto|auto].
  - apply dco_lz_bytes; auto.
Qed.

Lemma dco_blocks_bytes : forall w bs o, blocks_ok w o bs -> Forall byte_ok o -> Forall byte_ok (expand o bs).
Proof.
  induction bs; intros o H Ho; unfold expand; simpl in *; auto.
  destruct H as [H1 H2]. apply IHbs; auto.
  destruct a; simpl in *.
  - apply Forall_app; tauto.
  - eapply dco_syms_bytes; eauto.
  - destruct H1 as (_&_&_&_&_&_&_&_&_&Hs). eapply dco_syms_bytes; eauto.
Qed.

Lemma dco_full_bytes : forall G, dctx_ok G -> Forall byte_ok (full G).
Proof.
  intros G (Hs & _). destruct Hs as (_ & _ & _ & _ & Hh & Hb). eapply dco_blocks_bytes; eauto.
Qed.

Lemma dco_nblk : forall G, dctx_ok G -> 1 <= nblk G.
Proof.
  intros G (Hs & _). destruct Hs as (_ & _ & _ & Hne & _). unfold nblk.
  destruct (dc_bs G); [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma dco_bytes_ok : forall o r G, dctx_ok G -> full G = o ++ r -> bytes_ok o.
Proof.
  intros o r G HG Hf. pose proof (dco_full_bytes G HG) as H. rewrite Hf in H.
  apply Forall_app in H. destruct H as [H _]. unfold bytes_ok.
  eapply Forall_impl; [|exact H]. intros a Ha. unfold byte_ok in Ha.
  change Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma dco_fin_at : dkit_stmt -> forall G s o k, dctx_ok G -> 0 <= k <= nblk G -> o = outk G k ->
  (i_last s <> 0 -> k = nblk G) -> (i_last s = 0 -> k <= nblk G - 1) -> dco_concl G s o.
Proof.
  intros K G s o k HG Hk Ho H1 H0. pose proof (dco_nblk G HG).
  destruct (dk_full_len K G k Hk) as [_ [r Hr]].
  split; [|split; [|split; [|split]]].
  - destruct (dco_outk_le K G 0 k) as [e He]; [lia|lia|]. rewrite (dk_outk0 K) in He. subst o. eauto.
  - subst o. eauto.
  - subst o. eapply dco_bytes_ok; eauto.
  - intros Hl. specialize (H1 Hl). subst o k. apply dco_len_prefix, dco_outk_le; auto; lia.
  - intros Hl. specialize (H0 Hl). subst o. apply dco_len_prefix, dco_outk_le; auto; lia.
Qed.

Lemma dco_fin_between : dkit_stmt -> forall G s o k, dctx_ok G -> 0 <= k < nblk G ->
  i_last s = lastflag G k ->
  (exists e, o = outk G k ++ e) -> (exists e, outk G (k + 1) = o ++ e) -> dco_concl G s o.
Proof.
  intros K G s o k HG Hk Hl [e1 He1] [e2 He2].
  destruct (dk_full_len K G (k + 1)) as [_ [r Hr]]; [lia|].
  split; [|split; [|split; [|split]]].
  - destruct (dco_outk_le K G 0 k) as [e He]; [lia|lia|]. rewrite (dk_outk0 K) in He.
    rewrite He1, He, <- app_assoc. eauto.
  - rewrite Hr, He2, <- app_assoc. eauto.
  - eapply dco_bytes_ok; eauto. rewrite Hr, He2, <- app_assoc. eauto.
  - intros H1. unfold lastflag in Hl. destruct (Z.eqb_spec k (nblk G - 1)); [|lia].
    subst k. apply dco_len_prefix. eauto.
  - intros H0. unfold lastflag in Hl. destruct (Z.eqb_spec k (nblk G - 1)); [lia|].
    apply (Z.le_trans _ (Zlength (outk G (k + 1)))).
    + apply dco_len_prefix. eauto.
    + apply dco_len_prefix, dco_outk_le; auto; lia.
Qed.

Lemma dco_huff_blk : forall G s k j ll dl syms p0, in_huff G s k j ll dl syms p0 ->
  block_data (outk G k) (blk G k) = syms_data (outk G k) syms.
Proof.
  intros. destruct H as (_ & [[Hb _]|(nl & nd & cl & tk & Hb & _)] & _); rewrite Hb; reflexivity.
Qed.

Lemma dco_skipn_cons : forall {A} (l: list A) n d, (n < length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof. induction l; intros; destruct n; simpl in *; try lia; auto. apply IHl; lia. Qed.

Lemma dco_huff_between : dkit_stmt -> forall G s o k j ll dl syms p0, dctx_ok G ->
  in_huff G s k j ll dl syms p0 ->
  (exists e, o = outj G k syms j ++ e) ->
  (exists e, syms_data (outj G k syms j) (skipn (Z.to_nat j) syms) = o ++ e) -> dco_concl G s o.
Proof.
  intros K G s o k j ll dl syms p0 HG Hh [e1 He1] [e2 He2].
  pose proof Hh as Hh'. destruct Hh' as ((Hk & Hl) & _).
  apply (dco_fin_between K G s o k); auto.
  - destruct (dco_syms_ext (firstn (Z.to_nat j) syms) (outk G k)) as [e He].
    unfold outj in He1. rewrite He1, He, <- app_assoc. eauto.
  - rewrite (dk_outk K) by lia. rewrite (dco_huff_blk _ _ _ _ _ _ _ _ Hh).
    rewrite <- (firstn_skipn (Z.to_nat j) syms), dco_syms_app. fold (outj G k syms j). eauto.
Qed.

Lemma dco_shape : dkit_stmt -> forall G s c hold bits o,
  dctx_ok G -> at_mode G s c hold bits o ->
  (exists d, o = dc_hist G ++ d) /\ (exists r, full G = o ++ r) /\ bytes_ok o /\
  (i_last s <> 0 -> Zlength (outk G (nblk G - 1)) <= Zlength o) /\
  (i_last s = 0 -> Zlength o <= Zlength (outk G (nblk G - 1))).
Proof.
  intros K G s c hold bits o HG [_ Hm]. fold (dco_concl G s o).
  pose proof (dco_nblk G HG) as Hn.
  repeat match goal with H: _ \/ _ |- _ => destruct H end;
  match goal with H: _ /\ _ |- _ => destruct H as [_ Ha] end;
  assert (Hpre: forall x: list Z, exists e, x = x ++ e) by (intros; exists []; rewrite app_nil_r; auto).
    all: try solve [match goal with Ha: False |- _ => destruct Ha end].
    all: try solve [match goal with Ha: at_head _ _ _ _ _ |- _ =>
      destruct Ha as (Ho & _ & _ & Hl); apply (dco_fin_at K G s o 0); auto; lia end].
    all: try solve [match goal with Ha: at_gzhdr _ _ _ _ _ _ |- _ =>
      destruct Ha as (h & _ & Ho & Hl & _); apply (dco_fin_at K G s o 0); auto; lia end].
    all: try solve [match goal with Ha: at_type _ _ _ _ _ |- _ =>
      destruct Ha as (k & Hk & _ & Ho & _ & Hl); apply (dco_fin_at K G s o k); auto; intros H;
      rewrite Hl in H; destruct (Z.eqb_spec k 0); unfold lastflag in H;
      destruct (Z.eqb_spec (k - 1) (nblk G - 1)); lia end].
    all: try solve [match goal with Ha: at_stored _ _ _ _ _ |- _ =>
      destruct Ha as (k & bytes & [Hk Hl] & Hb & Ho & _); apply (dco_fin_between K G s o k); auto;
      [rewrite Ho; apply Hpre | rewrite (dk_outk K) by lia; rewrite Ho; apply dco_block_ext] end].
    all: try solve [match goal with Ha: at_copy _ _ _ _ _ |- _ =>
      destruct Ha as (k & bytes & [Hk Hl] & Hb & Hr & _ & _ & Ho); apply (dco_fin_between K G s o k); auto;
      [rewrite Ho; eauto
      | rewrite (dk_outk K) by lia; rewrite Hb, Ho; simpl;
        exists (sublist (Zlength bytes - i_length s) (Zlength bytes) bytes);
        rewrite <- app_assoc, <- sublist_split, sublist_same by lia; auto] end].
    all: try solve [match goal with Ha: at_table _ _ _ _ _ |- _ =>
      destruct Ha as (k & nl & nd & cl & tk & sy & [Hk Hl] & Hb & Ho & _);
      apply (dco_fin_between K G s o k); auto;
      [rewrite Ho; apply Hpre | rewrite (dk_outk K) by lia; rewrite Ho; apply dco_block_ext] end].
    all: try solve [match goal with Ha: at_lenlens _ _ _ _ _ |- _ =>
      destruct Ha as (k & nl & nd & cl & tk & sy & [Hk Hl] & Hb & Ho & _);
      apply (dco_fin_between K G s o k); auto;
      [rewrite Ho; apply Hpre | rewrite (dk_outk K) by lia; rewrite Ho; apply dco_block_ext] end].
    all: try solve [match goal with Ha: at_codelens _ _ _ _ _ |- _ =>
      destruct Ha as (k & nl & nd & cl & tk & sy & t & [Hk Hl] & Hb & Ho & _);
      apply (dco_fin_between K G s o k); auto;
      [rewrite Ho; apply Hpre | rewrite (dk_outk K) by lia; rewrite Ho; apply dco_block_ext] end].
    all: try solve [match goal with Ha: at_len _ _ _ _ _ |- _ =>
      destruct Ha as (k & j & ll & dl & sy & p0 & Hh & Ho & _);
      apply (dco_huff_between K G s o k j ll dl sy p0); auto;
      [rewrite Ho; apply Hpre | rewrite Ho; apply dco_syms_ext] end].
    all: try solve [match goal with Ha: at_lenext _ _ _ _ _ |- _ =>
      destruct Ha as (k & j & ll & dl & sy & p0 & len & dist & Hh & _ & _ & Ho & _);
      apply (dco_huff_between K G s o k j ll dl sy p0); auto;
      [rewrite Ho; apply Hpre | rewrite Ho; apply dco_syms_ext] end].
    all: try solve [match goal with Ha: at_dist _ _ _ _ _ |- _ =>
      destruct Ha as (k & j & ll & dl & sy & p0 & len & dist & Hh & _ & _ & Ho & _);
      apply (dco_huff_between K G s o k j ll dl sy p0); auto;
      [rewrite Ho; apply Hpre | rewrite Ho; apply dco_syms_ext] end].
    all: try solve [match goal with Ha: at_distext _ _ _ _ _ |- _ =>
      destruct Ha as (k & j & ll & dl & sy & p0 & len & dist & Hh & _ & _ & Ho & _);
      apply (dco_huff_between K G s o k j ll dl sy p0); auto;
      [rewrite Ho; apply Hpre | rewrite Ho; apply dco_syms_ext] end].
    all: try solve [match goal with Ha: at_lit _ _ _ _ _ |- _ =>
      destruct Ha as (k & j & ll & dl & sy & p0 & b & Hh & _ & _ & _ & Ho & _);
      apply (dco_huff_between K G s o k j ll dl sy p0); auto;
      [rewrite Ho; apply Hpre | rewrite Ho; apply dco_syms_ext] end].
    all: try solve [match goal with Ha: at_check _ _ _ _ _ |- _ =>
      destruct Ha as (Ho & Hl & _); apply (dco_fin_at K G s o (nblk G)); auto; try lia;
      rewrite (dk_full K); auto end].
    all: try solve [match goal with Ha: at_length _ _ _ _ _ |- _ =>
      destruct Ha as (Ho & Hl & _); apply (dco_fin_at K G s o (nblk G)); auto; try lia;
      rewrite (dk_full K); auto end].
    all: try solve [match goal with Ha: at_done _ _ _ _ _ |- _ =>
      destruct Ha as (Ho & Hl & _); apply (dco_fin_at K G s o (nblk G)); auto; try lia;
      rewrite (dk_full K); auto end].
  all: match goal with Ha: at_match _ _ _ _ _ |- _ =>
    destruct Ha as (k & j & ll & dl & sy & p0 & len & dist & Hh & Hj & Hs & _ & Hl & Ho & _) end.
  all: apply (dco_huff_between K G s o k j ll dl sy p0); auto; [rewrite Ho; apply dco_lz_ext|].
  all: assert (Hj0: 0 <= j) by (destruct Hh as (_ & _ & ? & _); lia).
  all: rewrite (dco_skipn_cons sy (Z.to_nat j) (Lit 0)) by (rewrite Zlength_correct in Hj; lia).
  all: unfold sym_at in Hs; rewrite Hs; change (syms_data (outj G k sy j) (Ref len dist :: skipn (S (Z.to_nat j)) sy)) with
        (syms_data (lz_copy (Z.to_nat len) dist (outj G k sy j)) (skipn (S (Z.to_nat j)) sy)).
  all: destruct (dco_syms_ext (skipn (S (Z.to_nat j)) sy) (lz_copy (Z.to_nat len) dist (outj G k sy j)))
        as [e He].
  all: destruct (dco_lz_le (Z.to_nat (len - i_length s)) (Z.to_nat len) dist (outj G k sy j)) as [e' He'];
        [lia|].
  all: rewrite He, He', <- app_assoc, <- Ho; eauto.
Qed.

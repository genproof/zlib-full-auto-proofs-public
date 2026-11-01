(* Law inflate_header, theory part: the NAME/COMMENT do-while (zstr_f) and EXTRA's put_bytes, in terms of fbuf *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihs_fbuf_lt (b0 f: list Z) k : 0 <= k <= Zlength f -> k <= Zlength b0 ->
  fbuf b0 (sublist 0 k f) = sublist 0 k f ++ sublist k (Zlength b0) b0.
Proof. intros K B. unfold fbuf. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, Z.min_l by lia. f_equal. list_solve. Qed.

Lemma ihs_fbuf_ge (b0 f: list Z) k : Zlength b0 <= k <= Zlength f ->
  fbuf b0 (sublist 0 k f) = sublist 0 (Zlength b0) f.
Proof.
  intros K. unfold fbuf. rewrite Zlength_sublist by (pose proof (Zlength_nonneg b0); lia).
  rewrite Z.sub_0_r, Z.min_r by lia. rewrite sublist_nil, app_nil_r. list_solve.
Qed.

Lemma ihs_fbuf_step (b0 f: list Z) k : 0 <= k -> k < Zlength f -> k < Zlength b0 ->
  upd_Znth k (fbuf b0 (sublist 0 k f)) (Znth k f) = fbuf b0 (sublist 0 (k + 1) f).
Proof.
  intros K0 K1 K2. rewrite ihs_fbuf_lt, ihs_fbuf_lt by lia. list_solve.
Qed.

Lemma ihs_zstr_gen (f bytes buf b0: list Z) (j have: Z) (wr: bool) :
  0 < Zlength f -> Znth (Zlength f - 1) f = 0 -> (forall i, 0 <= i < Zlength f - 1 -> Znth i f <> 0) ->
  0 <= j -> (forall i, 0 <= i < Z.min have (Zlength f - j) -> Znth i bytes = Znth (j + i) f) ->
  forall (k: nat) (copy: Z),
    0 <= copy -> j + copy < Zlength f -> copy < have -> have - copy <= Z.of_nat k ->
    (wr = true -> buf = fbuf b0 (sublist 0 (j + copy) f)) ->
    zstr_f k bytes have (if wr then Z.min (j + copy) (Zlength b0) else 0) (Zlength b0) wr buf copy =
    (Z.min have (Zlength f - j), Znth (j + Z.min have (Zlength f - j) - 1) f,
     (if wr then Z.min (j + Z.min have (Zlength f - j)) (Zlength b0) else 0),
     (if wr then fbuf b0 (sublist 0 (j + Z.min have (Zlength f - j)) f) else buf)).
Proof.
  intros Fl Fz Fnz J BY k. revert buf. induction k as [|k IH]; intros buf copy C0 C1 C2 Ck Hb.
  - cbn in Ck. lia.
  - cbn [zstr_f].
    assert (Eb: Znth copy bytes = Znth (j + copy) f) by (apply BY; lia).
    rewrite Eb.
    pose proof (Zlength_nonneg b0) as B0.
    (* the store *)
    assert (ST: (if (wr && ((if wr then Z.min (j + copy) (Zlength b0) else 0) <? Zlength b0))%bool
                 then ((if wr then Z.min (j + copy) (Zlength b0) else 0) + 1,
                       upd_Znth (if wr then Z.min (j + copy) (Zlength b0) else 0) buf (Znth (j + copy) f))
                 else (if wr then Z.min (j + copy) (Zlength b0) else 0, buf)) =
                (if wr then Z.min (j + copy + 1) (Zlength b0) else 0,
                 if wr then fbuf b0 (sublist 0 (j + copy + 1) f) else buf)).
    { destruct wr; cbn [andb].
      - specialize (Hb eq_refl). subst buf.
        destruct (Z.ltb_spec (j + copy) (Zlength b0)) as [L|L].
        + rewrite Z.min_l by lia. rewrite (proj2 (Z.ltb_lt _ _) L).
          rewrite Z.min_l by lia. rewrite ihs_fbuf_step by lia. reflexivity.
        + rewrite Z.min_r by lia. rewrite Z.ltb_irrefl. rewrite Z.min_r by lia.
          rewrite !ihs_fbuf_ge by lia. reflexivity.
      - reflexivity. }
    rewrite ST. clear ST.
    destruct (negb (Znth (j + copy) f =? 0) && (copy + 1 <? have))%bool eqn:G.
    + apply andb_true_iff in G. destruct G as [G1 G2]. apply negb_true_iff, Z.eqb_neq in G1.
      apply Z.ltb_lt in G2.
      assert (C1': j + (copy + 1) < Zlength f).
      { destruct (Z.eq_dec (j + copy) (Zlength f - 1)) as [Eq|Ne]; [rewrite Eq in G1; contradiction | lia]. }
      replace (j + copy + 1) with (j + (copy + 1)) by lia.
      destruct wr.
      * apply IH; try lia; intros _; reflexivity.
      * apply (IH buf (copy + 1)); try lia; intros W; discriminate.
    + apply andb_false_iff in G.
      assert (Cc: Z.min have (Zlength f - j) = copy + 1).
      { destruct G as [G|G].
        - apply negb_false_iff, Z.eqb_eq in G.
          assert (j + copy = Zlength f - 1).
          { destruct (Z.eq_dec (j + copy) (Zlength f - 1)) as [Eq|Ne]; [exact Eq|].
            exfalso. apply (Fnz (j + copy)); [lia | exact G]. }
          lia.
        - apply Z.ltb_ge in G. lia. }
      rewrite Cc. replace (j + (copy + 1) - 1) with (j + copy) by lia.
      replace (j + (copy + 1)) with (j + copy + 1) by lia. reflexivity.
Qed.

Lemma ihs_zstr : ih_zstr_stmt.
Proof.
  intros f bytes buf b0 j have wr k Fl Fz Fnz J Hv Hk BY Hb.
  pose proof (ihs_zstr_gen f bytes buf b0 j have wr Fl Fz Fnz ltac:(lia) BY k 0) as G.
  rewrite !Z.add_0_r in G. apply G; try lia. exact Hb.
Qed.

Lemma ihs_put : ih_put_stmt.
Proof.
  intros b0 xf j c J C JC XL.
  assert (U: u32 (j + c) = j + c) by (unfold u32; apply Z.mod_small; lia).
  rewrite U. split.
  - intros L. unfold put_bytes. rewrite ihs_fbuf_lt by lia.
    destruct (Z.ltb_spec (Zlength b0) (j + c)) as [M|M].
    + rewrite ihs_fbuf_ge by lia. replace (j + (Zlength b0 - j)) with (Zlength b0) by lia. list_solve.
    + rewrite ihs_fbuf_lt by lia. list_solve.
  - intros L. rewrite !ihs_fbuf_ge by lia. reflexivity.
Qed.

Lemma ih_str_proof : ih_zstr_stmt /\ ih_put_stmt.
Proof. exact (conj ihs_zstr ihs_put). Qed.

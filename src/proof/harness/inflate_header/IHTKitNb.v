(* Law inflate_header, theory part: NEEDBITS on whole bytes of src *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihn_le_app l b : ih_le (l ++ [b]) = ih_le l + b * 2 ^ (8 * Zlength l).
Proof.
  induction l as [|x l IH].
  - cbn. lia.
  - cbn [app ih_le]. rewrite IH, Zlength_cons.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256. ring.
Qed.

Lemma ihn_le_bound l : is_bytes l -> 0 <= ih_le l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|x l IH]; intros B.
  - cbn. lia.
  - inversion B as [|? ? Bx Bl]; subst. specialize (IH Bl). cbn [ih_le]. rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256.
    change Byte.max_unsigned with 255 in Bx. lia.
Qed.

Lemma ihn_q n : 0 < n -> 8 * ((n + 7) / 8) <= n + 7 /\ n + 7 < 8 * ((n + 7) / 8) + 8.
Proof.
  intros N. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia.
Qed.

Lemma ihn_nbf (src inp: list Z) (pos a n: Z) : forall (k: nat) (m: mst),
  is_bytes src -> 0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 < n <= 32 -> 0 <= a ->
  a <= pos + m_nx m <= a + (n + 7) / 8 -> (n + 7) / 8 - (pos + m_nx m - a) <= Z.of_nat k ->
  m_bits m = 8 * (pos + m_nx m - a) -> m_hold m = ih_le (sublist a (pos + m_nx m) src) ->
  exists nx' lv',
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') (ih_le (sublist a (pos + nx') src)))
                                     (8 * (pos + nx' - a))) lv' /\
    m_nx m <= nx' <= Zlength inp /\
    ((lv' = 1 /\ nx' = Zlength inp /\ pos + nx' < a + (n + 7) / 8) \/
     (lv' = m_leave m /\ pos + nx' = a + (n + 7) / 8)).
Proof.
  intros k. induction k as [|k IH]; intros m B P0 PL E Ki Kn Nn A Pr Fk Bb Bh.
  - exists (m_nx m), (m_leave m). split.
    + cbn [needbits_f]. rewrite <- Bh, <- Bb. destruct m; reflexivity.
    + split; [lia|]. right. split; [reflexivity | lia].
  - pose proof (ihn_q n ltac:(lia)) as [Q1 Q2].
    set (q := (n + 7) / 8) in *.
    cbn [needbits_f].
    destruct (Z.ltb_spec (m_bits m) n) as [Lt|Ge].
    + assert (Kq: pos + m_nx m - a < q) by lia.
      destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), 1. split.
        -- unfold set_leave. rewrite <- Bh, <- Bb. destruct m; reflexivity.
        -- unfold m_have in H0. rewrite Ki in H0. split; [lia|]. left. split; [reflexivity|]. split; lia.
      * unfold m_have in H0. rewrite Ki in H0.
        assert (Hp: 0 <= pos + m_nx m - a <= 3).
        { assert (q <= 4) by lia. lia. }
        assert (Zb: Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) src).
        { rewrite Ki. set (L := Zlength inp) in *. clearbody L. subst inp.
          rewrite Znth_sublist by lia. f_equal; lia. }
        assert (Lab: Zlength (sublist a (pos + m_nx m) src) = pos + m_nx m - a)
          by (rewrite Zlength_sublist; lia).
        assert (Bs: is_bytes (sublist a (pos + m_nx m) src)) by (apply is_bytes_sublist; exact B).
        pose proof (ihn_le_bound _ Bs) as LB. rewrite Lab in LB.
        assert (Bz: 0 <= Znth (pos + m_nx m) src <= 255)
          by (pose proof (is_bytes_Znth src (pos + m_nx m) B ltac:(lia)); change Byte.max_unsigned with 255 in *; lia).
        assert (Hold': u64 (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) =
                       ih_le (sublist a (pos + m_nx m + 1) src)).
        { rewrite (sublist_split a (pos + m_nx m) (pos + m_nx m + 1)) by lia.
          rewrite sublist_len_1 by lia. rewrite ihn_le_app, Lab, <- Bh, Zb, Bb.
          unfold u64. apply Z.mod_small.
          assert (2 ^ (8 * (pos + m_nx m - a)) <= 2 ^ 24) by (apply Z.pow_le_mono_r; lia).
          assert (0 <= 2 ^ (8 * (pos + m_nx m - a))) by (apply Z.pow_nonneg; lia).
          split; [nia|]. assert (2 ^ 24 * 256 < 2 ^ 64) by reflexivity. nia. }
        destruct (IH (pull m) B P0 PL E ltac:(exact Ki) ltac:(cbn; lia) Nn A ltac:(cbn; lia) ltac:(cbn; lia)
                    ltac:(cbn; unfold u32; rewrite Bb, Z.mod_small; [lia | split; lia])
                    ltac:(cbn [pull m_hold set_m_bits set_m_hold set_m_nx m_nx]; rewrite Hold'; f_equal; f_equal; lia))
          as (nx' & lv' & EN & R & C).
        exists nx', lv'. split.
        -- rewrite EN. destruct m; reflexivity.
        -- cbn [pull m_nx m_leave set_m_bits set_m_hold set_m_nx] in R, C. split; [lia | exact C].
    + assert (Kq: pos + m_nx m - a = q).
      { assert (pos + m_nx m - a >= q \/ pos + m_nx m - a < q) as [H|H] by lia; [lia|]. lia. }
      exists (m_nx m), (m_leave m). split.
      * rewrite <- Bh, <- Bb. destruct m; reflexivity.
      * split; [lia|]. right. split; [reflexivity | lia].
Qed.

Lemma ih_nb_proof : ih_nb_stmt.
Proof.
  intros src inp pos a n m B P0 PL E Ki Kn Nn A Pr Bb Bh.
  apply (ihn_nbf src inp pos a n 4 m); auto.
  pose proof (ihn_q n ltac:(lia)) as [Q1 Q2]. assert ((n + 7) / 8 <= 4) by lia. change (Z.of_nat 4) with 4. lia.
Qed.

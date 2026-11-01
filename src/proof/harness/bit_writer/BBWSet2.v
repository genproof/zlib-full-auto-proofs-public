(* Law rj_bad_block, main: statements 12-23 of main's body (BBWSetKit.bbs_set2_stmt), the writes of the broken
   block into the stream after its first bit: BTYPE (put_bits), kind 0's gp_assume on LEN and NLEN, the literals
   (put_literal, any number of them) and the bad element of kinds 2, 3 and 4; the stream then holds
   BBFacts.bb_bytes and the inputs satisfy BBWDefs.bbw_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Import Zlib.proof.harness.bit_writer.BBWSetKit.

Lemma bbs_set2 : bbs_set2_stmt.
Proof.
  intros Espec gv vs vbt vbit w kind which lits S0 room stream literal out Hbound K.
  unfold bbs_A1, bbw_seg12, POST_B, bbw_POST. abbreviate_semax.
  Intros.
  rename H0 into Hk, H1 into Hwc, H2 into Hn0, H3 into Bl0, H4 into B0, H5 into Hs.
  pose proof (Zlength_nonneg lits) as Hl0.
  (* bit = 1; unsigned btype[5] = {0, 3, 1, 1, 2}; put_bits(stream, &bit, btype[kind], 2, 0); *)
  forward. forward. forward. forward. forward. forward.
  match goal with |- context [upd_Znth 4 ?l (Vint (Int.repr 2))] =>
    replace (upd_Znth 4 l (Vint (Int.repr 2))) with (map Vint (map Int.repr [0; 3; 1; 1; 2])) by reflexivity end.
  forward.
  change (Znth kind [0; 3; 1; 1; 2]) with (bb_btype kind).
  pose proof (bb_btype_range kind Hk) as Hbt.
  rewrite Int.signed_repr by rep_lia.
  forward_call (Ews, stream, Tsh, vbit, S0, 1, bb_btype kind, 2, 0).
  rewrite bb_bytes_a, bb_ulong_a.
  set (S1 := put_bits_m S0 1 (bb_btype kind) 2 0).
  destruct (put_bits_m_ok S0 1 (bb_btype kind) 2 0 B0 ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 B1].
  fold S1 in L1, B1.
  (* if (kind == 0) gp_assume((stream[1] | stream[2] << 8) != (~(stream[3] | stream[4] << 8) & 0xffff)); *)
  forward_if (kind = 0 -> Z.lor (Znth 1 S1) (Z.shiftl (Znth 2 S1) 8) <>
                          Z.land (Z.lnot (Z.lor (Znth 3 S1) (Z.shiftl (Znth 4 S1) 8))) 65535).
  { assert (Hb1: 0 <= Znth 1 S1 <= 255) by (apply (is_bytes_Znth S1); auto; lia).
    assert (Hb2: 0 <= Znth 2 S1 <= 255) by (apply (is_bytes_Znth S1); auto; lia).
    assert (Hb3: 0 <= Znth 3 S1 <= 255) by (apply (is_bytes_Znth S1); auto; lia).
    assert (Hb4: 0 <= Znth 4 S1 <= 255) by (apply (is_bytes_Znth S1); auto; lia).
    do 4 (forward;
      [rewrite Znth_bytes_rep by lia; go_lower; apply prop_right; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ];
      rewrite Znth_bytes_rep by lia).
    forward_call (if Int.eq (Int.or (Int.repr (Znth 1 S1)) (Int.shl (Int.repr (Znth 2 S1)) (Int.repr 8)))
                    (Int.and (Int.not (Int.or (Int.repr (Znth 3 S1)) (Int.shl (Int.repr (Znth 4 S1)) (Int.repr 8))))
                       (Int.repr 65535)) then Int.zero else Int.one).
    { entailer!. simpl. destruct (Int.eq _ _); reflexivity. }
    entailer!. eapply bb_assume_z; eassumption. }
  { forward. entailer!. }
  rename H into Hw. Intros. match goal with Ha: kind = 0 -> _ |- _ => rename Ha into Hassume end.
  (* for (i = 0; i < literals; i++) put_literal(stream, &bit, literal[i]); *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_for_simple_bound (Zlength lits)
      (EX i: Z, PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (put_lits S1 3 (sublist 0 i lits))) stream ::
         data_at Tsh tulong (Vlong (Int64.repr (3 + lits_len (sublist 0 i lits)))) vbit :: R))))
  end.
  { entailer!. }
  { assert (Hli: 0 <= Znth i lits <= 255) by (apply (is_bytes_Znth lits); auto; lia).
    forward; [rewrite Znth_bytes_rep by lia; go_lower; apply prop_right; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia | ].
    rewrite Znth_bytes_rep by lia.
    set (Si := put_lits S1 3 (sublist 0 i lits)).
    pose proof (lits_len_bounds (sublist 0 i lits)) as Bi.
    pose proof (lits_len_bounds (sublist 0 (i + 1) lits)) as Bi1.
    rewrite !Zlength_sublist in Bi, Bi1 by lia.
    destruct (put_lits_snoc (sublist 0 i lits) (Znth i lits) S1 3) as [E1 E2].
    rewrite <- sublist_last_1 in E1, E2 by lia.
    destruct (put_lits_ok (sublist 0 i lits) S1 3 B1 ltac:(lia) ltac:(lia)) as [LSi BSi].
    fold Si in LSi, BSi, E1.
    rewrite <- L1, <- LSi.
    forward_call (Ews, stream, Tsh, vbit, Si, 3 + lits_len (sublist 0 i lits), Znth i lits).
    rewrite bb_bytes_a, bb_ulong_a.
    entailer!. rewrite E1, E2, Z.add_assoc, LSi, L1. cancel. }
  rewrite sublist_same by lia.
  Intros.
  set (S2 := put_lits S1 3 lits).
  set (b := 3 + lits_len lits).
  pose proof (lits_len_bounds lits) as Bl.
  destruct (put_lits_ok lits S1 3 B1 ltac:(lia) ltac:(lia)) as [L2 B2]. fold S2 in L2, B2.
  (* if (kind == 2) put_bits(stream, &bit, 0xc6 + which, 8, 1); *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0))
           (bytes_rep (if kind =? 2 then put_bits_m S2 b (198 + which) 8 1 else S2)) stream ::
         data_at Tsh tulong (Vlong (Int64.repr (if kind =? 2 then b + 8 else b))) vbit :: R))))
  end.
  { subst kind. rewrite <- L1, <- L2.
    forward_call (Ews, stream, Tsh, vbit, S2, b, 198 + which, 8, 1).
    rewrite bb_bytes_a, bb_ulong_a.
    entailer!. rewrite L2, L1. cancel. }
  { forward. entailer!. destruct (Z.eqb_spec kind 2); [lia | cancel]. }
  (* if (kind == 3) { put_bits(stream, &bit, 1, 7, 1); put_bits(stream, &bit, 30 + which, 5, 1); } *)
  set (S3 := if kind =? 2 then put_bits_m S2 b (198 + which) 8 1 else S2).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0))
           (bytes_rep (if kind =? 3 then put_bits_m (put_bits_m S3 b 1 7 1) (b + 7) (30 + which) 5 1 else S3))
           stream ::
         data_at Tsh tulong (Vlong (Int64.repr (if kind =? 3 then b + 12 else if kind =? 2 then b + 8 else b)))
           vbit :: R))))
  end.
  { subst kind. unfold S3. replace (3 =? 2) with false by reflexivity. cbv iota.
    rewrite <- L1, <- L2.
    forward_call (Ews, stream, Tsh, vbit, S2, b, 1, 7, 1).
    rewrite bb_bytes_a, bb_ulong_a.
    destruct (put_bits_m_ok S2 b 1 7 1 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L3 B3].
    rewrite <- L3.
    forward_call (Ews, stream, Tsh, vbit, put_bits_m S2 b 1 7 1, b + 7, 30 + which, 5, 1).
    rewrite bb_bytes_a, bb_ulong_a.
    entailer!. rewrite L3, L2, L1, <- Z.add_assoc. cancel. }
  { forward. entailer!. destruct (Z.eqb_spec kind 3); [lia | cancel]. }
  (* if (kind == 4) put_bits(stream, &bit, 30 + which, 5, 0); *)
  set (S4 := if kind =? 3 then put_bits_m (put_bits_m S3 b 1 7 1) (b + 7) (30 + which) 5 1 else S3).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: _ :: ?R)))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx (
         data_at Ews (tarray tuchar (Zlength S0))
           (bytes_rep (if kind =? 4 then put_bits_m S4 b (30 + which) 5 0 else S4)) stream ::
         data_at_ Tsh tulong vbit :: R))))
  end.
  { subst kind. unfold S4, S3. replace (4 =? 3) with false by reflexivity. replace (4 =? 2) with false by reflexivity.
    cbv iota.
    rewrite <- L1, <- L2.
    forward_call (Ews, stream, Tsh, vbit, S2, b, 30 + which, 5, 0).
    rewrite bb_bytes_a, bb_ulong_a.
    entailer!. rewrite L2, L1. cancel. }
  { forward. entailer!. destruct (Z.eqb_spec kind 4); [lia | ]. cancel. }
  replace (if kind =? 4 then put_bits_m S4 b (30 + which) 5 0 else S4) with (bb_bytes S0 kind which lits)
    by (first [exact (bb_bytes_eq S0 kind which lits Hk) | symmetry; exact (bb_bytes_eq S0 kind which lits Hk)]).
  (* the inputs main reaches inflate() with *)
  assert (Hok: bbw_ok S0 kind which lits).
  { assert (Hn: kind <> 2 -> kind <> 3 -> lits = []).
    { intros K2 K3. destruct Hn0 as [[E | E] | E]; [lia | lia | exact E]. }
    unfold bbw_ok. split; [lia | ]. split; [lia | ]. split; [exact Hn | ]. split; [exact Bl0 | ].
    split; [exact B0 | ]. split; [exact Hs | ].
    intros E. subst kind. rewrite (Hn ltac:(lia) ltac:(lia)) in *. exact (Hassume eq_refl). }
  clear Hassume. clearbody S1 S2 S3 S4 b.
  (* the rest from bbs_A2 *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K].
  unfold bbs_A2. entailer!.
Qed.

(* Law rj_bad_block, main: statements 1-10 of main's body (BBWSetKit.bbs_set1_stmt): window_bits, kind, which,
   literals (kinds 2 and 3: any number up to (PTRDIFF_MAX - 5) / 9), stream_len (5 + 2 * literals bytes at least,
   PTRDIFF_MAX at most), room (literals at least, PTRDIFF_MAX at most), in 64-bit arithmetic without overflow; the
   objects stream and literal (any_bytes) and out (malloc). *)
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

Lemma bbs_set1 : bbs_set1_stmt.
Proof.
  intros Espec gv vs vbt vbit K.
  unfold bbw_A0, bbw_seg1, POST_B, bbw_POST. abbreviate_semax.
  (* window_bits = -8 - (int) upto(7) *)
  forward_call 7. Intros u7. forward.
  { entailer!. rewrite Int.signed_repr by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia; rep_lia).
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rep_lia. }
  rewrite Int64.unsigned_repr, Int.neg_repr, sub_repr by rep_lia.
  bb_upto BBC._t'2 4. Intros kind. forward.
  rewrite Int64.unsigned_repr by rep_lia.
  forward_call tt. Intros wh. forward.
  rewrite and_repr.
  forward.
  (* if (kind == 2 || kind == 3) literals = upto((PTRDIFF_MAX - 5) / 9); *)
  bb_if BBC._t'5 (Vint (Int.repr (if ((kind =? 2) || (kind =? 3))%bool then 1 else 0))).
  { forward. entailer!. }
  { forward. entailer!. bb_zcase. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := bb_rm_temp BBC._literals Q in
    forward_if (EX nl: Z, PROPx ((0 <= nl <= (Int64.max_signed - 5) / 9) :: ((kind = 2 \/ kind = 3) \/ nl = 0) :: P)
                  (LOCALx (temp BBC._literals (Vlong (Int64.repr nl)) :: Q') (SEPx R)))
  end.
  { forward_call ((Int64.max_signed - 5) / 9). Intros nl. forward. Exists nl. entailer!. bb_zcase. }
  { forward. Exists 0. entailer!. }
  Intros nl.
  change ((Int64.max_signed - 5) / 9) with 1024819115206086200 in *.
  (* stream_len = 5 + 2 * literals + upto(PTRDIFF_MAX - 5 - 2 * literals) *)
  repeat (apply -> seq_assoc). forward_call (Int64.max_signed - 5 - 2 * nl); try rep_lia. Intros t6. forward.
  (* room = literals + upto(PTRDIFF_MAX - literals) *)
  repeat (apply -> seq_assoc). forward_call (Int64.max_signed - nl); try rep_lia. Intros t7. forward.
  rewrite Int.signed_repr, Int.signed_repr, mul64_repr, !add64_repr by rep_lia.
  (* stream = any_bytes(stream_len); literal = any_bytes(literals) *)
  bb_new_bytes BBC._t'8 (5 + 2 * nl + t6) gv. Intros stream S0. forward.
  bb_new_bytes BBC._t'9 nl gv. Intros literal lits. forward.
  (* out = malloc(room) *)
  set (room := nl + t7).
  repeat (apply -> seq_assoc).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX q: val,
             PROPx (is_pointer_or_null q :: P)
             (LOCALx (temp BBC._t'10 q :: Q)
             (SEPx ((if eq_dec q nullval then emp
                     else (malloc_token Ews (tarray tuchar room) q * data_at_ Ews (tarray tuchar room) q)) :: R))))
  end.
  { forward_call (tarray tuchar room, gv).
    { simpl. rewrite Z.max_r by rep_lia. rep_lia. }
    Intros q. Exists q. destruct (eq_dec q nullval); entailer!. }
  Intros out. forward.
  (* the rest from bbs_A10 *)
  rewrite <- H6, <- H8 in *.
  assert (Hwc: 0 <= Z.land wh 1 <= 1).
  { assert (E: Z.land wh 1 = wh mod 2) by (apply (Z.land_ones wh 1); lia).
    rewrite E. pose proof (Z.mod_pos_bound wh 2 ltac:(lia)). lia. }
  assert (Hn: (kind = 2 \/ kind = 3) \/ lits = []).
  { destruct H3 as [K23 | K0]; [left; exact K23 | right; apply Zlength_nil_inv; lia]. }
  assert (Hs: 5 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed) by lia.
  assert (Hr: Zlength lits <= room <= Int64.max_signed) by (unfold room; lia).
  assert (Hb: 9 * Zlength lits + 15 <= Int64.max_unsigned) by rep_lia.
  clearbody room. clear H3 H4 H5 H6.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K (-8 - u7) kind (Z.land wh 1) lits S0 room stream literal out)].
  unfold bbs_A10. entailer!.
Qed.

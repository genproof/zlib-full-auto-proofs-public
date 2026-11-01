(* Law rj_bad_dictionary, main (RDMain.v), statements 1-7: the inputs window_bits, stream_len (any length up
   to PTRDIFF_MAX), room and dict_len (up to UINT_MAX), and the three objects *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.harness.rj_bad_dictionary.code.
Local Open Scope Z_scope.

Lemma seg_inputs_ok : seg_inputs_stmt.
Proof.
  intros Espec gv v_strm K.
  unfold rd_seg1, rd_A0, POST_B, POST_rd, t_zsl. abbreviate_semax.
  forward_call 7. Intros t1.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.signed_repr by rep_lia.
    rep_lia. }
  rewrite Int64.unsigned_repr by rep_lia. rewrite add_repr.
  forward_call (Int64.max_signed - 6). Intros t2.
  forward.
  (* room = (size_t) nondet_u32(): the call and the cast as two statements *)
  rewrite <- seq_assoc. forward_call tt. Intros room.
  forward.
  rewrite <- seq_assoc. forward_call tt. Intros dlen.
  forward.
  rewrite !Int.unsigned_repr by rep_lia.
  change (Int.signed (Int.repr 6)) with 6. rewrite add64_repr.
  forward_call (6 + t2, gv).
  Intros vret. destruct vret as [streamp src]. simpl fst in *; simpl snd in *.
  forward_call (tarray tuchar room, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros outp.
  forward_call (dlen, gv).
  Intros vret. destruct vret as [dictp dict]. simpl fst in *; simpl snd in *.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K t1 t2 room dlen streamp src outp dictp dict)].
  unfold rd_A8, rd_in. rewrite ?rbd_bytes_adler_cs, ?rbd_tok_adler_cs.
  entailer!.
Qed.

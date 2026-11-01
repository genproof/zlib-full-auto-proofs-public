(* Law rj_truncated, main: statements 1-8 (data_len = upto(PTRDIFF_MAX), data = any_bytes(data_len),
   out = malloc(data_len), `return 0` if either is NULL, the four ints level, window_bits, mem_level, strategy from
   nondet_u32) (rt_A0 -> rt_A9). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.harness.rj_truncated.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.


Lemma seg_inputs_ok : seg_inputs_stmt.
Proof.
  intros Espec gv vc vd K.
  unfold rt_seg1, rt_A0, POST_B, POST_rt. abbreviate_semax.
  forward_call 9223372036854775807.
  Intros n.
  forward_call (n, gv).
  Intros vret. destruct vret as [dp D]. simpl fst in *; simpl snd in *.
  rt_law.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  (* if (data == NULL || out == NULL) return 0; *)
  destruct (eq_dec dp nullval) as [PD|PD].
  { subst dp.
    ifpost _t'4 (Int.repr 1).
    { forward. entailer!. }
    { rt_bad. }
    forward_if. { ret0. } { rt_bad. } }
  Intros.
  destruct (eq_dec op nullval) as [PO|PO].
  { subst op.
    ifpost _t'4 (Int.repr 1).
    { rt_bad. }
    { forward. entailer!; rt_cmp. }
    forward_if. { ret0. } { rt_bad. } }
  Intros.
  ifpost _t'4 (Int.repr 0).
  { rt_bad. }
  { forward. entailer!; rt_cmp. }
  forward_if. { rt_bad. }
  Intros.
  forward_call tt. Intros u1.
  forward_call tt. Intros u2.
  forward_call tt. Intros u3.
  forward_call tt. Intros u4.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K n D dp op (Int.signed (Int.repr u1)) (Int.signed (Int.repr u2))
                                (Int.signed (Int.repr u3)) (Int.signed (Int.repr u4)))].
  unfold rt_A9, rt_cf. rewrite !Int.repr_signed.
  entailer!.
  unfold rs32. repeat split; try rep_lia; destruct dp, op; try contradiction; simpl; auto.
Qed.

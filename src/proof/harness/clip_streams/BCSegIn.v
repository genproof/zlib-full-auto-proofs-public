(* Law rj_bad_checksum, main: statements 1-10, the inputs (data_len, data, out, the four ints, the 8 bytes of
   change) and their checks (bc_A0 -> bc_A11). *)
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
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.


Ltac simplify_remove_localdef_temp ::= bc_rlt.

Lemma seg_inputs_ok : seg_inputs_stmt.
Proof.
  intros Espec gv vc vd K.
  unfold bc_seg1, bc_A0, POST_B, POST_bc. abbreviate_semax.
  forward_call 9223372036854775807.
  Intros n.
  forward_call (n, gv).
  Intros vret. destruct vret as [dp D]. simpl fst in *; simpl snd in *.
  bc_law.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  (* if (data == NULL || out == NULL) return 0; *)
  destruct (eq_dec dp nullval) as [PD|PD].
  { subst dp.
    ifpost _t'4 (Int.repr 1).
    { forward. entailer!. }
    { bc_bad. }
    forward_if. { ret0. } { bc_bad. } }
  Intros.
  destruct (eq_dec op nullval) as [PO|PO].
  { subst op.
    ifpost _t'4 (Int.repr 1).
    { bc_bad. }
    { forward. entailer!; bc_cmp. }
    forward_if. { ret0. } { bc_bad. } }
  Intros.
  ifpost _t'4 (Int.repr 0).
  { bc_bad. }
  { forward. entailer!; bc_cmp. }
  forward_if. { bc_bad. }
  Intros.
  forward_call tt. Intros u1.
  forward_call tt. Intros u2.
  forward_call tt. Intros u3.
  forward_call tt. Intros u4.
  forward_call (8, gv).
  Intros vret. destruct vret as [chp C]. simpl fst in *; simpl snd in *.
  bc_law.
  (* if (change == NULL || window_bits < 8) return 0; *)
  destruct (eq_dec chp nullval) as [PC|PC].
  { subst chp.
    ifpost _t'10 (Int.repr 1).
    { forward. entailer!. }
    { bc_bad. }
    forward_if. { ret0. } { bc_bad. } }
  Intros.
  destruct (Int.lt (Int.repr u2) (Int.repr 8)) eqn:Hlt.
  { ifpost _t'10 (Int.repr 1).
    { bc_bad. }
    { forward. entailer!; bc_cmp. rewrite Hlt. reflexivity. }
    forward_if. { ret0. } { bc_bad. } }
  ifpost _t'10 (Int.repr 0).
  { bc_bad. }
  { forward. entailer!; bc_cmp. rewrite Hlt. reflexivity. }
  forward_if. { bc_bad. }
  Intros.
  assert (W8: 8 <= Int.signed (Int.repr u2)).
  { unfold Int.lt in Hlt. rewrite (Int.signed_repr 8) in Hlt by rep_lia.
    destruct (zlt _ _); [discriminate | lia]. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K n D dp op (Int.signed (Int.repr u1)) (Int.signed (Int.repr u2))
                                (Int.signed (Int.repr u3)) (Int.signed (Int.repr u4)) C chp)].
  unfold bc_A11, bc_cf, bc_chg_ok, bc_chg. rewrite !Int.repr_signed.
  entailer!.
  unfold rs32. repeat split; try rep_lia; destruct dp, op, chp; try contradiction; simpl; auto.
Qed.

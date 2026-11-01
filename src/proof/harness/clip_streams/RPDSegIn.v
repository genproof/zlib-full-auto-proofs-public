(* Law rt_partial, main: statements 1-10 (data_len = upto(PTRDIFF_MAX), data = alloc_any_bytes(data_len) and
   `return 0` if NULL, expected = copy_of(data, data_len), out = malloc(data_len), `return 0` if expected or out is
   NULL, the four ints level, window_bits, mem_level, strategy from nondet_u32) (rpd_A0 -> rpd_A11). *)
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
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.proof.harness.clip_streams.RPDKit.
Require Import Zlib.harness.rt_partial.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rpd_rlt.


Lemma rpd_seg_inputs : rpd_inputs_stmt.
Proof.
  intros Espec gv vc vd K.
  unfold rpd_seg1, rpd_A0, POST_B, POST_rp. abbreviate_semax.
  forward_call 9223372036854775807.
  Intros n.
  forward_call (n, gv).
  Intros vret. destruct vret as [dp D]. simpl fst in *; simpl snd in *.
  rpd_law.
  (* if (data == NULL) return 0; *)
  destruct (eq_dec dp nullval) as [PD|PD].
  { subst dp. forward_if. { ret0. } { rpd_bad. } }
  Intros.
  forward_if. { rpd_bad. }
  assert_PROP (isptr dp) as Pdp by entailer!.
  (* expected = copy_of(data, data_len) *)
  rewrite <- (rpd_bytes_adler Ews n (bytes_rep D) dp).
  forward_call (dp, Ews, dp, 0, n, bytes_rep D, n, D, gv).
  { subst n. apply cbuf_ok_whole; auto. }
  Intros ep.
  rpd_law.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  (* if (expected == NULL || out == NULL) return 0; *)
  destruct (eq_dec ep nullval) as [PE|PE].
  { subst ep.
    ifpost _t'5 (Int.repr 1).
    { forward. entailer!. }
    { rpd_bad. }
    forward_if. { ret0. } { rpd_bad. } }
  Intros.
  destruct (eq_dec op nullval) as [PO|PO].
  { subst op.
    ifpost _t'5 (Int.repr 1).
    { rpd_bad. }
    { forward. entailer!; rpd_cmp. }
    forward_if. { ret0. } { rpd_bad. } }
  Intros.
  ifpost _t'5 (Int.repr 0).
  { rpd_bad. }
  { forward. entailer!; rpd_cmp. }
  forward_if. { rpd_bad. }
  Intros.
  forward_call tt. Intros u1.
  forward_call tt. Intros u2.
  forward_call tt. Intros u3.
  forward_call tt. Intros u4.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K n D dp ep op (Int.signed (Int.repr u1)) (Int.signed (Int.repr u2))
                                (Int.signed (Int.repr u3)) (Int.signed (Int.repr u4)))].
  unfold rpd_A11, rpd_cf, rp_exp. rewrite !Int.repr_signed.
  entailer!.
  unfold rs32. repeat split; try rep_lia; destruct dp, ep, op; try contradiction; simpl; auto.
Qed.

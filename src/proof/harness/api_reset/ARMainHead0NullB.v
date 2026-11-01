(* Law api_reset, main: the test of the four new objects against NULL in phase 0 (ARMainHead0NullA.v), the
   cases where in_used and in_fresh are objects and out_used or out_fresh is NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainHead0Call Zlib.proof.harness.api_reset.ARMainHead0NullA.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

(* out_used is NULL *)
Lemma null0_ou {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ofr za La zb:
  iu <> nullval -> ifr <> nullval ->
  null0_goal J0 J1 gv va vb w inp src pos take room flush iu ifr nullval ofr za La zb.
Proof.
  intros N1 N2. null0_start.
  destruct (eq_dec iu nullval); [contradiction | ]. destruct (eq_dec ifr nullval); [contradiction | ].
  ifpostv _t'14 (Vint (Int.repr 0)); [infeas | cmpz | ].
  ifpostv _t'15 (Vint (Int.repr 1)); [infeas | cmpz | ].
  ifpostv _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  forward_if; [ret0 | infeas].
Qed.

(* out_fresh is NULL *)
Lemma null0_ofr {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou za La zb:
  iu <> nullval -> ifr <> nullval -> ou <> nullval ->
  null0_goal J0 J1 gv va vb w inp src pos take room flush iu ifr ou nullval za La zb.
Proof.
  intros N1 N2 N3. null0_start.
  destruct (eq_dec iu nullval); [contradiction | ]. destruct (eq_dec ifr nullval); [contradiction | ].
  destruct (eq_dec ou nullval); [contradiction | ].
  ifpostv _t'14 (Vint (Int.repr 0)); [infeas | cmpz | ].
  ifpostv _t'15 (Vint (Int.repr 0)); [infeas | cmpz | ].
  ifpostv _t'16 (Vint (Int.repr 1)); [infeas | cmpz | ].
  forward_if; [ret0 | infeas].
Qed.

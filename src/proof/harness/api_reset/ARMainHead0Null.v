(* Law api_reset, main: the test of the four new objects against NULL in phase 0 (ARMainHead0NullA.v): when all
   four are objects the body goes on with call0_stmt (ARMainHead0Call.v); null0_of gathers the five cases. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainHead0Call Zlib.proof.harness.api_reset.ARMainHead0NullA.
Require Import Zlib.proof.harness.api_reset.ARMainHead0NullB.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

Definition null0_stmt : Prop :=
  forall {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb,
  hd0_facts J0 J1 w inp src va vb pos take room flush za La zb ->
  null0_goal J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb.

(* the four objects are there *)
Lemma null0_all {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb:
  call0_stmt -> hd0_facts J0 J1 w inp src va vb pos take room flush za La zb ->
  iu <> nullval -> ifr <> nullval -> ou <> nullval -> ofr <> nullval ->
  null0_goal J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb.
Proof.
  intros CALL0 HF N1 N2 N3 N4. null0_start.
  destruct (eq_dec iu nullval); [contradiction | ]. destruct (eq_dec ifr nullval); [contradiction | ].
  destruct (eq_dec ou nullval); [contradiction | ]. destruct (eq_dec ofr nullval); [contradiction | ].
  assert_PROP (isptr iu /\ isptr ifr /\ isptr ou /\ isptr ofr) as Pp by entailer!.
  ifpostv _t'14 (Vint (Int.repr 0)); [infeas | cmpz | ].
  ifpostv _t'15 (Vint (Int.repr 0)); [infeas | cmpz | ].
  ifpostv _t'16 (Vint (Int.repr 0)); [infeas | cmpz | ].
  forward_if; [infeas | ].
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (CALL0 Espec J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb)].
  { unfold call0_pre, rest0, objb. entailer!. }
  split; [exact HF | exact Pp].
Qed.

Lemma null0_of : call0_stmt -> null0_stmt.
Proof.
  intros CALL0. unfold null0_stmt. intros Espec J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb HF.
  destruct (eq_dec iu nullval) as [->|N1]; [apply null0_iu | ].
  destruct (eq_dec ifr nullval) as [->|N2]; [apply null0_ifr; auto | ].
  destruct (eq_dec ou nullval) as [->|N3]; [apply null0_ou; auto | ].
  destruct (eq_dec ofr nullval) as [->|N4]; [apply null0_ofr; auto | ].
  apply null0_all; auto.
Qed.

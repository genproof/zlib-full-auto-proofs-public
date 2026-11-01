(* Law rt_session (harness/rt_session.c), main's statement 23 (SMA1Kit.v), the case where dict, extra and name are not NULL, comment is: main returns 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA1Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma sa1_c4 {Espec : OracleKind} gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc
    dict xf nm cm data dp xp np cmp datp :
  dp <> nullval -> xp <> nullval -> np <> nullval -> cmp = nullval ->
  a1_triple gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data dp xp np cmp datp.
Proof.
  intros Hd Hx Hn ->. sa1_start.
  sa1_nn dp dict. sa1_mkptr dp bd od. sa1_nn xp xf. sa1_mkptr xp bx ox.
  sa1_ifpost _t'24 (Vint Int.zero); [sa1_tceq | sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  sa1_nn np (nm ++ [0]). sa1_mkptr np bn on.
  sa1_ifpost _t'25 (Vint Int.zero); [sa1_nob | forward; [sa1_tceq | sa1_close] | ].
  sa1_nul. sa1_ifpost _t'26 (Vint Int.one); [sa1_nob | forward; sa1_close | ]. sa1_ones.
Qed.

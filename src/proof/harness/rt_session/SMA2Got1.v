(* Law rt_session, main's statements 39-40: got.extra = malloc(extra_len), got.extra_max = (uInt) extra_len. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA2Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma a2_got1 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op :
  semax Delta_s (QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op h00 []) (Ssequence S39 S40)
    (overridePost (EX gxp : val, QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op
       (gw gxp (vi (Zlength (su_xf u))) U U U U) [new0 gxp (Zlength (su_xf u))]) POST_s).
Proof.
  unfold QG, Qs, base, ctemps, cobjs, h00, gw, U, lvs, lv_locals, o_locals, d_locals, S39, S40.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  forward_call (tarray tuchar (Zlength (su_xf u)), gv).
  { simpl. rewrite Z.max_r by (apply Zlength_nonneg). rep_lia. }
  Intros gxp.
  forward. forward.
  Exists gxp.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QG, Qs, base, ctemps, cobjs, gw, U, lvs, lv_locals, o_locals, d_locals, new0, cnew.
  cbn [app].
  rewrite Int64.Z_mod_modulus_eq, (Z.mod_small (Zlength (su_xf u))) by rep_lia.
  fold (vi (Zlength (su_xf u))).
  entailer!.
Qed.

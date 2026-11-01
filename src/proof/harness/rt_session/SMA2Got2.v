(* Law rt_session, main's statements 41-42: got.name = malloc(name_len + 1), got.name_max = (uInt) (name_len + 1). *)
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

Lemma a2_got2 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op gxp :
  semax Delta_s (QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op
       (gw gxp (vi (Zlength (su_xf u))) U U U U) [new0 gxp (Zlength (su_xf u))]) (Ssequence S41 S42)
    (overridePost (EX gnp : val, QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op
       (gw gxp (vi (Zlength (su_xf u))) gnp (vi (Zlength (su_nm u) + 1)) U U)
       [new0 gxp (Zlength (su_xf u)); new0 gnp (Zlength (su_nm u) + 1)]) POST_s).
Proof.
  unfold QG, Qs, base, ctemps, cobjs, gw, U, lvs, lv_locals, o_locals, d_locals, S41, S42.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  forward_call (tarray tuchar (Zlength (su_nm u) + 1), gv).
  { simpl. rewrite Z.max_r by (pose proof (Zlength_nonneg (su_nm u)); lia). rep_lia. }
  Intros gnp.
  forward. forward.
  Exists gnp.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold QG, Qs, base, ctemps, cobjs, gw, U, lvs, lv_locals, o_locals, d_locals, new0, cnew.
  cbn [app].
  rewrite ?Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small (Zlength (su_nm u)) Int64.modulus), (Z.mod_small (Zlength (su_nm u) + 1) Int64.modulus)
    by rep_lia.
  fold (vi (Zlength (su_nm u) + 1)).
  entailer!.
Qed.

(* Law rt_session, main's statements 43-44: got.comment = malloc(comment_len + 1), got.comm_max = (uInt)
   (comment_len + 1); every value drawn and stored, as the setup of A47 (its pointers possibly NULL). *)
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

Lemma a2_got3 {Espec : OracleKind} gv vh vg vc va vd u dcp xcp ncp ccp ep cp op gxp gnp :
  semax Delta_s (QG gv vh vg vc va vd u dcp xcp ncp ccp ep cp op
       (gw gxp (vi (Zlength (su_xf u))) gnp (vi (Zlength (su_nm u) + 1)) U U)
       [new0 gxp (Zlength (su_xf u)); new0 gnp (Zlength (su_nm u) + 1)]) (Ssequence S43 S44)
    (overridePost (EX gcp : val, NS gv vh vg vc va vd (withp u dcp xcp ncp ccp ep cp op gxp gnp gcp) []) POST_s).
Proof.
  unfold QG, Qs, base, ctemps, cobjs, gw, U, lvs, lv_locals, o_locals, d_locals, S43, S44.
  cbn [app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. a2_facts.
  forward_call (tarray tuchar (Zlength (su_cm u) + 1), gv).
  { simpl. rewrite Z.max_r by (pose proof (Zlength_nonneg (su_cm u)); lia). rep_lia. }
  Intros gcp.
  forward. forward.
  Exists gcp.
  destruct POST_s as [r1 r2 r3 r4]; cbn [tycontext.RA_normal].
  unfold NS. rewrite su_dok_withp.
  unfold base, cobjs, c_locals, gval, lvs, lv_locals, o_locals, d_locals, dictobj, datobj, withp, new0, cnew.
  cbn [app su_level su_wbits su_mem su_strategy su_choice su_dict su_xf su_nm su_cm su_data su_cap su_text su_time
       su_os su_hcrc su_dictp su_xp su_np su_cmp su_dp su_dcp su_xcp su_ncp su_ccp su_ep su_cp su_op su_gxp su_gnp
       su_gcp].
  rewrite hvals_withp, with_dict_withp, with_head_withp.
  rewrite ?Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small (Zlength (su_cm u)) Int64.modulus), (Z.mod_small (Zlength (su_cm u) + 1) Int64.modulus)
    by rep_lia.
  fold (vi (Zlength (su_cm u) + 1)).
  entailer!.
Qed.

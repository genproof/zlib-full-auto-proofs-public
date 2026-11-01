(* Law rt_session (harness/rt_session.c), main's statements 53-56 (SMA3Kit.segA3_stores): next_in = data,
   next_out = compressed, offered = 0, flush = Z_NO_FLUSH, and the deflate loop's invariant DI with no data
   consumed and no output yet.  The proof is rt_stream's (its stores before the deflate loop) on this main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA3Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma a3_stores : a3_stores_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u c msg hx Hr JF.
  destruct c as [s ni ain tin no aout tout msgv adler].
  unfold AS, segA3_stores, POST_A3. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. subst ni no.
  unfold cstream, api_fields. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler]. Intros.
  rewrite a3_next_in_cs, a3_next_out_cs.
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  forward. forward. forward. forward.
  rewrite <- a3_next_in_cs, <- a3_next_out_cs.
  Exists (mkDL [] [] None 0 0 msg (mkCS s (su_dp u) ain tin (su_cp u) aout tout msgv adler)) hx Hr.
  unfold DI, cstream, api_fields, dl_ok, c_locals, d_locals, lvs, lv_locals.
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler
       app].
  entailer!.
  match goal with Hs : su_ok u |- _ =>
    pose proof Hs as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & Hcap & _ & _ & _ & _ &
                       _ & _ & _ & _ & Pdp) & _ & _ & _ & _ & _ & Pcp & _) end.
  rewrite !Zlength_nil, !isptr_offset_val_zero by assumption.
  split; [pose proof (Zlength_nonneg (su_data u)); lia|].
  split; [intros Hf; exfalso; compute in Hf; discriminate Hf|].
  split; [lia|]. split; [constructor|]. split; reflexivity.
Qed.

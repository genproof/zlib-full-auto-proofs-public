(* Law inflate_dict, main: the encoder half (main's start up to `slen = w.len`: the draws, the four objects,
   the dictionary and the wrong one, the zlib header, the blocks by deflate_ref.h, the trailer), continuation
   style: main's body from ANY proof of the inflate half (seg_inf) from enc_done (ITMainKit.v), the hypothesis
   for every Espec, as semax_body quantifies over every Espec (ITMainKit.main_enc_stmt; ITMainEnc.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_dict.ITEncKit Zlib.proof.harness.inflate_dict.ITEncPro
               Zlib.proof.harness.inflate_dict.ITEncStored Zlib.proof.harness.inflate_dict.ITEncLit
               Zlib.proof.harness.inflate_dict.ITEncRef Zlib.proof.harness.inflate_dict.ITEncTrl
               Zlib.proof.harness.inflate_dict.ITEncLoop.

(* main_enc_stmt with its hypothesis for every Espec (semax_body quantifies over every Espec) *)
Lemma main_enc_fx :
  (forall Es: OracleKind, @seg_inf_ok Es (fun _ => True)) ->
  semax_body (QPvarspecs p) Gmain_k f_main (_main, main_core_spec R).
Proof.
  intros H.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  apply semax_seq with FF; [ | apply semax_ff ].
  eapply semax_post; [ | | | | eapply semax_pre;
     [ | apply (seg_pro_ok gv v_w v_s v_osnap v_dl) ] ].
  5: { unfold pro_pre. entailer!. }
  5: { intros E. apply (seg_loop_ok seg_stored_ok seg_lit_ok_n seg_ref_ok E).
       intros bs dcont. apply (seg_trl_ok (H Espec)). }
  all: unfold POST_m; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return.
  all: first [ apply andp_left2; intro rho; simpl; normalize | apply andp_left2; apply derives_refl
             | intros vl; apply andp_left2; apply derives_refl ].
Qed.

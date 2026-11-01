(* The main of harness/rj_bad_dictionary.c, proved against MainLib.main_core_spec R (RDGlobals.v) from the
   theory of its inflate() call (RDFacts.rbd_theory_stmt): main's chain of statements in five segments
   (RDKit.v: the cuts and their assertions), RDSegIn (the inputs and the objects), RDSegNull (their NULL test),
   RDSegHdr (the header bytes and the dictionary id), RDSegInit (the gp_assume on the dictionary, new_stream,
   inflateInit2) and RDSegCalls (offer, inflate, inflateSetDictionary). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDLawCS.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDGlobals.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDKit.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDSegIn.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDSegNull.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDSegHdr.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDSegInit.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDSegCalls.
Require Import Zlib.harness.rj_bad_dictionary.code.

Lemma body_main : rbd_theory_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros TH.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  eapply semax_pre; [ | apply (seg_inputs_ok _ gv v_strm)].
  { unfold rd_A0, t_zsl. entailer!. }
  intros t1 t2 room dlen streamp src outp dictp dict.
  apply seg_null_ok. apply seg_header_ok. intros s cinfo x.
  apply seg_init_ok. intros sp.
  apply (seg_calls_ok TH).
Qed.

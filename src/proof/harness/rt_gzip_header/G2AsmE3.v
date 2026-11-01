(* Law rt_gzip_header on the round-2 harness: the entries of main (its body, for the loop invariants that
   G2DFacts / G2IFacts provide, with the globals of G2Globals.v), of inflate_table (inftrees.c) and of
   inflateReset (Spec5), moved into the law's program and its specifications G of G2AsmKit.v.  A file of its own
   for the time they take; used by G2Asm.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.deflate.MainCoreCfg.
Require Zlib.proof.deflate.GlobalsFixed.
Require Zlib.proof.inftrees.spec.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Zlib.proof.harness.rt_gzip_header.G2Globals.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2AsmKit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

(* main's entry: its body for the invariants the two loop interfaces provide *)
Lemma rtg2_entry_main (fast g1 g2 g3 g4 g5 g6 g7 g8 : funspec) :
  body_main2_stmt -> Zlib.proof.harness.rt_gzip_header.G2DFacts.g2_dfacts_stmt ->
  Zlib.proof.harness.rt_gzip_header.G2IFacts.g2_ifacts_stmt ->
  entry_of_prog (@HonestEspec CS) CS p
    (G fast g1 g2 g3 g4 g5 g6 g7 g8 ++ vacuous_internals p (G fast g1 g2 g3 g4 g5 g6 g7 g8))
    (_main, QPmain_spec_ext' p tt main_post_TT).
Proof.
  intros BMS (J0 & J & DF) (P & IF).
  pose proof (semax_body_main_core_cfg _ _ p Zlib.proof.deflate.GlobalsFixed.cfg_funs _ _ R
    Zlib.proof.harness.rt_gzip_header.G2Globals.rtg2_globals (BMS J0 J P DF IF) eq_refl) as BM.
  apply (Forall_inv (l := [])).
  entry_fast BM. apply Forall_nil.
Qed.

Lemma rtg2_entries3 (fast g1 g2 g3 g4 g5 g6 g7 g8 : funspec) :
  Forall (entry_of_prog (@HonestEspec CS) CS p
            (G fast g1 g2 g3 g4 g5 g6 g7 g8 ++ vacuous_internals p (G fast g1 g2 g3 g4 g5 g6 g7 g8)))
    [Zlib.proof.inflate_api.Spec5.inflateReset_spec; Zlib.proof.inftrees.spec.inflate_table_spec].
Proof.
  destruct Zlib.proof.inflate_api.Body5_reset.api5_reset as [_ Hreset].
  destruct (Hreset NullExtension.Espec) as (_ & B_reset & _ & _).
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table.
  entry_fast B_reset.
  (* inflate_table's context has inftrees' PROP-False inflate_fixed_spec (never called): G's real one is a
     subspecification of it *)
  apply Forall_cons;
  [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B_table);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity
    | let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
      intros i phi E; simpl in E;
      (if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ]);
      (if_tac in E; [ | discriminate ]);
      inv E; eexists; split; [ reflexivity | ];
      apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
      let x := fresh "x" in let ge := fresh "ge" in let args := fresh "args" in
      intros x [ge args]; simpl; unfold PROPx; simpl; normalize ]
  | ].
  apply Forall_nil.
Qed.

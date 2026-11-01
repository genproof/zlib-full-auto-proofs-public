(* Law rt_session, main's inflate loop with a header (SMLoopI9.v): the first statement of the body,
   decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input))), from the
   loop's invariant (its facts as hypotheses) to the offer state OI9 with avail_in = take, at most 2^32 - 1 and at
   most the bytes of the input object left.  The second statement is SLI9OfferOut.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_session.SLI9Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module R8 := Zlib.proof.roundtrip.RTH8Spec.
Module R9 := Zlib.proof.roundtrip.RTH9Spec.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

Lemma offer_in9_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip pos out asked L z :
  su_ok u -> SIFacts.src_ok O src -> isptr ip -> il_ok P u O src ip (mkIL pos out asked L z) ->
  semax Delta_9
    (PROPx []
     (LOCALx (i9_locals gv vh vg vc va vd u O src ip asked)
     (SEPx [R8.istream8 gv Tsh vd z (Some L); R9.head_mem9 L; gtoks u;
            cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out;
            data_at_ Tsh t_p va; iobj src ip; hobj vh u; dictobj u; dcopy u])))
    offerIn9
    (normal_ret_assert (EX take : Z,
       OI9 gv vh vg vc va vd u O c src ip
         [0 <= take <= Zlength src - pos; take <= Int.max_unsigned; zf_ok z; R8.live_ok8 L; isptr vd]
         pos out asked z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))).
Proof.
  intros SU SO Pip IL.
  unfold Delta_9; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SO as (HO & _ & _).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  unfold offerIn9, i9_locals, lvs, lv_locals. simpl app.
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite istream8_unfold. Intros. unfold tup9. rewrite Eni, Eno.
  abbreviate_semax.
  forward.
  forward_call (Zlength src - pos).
  all: try solve [upto_side9].
  { (* compressed_len + after = |src| *)
    entailer!. replace (Zlength O + (Zlength src - Zlength O)) with (Zlength src) by lia.
    unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *. rewrite UK.ptr_sub by (auto; rep_lia). reflexivity. }
  Intros t0.
  forward_call t0.
  { unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). unfold OI9, oS9, i9_locals, lvs, lv_locals. simpl app. entailer!.
Qed.

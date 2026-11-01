(* Law rt_stream_trailing, main's inflate loop: the first statement of the body,
   decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input))),
   from the loop's invariant (its facts as hypotheses) to the offer state OI_t with avail_in = take, at most
   2^32 - 1 and at most the bytes of the input object left.  rt_stream's ULoopIOfferIn.v on the input object. *)
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
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TLoopIKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

Lemma offer_in_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip pos out L z :
  su_ok u -> src_ok O src -> isptr ip -> il_ok_t P u O src ip (mkIL pos out L z) ->
  semax Delta_t
    (PROPx []
     (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
              temp _input ip :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
     (SEPx [istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
           cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u out; data_at_ Tsh t_p va;
           iobj src ip])))
    offerIn_t
    (normal_ret_assert (EX take : Z,
       OI_t [0 <= take <= Zlength src - pos; take <= Int.max_unsigned; zf_ok z; live_ok L; isptr vd]
          gv vc vd va u O c src ip pos out z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))).
Proof.
  intros SU SO Pip IL.
  unfold Delta_t; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  pose proof SO as (HO & _ & _).
  cbn [il_pos il_out il_L il_z] in *.
  unfold offerIn_t, su_locals, lv_locals. simpl app.
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite UK.istreamA_unfold. Intros. unfold UK.istrm_tup. rewrite Eni, Eno.
  abbreviate_semax.
  forward.
  forward_call (Zlength src - pos).
  all: try solve [upto_side].
  { (* compressed_len + after = |src| *)
    entailer!. replace (Zlength O + (Zlength src - Zlength O)) with (Zlength src) by lia.
    unfold UDFacts.max_size in *. rewrite UK.ptr_sub by (auto; rep_lia). reflexivity. }
  Intros t0.
  forward_call t0.
  { unfold UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). unfold OI_t, oS_t, su_locals, lv_locals. simpl app. entailer!.
Qed.

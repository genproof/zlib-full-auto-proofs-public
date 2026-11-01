(* Law rt_stream_trailing, main's inflate loop: the second statement of the body,
   decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out))),
   from the offer state OI_t with avail_in = take to OI_t with avail_out = room, at most 2^32 - 1.
   rt_stream's ULoopIOfferOut.v on the input object. *)
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

Lemma offer_out_t_ok {Espec : OracleKind} P gv vc vd va u O c src ip pos out L z take :
  su_ok u -> il_ok_t P u O src ip (mkIL pos out L z) ->
  semax Delta_t
    (OI_t [] gv vc vd va u O c src ip pos out z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))
    offerOut_t
    (normal_ret_assert (EX room : Z,
       OI_t [0 <= room <= Zlength (su_data u) - Zlength out; room <= Int.max_unsigned]
          gv vc vd va u O c src ip pos out z L (vi take) (vi room) (data_at_ Tsh t_p va))).
Proof.
  intros SU IL.
  unfold Delta_t; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  cbn [il_pos il_out il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold offerOut_t, OI_t, oS_t, su_locals, lv_locals. simpl app.
  abbreviate_semax.
  forward.
  forward_call (Zlength (su_data u) - Zlength out).
  all: try solve [upto_side].
  Intros t0.
  forward_call t0.
  { unfold UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). entailer!.
Qed.

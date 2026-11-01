(* Law rt_session, main's inflate loop with a header (SMLoopI9.v): the second statement of the body,
   decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out))), from the offer state
   OI9 with avail_in = take to OI9 with avail_out = room, at most 2^32 - 1 and at most the room left in out. *)
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

Lemma offer_out9_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip pos out asked L z take :
  su_ok u -> il_ok P u O src ip (mkIL pos out asked L z) ->
  semax Delta_9
    (OI9 gv vh vg vc va vd u O c src ip [] pos out asked z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))
    offerOut9
    (normal_ret_assert (EX room : Z,
       OI9 gv vh vg vc va vd u O c src ip [0 <= room <= Zlength (su_data u) - Zlength out; room <= Int.max_unsigned]
         pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))).
Proof.
  intros SU IL.
  unfold Delta_9; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _) & _).
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold offerOut9, OI9, oS9, i9_locals, lvs, lv_locals. simpl app.
  abbreviate_semax.
  forward.
  forward_call (Zlength (su_data u) - Zlength out).
  all: try solve [upto_side9].
  Intros t0.
  forward_call t0.
  { unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). entailer!.
Qed.

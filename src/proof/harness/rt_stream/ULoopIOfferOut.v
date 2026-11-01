(* Law rt_stream (data of any length), main's inflate loop: the second statement of the body,
   decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out))),
   from the offer state OI with avail_in = take to OI with avail_out = room, at most 2^32 - 1. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Import Zlib.proof.harness.rt_stream.ULoopIKit.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Lemma offer_out_ok {Espec : OracleKind} P gv vc vd va u O c pos out L z take :
  su_ok u -> il_ok P u O (mkIL pos out L z) ->
  semax Delta_m
    (OI [] gv vc vd va u O c pos out z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))
    offerOut
    (normal_ret_assert (EX room : Z,
       OI [0 <= room <= Zlength (su_data u) - Zlength out; room <= Int.max_unsigned] gv vc vd va u O c pos out z L (vi take) (vi room)
          (data_at_ Tsh t_p va))).
Proof.
  intros SU IL.
  unfold Delta_m; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  cbn [il_pos il_out il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold offerOut, OI, oS, su_locals, lv_locals. simpl app.
  forward.
  forward_call (Zlength (su_data u) - Zlength out).
  all: try solve [upto_side].
  Intros t0.
  forward_call t0.
  { unfold UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). entailer!.
Qed.

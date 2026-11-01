(* Law rt_stream (data of any length), main's inflate loop: the first statement of the body,
   decompressor.avail_in = clip(upto(compressed_len - (size_t) (decompressor.next_in - compressed))),
   from the loop's invariant (its facts as hypotheses) to the offer state OI with avail_in = take, at most
   2^32 - 1. *)
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

Lemma offer_in_ok {Espec : OracleKind} P gv vc vd va u O c pos out L z :
  su_ok u -> Zlength O <= su_cap u -> il_ok P u O (mkIL pos out L z) ->
  semax Delta_m
    (PROPx []
     (LOCALx (temp _compressed_len (vl (Zlength O)) :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
     (SEPx [istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
           cstream gv vc c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out; data_at_ Tsh t_p va])))
    offerIn
    (normal_ret_assert (EX take : Z,
       OI [0 <= take <= Zlength O - pos; take <= Int.max_unsigned; zf_ok z; live_ok L; isptr vd] gv vc vd va u O c pos out z L
          (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))).
Proof.
  intros SU HO IL.
  unfold Delta_m; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  cbn [il_pos il_out il_L il_z] in *.
  unfold offerIn, su_locals, lv_locals. simpl app.
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite istreamA_unfold. Intros. unfold istrm_tup. rewrite Eni, Eno.
  forward.
  forward_call (Zlength O - pos).
  all: try solve [upto_side].
  Intros t0.
  forward_call t0.
  { unfold UDFacts.max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned). unfold OI, oS, su_locals, lv_locals. simpl app. entailer!.
Qed.

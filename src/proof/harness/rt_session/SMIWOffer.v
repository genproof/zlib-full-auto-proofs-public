(* Law rt_session, main's inflate loop without a header (SMLoopIW.v): the first two statements of the body,
   decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input))) and
   decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out))),
   from the loop's invariant II_W (its facts as hypotheses) to the offer state OI_w with avail_in = take (at most
   2^32 - 1 and at most the bytes of the input object left) and avail_out = room (at most 2^32 - 1 and at most
   the room left in out). *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMIWKit.
Require Import Zlib.proof.harness.rt_session.SMIWOfferIn.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the side conditions of upto(m - (size_t) (p + k - p)) *)
Ltac upto_side := first
  [ unfold max_size in *; rep_lia
  | entailer!; unfold max_size in *;
    first [apply sameblock_off; auto | unfold vl; rewrite ptr_sub by (auto; rep_lia); reflexivity] ].

(* the second statement: avail_out = room, at most 2^32 - 1 and at most the room left in out *)
Lemma offer_out_w_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip pos out asked L z take :
  su_ok u -> il_ok P u O src ip (mkIL pos out asked L z) ->
  semax Delta_W
    (OI_w gv vh vg vc va vd [] u O c src ip pos out asked z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))
    offerOut_w
    (normal_ret_assert (EX room : Z,
       OI_w gv vh vg vc va vd [0 <= room <= Zlength (su_data u) - Zlength out; room <= Int.max_unsigned]
          u O c src ip pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))).
Proof.
  intros SU IL.
  unfold Delta_W; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (DK & _ & _ & _ & _ & _ & _ & Pop & _).
  pose proof DK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & Hcap & _).
  cbn [il_pos il_out il_L il_z il_asked] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold offerOut_w, OI_w, oS_w, iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals. simpl app.
  abbreviate_semax.
  forward.
  forward_call (Zlength (su_data u) - Zlength out).
  all: try solve [upto_side].
  Intros t1.
  forward_call t1.
  { unfold max_size in *; rep_lia. }
  forward.
  Exists (Z.min t1 Int.max_unsigned). entailer!.
Qed.

Lemma offers_w_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip pos out asked L z :
  su_ok u -> src_ok O src -> isptr ip -> il_ok P u O src ip (mkIL pos out asked L z) ->
  semax Delta_W
    (PROPx []
     (LOCALx (iw_locals gv vh vg vc va vd u O src ip asked)
     (SEPx ([istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
             cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out;
             data_at_ Tsh t_p va] ++ iw_rest vh vg u O c src ip))))
    (Ssequence offerIn_w offerOut_w)
    (normal_ret_assert (EX take : Z, EX room : Z,
       OI_w gv vh vg vc va vd
          [0 <= take <= Zlength src - pos; take <= Int.max_unsigned; zf_ok z; live_ok L; isptr vd;
           0 <= room <= Zlength (su_data u) - Zlength out; room <= Int.max_unsigned]
          u O c src ip pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))).
Proof.
  intros SU SO Pip IL.
  eapply semax_seq'; [apply (offer_in_w_ok P gv vh vg vc va vd u O c src ip pos out asked L z); auto | ].
  Intros take. unfold OI_w at 1. Intros.
  eapply semax_post_flipped'; [apply (offer_out_w_ok P gv vh vg vc va vd u O c src ip pos out asked L z take); auto | ].
  Intros room. Exists take room. unfold OI_w, iw_rest. simpl app. Intros.
  unfold iw_locals, c_locals, d_locals, lvs, lv_locals; simpl app; entailer!.
Qed.

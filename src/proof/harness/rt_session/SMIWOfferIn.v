(* Law rt_session, main's inflate loop without a header (SMLoopIW.v): the first statement of the body,
   decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input))),
   from the loop's invariant II_W (its facts as hypotheses) to the offer state OI_w with avail_in = take, at most
   2^32 - 1 and at most the bytes of the input object left. *)
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

Lemma offer_in_w_ok {Espec : OracleKind} P gv vh vg vc va vd u O c src ip pos out asked L z :
  su_ok u -> src_ok O src -> isptr ip -> il_ok P u O src ip (mkIL pos out asked L z) ->
  semax Delta_W
    (PROPx []
     (LOCALx (iw_locals gv vh vg vc va vd u O src ip asked)
     (SEPx ([istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
             cstream gv vc (ghp vh u) c; mem_mgr gv; zfuncs gv; Rm gv; dobj u; cobj u O; oobj u out;
             data_at_ Tsh t_p va] ++ iw_rest vh vg u O c src ip))))
    offerIn_w
    (normal_ret_assert (EX take : Z,
       OI_w gv vh vg vc va vd [0 <= take <= Zlength src - pos; take <= Int.max_unsigned; zf_ok z; live_ok L; isptr vd]
          u O c src ip pos out asked z L (vi take) (vi (zf_ao z)) (data_at_ Tsh t_p va))).
Proof.
  intros SU SO Pip IL.
  unfold Delta_W; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SO as (HO & _ & _).
  cbn [il_pos il_out il_L il_z il_asked] in *.
  unfold offerIn_w, iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals. simpl app.
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite istreamA_unfold. Intros. unfold istrm_tup. rewrite Eni, Eno.
  abbreviate_semax.
  forward.
  forward_call (Zlength src - pos).
  all: try solve [upto_side].
  { (* compressed_len + after = |src| *)
    entailer!. replace (Zlength O + (Zlength src - Zlength O)) with (Zlength src) by lia.
    unfold max_size in *. rewrite ptr_sub by (auto; rep_lia). reflexivity. }
  Intros t0.
  forward_call t0.
  { unfold max_size in *; rep_lia. }
  forward.
  Exists (Z.min t0 Int.max_unsigned).
  unfold OI_w, oS_w, iw_locals, iw_rest, c_locals, d_locals, lvs, lv_locals. simpl app. entailer!.
Qed.

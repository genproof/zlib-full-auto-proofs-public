(* Law rt_session (harness/rt_session.c), main's statement 51 (SMA3Kit.segA3_dict):
   if (with_dict) gp_assert(deflateSetDictionary(&compressor, dict, (uInt) dict_len) == Z_OK).
   With a raw or zlib wrapper, right after deflateInit2_, the dictionary of 1 to 2^32 - 1 bytes is accepted and
   the deflate invariant holds with it (SDFacts.sd_dict); the header is SMA3Head.a3_head.  The proof is
   dictionary_w's (DWSegDict.v) on this main. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMA3Kit.
Require Import Zlib.proof.harness.rt_session.SMA3Head.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac a3_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in a3_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := a3_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the dictionary object at main's compspecs: the object deflateSetDictionary reads and its malloc token *)
Lemma a3_dict_obj (u : setup) :
  1 <= Zlength (su_dict u) -> rbytes (su_dict u) ->
  dictobj u =
  opt_obj Ews (Some (su_dict u)) (su_dictp u) *
  @malloc_token Zlib.proof.deflate.DCS.CS Ews (tarray tuchar (Zlength (su_dict u))) (su_dictp u).
Proof.
  intros L B. unfold dictobj. rewrite bobj_obj, (BoundKit.obj_opt_obj _ _ B). unfold BoundKit.obj_rest.
  replace (Zlength (su_dict u) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma a3_dict : a3_dict_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u c msg JF.
  destruct c as [s ni ain tin no aout tout msgv adler].
  unfold AS, segA3_dict. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. subst ni no.
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  match goal with Hs : su_ok u, HJ : J _ _ _ _ _ _ _ _ _ _ |- _ => rename Hs into OK; rename HJ into HJ0 end.
  pose proof OK as ((_ & _ & _ & _ & _ & _ & Hdl & Hdb & _) & _).
  forward_if (EX c' : cst, EX msg' : option Z,
    AS gv vh vg vc va vd J u (sdict u) None nullval c' msg' True [hobj vh u]).
  - (* the dictionary *)
    match goal with W : with_dict u = true |- _ => rename W into Wd end.
    unfold cstream. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler].
    assert_PROP (u32_ok ain /\ u32_ok aout) as Uaio by (unfold api_fields; entailer!).
    destruct Uaio as (Uai & Uao).
    destruct (sd_dict _ JF (su_wbits u) s tin tout adler (su_dict u) ain aout msg HJ0
                (with_dict_wrap u Wd) Hdb Hdl ltac:(unfold u32_ok in *; rep_lia) ltac:(unfold u32_ok in *; rep_lia))
      as (s' & z' & Hc & HJ1).
    rewrite (a3_dict_obj u) by (auto; lia).
    unfold Rm.
    forward_call (Some s, vc, nullval, nullval, ain, tin, nullval, aout, tout, msgv, msg, adler,
                  su_dictp u, Ews, su_dict u, (Some s', z', Z_OK), gv).
    { pose proof OK as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pd & _) & _).
      entailer!. cbv [firstn Datatypes.length typeof eval_cast]. simpl.
      destruct vc; try contradiction; destruct (su_dictp u); try contradiction; simpl;
        rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia; reflexivity. }
    { cancel. }
    { unfold on_state, c_on_state.
      change (zmk [] 0 ain tin aout tout adler msg) with (rzcall [] 0 ain tin aout tout adler msg).
      rewrite Hc. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward_call (Int.one).
    Exists (mkCS s' nullval (z_avail_in z') (z_total_in z') nullval (z_avail_out z') (z_total_out z') msgv'
              (z_adler z')) (z_msg z').
    unfold AS, cstream, sdict, Rm. rewrite Wd.
    cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
    unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
    rewrite (a3_dict_obj u) by (auto; lia).
    entailer!.
  - (* no dictionary *)
    match goal with W : with_dict u = false |- _ => rename W into Wd end.
    forward.
    Exists (mkCS s nullval ain tin nullval aout tout msgv adler) msg.
    unfold AS, sdict. rewrite Wd.
    cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
    unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
    entailer!.
  - Intros c' msg'. exact (a3_head Espec J gv vh vg vc va vd u c' msg' JF).
Qed.

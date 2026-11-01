(* Law rt_gzip_header on the round-2 harness, main's body, segment 6: the test of the inflate loop,
   `code == Z_BUF_ERROR && next_in != compressed + compressed_len` (G2MS6Kit.g6_test_stmt), after a call that
   returned Z_BUF_ERROR with input left: back to the invariant at the new position (G2IFacts.gi_call's P). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_compressed against _compressed_len); each identifier comparison is decided by vm_compute. *)
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

Lemma g6_test_more : g6_test_stmt (fun O r pos => r = Z_BUF_ERROR /\ pos <> Zlength O).
Proof.
  intros Espec P gv vh vg vc vd vr g b cbp O r pos z0 L0 Rc Rr [Er Ep].
  unfold g6_incr, Delta_m. simplify_func_tycontext.
  abbreviate_semax.
  unfold g6_cont_at. Intros.
  match goal with G : g6_glob _ _ _ _, HL : g6_live _ _ _ _ _ _ _ _ |- _ =>
    pose proof G as G0; destruct G as (Gok & DF & BO & Hb & Pc & Opos');
    pose proof HL as HL0;
    destruct HL as (Zo & Lo & Sw & Hh & Eni0 & Eno0 & Eao0 & Ehp & Ehs & Exb & Enb & Ecb & Hpos) end.
  match goal with Hc : _ = Z_BUF_ERROR -> _ |- _ => rename Hc into Hcont end.
  match goal with He : _ \/ _ -> GI.g2_hdr_out _ _ _ _ |- _ => rename He into Hend end.
  unfold g6_sep, g6_locals, gp_locals, gs_locals, lv_locals, g6_tup. cbn [app].
  rewrite Eni0.
  subst r.
  g6_ifk _t'41 1.
  * forward. forward.
    { entailer!. g6_cmp_tc. }
    { entailer!. g6_cmp_val. }
  * g6_infeas.
  * forward_if; try g6_infeas.
    (* input left: the invariant again, at the same position (G2IFacts.gi_call's P) *)
    assert (HP : P (g_wb g - 16) (gh_of g) O (h0 g) pos z0 L0) by (apply Hcont; [reflexivity | lia]).
    try forward.
    unfold g6_inv. Exists pos z0 L0.
    unfold g6_sep, g6_locals, g6_tup, gp_locals, gs_locals, lv_locals. cbn [app].
    rewrite Eni0. entailer!.
Qed.

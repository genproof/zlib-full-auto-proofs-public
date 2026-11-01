(* Law rt_session (harness/rt_session.c), main's statement 52 (SMA3Kit.segA3_head):
   if (with_head) gp_assert(deflateSetHeader(&compressor, &head) == Z_OK).
   With a gzip wrapper, right after deflateInit2_ (no dictionary then), the header head is accepted and the
   deflate invariant holds with it (SDFacts.sd_head); the compressor then holds head's Ews part and the objects of
   the fields present (gzh_at), main keeps the rest (SMA3Kit.Hr_of), and they give head back (SMA3Kit.head_close).
   Without a header the state's gzhead stays Z_NULL and main keeps head.  The stores are SMA3Stores.a3_stores.
   The proof is rt_gzip_header's (G2MainSeg3.v) on this main. *)
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
Require Import Zlib.proof.harness.rt_session.SMA3Stores.
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

Lemma a3_head : a3_head_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u c msg JF.
  destruct c as [s ni ain tin no aout tout msgv adler].
  unfold AS, segA3_head. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros. subst ni no.
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  match goal with Hs : su_ok u, HJ : J _ _ _ _ _ _ _ _ _ _ |- _ => rename Hs into OK; rename HJ into HJ0 end.
  forward_if (EX c' : cst, EX hx : share * val * val * val, EX Hr : mpred,
    AS gv vh vg vc va vd J u (sdict u) (sgh u) (ghp vh u) c' msg (hclose vh u (cs_s c') hx Hr)
      [hdr_at (Some (cs_s c')) (ghp vh u) hx; Hr]).
  - (* a header: deflateSetHeader; with a gzip wrapper there is no dictionary *)
    match goal with W : with_head u = true |- _ => rename W into Wh end.
    assert (Wd : with_dict u = false)
      by (destruct (with_dict u) eqn:E; [rewrite (with_dict_head u E) in Wh; discriminate | reflexivity]).
    unfold sdict in HJ0; rewrite Wd in HJ0.
    destruct (sd_head _ JF (su_wbits u) s tin tout adler (gh_of u) zrst0 HJ0 (with_head_wrap u Wh) (gh_of_ok7 u OK))
      as [Hc HJ1].
    set (s1 := set_d_gzhead s (Some (gh_of u))) in *.
    sep_apply (head_open u vh OK).
    unfold cstream. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler]. rewrite af_split.
    forward_call (Some s, vc, nullval, nullval, vh, gh_of u, selp u 2 (su_xp u), selp u 4 (su_np u),
      selp u 8 (su_cmp u), (Some s1, zrst0, Z_OK), zrst0, gv).
    { cancel. }
    { unfold on_state, c_on_state. rewrite Hc. reflexivity. }
    cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
    forward_call (Int.one).
    Exists (mkCS s1 nullval ain tin nullval aout tout msgv adler) (hx_of u) (Hr_of u vh).
    assert (Ehc : hclose vh u s1 (hx_of u) (Hr_of u vh)) by (apply head_close; [exact OK | exact Wh | reflexivity]).
    change (gzh_at Ews (gh_of u) vh (selp u 2 (su_xp u)) (selp u 4 (su_np u)) (selp u 8 (su_cmp u)))
      with (hdr_at (Some s1) vh (hx_of u)).
    unfold AS, cstream, sdict, sgh, ghp. rewrite Wd, Wh.
    cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
    unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
    rewrite af_split. entailer!.
  - (* no header: the state's gzhead stays Z_NULL, main keeps head *)
    match goal with W : with_head u = false |- _ => rename W into Wh end.
    destruct (sd_range _ JF _ _ _ _ _ _ _ _ _ _ HJ0) as (_ & _ & _ & Hg).
    forward.
    Exists (mkCS s nullval ain tin nullval aout tout msgv adler) (hx_of u) (hobj vh u).
    pose proof (head_none u vh s (hx_of u) Wh Hg) as Ehc.
    assert (Eg : sgh u = None) by (unfold sgh; rewrite Wh; reflexivity).
    assert (Ep : ghp vh u = nullval) by (unfold ghp; rewrite Wh; reflexivity).
    unfold AS. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
    rewrite (hdr_none u vh s (hx_of u) Wh Hg), Eg, Ep.
    unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
    entailer!.
  - Intros c' hx Hr. exact (a3_stores Espec J gv vh vg vc va vd u c' msg hx Hr JF).
Qed.

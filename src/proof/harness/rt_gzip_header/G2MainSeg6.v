(* Law rt_gzip_header on the round-2 harness, main's body, segment 6 (G2MainKit.seg6_stmt): statements 46-47,
     offer(&decompressor, compressed, 0, room, 1);
     do { decompressor.avail_in = clip(compressed_len - (size_t) (decompressor.next_in - compressed));
          code = inflate(&decompressor, Z_FINISH); if (code == Z_MEM_ERROR) return 0; }
     while (code == Z_BUF_ERROR && decompressor.next_in != compressed + compressed_len);
   The loop invariant G2MS6Kit.g6_inv is the theory's P (G2IFacts.g2_ifacts: gi_init at position 0, gi_call for
   each call) with the stream's InvW.swfW; when the loop ends got holds the header (g2_hdr_out). *)
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
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6Body.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6TestA.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6TestB.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6TestC.
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

Lemma g2seg6_ok : seg6_stmt.
Proof.
  intros Espec P gv vh vg vc vd vr g b cbp O z sp PF.
  unfold A38, seg6, POST_m, Delta_m, gp_locals, gs_locals, lv_locals. simplify_func_tycontext.
  cbn [app].
  Intros.
  abbreviate_semax.
  destruct H3 as (Zok & Eni & Eai & Eno & Eao & Etin & Etout & Emsg).
  pose proof (g6_O_pos _ _ _ H0) as Opos.
  assert_PROP (isptr vd /\ isptr vr) as Pv by entailer!. destruct Pv as [Pvd Pvr].
  rewrite g6_open. Intros.
  unfold g6_tup. rewrite <- g6_cs_compress.
  (* offer(&decompressor, compressed, 0, room, 1) *)
  forward_call (vd, Tsh, cbp, 0, vr, 1, AM.zf_ni z, vi (AM.zf_ai z), vl (AM.zf_tin z), AM.zf_no z,
    vi (AM.zf_ao z), vl (AM.zf_tout z), Zlib.proof.inflate.Rep.msg_val gv (AM.zf_msg z), S5.l_sp (gL g sp vg),
    gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, vi (AM.zf_dt z), vl (AM.zf_adler z),
    AM.zf_res z).
  rewrite g6_cs_compress.
  sep_apply (g6_head_entry g sp vg).
  forward_loop (g6_inv gv vh vg vc vd vr P g b cbp O)
    continue: (g6_cont gv vh vg vc vd vr P g b cbp O)
    break: (EX L1 : S5.live, EX Fr : mpred, A40 gv vh vg vc vd vr g L1 Fr).
  { (* the invariant at position 0 (G2IFacts.gi_init) *)
    set (z1 := GI.offer_z z cbp 0 vr 1).
    assert (Z1 : S5.zf_ok z1) by (unfold z1, S5.zf_ok, GI.offer_z in *; cbn; rep_lia).
    assert (HP0 := g6_P0 P g O z1 sp vg PF H H0 ltac:(lia) H3 Z1 Etout).
    assert (G : g6_glob g b cbp O) by exact (conj H (conj H0 (conj H1 (conj H2 (conj Pcbp Opos))))).
    assert (LV : g6_live vg vr g cbp O 0 z1 (gL g sp vg)).
    { unfold g6_live. refine (conj Z1 (conj H3 (conj (g6_gL_swfW g sp vg) (conj (g6_gL_head g sp vg) _)))).
      unfold z1, GI.offer_z; cbn. split; [destruct cbp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
      repeat split; lia. }
    unfold g6_inv. Exists 0 z1 (gL g sp vg).
    unfold g6_sep, g6_locals, g6_tup, gp_locals, gs_locals, lv_locals. cbn [app].
    entailer!. }
  { (* the body (G2MS6Body.v) *)
    exact (g6_body_ok Espec P gv vh vg vc vd vr g b cbp O _ _ PF Pvd Pvr). }
  { (* the loop's test, by the code and the position (G2MS6TestA.v, G2MS6TestB.v, G2MS6TestC.v) *)
    unfold g6_cont. Intros r pos z0 L0.
    destruct (Z.eq_dec r Z_BUF_ERROR) as [Er | Er]; [destruct (Z.eq_dec pos (Zlength O)) as [Ep | Ep] | ].
    - exact (g6_test_end Espec P gv vh vg vc vd vr g b cbp O r pos z0 L0 _ _ (conj Er Ep)).
    - exact (g6_test_more Espec P gv vh vg vc vd vr g b cbp O r pos z0 L0 _ _ (conj Er Ep)).
    - exact (g6_test_other Espec P gv vh vg vc vd vr g b cbp O r pos z0 L0 _ _ Er). }
  (* after the loop: its break assertion is the segment's postcondition *)
  unfold POSTCONDITION, abbreviate. unfold overridePost. destruct (frame_ret_assert _ _). cbv beta iota.
  apply ENTAIL_refl.
Qed.

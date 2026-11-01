(* Law inflate_header: main of harness/inflate_header.c (IHMainStmt.v), for ANY invariant with the facts of
   IHFacts.v.  The body b0 is cut into segments (IHMainKit.v): IHMainPro (draws, mallocs), IHMainBuild (the
   member), IHMainInit (inflateInit2, the gz_header, inflateGetHeader), the loop (IHMainLoop: IHMainPre,
   IHMainCall, IHMainChk, IHMainDone), and the tail below (inflateEnd, return). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.
Require Import Zlib.proof.harness.inflate_header.IHMainPro Zlib.proof.harness.inflate_header.IHMainBuild
               Zlib.proof.harness.inflate_header.IHMainInit Zlib.proof.harness.inflate_header.IHMainLoop.

(* after the loop: inflateEnd(&s); return 0; *)
Lemma tail_ok {Espec: OracleKind} I gv V g b P h0 H Fr:
  ih_glob I g b P h0 H ->
  semax Delta_m (ih_inv I gv V g b P h0 H Fr) seg_76 POST_b.
Proof.
  intros G.
  pose proof G as G'. destruct G' as (CF & _).
  unfold ih_inv. Intros pos z L.
  apply semax_extract_prop. intros (HI & Hpos & HL).
  destruct V as [vs vh vxs vns vcs vosn]; simpl in *.
  assert (Hlive: i_head (l_s L) = true) by (apply (proj1 (ihf_live I CF g (b_w b) h0 pos z L HI))).
  destruct HL as (Hhp & Hhs & _).
  unfold ih_at, seg_76, Delta_m, Gmain, POST_b, POST_m. simplify_func_tycontext. abbreviate_semax.
  Intros. simpl v_s_ in *.
  assert_PROP (isptr vs) as Pvs by entailer!.
  rewrite <- (ih_istream_opt gv Tsh vs z (Some L)) by auto.
  forward_call (gv, Tsh, vs, z, Some L).
  rewrite (ih_istream_opt gv Tsh vs z None) by auto.
  sep_apply (ih_istream_to_undef gv vs z None).
  sep_apply (ih_head_mem_undef L vh); auto.
  forward. Exists (Int.repr 0). entailer!.
Qed.

(* the loop and the tail *)
Lemma seg75_ok {Espec: OracleKind} I gv V g b P h0 H Fr:
  ih_glob I g b P h0 H ->
  semax Delta_m (ih_inv I gv V g b P h0 H Fr) seg_75 POST_b.
Proof.
  intros G.
  rewrite ih_seg75_eq.
  apply semax_seq with (Q := ih_inv I gv V g b P h0 H Fr); [ | apply (tail_ok I); auto ].
  apply semax_loop with (Q' := ih_inv I gv V g b P h0 H Fr).
  - unfold ih_inv at 1. Intros pos z L.
    apply semax_extract_prop. intros (HI & Hpos & HL).
    apply (proj1 (semax_skip_seq _ _ _ _)).
    eapply semax_post; [ .. | apply (loop_ok I gv V g b P h0 H Fr pos z L); auto ];
      intros; unfold ih_PL, loop_nocontinue_ret_assert, loop1_ret_assert, overridePost; simpl RA_normal;
      simpl RA_break; simpl RA_continue; simpl RA_return; try (apply andp_left2; apply derives_refl);
      try (apply andp_left2; intro; apply prop_left; contradiction).
  - eapply semax_post; [ .. | apply semax_skip ];
      intros; unfold loop2_ret_assert, normal_ret_assert; simpl RA_normal;
      simpl RA_break; simpl RA_continue; simpl RA_return; try (apply andp_left2; apply derives_refl);
      try (apply andp_left2; intro; apply prop_left; contradiction).
Qed.

Lemma ih_body_main : ih_main_stmt.
Proof.
  intros I CF.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  eapply semax_seq; [ | apply semax_ff ].
  eapply semax_pre; [ | apply (pro_ok gv (IHV v_s v_h v_xs v_ns v_cs v_osnap)) ].
  { unfold ih_pre0. entailer!. }
  intros n b P F24.
  apply (build_ok gv _ n b P F24). intros g F53.
  apply (init_ok I); auto. intros h0 H G.
  apply (seg75_ok I); auto.
Qed.

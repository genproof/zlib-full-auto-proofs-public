(* Law rt_gzip_header on the round-2 harness, main's body, segment 2 (G2MainKit.seg2_stmt): statements 34-35:
   new_stream(&compressor), deflateInit2_ and its test (round 1's MainSeg3.v).

   new_stream (laws_common.h) and deflateInit2_ (DSpec9.deflateInit2__spec_v9) work on the Ews half of the local
   compressor; the other half and the struct's padding are G2MainKit.srest.  deflateInit2_'s precondition asks the
   model call to exist for every allocation outcome, and on Z_OK the deflate state satisfies J0: both from
   G2DFacts.gd_init (the spec's zrst0 is G2DFacts.dz0).  On any other code there is no state and main returns 0.
   The compressor's memory (its compspecs, its fields) is handled by the lemmas of G2MS2Strm.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS2Strm.
Require Zlib.deflate.code.
Require Zlib.units.Compress.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac g2ms2_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in g2ms2_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := g2ms2_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the return codes of deflateInit2_: Z_OK, or no state and Z_STREAM_ERROR (parameters) or Z_MEM_ERROR (an
   allocation) *)
Lemma g2ms2_code level wbits mem strategy a1 a2 a3 a4 a5 z os z' code :
  c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
  code = Z_OK \/ (os = None /\ (code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR)).
Proof.
  intros E. rewrite Zlib.proof.deflate.LTApiInit.init_shape in E.
  destruct (Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy) eqn:P; [| inversion E; auto].
  destruct a1; [| inversion E; auto].
  destruct (a2 && a3 && a4 && a5)%bool; [| inversion E; auto].
  destruct (Zlib.proof.deflate.LTCInit.init_ok level 8 wbits mem strategy z P) as (s0 & z0 & E0 & _).
  rewrite E0 in E. inversion E. auto.
Qed.

Lemma g2seg2_ok : seg2_stmt.
Proof.
  intros Espec J0 J gv vh vg vc vd vr g DF.
  unfold A26, seg2, gp_locals, gs_locals, lv_locals.
  cbn [app]. Intros.
  unfold Delta_m. simplify_func_tycontext. abbreviate_semax.
  pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & Hlev & Hwb & Hmem & Hstr & _).
  rewrite (BoundKit.data_at__Tsh_split t_z vc).
  sep_apply (g2ms2_strm_undef vc).
  forward_call (vc, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (g2ms2_new_stream_split vc).
  unfold R, version_at.
  forward_call (vc, g_level g, 8, g_wb g, g_mem g, g_strat g, gv ___stringlit_rt_gzip_header_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { change (Zlength [49; 46; 51; 46; 50; 0]) with 6. cancel. }
  { repeat (split; [unfold s32_ok, rs32 in *; rep_lia |]). split; [list_solve |]. split; [cbn; rep_lia |].
    intros a1 a2 a3 a4 a5.
    exact (proj1 (gd_init _ _ DF (g_level g) (g_wb g) (g_mem g) (g_strat g) a1 a2 a3 a4 a5
                    Hlev Hwb Hmem Hstr)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  Intros msgv'.
  destruct (g2ms2_code _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as [Hc | [Hos Hc]].
  - (* Z_OK: the deflate state satisfies J0, A28 *)
    subst code.
    destruct (proj2 (gd_init _ _ DF (g_level g) (g_wb g) (g_mem g) (g_strat g) a1 a2 a3 a4 a5
                       Hlev Hwb Hmem Hstr) _ _ _ HI eq_refl) as (s & -> & HJ).
    forward_if; [discriminate |].
    forward.
    Exists (mkDside s (z_total_in z') (z_total_out z') (z_adler z') (z_msg z') msgv').
    unfold A28, st_raw, srest, gside, R, version_at, gp_locals, gs_locals, lv_locals.
    cbn [st_s st_tin st_tout st_adler st_msg st_msgv app] in *.
    change (Z_OK =? Z_OK) with true in *. change (Z_OK =? Z_VERSION_ERROR) with false in *.
    cbn [rfv] in *. change (Zlength [49; 46; 51; 46; 50; 0]) with 6.
    entailer!.
  - (* no state: the local back, return 0 *)
    subst os.
    forward_if.
    + Intros st za zf op dt.
      sep_apply (g2ms2_fields_back vc nullval (rfv (code =? Z_OK) (z_total_in z') Vundef)
                   (rfv (code =? Z_OK) (z_total_out z') Vundef) msgv'
                   (rfv (code =? Z_OK) (z_adler z') Vundef) (vi 0) nullval (vi 0) st za zf op dt).
      sep_apply (g2ms2_rejoin vc).
      forward. Exists (Int.repr 0).
      (* not entailer!: it runs for minutes on data_at -> data_at_ of the gz_header structs *)
      apply andp_right; [apply prop_right; reflexivity |].
      sep_apply (data_at_data_at_ Tsh t_g (hvals g) vh). sep_apply (data_at_data_at_ Tsh t_g (gval g) vg).
      cancel.
    + exfalso. destruct Hc as [-> | ->];
        match goal with H : Int.repr _ = Int.repr 0 |- _ => inversion H end.
Qed.

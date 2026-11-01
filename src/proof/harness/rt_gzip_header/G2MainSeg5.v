(* Law rt_gzip_header on the round-2 harness, main's body, segment 5 (G2MainKit.seg5_stmt): statements 44-45:
   new_stream(&decompressor), inflateInit2_ || inflateGetHeader and the test (round 1's MainSeg6.v on the round-2
   kit).

   new_stream (laws_common.h) sees the local decompressor at the compress unit's compspecs, inflate.c at
   Inflate.CS.  inflateInit2_ (Spec5.inflateInit2__spec) with window_bits 25..31 returns Z_OK or Z_MEM_ERROR;
   on Z_MEM_ERROR main returns 0 with its locals.  On Z_OK the stream is a gzip-only stream (wrap 6) in mode
   HEAD with the fields of new_stream and inflateResetKeep (ms5_z0), and inflateGetHeader
   (RTH8Spec.inflateGetHeader_spec8) takes got with its three fresh buffers as the header G2MainKit.h0 (ms5_raw,
   ms5_toks) and returns Z_OK with the header attached: A38. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Zlib.units.Compress Zlib.units.Inflate.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.harness.rt_gzip_header.code.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS5Kit.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Lemma g2seg5_ok : seg5_stmt.
Proof.
  intros Espec gv vh vg vc vd vr g b cbp O.
  unfold A36, seg5, gp_locals, gs_locals, lv_locals.
  cbn [app]. Intros.
  unfold Delta_m. simplify_func_tycontext. abbreviate_semax.
  unfold gside, gbufs, cnew. Intros.
  rewrite (ms5_strm_undef vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  match goal with |- context [@data_at _ Tsh t_zs ?v vd] => rewrite (ms5_cs_compress Tsh v vd) end.
  rewrite <- ms5_cs_inflate.
  match goal with |- context [@data_at Zlib.units.Inflate.CS Tsh Zlib.proof.inflate.Rep.t_strm ?v vd] =>
    change (@data_at Zlib.units.Inflate.CS Tsh Zlib.proof.inflate.Rep.t_strm v vd)
      with (S5.raw_strm gv Tsh vd ms5_r0 Vundef Vundef nullval nullval nullval) end.
  unfold R, version_at. Intros.
  rewrite ms5_ver_cs.
  assert_PROP (isptr vd) as Pd by entailer!.
  assert (Nd : vd <> nullval) by (destruct vd; try contradiction; discriminate).
  assert_PROP (isptr (gv ___stringlit_rt_gzip_header_1)) as Pv by entailer!.
  pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwb & _).
  unfold ifz.
  forward_call (gv, Tsh, vd, ms5_r0, Vundef, Vundef, nullval, g_wb g, gv ___stringlit_rt_gzip_header_1, Ers,
                map Zlib.proof.deflate.Rep.vi [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by auto. cancel. }
  { repeat split; auto; unfold Zlength; simpl; rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  destruct (ms5_init_facts sp (g_wb g) Hwb) as (Wok & Wrap & Wmode).
  replace (S5.init_ret vd 49 112 (g_wb g) aok) with (if aok then 0 else -4)
    by (unfold S5.init_ret; simpl; rewrite if_false by auto; rewrite Wok; destruct aok; reflexivity).
  apply semax_if_seq.
  destruct aok.
  2: { (* the allocation failed: return 0 *)
    replace (S5.init_mem gv Tsh vd ms5_r0 Vundef Vundef nullval (-4) sp (g_wb g))
      with (S5.raw_strm gv Tsh vd ms5_r0 nullval Vundef (gv Zlib.inflate.code._zcalloc)
              (gv Zlib.inflate.code._zcfree) nullval)
      by (unfold S5.init_mem; rewrite if_false by auto; reflexivity).
    unfold S5.raw_strm. rewrite ms5_cs_inflate.
    forward_if; [ | discriminate].
    forward.
    forward_if; [ | discriminate].
    sep_apply (data_at_data_at_ Tsh t_z).
    forward. Exists (Int.repr 0).
    (* not entailer!: it runs for minutes on data_at -> data_at_ of the gz_header structs *)
    apply andp_right; [apply prop_right; reflexivity |].
    sep_apply (data_at_data_at_ Tsh t_g (hvals g) vh). sep_apply (data_at_data_at_ Tsh t_g (gval g) vg).
    cancel. }
  (* Z_OK: a gzip stream in mode HEAD; inflateGetHeader attaches got *)
  replace (S5.init_mem gv Tsh vd ms5_r0 Vundef Vundef nullval 0 sp (g_wb g))
    with (S5.istream_raw gv Tsh vd (S5.raw_after_init ms5_r0 (S5.l_s (S5.init_live sp (g_wb g))))
            (S5.init_live sp (g_wb g)))
    by (unfold S5.init_mem; rewrite if_false by auto; reflexivity).
  sep_apply (ms5_istream gv vd sp (g_wb g) Nd Wrap).
  forward_if.
  { discriminate. }
  sep_apply (ms5_raw g vg H).
  sep_apply (ms5_toks g H).
  forward_call (gv, Tsh, vd, ms5_z0, Some (S5.init_live sp (g_wb g)), vg, Tsh, g_gxp g, g_gnp g, g_gcp g, h0 g).
  { cancel. }
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     Px & Pn & Pc & _).
    split; [apply ms5_hwf; auto |].
    split; [unfold RTHSpec.hattach_ok, S5.is_live; rewrite if_false by auto; intros _; left; exact Wmode |].
    cbn [IR.h_xp IR.h_np IR.h_cp h0].
    split; [intros _ E; rewrite E in Px; exact Px |].
    split; [intros _ E; rewrite E in Pn; exact Pn |].
    intros _ E; rewrite E in Pc; exact Pc. }
  unfold S5.is_live. rewrite if_false by auto. cbv iota. rewrite Wrap.
  change (Z.land 6 2 =? 0) with false. cbv iota. Intros.
  forward.
  forward_if.
  { discriminate. }
  forward.
  generalize POST_m; intros [r1 r2 r3 r4]; cbv iota beta; cbn [RA_normal].
  Exists ms5_z0 sp.
  unfold A38, gL, Zlib.proof.roundtrip.RTIIface.head_live, R, version_at, ifz, gp_locals, gs_locals, lv_locals.
  cbn [app].
  unfold RTH8Spec.istream8_opt. rewrite if_false by auto.
  change (Zlength (map Zlib.proof.deflate.Rep.vi [49; 46; 51; 46; 50; 0])) with 6.
  rewrite <- ms5_ver_cs.
  pose proof ms5_izinit.
  entailer!.
Qed.

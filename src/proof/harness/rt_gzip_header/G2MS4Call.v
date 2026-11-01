(* Law rt_gzip_header on the round-2 harness, main's body, segment 4: the call of one iteration of the deflate loop,
   `code = deflate(&compressor, Z_FINISH)` with avail_out = clip(capacity - |O|) and no input (s4_X1 -> s4_LC,
   G2DFacts.gd_call).  deflate_specN is used with pin = Z_NULL and inb = [] (new_stream left next_in Z_NULL and
   avail_in 0) and the model run c_deflate itself (ef = the identity, as roundtrip/RTRLoopCall.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpecN.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS4Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= s4_rlt.

Lemma s4_call_ok {Espec : OracleKind} J0 J gv vh vg vc vd vr g hx Hr b cbp O s tin tout adler msg msgv :
  g2_dfacts J0 J ->
  semax Delta_m (s4_X1 gv vh vg vc vd vr J g hx Hr b cbp O s tin tout adler msg msgv) s4_call
    (normal_ret_assert (s4_LC gv vh vg vc vd vr J g hx Hr b cbp)).
Proof.
  intros DF.
  unfold s4_call, s4_X1, s4_mem, s4_locals, gp_locals, gs_locals, lv_locals, Delta_m. simplify_func_tycontext.
  cbn [app]. abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  destruct (gd_range _ _ DF _ _ _ _ _ _ _ _ HJ) as (Hwb & Hgh & HO & Hb & RO & Hgz & Htin & Htout & Had).
  destruct (gd_call _ _ DF _ _ _ _ _ _ _ _ msg HJ) as (s' & z' & code & Hrun & Hrc & Hgz' & Hcode & HOK & HEND).
  sep_apply (s4_out_open b O cbp HO).
  unfold s4_win. Intros W Rout.
  match goal with Hx : clipz _ = 0 -> wv_ok W |- _ => rename Hx into HW end.
  match goal with Hx : forall zo : list Z, _ |- _ => rename Hx into HCL end.
  assert (Ha : 0 <= clipz (b - Zlength O) <= b - Zlength O) by (unfold clipz, umax; rep_lia).
  assert (Ha' : clipz (b - Zlength O) <= Int.max_unsigned) by (unfold clipz, umax; rep_lia).
  set (aout := clipz (b - Zlength O)) in *.
  rewrite dstream_sp_eq. Intros sp.
  unfold R. Intros.
  replace (api_fields vc nullval 0 tin (offset_val (Zlength O) cbp) aout tout msgv adler)
    with (api_fields vc (in_ptrN nullval 0) 0 tin (offset_val (Zlength O) cbp) (Zlength (Zrepeat Vundef aout))
            tout msgv adler)
    by (rewrite s4_in_ptr, Zlength_Zrepeat by lia; reflexivity).
  replace (@data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar aout) (Zrepeat Vundef aout)
             (offset_val (Zlength O) cbp))
    with (@data_at Zlib.proof.deflate.DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef aout)))
             (Zrepeat Vundef aout) (offset_val (Zlength O) cbp))
    by (rewrite Zlength_Zrepeat by lia; reflexivity).
  forward_call (Some s, vc, vh, sp, hx, nullval, Ews, @nil Z, 0, 0, tin, offset_val (Zlength O) cbp,
                Zrepeat Vundef aout, W, tout, msgv, msg, adler, Z_FINISH, (Some s', z', code), gv).
  { rewrite s4_in_obj. cancel. }
  { rewrite Zlength_Zrepeat by lia. split; [| split; [| split]].
    - exact HW.
    - unfold s32_ok, Z_FINISH. rep_lia.
    - unfold strm_ranges, zmk; simpl. unfold u32_ok, u64_ok, max_u64 in *.
      rewrite Zlength_nil. repeat split; auto; rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id.
      change (zmk ?a ?c ?e ?f ?g ?h ?i ?j) with (rzcall a c e f g h i j). rewrite Hrun. reflexivity. }
  simpl fst; simpl snd. Intros msgv'.
  forward.
  rewrite s4_in_obj, s4_in_ptr.
  destruct Hrc as (Hzi & Hai & Hni & Hti & Hao & Hzo & Hto & Rzo).
  rewrite Zlength_nil in Hai.
  replace (z_avail_in z') with 0 by lia.
  rewrite Zlength_Zrepeat by lia.
  sep_apply (HCL (z_out z') ltac:(rep_lia)).
  sep_apply (BoundKit.dstream_sp_dstream 2 (Some s') vc vh sp gv).
  rewrite <- (s4_hdr_at_eq s s' vh hx) by congruence.
  rewrite offset_offset_val.
  replace (Zlength O + Zlength (z_out z')) with (Zlength (O ++ z_out z')) by (rewrite Zlength_app; lia).
  Exists code (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z') (z_avail_out z') (z_msg z') msgv'.
  assert (P1 : rs32 code)
    by (unfold rs32; destruct Hcode as [-> | [-> | ->]]; compute; split; intro X; discriminate).
  assert (P2 : 0 <= Zlength (O ++ z_out z') <= b) by (rewrite Zlength_app; rep_lia).
  assert (P3 : rbytes (O ++ z_out z')) by (unfold rbytes in *; rewrite Forall_app; auto).
  assert (P4 : hclose vh g s' hx Hr) by (eapply s4_hclose_step; [eassumption | congruence]).
  unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals, R. cbn [app].
  entailer!.
Qed.

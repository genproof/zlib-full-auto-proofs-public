(* Law rt_gzip_header on the round-2 harness, main's body, segment 4 (G2MainKit.seg4_stmt): statements 40-43,
     compressor.next_out = compressed;
     do { compressor.avail_out = clip(capacity - (next_out - compressed)); code = deflate(&compressor, Z_FINISH); }
     while (code == Z_OK);
     if (code != Z_STREAM_END) return 0;
     compressed_len = next_out - compressed;
   The loop's invariant is G2MS4Kit.s4_LI (J of the bytes O produced so far, next_out = compressed + |O|), one
   iteration is G2MS4Body.s4_body_ok.  At Z_STREAM_END O is the gzip stream of no data with main's header (gd_call);
   the compressor is given back as the local's memory and head with its objects (hclose). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS4Kit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS4Body.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= s4_rlt.

Lemma g2seg4_ok : seg4_stmt.
Proof.
  intros Espec J0 J gv vh vg vc vd vr g st hx Hr b cbp DF.
  destruct st as [s tin tout adler msg msgv].
  unfold A32, seg4. cbn [st_s st_tin st_tout st_adler st_msg st_msgv].
  abbreviate_semax.
  Intros.
  match goal with Hj : J _ _ _ _ _ _ _ _ |- _ => rename Hj into HJ end.
  destruct (gd_range _ _ DF _ _ _ _ _ _ _ _ HJ) as (Hwb & Hgh & HO & Hb & RO & Hgz & Htin & Htout & Had).
  unfold st_fields, gp_locals, gs_locals, lv_locals. cbn [app].
  rewrite s4_fields_L. unfold s4_fieldsL. Intros.
  forward.
  forward_loop (s4_LI gv vh vg vc vd vr J g hx Hr b cbp)
    continue: (s4_LC gv vh vg vc vd vr J g hx Hr b cbp)
    break: (s4_LC gv vh vg vc vd vr J g hx Hr b cbp).
  { (* entry: nothing produced *)
    unfold s4_LI. Exists (@nil Z) s tin tout adler 0 msg msgv.
    unfold s4_mem, s4_comp, s4_locals, gp_locals, gs_locals, lv_locals, cnew. cbn [app].
    rewrite Zlength_nil, isptr_offset_val_zero by exact Pcbp.
    replace (cbytes b []) with (Zrepeat Vundef b) by (unfold cbytes; rewrite Zlength_nil, Z.sub_0_r; reflexivity).
    change (@data_at_ CS Ews (tarray tuchar b) cbp) with (@data_at CS Ews (tarray tuchar b) (Zrepeat Vundef b) cbp).
    sep_apply (s4_fields_fold vc nullval 0 tin cbp 0 tout msgv adler); auto.
    entailer!. }
  { (* one iteration *)
    eapply semax_post; [ | | | | apply (s4_body_ok J0 J gv vh vg vc vd vr g hx Hr b cbp DF) ];
      intros; simpl RA_normal; simpl RA_break; simpl RA_continue; simpl RA_return; normalize. }
  { (* while (code == Z_OK) *)
    unfold s4_LC. Intros code O s' tin' tout' adler' ao msg' msgv'.
    unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
    forward_if.
    - forward. unfold s4_LI.
      assert (code = 0) by (apply repr_inj_signed; auto; unfold rs32, repable_signed in *; rep_lia).
      Exists O s' tin' tout' adler' ao msg' msgv'.
      unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
      entailer!.
    - forward. unfold s4_LC. Exists code O s' tin' tout' adler' ao msg' msgv'.
      unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
      entailer!. }
  (* after the loop *)
  unfold s4_LC. Intros code O s' tin' tout' adler' ao msg' msgv'.
  unfold s4_mem, s4_locals, gp_locals, gs_locals, lv_locals. cbn [app].
  forward_if.
  { (* not Z_STREAM_END: return 0, main's locals back *)
    forward. Exists (Int.repr 0).
    sep_apply (s4_comp_back vc gv (Some s') vh nullval 0 tin' (offset_val (Zlength O) cbp) ao tout' msgv' adler').
    sep_apply (H13 s' eq_refl). unfold gside.
    sep_apply (data_at_data_at_ Tsh t_g (hvals g) vh).
    sep_apply (data_at_data_at_ Tsh t_g (gval g) vg).
    entailer!. }
  (* Z_STREAM_END: compressed_len = next_out - compressed *)
  assert (code = 1) by (apply repr_inj_signed; auto; unfold rs32, repable_signed in *; rep_lia). subst code.
  rewrite s4_fields_L. unfold s4_fieldsL. Intros.
  forward.
  forward.
  { entailer!. apply prop_right. apply s4_sameblock; auto. }
  rewrite s4_sub_ptr by (auto; unfold max_u64 in *; rep_lia).
  sep_apply (s4_fields_fold vc nullval 0 tin' (offset_val (Zlength O) cbp) ao tout' msgv' adler').
  sep_apply (s4_comp_back vc gv (Some s') vh nullval 0 tin' (offset_val (Zlength O) cbp) ao tout' msgv' adler').
  sep_apply (H13 s' eq_refl).
  specialize (H11 ltac:(reflexivity)).
  unfold POST_m. simpl RA_normal.
  match goal with |- _ |-- ?P => change P with (EX x : list Z, A36 gv vh vg vc vd vr g b cbp x) end.
  Exists O.
  unfold A36, s4_comp, gp_locals, gs_locals, lv_locals. cbn [app].
  entailer!.
Qed.

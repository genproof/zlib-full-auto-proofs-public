(* Law rj_bad_checksum, main: statements 26-30, new_stream(&decompressor), window_bits 8 -> 9, inflateInit2 and
   its check, next_in, next_out (bc_TH -> bc_inv, IFacts.bd_init). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.proof.harness.clip_streams.BCSegILoop.
Require Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.


Ltac simplify_remove_localdef_temp ::= bc_rlt.

Lemma bcs_strm_cs_c sh (v : bci_tuple) q :
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. bci_cs_tac CC_compress. Qed.

(* the local z_stream before new_stream() *)
Lemma bcs_strm_undef sh q :
  @data_at_ CS.CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite bcs_strm_cs_c. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition bcs_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma bcs_ns_raw_eq gv q :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  raw_strm gv Tsh q bcs_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, bcs_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite bci_strm_cs, bcs_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma bcs_raw_frame gv sh q r m s za zf o : raw_strm gv sh q r m s za zf o |-- @data_at_ CS.CS sh t_zsl q.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite bci_strm_cs. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" (GlobalsInit.version_at, deflate's compspecs) as inflateInit2_ takes it *)
Definition bcs_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma bcs_hversion i gv :
  GlobalsInit.version_at gv i = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength bcs_hv)) bcs_hv (gv i).
Proof.
  unfold GlobalsInit.version_at, bcs_hv. change (Zlength _) with 6.
  rewrite (equal_f (@data_at_change_composite _ _ CC_dcs Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  rewrite (equal_f (@data_at_change_composite _ _ CC_inflate Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  reflexivity.
Qed.

(* the fields after a successful inflateInit2_ (next_in / next_out NULL and avail_in / avail_out 0 from
   new_stream, totals 0, msg NULL, data_type 0, adler = wrap & 1 for a wrapped stream) *)
Definition bcs_z_init (L : live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma bcs_land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma bcs_init_istreamA gv shs vs L :
  istream_raw gv shs vs (raw_after_init bcs_raw (l_s L)) L |-- istreamA gv shs vs (bcs_z_init L) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, bcs_z_init, adler_v, raw_live, bcs_raw.
  Intros. simpl. pose proof (bcs_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

Lemma bcs_init_ret vs w a : isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

Lemma seg_isetup_ok : seg_isetup_stmt.
Proof.
  intros Espec P wbits n b D O src dp op cp vc vd gv PF FA K.
  pose proof FA as FA'.
  destruct FA' as (DF & HD & Hn & HO & Hb & Hw & Hw8 & BD & BD' & BO & Pdp & Pop & Pcp & SRC).
  destruct SRC as (Hsl & Hsb & Hpre & Htr).
  unfold bc_seg26, bc_TH, POST_B, POST_bc. abbreviate_semax.
  Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite (bcs_strm_undef Tsh vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (bcs_ns_raw_eq gv vd).
  forward_if (temp _window_bits (Vint (Int.repr (iwb wbits)))).
  { forward. entailer!;
    try (unfold iwb; assert (wbits = 8) by (apply repr_inj_signed; auto; unfold repable_signed; rep_lia);
         subst wbits; reflexivity). }
  { forward. entailer!;
    try (unfold iwb; destruct (Z.eqb_spec wbits 8); [ subst; contradiction | reflexivity ]). }
  assert (Hiw : Int.min_signed <= iwb wbits <= Int.max_signed) by (unfold iwb; destruct (wbits =? 8); rep_lia).
  unfold R_bc, R_of. Intros.
  rewrite (bcs_hversion lit_bc gv). unfold lit_bc.
  assert_PROP (isptr (gv ___stringlit_rj_bad_checksum_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vd, bcs_raw, Vundef, Vundef, nullval, iwb wbits, gv ___stringlit_rj_bad_checksum_1, Ers,
                bcs_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { repeat split; auto; try rep_lia; change (Zlength bcs_hv) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  rewrite bcs_init_ret by auto.
  destruct alloc_ok; [destruct (wbits_ok (iwb wbits)) eqn:WB | ];
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3: (forward_if; [ forward; Exists (Int.repr 0); sep_apply bcs_raw_frame; entailer! | idtac ]).
  2,3: exfalso; first [ discriminate
                      | match goal with Hx : Int.repr _ = Int.repr 0 |- _ =>
                          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].
  forward_if.
  { exfalso; discriminate. }
  Intros. set (L0 := init_live sp (iwb wbits)) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply (bcs_init_istreamA gv Tsh vd L0).
  rewrite bci_istreamA_unfold. Intros.
  unfold bci_tup.
  forward. forward.
  set (z0 := bcs_z_init L0) in *.
  set (z1 := ZF cp (zf_ai z0) (zf_tin z0) op (zf_ao z0) (zf_tout z0) (zf_msg z0) (zf_dt z0) (zf_adler z0)
                (zf_res z0)).
  assert (Zo0 : zf_ok z0) by assumption.
  assert (Zo1 : zf_ok z1) by (unfold z1, zf_ok in *; simpl; exact Zo0).
  assert (Hsp : isptr sp)
    by (match goal with Hx : true = true -> isptr sp |- _ => exact (Hx eq_refl) end).
  assert (Hsw : swfW (l_s L0)).
  { unfold L0, init_live. simpl l_s. unfold swfW.
    destruct (reset2_wb (iwb wbits)) as [[wr wb] | ]; cbn; split; intro E; inversion E. }
  assert (HI : init_ok (iwb wbits) z1 sp).
  { unfold init_ok. split; [exact WB | ]. split; [exact Hsp | ]. split; [exact Zo1 | ].
    split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ]. exact HL0. }
  assert (HP : P wbits D O src 0 [] z1 L0)
    by (apply (bd_init P PF wbits D O src z1 sp); auto; unfold Ptrofs.max_unsigned in Hb; simpl in Hb; lia).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K ].
  unfold bc_inv. Exists 0 (@nil Z) z1 L0.
  rewrite bci_istreamA_unfold. unfold bci_tup.
  unfold R_bc, R_of. rewrite (bcs_hversion lit_bc gv). unfold lit_bc.
  entailer!.
  rewrite app_nil_l. unfold data_at_. cancel.
Qed.

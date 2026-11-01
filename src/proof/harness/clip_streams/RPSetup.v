(* Law rt_partial, main: the part rp_setup_stmt of the inflate half (RPKit.v), statements 20-25:
   prefix_len = upto(compressed_len - 1), new_stream(&decompressor), window_bits 8 -> 9,
   inflateInit2_(&decompressor, window_bits, "1.3.2", sizeof(z_stream)) (every outcome but Z_OK returns),
   next_in = compressed, next_out = out; the loop's invariant then holds at pos 0 with no output
   (IFacts.px_init). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.harness.rt_partial.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support and moves between the units' compspecs and the law's                           *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma rps_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rps_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rps_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rps_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rps_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac rps_rlt :=
  repeat first [ rewrite rps_rlt_nil | rewrite rps_rlt_gvars | rewrite rps_rlt_lvar | rewrite rps_rlt_same
               | rewrite rps_rlt_cons by (let X := fresh in intro X; discriminate X) ].

Ltac simplify_remove_localdef_temp ::= rps_rlt.

Ltac rps_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

(* the 14 members of struct z_stream *)
Definition rps_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma rps_strm_cs sh (v: rps_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. rps_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition rps_tup (gv: globals) (z: zfields) (adv sp: val) : rps_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma rps_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (rps_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rps_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma rps_strm_cs_c sh (v : rps_tuple) q :
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. rps_cs_tac CC_compress. Qed.

(* the local z_stream before new_stream() *)
Lemma rps_strm_undef sh q :
  @data_at_ CS.CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite rps_strm_cs_c. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition rps_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma rps_ns_raw_eq gv q :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  raw_strm gv Tsh q rps_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, rps_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite rps_strm_cs, rps_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma rps_raw_frame gv sh q r m s za zf o : raw_strm gv sh q r m s za zf o |-- @data_at_ CS.CS sh t_zsl q.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite rps_strm_cs. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" (GlobalsInit.version_at, deflate's compspecs) as inflateInit2_ takes it *)
Definition rps_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma rps_hversion i gv :
  GlobalsInit.version_at gv i = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength rps_hv)) rps_hv (gv i).
Proof.
  unfold GlobalsInit.version_at, rps_hv. change (Zlength _) with 6.
  rewrite (equal_f (@data_at_change_composite _ _ CC_dcs Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  rewrite (equal_f (@data_at_change_composite _ _ CC_inflate Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  reflexivity.
Qed.

(* the fields after a successful inflateInit2_ (next_in / next_out NULL and avail_in / avail_out 0 from
   new_stream, totals 0, msg NULL, data_type 0, adler = wrap & 1 for a wrapped stream) *)
Definition rps_z_init (L : live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma rps_land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma rps_init_istreamA gv shs vs L :
  istream_raw gv shs vs (raw_after_init rps_raw (l_s L)) L |-- istreamA gv shs vs (rps_z_init L) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, rps_z_init, adler_v, raw_live, rps_raw.
  Intros. simpl. pose proof (rps_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

Lemma rps_init_ret vs w a : isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

Lemma rp_setup : rp_setup_stmt.
Proof.
  intros Espec P wbits n b D O dp ep op cp vc vd gv PF K.
  unfold rp_seg20, rp_DH, POST_B, POST_rp. abbreviate_semax.
  Intros.
  match goal with Hd : DFacts.dfinal_of _ _ _ |- _ => rename Hd into DF end.
  assert (HO1 : 1 <= Zlength O) by (apply (px_len P PF wbits D O); exact DF).
  forward_call (Zlength O - 1).
  Intros lim.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite (rps_strm_undef Tsh vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (rps_ns_raw_eq gv vd).
  forward_if (temp _window_bits (Vint (Int.repr (iwb wbits)))).
  { forward. entailer!;
    try (unfold iwb; assert (wbits = 8) by (apply repr_inj_signed; auto; unfold repable_signed; rep_lia);
         subst wbits; reflexivity). }
  { forward. entailer!;
    try (unfold iwb; destruct (Z.eqb_spec wbits 8); [ subst; contradiction | reflexivity ]). }
  assert (Hiw : Int.min_signed <= iwb wbits <= Int.max_signed) by (unfold iwb; destruct (wbits =? 8); rep_lia).
  unfold R_rp, R_of. Intros.
  rewrite (rps_hversion lit_rp gv). unfold lit_rp.
  assert_PROP (isptr (gv ___stringlit_rt_partial_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vd, rps_raw, Vundef, Vundef, nullval, iwb wbits, gv ___stringlit_rt_partial_1, Ers,
                rps_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { repeat split; auto; try rep_lia; change (Zlength rps_hv) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  rewrite rps_init_ret by auto.
  destruct alloc_ok; [destruct (wbits_ok (iwb wbits)) eqn:WB | ];
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3: (forward_if; [ forward; Exists (Int.repr 0); sep_apply rps_raw_frame; entailer! | idtac ]).
  2,3: exfalso; first [ discriminate
                      | match goal with Hx : Int.repr _ = Int.repr 0 |- _ =>
                          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].
  forward_if.
  { exfalso; discriminate. }
  Intros. set (L0 := init_live sp (iwb wbits)) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply (rps_init_istreamA gv Tsh vd L0).
  rewrite rps_istreamA_unfold. Intros.
  unfold rps_tup.
  forward. forward.
  set (z0 := rps_z_init L0) in *.
  set (z1 := ZF cp (zf_ai z0) (zf_tin z0) op (zf_ao z0) (zf_tout z0) (zf_msg z0) (zf_dt z0) (zf_adler z0)
                (zf_res z0)).
  assert (Zo1 : zf_ok z1) by (unfold z1, zf_ok in *; simpl; exact H10).
  assert (Hsw : swfW (l_s L0)).
  { unfold L0, init_live. simpl l_s. unfold swfW.
    destruct (reset2_wb (iwb wbits)) as [[wr wb] | ]; cbn; split; intro E; inversion E. }
  assert (HI : init_ok (iwb wbits) z1 sp).
  { unfold init_ok. split; [exact WB | ]. split; [exact (H8 eq_refl) | ]. split; [exact Zo1 | ].
    split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ]. exact HL0. }
  assert (HP : P wbits D O O 0 [] z1 L0)
    by (apply (px_init P PF wbits D O z1 sp); auto; unfold Ptrofs.max_unsigned in H3; simpl in H3; lia).
  assert (FA : rp_facts wbits n b lim D O dp ep op cp)
    by (unfold rp_facts; split; [exact DF | ]; repeat split; auto; lia).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K lim FA) ].
  unfold rp_inv. Exists 0 (@nil Z) z1 L0.
  rewrite rps_istreamA_unfold. unfold rps_tup.
  unfold R_rp, R_of. rewrite (rps_hversion lit_rp gv). unfold lit_rp.
  entailer!.
  rewrite app_nil_l. unfold data_at_. cancel.
Qed.

(* Law rfc_trailing_bytes, main: statements 27-33 of TBKit.v (new_stream, window_bits 8 -> 9, code =
   inflateInit2_, `if (code == Z_MEM_ERROR) return 0`, gp_assert(code == Z_OK), next_in = input, next_out = out),
   from TBKit.tb_TH to the inflate loop's invariant TBKit.tb_inv; the invariant then holds at pos 0 with no output
   (TBFacts.tl_init). The windowBits are those deflateInit2_ accepted, so inflateInit2_ returns Z_OK or, when its
   allocation fails, Z_MEM_ERROR. As RPSetup.v (rt_partial) with the input object ip of exactly |src| bytes instead of the
   compressed bytes. *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.clip_streams.TBKit.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactic support and moves between the units' compspecs and the law's                           *)

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) takes minutes
   after a call that stores into a temp: remove the temp by rewriting instead *)
Lemma tbs_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma tbs_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma tbs_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma tbs_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma tbs_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac tbs_rlt :=
  repeat first [ rewrite tbs_rlt_nil | rewrite tbs_rlt_gvars | rewrite tbs_rlt_lvar | rewrite tbs_rlt_same
               | rewrite tbs_rlt_cons by (let X := fresh in intro X; discriminate X) ].

Ltac simplify_remove_localdef_temp ::= tbs_rlt.

Ltac tbs_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

(* the 14 members of struct z_stream *)
Definition tbs_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma tbs_strm_cs sh (v: tbs_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. tbs_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition tbs_tup (gv: globals) (z: zfields) (adv sp: val) : tbs_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma tbs_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (tbs_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite tbs_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma tbs_strm_cs_c sh (v : tbs_tuple) q :
  @data_at Zlib.units.Compress.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. tbs_cs_tac CC_compress. Qed.

(* the local z_stream before new_stream() *)
Lemma tbs_strm_undef sh q :
  @data_at_ CS.CS sh t_zsl q =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) q.
Proof. unfold data_at_. change t_zs with t_zsl. unfold zs_val. rewrite tbs_strm_cs_c. reflexivity. Qed.

(* the struct after new_stream(): inflateInit2_'s raw stream *)
Definition tbs_raw : rawf :=
  RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef.

Lemma tbs_ns_raw_eq gv q :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef nullval nullval
       nullval Vundef Vundef Vundef) q =
  raw_strm gv Tsh q tbs_raw Vundef Vundef nullval nullval nullval.
Proof.
  unfold raw_strm, tbs_raw, zs_val; simpl. change t_zs with t_zsl. change Rep.t_strm with t_zsl.
  rewrite tbs_strm_cs, tbs_strm_cs_c. reflexivity.
Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma tbs_raw_frame gv sh q r m s za zf o : raw_strm gv sh q r m s za zf o |-- @data_at_ CS.CS sh t_zsl q.
Proof. unfold raw_strm. change Rep.t_strm with t_zsl. rewrite tbs_strm_cs. apply data_at_data_at_. Qed.

(* the harness's "1.3.2" (GlobalsInit.version_at, deflate's compspecs) as inflateInit2_ takes it *)
Definition tbs_hv : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma tbs_hversion i gv :
  GlobalsInit.version_at gv i = @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength tbs_hv)) tbs_hv (gv i).
Proof.
  unfold GlobalsInit.version_at, tbs_hv. change (Zlength _) with 6.
  rewrite (equal_f (@data_at_change_composite _ _ CC_dcs Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  rewrite (equal_f (@data_at_change_composite _ _ CC_inflate Ers (tarray tschar 6) _ _ (JMeq_refl _) eq_refl) (gv i)).
  reflexivity.
Qed.

(* the fields after a successful inflateInit2_ (next_in / next_out NULL and avail_in / avail_out 0 from
   new_stream, totals 0, msg NULL, data_type 0, adler = wrap & 1 for a wrapped stream) *)
Definition tbs_z_init (L : live) : zfields :=
  ZF nullval 0 0 nullval 0 0 None 0 (if i_wrap (l_s L) =? 0 then 0 else Z.land (i_wrap (l_s L)) 1) Vundef.

Lemma tbs_land1_range x : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma tbs_init_istreamA gv shs vs L :
  istream_raw gv shs vs (raw_after_init tbs_raw (l_s L)) L |-- istreamA gv shs vs (tbs_z_init L) Vundef (Some L).
Proof.
  unfold istream_raw, istreamA, raw_strm, zstrm_atA, raw_after_init, tbs_z_init, adler_v, raw_live, tbs_raw.
  Intros. simpl. pose proof (tbs_land1_range (i_wrap (l_s L))).
  destruct (i_wrap (l_s L) =? 0) eqn:E; entailer!; unfold zf_ok; simpl; rep_lia.
Qed.

Lemma tbs_init_ret vs w a : isptr vs ->
  init_ret vs 49 112 w a = if a then (if wbits_ok w then Z_OK else Z_STREAM_ERROR) else Z_MEM_ERROR.
Proof.
  intros Pv. unfold init_ret. simpl.
  destruct (EqDec_val vs nullval); [subst; contradiction | ]. destruct a; reflexivity.
Qed.

(* the windowBits deflateInit2_ accepted (DFacts.wbits_acc), 8 changed to 9 as the harness does (IFacts.iwb), are
   windowBits that inflateInit2_ accepts: zlib -15..-9 raw, 9..15 zlib, 25..31 gzip *)
Lemma tbs_wbits_ok w : wbits_acc w = true -> wbits_ok (iwb w) = true.
Proof.
  intros H.
  assert (R : -15 <= w <= 31).
  { unfold wbits_acc, rwb_of in H. repeat rewrite andb_true_iff in H. destruct H as [[[H1 _] H3] _].
    rewrite negb_true_iff, Z.ltb_ge in H1. apply Z.leb_le in H3.
    destruct (w <? 0) eqn:E1; [lia|]. destruct (w >? 15) eqn:E2; lia. }
  assert (C : forallb (fun k => implb (wbits_acc (k - 15)) (wbits_ok (iwb (k - 15))))
                (map Z.of_nat (seq 0 47)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (w + 15)).
  replace (w + 15 - 15) with w in C by lia. rewrite H in C. apply C.
  apply in_map_iff. exists (Z.to_nat (w + 15)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma tb_setup : tb_setup_stmt.
Proof.
  intros Espec P wbits n D O src dp op ip vc vd gv PF FA K.
  pose proof FA as FA'.
  destruct FA' as (DF & Hn & Hnr & (HO & Hsrc) & Hsub & Hbs & Hw & rD & iD & rO & Pdp & Pop & Pip).
  unfold tb_seg27, tb_TH, POST_B, POST_tb. abbreviate_semax.
  Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite (tbs_strm_undef Tsh vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (tbs_ns_raw_eq gv vd).
  forward_if (temp _window_bits (Vint (Int.repr (iwb wbits)))).
  { forward. entailer!;
    try (unfold iwb; assert (wbits = 8) by (apply repr_inj_signed; auto; unfold repable_signed; rep_lia);
         subst wbits; reflexivity). }
  { forward. entailer!;
    try (unfold iwb; destruct (Z.eqb_spec wbits 8); [ subst; contradiction | reflexivity ]). }
  assert (Hiw : Int.min_signed <= iwb wbits <= Int.max_signed) by (unfold iwb; destruct (wbits =? 8); rep_lia).
  unfold R_tb, R_of. Intros.
  rewrite (tbs_hversion lit_tb gv). unfold lit_tb.
  assert_PROP (isptr (gv ___stringlit_rfc_trailing_bytes_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vd, tbs_raw, Vundef, Vundef, nullval, iwb wbits, gv ___stringlit_rfc_trailing_bytes_1,
                Ers, tbs_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { repeat split; auto; try rep_lia; change (Zlength tbs_hv) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  rewrite tbs_init_ret by auto.
  (* the windowBits are valid: Z_OK, or Z_MEM_ERROR when the state's allocation fails *)
  assert (WB : wbits_ok (iwb wbits) = true) by (apply tbs_wbits_ok; destruct DF as [A _]; exact A).
  rewrite WB.
  destruct alloc_ok;
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2: { forward_if; [ forward; Exists (Int.repr 0); sep_apply tbs_raw_frame; entailer! | ].
       exfalso. match goal with Hx : Int.repr _ <> _ |- _ => apply Hx; reflexivity end. }
  forward_if.
  { exfalso. match goal with Hx : Int.repr _ = _ |- _ =>
      apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end. }
  (* gp_assert(code == Z_OK) *)
  forward_call (Int.one).
  Intros. set (L0 := init_live sp (iwb wbits)) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply (tbs_init_istreamA gv Tsh vd L0).
  rewrite tbs_istreamA_unfold. Intros.
  unfold tbs_tup.
  forward. forward.
  set (z0 := tbs_z_init L0) in *.
  set (z1 := ZF ip (zf_ai z0) (zf_tin z0) op (zf_ao z0) (zf_tout z0) (zf_msg z0) (zf_dt z0) (zf_adler z0)
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
    by (apply (tl_init P PF wbits D O src z1 sp); auto; unfold Ptrofs.max_unsigned in Hsrc; simpl in Hsrc; lia).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K ].
  unfold tb_inv. Exists 0 (@nil Z) z1 L0.
  rewrite tbs_istreamA_unfold. unfold tbs_tup.
  unfold R_tb, R_of. rewrite (tbs_hversion lit_tb gv). unfold lit_tb.
  entailer!.
  rewrite app_nil_l. unfold data_at_. cancel.
Qed.

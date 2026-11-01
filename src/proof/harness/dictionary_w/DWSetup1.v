(* Laws rt_dictionary and api_dict_id, main (DWKit.v), statements 24-27 (rt_dictionary's numbers): the moves of the decompressor in
   and out of set_buffer() and the proof for rt_dictionary (DWSetup.v has api_dict_id's and the conjunction). *)
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
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.clip_streams.RTSetup.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Import DRT.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the decompressor as set_buffer() takes it (laws_common.h's helpers are specified at the compress unit's compspecs) *)
Lemma dws_offer_pre gv z adv sp q :
  @data_at CS.CS Tsh t_zsl (rtl_tup gv z adv sp) q =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
       (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) sp
       (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
       adv (zf_res z)) q.
Proof. unfold rtl_tup, zs_val. change t_zs with t_zsl. rewrite rts_strm_cs_c. reflexivity. Qed.

(* and as set_buffer() gives it back: the fields offer_z *)
Lemma dws_offer_post gv z adv sp q ni ai no ao :
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr (zf_tin z))) no
       (Vint (Int.repr ao)) (Vlong (Int64.repr (zf_tout z))) (msg_val gv (zf_msg z)) sp
       (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval (Vint (Int.repr (zf_dt z)))
       adv (zf_res z)) q =
  @data_at CS.CS Tsh t_zsl (rtl_tup gv (offer_z z ni ai no ao) adv sp) q.
Proof. unfold rtl_tup, zs_val, offer_z. simpl. change t_zs with t_zsl. rewrite rts_strm_cs_c. reflexivity. Qed.

Lemma dws_adler_offer raw z ni ai no ao av : adler_v raw (offer_z z ni ai no ao) av = adler_v raw z av.
Proof. reflexivity. Qed.

Lemma dws_clipz_range x : 0 <= x -> 0 <= IFacts.clipz x <= Int.max_unsigned.
Proof. intros. unfold IFacts.clipz, umax. rep_lia. Qed.

(* rt_dictionary: statements 21-24 from DH to A25 *)
Lemma seg_setup_drt_ok : seg_setup_drt_stmt.
Proof.
  intros Espec gv vc vd wbits n b D O dict dp op ddp cp.
  unfold DH, seg_setup_drt, POST_drt, POST_of. abbreviate_semax.
  Intros.
  match goal with Hf : dw_hf _ _ _ _ _ _ _ _ _ _ |- _ => rename Hf into HF end.
  pose proof HF as (DF & CF & HO & Hb & RD & RO & Pcp).
  pose proof CF as (Hn & HD & BD & Pdp & Pop & Hdict & Bdict & Pddp & Hwb).
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  assert_PROP (isptr vd) as Pvd by entailer!.
  rewrite (rts_strm_undef Tsh vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (rts_ns_raw_eq gv vd).
  forward_if (temp _window_bits (Vint (Int.repr (iwb wbits)))).
  { forward. entailer!;
    try (unfold iwb; assert (wbits = 8) by (apply repr_inj_signed; auto; unfold repable_signed; rep_lia);
         subst wbits; reflexivity). }
  { forward. entailer!;
    try (unfold iwb; destruct (Z.eqb_spec wbits 8); [ subst; contradiction | reflexivity ]). }
  assert (Hiw : Int.min_signed <= iwb wbits <= Int.max_signed) by (unfold iwb; destruct (wbits =? 8); rep_lia).
  unfold R_of. Intros.
  rewrite (rts_hversion lit_drt gv). unfold lit_drt.
  assert_PROP (isptr (gv Zlib.harness.rt_dictionary.code.___stringlit_rt_dictionary_1)) as Pver by entailer!.
  forward_call (gv, Tsh, vd, rts_raw, Vundef, Vundef, nullval, iwb wbits,
                gv Zlib.harness.rt_dictionary.code.___stringlit_rt_dictionary_1, Ers, rts_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { repeat split; auto; try rep_lia; change (Zlength rts_hv) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  rewrite rts_init_ret by auto.
  destruct alloc_ok; [destruct (wbits_ok (iwb wbits)) eqn:WB | ];
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2,3: (forward_if; [ forward; Exists (Int.repr 0); sep_apply rts_raw_frame; entailer! | idtac ]).
  2,3: exfalso; first [ discriminate
                      | match goal with Hx : Int.repr _ = Int.repr 0 |- _ =>
                          apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].
  forward_if.
  { exfalso; discriminate. }
  Intros. set (L0 := init_live sp (iwb wbits)) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply (rts_init_istreamA gv Tsh vd L0).
  set (z0 := rts_z_init L0).
  rewrite rtl_istreamA_unfold. Intros.
  rewrite dws_offer_pre.
  forward_call (Zlength O).
  forward_call n.
  { unfold DFacts.max_size in Hn. change Int64.max_unsigned with 18446744073709551615. lia. }
  assert (E1 : IFacts.clipz (Zlength O) = Z.min (Zlength O) Int.max_unsigned) by reflexivity.
  assert (E2 : IFacts.clipz n = Z.min n Int.max_unsigned) by reflexivity.
  assert (Hc1 := dws_clipz_range (Zlength O) ltac:(lia)).
  assert (Hc2 := dws_clipz_range n ltac:(lia)).
  rewrite E1 in Hc1. rewrite E2 in Hc2.
  forward_call (vd, Tsh, cp, Z.min (Zlength O) Int.max_unsigned, op, Z.min n Int.max_unsigned, zf_ni z0,
                Vint (Int.repr (zf_ai z0)), Vlong (Int64.repr (zf_tin z0)), zf_no z0, Vint (Int.repr (zf_ao z0)),
                Vlong (Int64.repr (zf_tout z0)), msg_val gv (zf_msg z0), l_sp L0, gv Zlib.inflate.code._zcalloc,
                gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt z0)),
                adler_v (raw_live (Some L0)) z0 Vundef, zf_res z0).
  rewrite <- E1, <- E2 in *.
  rewrite (dws_offer_post gv z0). rewrite <- (dws_adler_offer _ z0 cp (IFacts.clipz (Zlength O)) op (IFacts.clipz n)).
  set (z1 := offer_z z0 cp (IFacts.clipz (Zlength O)) op (IFacts.clipz n)).
  assert (Zo1 : zf_ok z1) by (unfold z1, offer_z, zf_ok in *; simpl in *; tauto).
  assert (Hsw : swfW (l_s L0)).
  { unfold L0, init_live. simpl l_s. unfold swfW.
    destruct (reset2_wb (iwb wbits)) as [[wr wb] | ]; cbn; split; intro E; inversion E. }
  assert (HI : init_ok (iwb wbits) z0 sp).
  { unfold init_ok. split; [exact WB | ]. split; [exact (H eq_refl) | ]. split; [exact H1 | ].
    split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ]. exact HL0. }
  Exists z0 sp. unfold A25. fold L0. fold z1.
  rewrite rtl_istreamA_unfold.
  unfold R_of. rewrite (rts_hversion lit_drt gv). unfold lit_drt.
  entailer!.
Qed.


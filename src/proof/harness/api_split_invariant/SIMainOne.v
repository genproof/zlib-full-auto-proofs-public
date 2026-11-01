(* Law api_split_invariant, main: statements 16-22, the one stream: new_stream(&one), code_one = inflateInit2_(&one,
   window, "1.3.2", sizeof(z_stream)) (`return 0` on Z_MEM_ERROR, then gp_assert(code_one == Z_OK): the window is
   accepted, so the init returns Z_OK or Z_MEM_ERROR), set_buffer(&one, input, input_len, out_one, room),
   code_one = inflate(&one, flush), `return 0` on Z_MEM_ERROR: by SIFacts.sf_init and sf_call (P = 0, O = []), the
   one call stops where the stream stops (Max) (sm_A -> sm_B). *)
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
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

Lemma seg_one_ok {Espec: OracleKind} Inv Max gv vwb vone vsplit w src room flush inp ins o1 o2:
  si_facts Inv Max -> sm_A_facts w src room flush inp ins o1 o2 ->
  (forall r1 z1 L1 ow1, sm_B_facts Max w src room r1 z1 ow1 ->
     semax Delta_m (sm_B gv vwb vone vsplit w src room inp ins o1 o2 r1 z1 L1 ow1) sm_seg23 POST_B) ->
  semax Delta_m (sm_A gv vwb vone vsplit w src room flush inp ins o1 o2) sm_seg16 POST_B.
Proof.
  intros SF HA K.
  unfold sm_seg16, sm_A, Delta_m, Gmain_k, POST_B. simplify_func_tycontext. abbreviate_semax.
  destruct HA as (Hw & Bs & Hl & Hr & Hfl & Hb & Ht & Pi & Pc & Po1 & Po2).
  assert_PROP (isptr vone) as Pv by entailer!.
  (* new_stream(&one) *)
  rewrite (sm_strm_undef Tsh vone).
  forward_call (vone, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite (sm_ns_raw_eq gv vone).
  rewrite (sm_hversion gv).
  sm_aptr (gv ___stringlit_api_split_invariant_1) Pver.
  (* inflateInit2_(&one, window, "1.3.2", sizeof(z_stream)): an allocation failure returns, w is accepted *)
  forward_call (gv, Tsh, vone, sm_ns_raw, Vundef, Vundef, nullval, w, gv ___stringlit_api_split_invariant_1, Ers,
                sm_hv, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength sm_hv) with 6; destruct Hw as [E|[E|[E|E]]]; subst w; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *; simpl snd in *.
  rewrite sm_init_ret by auto.
  rewrite (sm_window_wbits w Hw).
  destruct alloc_ok; unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  (* code_one = Z_MEM_ERROR returns; otherwise gp_assert(code_one == Z_OK) holds *)
  2: { forward_if; [ | sm_infeas]. forward. Exists (Int.repr 0). sep_apply sm_raw_frame. entailer!. }
  forward_if; [sm_infeas | ].
  forward_call Int.one.
  set (L0 := init_live sp w) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply sm_init_istreamA.
  sep_apply (sm_istreamA_zs gv vone (sm_z_init L0) Vundef L0). Intros.
  (* set_buffer(&one, input, input_len, out_one, room) *)
  set (z0 := sm_z_init L0) in *.
  forward_call (vone, Tsh, inp, Zlength src, o1, room, zf_ni z0, Vint (Int.repr (zf_ai z0)),
                Vlong (Int64.repr (zf_tin z0)), zf_no z0, Vint (Int.repr (zf_ao z0)), Vlong (Int64.repr (zf_tout z0)),
                msg_val gv (zf_msg z0), l_sp L0, gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval,
                Vint (Int.repr (zf_dt z0)), adler_v (raw_live (Some L0)) z0 Vundef, zf_res z0).
  (* the offered stream *)
  set (zA := sm_next (sm_avail z0 (Zlength src) room) inp o1).
  assert (HzA: zf_ok zA).
  { unfold zA, sm_next, sm_avail, zf_ok in *; simpl in *. pose proof (Zlength_nonneg src). intuition (try lia). }
  change t_zs with t_zsl. rewrite sm_strm_cs_c.
  sep_apply (sm_istreamA_fold gv Tsh vone zA Vundef L0); [auto | ].
  assert (EO: data_at_ Ews (tarray tuchar room) o1 = data_at Ews (tarray tuchar room) (sm_out [] room) o1).
  { rewrite sm_out_nil by lia. rewrite data_at__eq. reflexivity. }
  rewrite EO. clear EO.
  sep_apply (sm_bufs_pre vone L0 inp src 0 o1 [] room); [change (Zlength (@nil Z)) with 0; lia | ].
  assert (INOK: in_ok (sm_ib inp src 0) src).
  { pose proof (sm_in_ok inp src 0 (Zlength src) Pi Bs ltac:(lia) ltac:(list_solve) ltac:(lia) ltac:(rep_lia)) as X.
    rewrite Z.add_0_l, sublist_same in X by lia. exact X. }
  assert (OUTOK: out_ok (sm_ob o1 [] room) room).
  { apply sm_out_ok; auto; try lia; change (Zlength (@nil Z)) with 0; rep_lia. }
  rewrite <- (sm_istreamA_opt_ptr gv Tsh vone zA Vundef (Some L0)) by auto.
  (* code_one = inflate(&one, flush) *)
  forward_call (gv, Tsh, vone, zA, Vundef, Some L0, sm_ib inp src 0, src, Some (sm_ob o1 [] room), flush, Ers, Ers,
                true, true).
  { rewrite sm_is_live_ptr by auto. unfold L0. rewrite sm_head_init. cancel. }
  { split; [unfold in_ptr, sm_ib, zA, sm_next; simpl; symmetry; apply isptr_offset_val_zero; auto | ].
    split; [split; [exact INOK | reflexivity] | ].
    split; [unfold out_ptr, sm_ob, zA, sm_next; simpl; symmetry; apply isptr_offset_val_zero; auto | ].
    apply sm_swfW_init; auto. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  pose proof (sm_inflate_ret _ _ _ _ _ _ _ _ _ _ _ REL) as Hr5.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply sm_a_frame_opt. entailer!. }
  match goal with H: Int.repr r <> _ |- _ => rename H into Hnm end.
  assert (Hm: r <> Z_MEM_ERROR) by (intro E; subst r; apply Hnm; reflexivity).
  (* the call from the initial state, offered all of the input and of the space *)
  assert (HI0: Inv w src room 0 [] L0) by (apply (sf_init _ _ SF); auto; lia).
  destruct (sf_call _ _ SF w src room 0 [] L0 flush vone zA (sm_ib inp src 0) src (sm_ob o1 [] room) r z' st' ow
              HI0 HL0 HzA ltac:(reflexivity) ltac:(intro E; subst vone; contradiction) ltac:(discriminate)
              ltac:(reflexivity) ltac:(rewrite Z.add_0_l, sublist_same by lia; reflexivity) ltac:(lia)
              ltac:(change (Zlength (@nil Z)) with 0; simpl; lia) REL Hm)
    as (L1 & Est & Hai & How & HI1 & Hni & Hno & Hao & Htout & Hfin & Hnf).
  subst st'. rewrite app_nil_l in Htout, Hfin, Hnf.
  assert (HB: sm_B_facts Max w src room r z' ow).
  { unfold sm_B_facts, sm_stop. simpl in How. split; [ | split; [lia | split; [exact Htout | lia]]].
    destruct (final_code r) eqn:F; [apply Hfin; auto | apply Hnf; auto; change (Zlength (@nil Z)) with 0; simpl; lia]. }
  rewrite sm_istreamA_opt_ptr by auto.
  sep_apply (sm_bufs_post vone L0 inp src 0 o1 [] room ow). Intros.
  rewrite app_nil_l, sm_is_live_ptr by auto.
  (* forward_call moved the version literal to the law's compspecs *)
  change (@data_at CS Ers (tarray tschar (Zlength sm_hv)) sm_hv (gv ___stringlit_api_split_invariant_1))
    with (si_hversion gv).
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (K r z' L1 ow HB)].
  unfold sm_B, sm_one. entailer!.
Qed.

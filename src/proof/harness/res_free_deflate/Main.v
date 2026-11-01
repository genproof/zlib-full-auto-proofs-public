(* Law res_free_deflate: main of harness/res_free_deflate.c against main_core_spec (Ra lit) at the law's
   compspecs CSa, with the callees of Gmain (src/proof/harness/res_alloc_deflate/).

   main draws the parameters, the data and the output space, makes the stream count through the harness's
   counting allocator (counted_stream) and calls deflateInit2_ with any parameters.  On failure deflateInit2_
   gave back every block it took (the bytes held are 0).  On success main offers everything, calls deflate()
   once and deflateEnd: the allocator's events are deflateInit2_'s five allocations [dinit_events s] (deflate()
   allocates nothing: its specification does not touch the allocator's state) and deflateEnd's five releases
   [dend_events s' p] of the state s' after deflate(), of the same sizes (DeflateKeep.v; deflateEnd frees since
   s' has a valid status, DeflateStatus.v).  So count.now is 0 at the check.  deflateInit2_'s result is
   Z_MEM_ERROR only after an allocation failed (its specification, za/deflate/ZSpec.v), which sets count.failed;
   on success it is Z_OK.  So `code != Z_MEM_ERROR || count.failed` holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.GlobalsInit Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS Zlib.proof.harness.res_alloc_deflate.Specs
               Zlib.proof.harness.res_alloc_deflate.Gmain Zlib.proof.harness.res_alloc_deflate.InitFacts
               Zlib.proof.harness.res_alloc_deflate.StrmKit Zlib.proof.harness.res_alloc_deflate.MainKit
               Zlib.proof.harness.res_alloc_deflate.DeflateKeep Zlib.proof.harness.res_alloc_deflate.DeflateStatus.
Require Import Zlib.proof.harness.res_free_deflate.Facts Zlib.proof.harness.res_free_deflate.TailKit
               Zlib.proof.harness.res_free_deflate.MainStmt.
Require Zlib.proof.deflate.LTCInitKit.
Require Zlib.contracts.res_free_deflate.
Require Import Zlib.harness.res_free_deflate.code.
Local Open Scope logic.

(* after `if (code == Z_OK) { .. }`: main's z_stream is again its uninitialised local, the counting
   allocator's events [tr] leave count.now = 0, and deflateInit2_'s result [code] is Z_MEM_ERROR (-4) only if
   an allocation failed (count.failed = 1) *)
Definition J2 (sp cp : val) (gv : globals) (code : Z) : environ -> mpred :=
  EX tr : list zev,
  PROP (fst (cnt tr) = 0; code <> -4 \/ cnt_failed tr = 1)
  LOCAL (temp _code (Vint (Int.repr code)); lvar _strm (Tstruct _z_stream_s noattr) sp;
         lvar _count__1 (Tstruct _count noattr) cp)
  SEP (@data_at_ CSa Tsh (Tstruct HL._z_stream_s noattr) sp; count_res cp gv tr; TT).

Lemma body_main : za_deflate_model_stmt -> za_dstream_end_stmt -> za_deflate_bodies_stmt -> main_free_stmt.
Proof.
  intros MODEL HEND HB. unfold main_free_stmt.
  start_function.
  forward_call tt. Intros lv.
  forward_call tt. Intros wb.
  forward_call tt. Intros ml.
  forward_call tt. Intros st.
  call_alone. forward_call tt. Intros n. forward. rewrite Int.unsigned_repr by rep_lia.
  call_alone. forward_call tt. Intros room. forward. rewrite Int.unsigned_repr by rep_lia.
  call_alone. forward_call (n, gv). Intros vret. destruct vret as [dp bs]. cbn [fst snd] in *. forward.
  call_alone. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros op. forward.
  destruct (eq_dec dp nullval) as [Ed | Nd].
  { subst dp. ifpost _t'9 (Int.repr 1).
    { forward. entailer!. }
    { contradiction. }
    forward_if.
    { ret0. }
    { discriminate. } }
  Intros.
  destruct (eq_dec op nullval) as [Eo | No].
  { subst op. ifpost _t'9 (Int.repr 1).
    { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
      sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { ret0. }
    { discriminate. } }
  Intros.
  ifpost _t'9 (Int.repr 0).
  { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
  { forward. entailer!. }
  { forward. entailer!. destruct op; try contradiction. reflexivity. }
  forward_if.
  { exfalso; lia. }
  rewrite strm_local, count_local_.
  forward_call (v_strm, Tsh, v_count__1, gv, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef, Vundef, Vundef).
  match goal with |- context [@data_at _ Tsh t_zs ?v v_strm] =>
    sep_apply (@data_at_Tsh_split Zlib.units.Compress.CS t_zs v v_strm) end.
  sep_apply zs_init_pre.
  make_func_ptr HC._counted_alloc. make_func_ptr HC._counted_free.
  match goal with |- context [func_ptr' ?f (gv HC._counted_alloc)] =>
    change (func_ptr' f (gv HC._counted_alloc)) with (func_ptr' (snd count_alloc_spec) (gv HC._counted_alloc)) end.
  match goal with |- context [func_ptr' ?f (gv HC._counted_free)] =>
    change (func_ptr' f (gv HC._counted_free)) with (func_ptr' (snd count_free_spec) (gv HC._counted_free)) end.
  assert_PROP (isptr (gv HC._counted_alloc)) as Pza.
  { sep_apply (func_ptr'_isptr (snd count_alloc_spec) (gv HC._counted_alloc)). entailer!. }
  assert_PROP (isptr (gv HC._counted_free)) as Pzf.
  { sep_apply (func_ptr'_isptr (snd count_free_spec) (gv HC._counted_free)). entailer!. }
  sep_apply (counted_pieces v_count__1 (gv HC._counted_alloc) (gv HC._counted_free) gv).
  unfold Ra, version_at. Intros.
  rewrite (vint_signed lv), (vint_signed wb), (vint_signed ml), (vint_signed st).
  pose proof (Int.signed_range (Int.repr lv)). pose proof (Int.signed_range (Int.repr wb)).
  pose proof (Int.signed_range (Int.repr ml)). pose proof (Int.signed_range (Int.repr st)).
  set (level := Int.signed (Int.repr lv)) in *. set (wbits := Int.signed (Int.repr wb)) in *.
  set (mem := Int.signed (Int.repr ml)) in *. set (strategy := Int.signed (Int.repr st)) in *.
  clearbody level wbits mem strategy. clear lv wb ml st H H0 H1 H2.
  assert_PROP (isptr v_count__1) as Pcp by entailer!.
  change (counted v_count__1 (gv HC._counted_alloc) (gv HC._counted_free))
    with (kc (v_count__1, gv HC._counted_alloc, gv HC._counted_free)).
  forward_call ((v_count__1, gv HC._counted_alloc, gv HC._counted_free),
    (v_strm, level, 8, wbits, mem, strategy, gv ___stringlit_res_free_deflate_1, Ers, [49; 46; 51; 46; 50; 0], 112,
     nullval, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, gv, @nil zev)).
  { split; [unfold s32_ok; rep_lia | ]. split; [unfold s32_ok; rep_lia | ].
    split; [rewrite Zlength_correct; simpl; lia | ].
    split; [cbn; lia | ]. split; [intros; apply init_total | ].
    cbn. repeat split;
      first [ intro E; rewrite E in Pza; contradiction | intro E; rewrite E in Pzf; contradiction
            | apply isptr_is_pointer_or_null; auto | lia ]. }
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] [[os z1] code]] tr]. cbn [fst snd] in *.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in *. change (112 =? 112) with true in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  pose proof (init_code_range _ _ _ _ _ _ _ _ _ _ _ _ HI) as Hcr. cbn [snd] in Hcr.
  forward_if (J2 v_strm v_count__1 gv code).
  { (* deflateInit2_ returned Z_OK: offer, deflate, deflateEnd *)
    destruct os as [s | ].
    2:{ exfalso. apply (init_none_code _ _ _ _ _ _ _ _ _ _ _ _ HI eq_refl). assumption. }
    destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Ecode & Pok & HIt & Hgz & Hz1).
    subst code. destruct Hz1 as (T1 & T2 & T3 & T4).
    Intros msgv'.
    unfold rfv in *. rewrite T3 in *.
    match goal with Hm : (if _ =? Z_VERSION_ERROR then _ else _) |- _ => cbn in Hm; subst msgv' end.
    replace (if 0 =? Z_OK then vl (z_total_in z1) else Vundef) with (vl (z_total_in z1)) by reflexivity.
    replace (if 0 =? Z_OK then vl (z_total_out z1) else Vundef) with (vl (z_total_out z1)) by reflexivity.
    replace (if 0 =? Z_OK then vl (z_adler z1) else Vundef) with (vl (z_adler z1)) by reflexivity.
    set (c := (v_count__1, gv HC._counted_alloc, gv HC._counted_free)).
    sep_apply (@dstream_za_open (kc c) s v_strm nullval gv). Intros spp.
    sep_apply (@offer_pre (kc c) v_strm nullval (Vint (Int.repr 0)) (vl (z_total_in z1)) nullval (Vint (Int.repr 0))
                 (vl (z_total_out z1)) (Vlong Int64.zero) spp (vi (tr_data_type (d_tr s))) (vl (z_adler z1))).
    forward_call (v_strm, Ews, dp, n, op, room, nullval, Vint (Int.repr 0), vl (z_total_in z1), nullval,
                  Vint (Int.repr 0), vl (z_total_out z1), Vlong Int64.zero, spp, @za_alloc (kc c), @za_free (kc c),
                  @za_opaque (kc c), vi (tr_data_type (d_tr s)), vl (z_adler z1), Vundef).
    sep_apply (@offer_post (kc c)).
    sep_apply (wand_frame_elim (@strm_live (kc c) v_strm spp (vi (tr_data_type (d_tr s))))
                               (@dstream_sp_za (kc c) 2 (Some s) v_strm nullval spp gv)).
    subst n.
    assert_PROP (isptr dp) as Pdp.
    { entailer. apply prop_right.
      match goal with H : field_compatible (Tarray tuchar _ _) [] dp |- _ => destruct H; auto end. }
    assert (U : u32_ok (Zlength bs) /\ u64_ok (z_total_in z1) /\ u32_ok room /\ u64_ok (z_total_out z1) /\
                u64_ok (z_adler z1)) by (rewrite T1, T2; unfold u32_ok, u64_ok; rep_lia).
    destruct U as (U1 & U2 & U3 & U4 & U5).
    sep_apply (api_fold v_strm dp (Zlength bs) (z_total_in z1) op room (z_total_out z1) (Vlong Int64.zero)
                 (z_adler z1) Pdp U1 U2 U3 U4 U5).
    rewrite (data_at_tuchar_cs Zlib.units.Adler32.CS DCS.CS Ews (Zlength bs) (bytes_rep bs) dp).
    sep_apply (out_split room op ltac:(lia)).
    Intros.
    forward_call tt. Intros fl.
    rewrite (vint_signed fl).
    pose proof (Int.signed_range (Int.repr fl)) as Hfl.
    set (flush := Int.signed (Int.repr fl)) in *. clearbody flush.
    assert (Hm : exists r, c_deflate s (zmk bs 0 (Zlength bs) (z_total_in z1) room (z_total_out z1) (z_adler z1)
                                             (z_msg z1)) flush = Some r).
    { apply (MODEL level 8 wbits mem strategy s z1 bs room flush); try (unfold s32_ok; rep_lia); auto.
      eapply Forall_impl; [ | exact H6]. intros b Hb; simpl in Hb; rep_lia. }
    destruct Hm as [r Hr].
    forward_call (c, (Some s, v_strm, nullval, spp, (Ews, nullval, nullval, nullval), dp, Ews, bs, 0, Zlength bs,
                      z_total_in z1, op, Zrepeat Vundef room, out_wv room, z_total_out z1, Vlong Int64.zero,
                      @None Z, z_adler z1, flush, (Some (fst (fst r)), snd (fst r), snd r), gv)).
    { replace (Zlength (Zrepeat Vundef room)) with room by list_solve.
      unfold hdr_at. rewrite Hgz. rewrite prop_true_andp by auto. subst c. cbn [fst snd]. cancel. }
    { replace (Zlength (Zrepeat Vundef room)) with room by list_solve.
      split; [intros E; apply out_wv_ok; exact E | ].
      split.
      - unfold strm_ranges, zmk. cbn. rewrite T1, T2 in *. unfold u32_ok, u64_ok in *.
        repeat split; try rep_lia.
        + eapply Forall_impl; [ | exact H6]. intros b Hb; simpl in Hb; rep_lia.
        + constructor.
      - exists (fun f => f). split; [apply ef_ok_id | ].
        unfold on_state, c_on_state. rewrite c_deflate_g_id. rewrite T3 in Hr. rewrite Hr.
        destruct r as [[s' z'] code']. reflexivity. }
    Intros msgv2.
    cbn [fst snd] in *.
    destruct r as [[s' z'] code']. cbn [fst snd] in *.
    assert (HR : strm_ranges (zmk bs 0 (Zlength bs) (z_total_in z1) room (z_total_out z1) (z_adler z1) (z_msg z1))).
    { unfold strm_ranges, zmk. cbn. rewrite T1, T2 in *. unfold u32_ok, u64_ok in *.
      repeat split; try rep_lia.
      + eapply Forall_impl; [ | exact H6]. intros b Hb; simpl in Hb; rep_lia.
      + constructor. }
    pose proof (c_deflate_dkeep _ _ _ _ _ _ HR Hr) as HK.
    pose proof (c_deflate_status_ok _ _ _ _ _ _ HR (init_status _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) Hr) as HS.
    destruct (init_sizes _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Pok' & Sw & Sh & Sl).
    destruct (Zlib.proof.deflate.LTCInitKit.params_bounds _ _ _ _ _ Pok') as (_ & _ & _ & Bm & _).
    destruct HK as (Kg & Kw & Kh & Kl & Kd).
    assert (P1 : 0 < d_w_size s') by (rewrite Kw, Sw; apply Z.pow_pos_nonneg; lia).
    assert (P2 : 0 < d_hash_size s') by (rewrite Kh, Sh; apply Z.pow_pos_nonneg; lia).
    assert (P3 : 0 < tr_lit_bufsize (d_tr s')) by (rewrite Kl, Sl; apply Z.pow_pos_nonneg; lia).
    sep_apply (@end_pre (kc c) s' v_strm spp gv HEND P1 P2 P3). Intros p.
    sep_apply api_fields_split.
    forward_call (c, (Some s', p, v_strm, offset_val (z_next_in z') dp, z',
                      (@None dstate, z', if d_status s' =? BUSY_STATE then Z_DATA_ERROR else Z_OK), gv, tr)).
    { subst c; cbn [fst snd]. cancel. }
    { unfold c_deflateEnd, bad_state, c_deflateStateCheck. rewrite HS. reflexivity. }
    Intros tr2. cbn [fst snd] in *.
    unfold J2. Exists tr2.
    sep_apply (@closed_back (kc c)). sep_apply strm_back.
    match goal with |- context [@za_res ?Z gv tr2] => change (@za_res Z gv tr2) with (count_res v_count__1 gv tr2) end.
    entailer!.
    repeat match goal with H : ?t = _ |- _ => is_var t; subst t end.
    apply (@free_count (kc c) s s' p (conj Kg (conj Kw (conj Kh (conj Kl Kd))))); tauto. }
  { (* deflateInit2_ failed *)
    destruct os as [s | ].
    { exfalso. destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI) as (Ecode & _). subst code. auto. }
    pose proof (init_none_code _ _ _ _ _ _ _ _ _ _ _ _ HI eq_refl) as Hc. cbn [fst snd] in Hc.
    Intros st dt' msgv'.
    destruct H0 as [Hnow Hfail].
    forward. unfold J2. Exists tr.
    sep_apply (@init_fail_back (kc (v_count__1, gv HC._counted_alloc, gv HC._counted_free))).
    sep_apply strm_back.
    change (@za_res (kc (v_count__1, gv HC._counted_alloc, gv HC._counted_free)) gv tr)
      with (count_res v_count__1 gv tr).
    entailer!.
    split.
    + rewrite cnt_now_mod, Hnow. reflexivity.
    + destruct (Z.eq_dec code (-4)) as [E | E]; [right | left; exact E].
      unfold cnt_failed. rewrite (Hfail E). reflexivity. }
  (* the checks code != Z_MEM_ERROR || count.failed and count.now == 0, and the return *)
  unfold J2. Intros tr0. unfold count_res. rewrite count_local. Intros.
  freeze FR := (data_at_ _ _ v_strm) (mem_mgr gv) TT.
  forward_if (PROP () LOCAL (temp _t'12 (Vint Int.one); lvar _strm (Tstruct _z_stream_s noattr) v_strm;
                             lvar _count__1 (Tstruct _count noattr) v_count__1)
              SEP (FRZL FR; @data_at CSa Tsh (Tstruct HC._count noattr)
                     (Vlong (Int64.repr (fst (cnt tr0))),
                      (Vlong (Int64.repr (snd (cnt tr0))), Vint (Int.repr (cnt_failed tr0)))) v_count__1)).
  { forward. entailer!. }
  { forward. forward. entailer!.
    apply repr_inj_signed in H2; [ | rep_lia | rep_lia].
    destruct H1 as [H1 | H1]; [contradiction | ]. rewrite H1. reflexivity. }
  forward_call (Int.one).
  forward.
  forward_call (Int.repr 1).
  { apply prop_right. match goal with H : fst (cnt tr0) = 0 |- _ => rewrite H end. reflexivity. }
  forward. Exists (Int.repr 0). thaw FR. entailer!.
Qed.

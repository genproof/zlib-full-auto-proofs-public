(* Law res_free_inflate: main of harness/res_free_inflate.c against main_core_spec at the law's compspecs. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.res_inflate.ResICS Zlib.proof.harness.res_inflate.ResISpecs
               Zlib.proof.harness.res_inflate.ResIKit Zlib.proof.harness.res_inflate.ResITheory.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Import Zlib.proof.harness.res_inflate.ResIFreeKit.
Require Import Zlib.harness.res_free_inflate.code.
Local Open Scope logic.

(* after `if (code == Z_OK) { .. }`: main's z_stream is again its uninitialised local, the counting
   allocator's events [tr] leave count.now = 0, and the result code (of inflateInit2_, or of inflate() when
   inflateInit2_ returned Z_OK) is Z_MEM_ERROR only when an allocation of the counting allocator failed *)
Definition Jc (sp cp : val) (gv : globals) : environ -> mpred :=
  EX tr : list zev, EX code : Z,
  PROP (fst (cnt tr) = 0; Int.min_signed <= code <= Int.max_signed; code = -4 -> za_failed tr = true)
  LOCAL (temp _code (Vint (Int.repr code)); lvar _strm tzs sp; lvar _count__1 tcount cp; gvars gv)
  SEP (@data_at_ CSi Tsh tzs sp; count_res cp gv tr; TT).

Lemma body_main_free : res_model_stmt -> main_free_stmt.
Proof.
  intros MODEL. unfold main_free_stmt.
  start_function.
  unfold Ri. Intros.
  forward_call tt. Intros wb.
  call_alone. forward_call tt. Intros n. forward. rewrite Int.unsigned_repr by rep_lia.
  call_alone. forward_call tt. Intros room. forward. rewrite Int.unsigned_repr by rep_lia.
  call_alone. forward_call (n, gv). Intros vret. destruct vret as [dp bs]. cbn [fst snd] in *. forward.
  call_alone. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros op. forward.
  destruct (eq_dec dp nullval) as [Ed | Nd].
  { subst dp. ifpost _t'6 (Int.repr 1).
    { forward. entailer!. }
    { contradiction. }
    forward_if.
    { ret0. }
    { discriminate. } }
  Intros.
  destruct (eq_dec op nullval) as [Eo | No].
  { subst op. ifpost _t'6 (Int.repr 1).
    { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
      sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
    { forward. entailer!. }
    { forward. entailer!. }
    forward_if.
    { ret0. }
    { discriminate. } }
  Intros.
  ifpost _t'6 (Int.repr 0).
  { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
  { forward. entailer!. }
  { forward. entailer!. destruct op; try contradiction. reflexivity. }
  forward_if.
  { exfalso; lia. }
  change (Tstruct _z_stream_s noattr) with tzs. change (Tstruct _count noattr) with tcount.
  rewrite strm_local, count_local_.
  forward_call (v_strm, Tsh, v_count__1, gv, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef, Vundef, Vundef).
  make_func_ptr HC._counted_alloc. make_func_ptr HC._counted_free.
  match goal with |- context [func_ptr' ?f (gv HC._counted_alloc)] =>
    change (func_ptr' f (gv HC._counted_alloc)) with (func_ptr' (snd count_alloc_spec) (gv HC._counted_alloc)) end.
  match goal with |- context [func_ptr' ?f (gv HC._counted_free)] =>
    change (func_ptr' f (gv HC._counted_free)) with (func_ptr' (snd count_free_spec) (gv HC._counted_free)) end.
  assert_PROP (isptr (gv HC._counted_alloc)) as Pza.
  { sep_apply (func_ptr'_isptr (snd count_alloc_spec) (gv HC._counted_alloc)). entailer!. }
  assert_PROP (isptr (gv HC._counted_free)) as Pzf.
  { sep_apply (func_ptr'_isptr (snd count_free_spec) (gv HC._counted_free)). entailer!. }
  assert_PROP (isptr v_count__1) as Pcp by entailer!.
  assert_PROP (isptr v_strm) as Ps by entailer!.
  sep_apply (counted_pieces v_count__1 (gv HC._counted_alloc) (gv HC._counted_free) gv).
  rewrite (zs_raw gv).
  rewrite (vint_signed wb). pose proof (Int.signed_range (Int.repr wb)) as Hw.
  set (w := Int.signed (Int.repr wb)) in *. clearbody w.
  assert_PROP (isptr (gv ___stringlit_res_free_inflate_1)) as Pver by (unfold hversion_lit; entailer!).
  unfold hversion_lit.
  set (cp := v_count__1). set (za := gv HC._counted_alloc). set (zf := gv HC._counted_free).
  change (counted cp za zf) with (zai_a Ac (ix cp za zf false)).
  change (count_res cp gv []) with (@za_res (zai_a Ac (ix cp za zf false)) gv []).
  forward_call (ix cp za zf false,
                (gv, Tsh, v_strm,
                 RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef,
                 Vundef, Vundef, w, gv ___stringlit_res_free_inflate_1, Ers, hver_vals, 49, 112, @nil zev)).
  { rewrite if_false by (destruct v_strm; try contradiction; discriminate). unfold zfuncs_za.
    simpl za_alloc. simpl za_free. simpl za_opaque. cancel. }
  { split; [unfold hver_vals; cbn; rep_lia | simpl za_cap; unfold ZEvents.state_size; rep_lia]. }
  Intros vret. destruct vret as [alloc_ok sp]. cbn [fst snd] in *.
  assert (Hret : init_ret v_strm 49 112 w alloc_ok = if alloc_ok then (if wbits_ok w then 0 else -2) else -4).
  { unfold init_ret. simpl. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    destruct alloc_ok; reflexivity. }
  rewrite Hret.
  destruct (eq_dec v_strm nullval) as [Esn | _]; [subst v_strm; contradiction | ].
  forward_if (Jc v_strm cp gv).
  { (* inflateInit2_ returned Z_OK *)
    destruct alloc_ok; [ | discriminate]. destruct (wbits_ok w) eqn:Hwb; [ | discriminate].
    unfold init_mem_za. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    simpl Z.eqb. cbv iota beta.
    change (RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef) with raw0.
    match goal with |- context [@istream_raw_za ?Z gv Tsh v_strm ?r ?L] =>
      change (@istream_raw_za Z gv Tsh v_strm r L) with (@istream_raw_za (counted cp za zf) gv Tsh v_strm r L) end.
    sep_apply (init_offer_pre gv cp za zf sp w v_strm). Intros. rename H7 into HL.
    forward_call (v_strm, Tsh, dp, n, op, room, nullval, Vint (Int.repr 0), Vlong (Int64.repr 0), nullval,
                  Vint (Int.repr 0), Vlong (Int64.repr 0), nullval, sp, za, zf, cp, Vint (Int.repr 0),
                  @adler_val (init_cell w) (init_adler w), Vundef).
    sep_apply (offer_istream gv cp za zf sp w v_strm dp n op room ltac:(rep_lia) ltac:(rep_lia) HL).
    replace ([] ++ ZEvents.init_ev false 49 112 w true) with [ZAlloc ZEvents.state_size]
      by (unfold ZEvents.init_ev; rewrite Hwb; reflexivity).
    assert_PROP (isptr dp /\ isptr op) as Pdo.
    { entailer. apply prop_right. match goal with H : field_compatible _ [] dp |- _ => exact (proj1 H) end. }
    destruct Pdo as [Pdp Pop].
    sep_apply (bufs_pre (init_live sp w) dp n bs op room H2 ltac:(lia)).
    forward_call tt. Intros fl.
    rewrite (vint_signed fl). pose proof (Int.signed_range (Int.repr fl)) as Hfl.
    set (flush := Int.signed (Int.repr fl)) in *. clearbody flush.
    forward_call (ix cp za zf (init_wrap w =? 0),
                  (gv, Tsh, v_strm, zinit dp n op room w, Some (init_live sp w), ibuf dp n bs, bs,
                   Some (obuf op room), flush, Ers, Ers, true, true, [ZAlloc ZEvents.state_size])).
    { unfold istream_opt_za, is_live. rewrite !if_false by (destruct v_strm; try contradiction; discriminate).
      unfold head_opt, head_mem. rewrite init_head.
      cbn [zai_a zai_v ix Ac fst snd]. unfold init_cell. cancel. }
    { unfold zinit, ibuf, obuf, in_ok, out_ok, in_ptr, out_ptr. cbn [zf_ni zf_ai zf_no zf_ao].
      rewrite !Z.add_0_r, !isptr_offset_val_zero by auto.
      split; [reflexivity | ]. split.
      { split; [ | lia]. unfold bytes_rep. rewrite Zlength_map.
        repeat split; auto; try lia; try apply readable_Ews; try rep_lia.
        rewrite Z.add_0_l, sublist_same by (rewrite ?Zlength_map; lia). reflexivity. }
      split; [split; [reflexivity | ] | ].
      { repeat split; auto; try lia; try apply writable_Ews; try rep_lia.
        rewrite Zlength_Zrepeat; lia. }
      split; [apply init_swfW | ].
      simpl za_cap. unfold za_now, za_count, ZEvents.state_size. simpl. rep_lia. }
    Intros vret. destruct vret as [[[r z'] st'] ow]. cbn [fst snd] in *.
    match goal with H : inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HR end.
    assert (Hsn : v_strm <> nullval) by (destruct v_strm; try contradiction; discriminate).
    assert (Hib : ibuf dp n bs <> InNull) by (unfold ibuf; discriminate).
    destruct (inflate_rel_ret _ _ _ _ _ _ _ _ _ _ _ Hsn Hib HR) as (res & winp & Est & Hrun & Er & Hr).
    set (L' := Live (l_sp (init_live sp w)) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp (init_live sp w))
                    (l_hsh (init_live sp w)) (l_xb (init_live sp w)) (l_nb (init_live sp w))
                    (l_cb (init_live sp w))) in Est.
    subst st'.
    forward.
    forward_call (ix cp za zf (init_wrap w =? 0),
                  (gv, Tsh, v_strm, z', Some L',
                   [ZAlloc ZEvents.state_size] ++ ZEvents.win_ev (l_s (init_live sp w)) (l_s L'))).
    unfold Jc, istream_opt_za, is_live. rewrite !if_false by exact Hsn.
    Exists (([ZAlloc ZEvents.state_size] ++ ZEvents.win_ev (l_s (init_live sp w)) (l_s L')) ++
            ZEvents.end_ev (l_s L')) r.
    match goal with |- context [@istream_za ?Z ?V gv Tsh v_strm z' None] =>
      sep_apply (@closed_local Z V gv Tsh v_strm z') end.
    match goal with |- context [@za_res ?Z gv ?t] => change (@za_res Z gv t) with (count_res cp gv t) end.
    entailer!.
    split; [rewrite <- app_assoc; apply free_count, init_win | ].
    intros E.
    pose proof (call_mem_failed sp w flush (zinit dp (Zlength bs) op room w) bs res MODEL Hwb HL
                  (zinit_ok dp (Zlength bs) op room w H0 H1) H3 ltac:(rep_lia) Hrun E) as K.
    exact K. }
  { (* inflateInit2_ failed: the stream is a raw_strm again, and the state (if allocated) was freed *)
    assert (Hev : ZEvents.init_ev false 49 112 w alloc_ok <> [ZAlloc ZEvents.state_size]).
    { unfold ZEvents.init_ev. simpl. destruct alloc_ok, (wbits_ok w); simpl in *; try discriminate.
      exfalso. match goal with H : Int.repr 0 <> Int.repr 0 |- _ => apply H; reflexivity end. }
    assert (Hr : (if alloc_ok then if wbits_ok w then 0 else -2 else -4) <> 0).
    { destruct alloc_ok, (wbits_ok w); try discriminate.
      exfalso. match goal with H : Int.repr 0 <> Int.repr 0 |- _ => apply H; reflexivity end. }
    forward. unfold Jc. Exists ([] ++ ZEvents.init_ev false 49 112 w alloc_ok)
                              (if alloc_ok then if wbits_ok w then 0 else -2 else -4).
    unfold init_mem_za. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    match goal with |- context [@za_res ?Z gv ?t] => change (@za_res Z gv t) with (count_res cp gv t) end.
    destruct alloc_ok, (wbits_ok w); try (exfalso; apply Hr; reflexivity); simpl Z.eqb; cbv iota beta;
      sep_apply raw_undef; entailer!;
      repeat match goal with |- _ /\ _ => split end;
      first [apply init_fail_count; exact Hev | intros; reflexivity | rep_lia]. }
  (* the two checks: code != Z_MEM_ERROR || count.failed, and count.now == 0; and the return *)
  unfold Jc. Intros tr0 code. unfold count_res. rewrite count_local. Intros.
  freeze FR := (data_at_ _ _ v_strm) (mem_mgr gv) TT.
  forward_if (temp _t'10 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { (* code is Z_MEM_ERROR: an allocation failed, count.failed is 1 *)
    forward. forward. entailer!.
    match goal with E : Int.repr code = Int.repr _, F : code = -4 -> _ |- _ =>
      apply repr_inj_signed in E; [unfold cnt_failed; rewrite (F E); reflexivity | rep_lia | rep_lia] end. }
  forward_call (Int.repr 1).
  forward.
  forward_call (Int.repr 1).
  { apply prop_right. match goal with H : fst (cnt tr0) = 0 |- _ => rewrite H end. reflexivity. }
  forward. Exists (Int.repr 0). thaw FR. entailer!.
Qed.

(* The main of harness/inflate_buffers.c, proved against MainLib.main_core_spec R (IBGlobals.v) for ANY proofs of the
   facts of IBFacts.v (ib_facts), calling inflate.c's API through its shared specifications (inflate_api/Spec5.v, at
   the inflate unit's compspecs: moved to the law's with IBLawCS's instances) and the harness helpers through theirs
   (inflate_common/HarnessLib.v, adler32/HarnessBytes.v), as harness/inflate_codes/Main*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_buffers.IBMainKit Zlib.proof.harness.inflate_buffers.IBMainHelp
  Zlib.proof.harness.inflate_buffers.IBMainOps Zlib.proof.harness.inflate_buffers.IBMainChecks
  Zlib.proof.harness.inflate_buffers.IBMainLoop.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateSync_spec; inflateGetDictionary_spec; inflateSetDictionary_spec;
   inflatePrime_spec; inflateReset_spec; inflateReset2_spec; inflateValidate_spec; inflateMark_spec;
   inflateCodesUsed_spec; inflateSyncPoint_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   bytes_same_spec; bytes_copy_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

(* an if whose branches end in the state before it (the guard r != Z_MEM_ERROR of the windowBits assertion) *)
Ltac ifkeep := match goal with |- semax _ ?P _ _ => forward_if P end.

(* r != Z_OK after inflateInit2_: free(src); return 0 *)
Ltac ret_init src srcp gv :=
  forward_call (tarray tuchar (Zlength src), srcp, gv);
  [ rewrite if_false by auto; sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))); cancel | ];
  forward; Exists (Int.repr 0);
  unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl;
  unfold raw_strm; sep_apply strm_to_undef; entailer!.

Lemma body_main : ib_facts -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros FI. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros wb.
  forward_call tt. Intros n.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  forward_call (Int.repr (if n <=? 2^24 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 24)) with (Int.repr (2 ^ 24)). arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros srcp.
  destruct (eq_dec srcp nullval) as [PS|PS].
  { subst srcp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward_call (srcp, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros src. rewrite if_false by auto.
  match goal with H: Zlength src = n |- _ => rename H into Hsrcn end.
  match goal with H: Forall _ src |- _ => rename H into Hsrcb end.
  subst n. fold (bytes_rep src).
  assert_PROP (isptr v_s) as Ps by entailer!.
  rewrite strm_undef_cs.
  forward_call (v_s, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  set (rr := RF nullval (Vint (Int.repr 0)) (Vlong (Int64.repr tin)) nullval (Vint (Int.repr 0))
               (Vlong (Int64.repr tout)) (Vint (Int.repr dt)) (Vlong (Int64.repr adl)) (Vlong (Int64.repr rs))).
  match goal with |- context [@data_at ?cs Tsh Rep.t_strm ?v v_s] =>
    replace (@data_at cs Tsh Rep.t_strm v v_s) with (raw_strm gv Tsh v_s rr Vundef Vundef nullval nullval nullval)
      by reflexivity end.
  unfold hversion_lit.
  change (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0]) with hver_vals.
  change (tarray tschar 6) with (tarray tschar (Zlength hver_vals)).
  rewrite <- tschar_cs.
  assert_PROP (isptr (gv ___stringlit_x_inflate_buffers_1)) as Pver by entailer!.
  forward_call (gv, Tsh, v_s, rr, Vundef, Vundef, nullval, w, gv ___stringlit_x_inflate_buffers_1, Ers,
                hver_vals, 49, 112).
  { destruct (eq_dec v_s nullval) as [X|_]; [subst; contradiction | ]. cancel. }
  { unfold hver_vals; repeat split; auto with share; try rep_lia; try reflexivity; rewrite Zlength_map; change (Zlength [49; 46; 51; 46; 50; 0]) with 6; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  rewrite init_ret_ib by auto.
  destruct alloc_ok; [destruct (wbits_ok w) eqn:Wok | destruct (wbits_ok w) eqn:Wok]; cbn [negb].
  - (* Z_OK *)
    ifpost _t'5 (Int.repr 1). { forward. entailer!. } { infeas. }
    ifpost _t'6 (Int.repr 1). { forward. entailer!. } { infeas. }
    gpa.
    ifkeep. { forward_call w. rewrite Wok. gpa. entailer!. } { infeas. }
    forward_if. { infeas. }
    unfold init_mem. destruct (eq_dec v_s nullval) as [X|_]; [subst; contradiction | ].
    remember (init_live sp w) as L0 eqn:HL0. simpl.
    replace (istream_raw gv Tsh v_s (raw_after_init rr (l_s L0)) L0)
      with (istream gv Tsh v_s (z_init adl rs L0) (Some L0)) by (symmetry; apply init_istream; auto).
    assert (HI0: ib_inv L0) by (subst L0; apply (fi_init FI); auto).
    rewrite ib_istream_unfold. Intros.
    forward.
    ifpost _t'8 (Int.repr 1).
    { forward. forward. entailer!. }
    { infeas. }
    gpa.
    sep_apply (ib_istream_fold gv Tsh v_s (z_init adl rs L0) L0); auto.
    forward. forward.
    assert_PROP (isptr srcp) as Psrc by entailer!.
    set (Fr := (data_at Ers (tarray tschar (Zlength hver_vals)) hver_vals (gv ___stringlit_x_inflate_buffers_1) *
                version_lit gv * msg_lits gv)%logic).
    forward_loop (ib_loop_inv gv v_s v_osnap v_dl srcp src Fr)
      break: (ib_loop_inv gv v_s v_osnap v_dl srcp src Fr).
    { unfold ib_loop_inv. Exists 0 (z_init adl rs L0) L0. unfold Fr. entailer!. }
    { unfold ib_loop_inv at 1. Intros pos z L.
      unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
      apply (proj1 (semax_seq_skip _ _ _ _)).
      eapply semax_pre; [ | apply (seg_loop_ok gv v_s v_osnap v_dl srcp src Fr pos z L); auto ].
      - entailer!.
      - exact (@seg_ops_ok Espec).
      - exact (@seg_checks_ok Espec). }
    unfold ib_loop_inv. Intros pos z L.
    forward_call (gv, Tsh, v_s, z, Some L).
    { rewrite ib_istream_opt by auto. cancel. }
    rewrite ib_istream_opt, ib_is_live by auto.
    gpa.
    forward_call (tarray tuchar (Zlength src), srcp, gv).
    { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength src))). cancel. }
    forward. Exists (Int.repr 0).
    sep_apply istream_to_undef. entailer!.
  - (* Z_STREAM_ERROR *)
    ifpost _t'5 (Int.repr 1). { infeas. } { forward. entailer!. }
    ifpost _t'6 (Int.repr 1). { forward. entailer!. } { infeas. }
    gpa.
    ifkeep. { forward_call w. rewrite Wok. gpa. entailer!. } { infeas. }
    forward_if. { ret_init src srcp gv. } { infeas. }
  - (* Z_MEM_ERROR, windowBits accepted *)
    ifpost _t'5 (Int.repr 0). { infeas. } { forward. entailer!. }
    ifpost _t'6 (Int.repr 1). { infeas. } { forward. entailer!. }
    gpa.
    ifkeep. { infeas. } { forward. entailer!. }
    forward_if. { ret_init src srcp gv. } { infeas. }
  - (* Z_MEM_ERROR, windowBits rejected: the harness states the Z_STREAM_ERROR condition only when r != Z_MEM_ERROR *)
    ifpost _t'5 (Int.repr 0). { infeas. } { forward. entailer!. }
    ifpost _t'6 (Int.repr 1). { infeas. } { forward. entailer!. }
    gpa.
    ifkeep. { infeas. } { forward. entailer!. }
    forward_if. { ret_init src srcp gv. } { infeas. }
Qed.

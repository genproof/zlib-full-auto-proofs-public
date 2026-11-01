(* Law inflate_reset, main: the whole body from the loop's statement (loop_stmt, IRMainLoop.v): the draws of
   wbits and n, src, stream_defaults(&a), stream_defaults(&b), inflateInit2(&a, wbits) (IRFacts.rf_init), the
   loop (forward_loop with IRMainKit.loop_inv, break: brk_inv) and the tail (inflateEnd(&a), inflateEnd(&b),
   return 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts Zlib.proof.harness.inflate_reset.IRMainKit.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.

Definition ir_hver_vals : list val := map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0].

Lemma ir_hver_cs gv:
  ir_hversion_lit gv =
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ir_hver_vals)) ir_hver_vals
    (gv ___stringlit_x_inflate_reset_1).
Proof.
  unfold ir_hversion_lit. symmetry.
  apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

Lemma ir_hver_to gv:
  ir_hversion_lit gv |--
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ir_hver_vals)) ir_hver_vals
    (gv ___stringlit_x_inflate_reset_1).
Proof. rewrite ir_hver_cs. apply derives_refl. Qed.

Lemma ir_hver_back gv:
  @data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ir_hver_vals)) ir_hver_vals
    (gv ___stringlit_x_inflate_reset_1) |-- ir_hversion_lit gv.
Proof. rewrite ir_hver_cs. apply derives_refl. Qed.

Ltac top_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Ltac top_gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma main_of : loop_stmt -> forall I1 I2, reset_facts I1 I2 ->
  semax_body (QPvarspecs p) Gmain_k f_main (_main, main_core_spec R).
Proof.
  intros LS I1 I2 RF.
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
  change (Tstruct _z_stream_s noattr) with t_z.
  rewrite (strm_undef_cs Tsh v_a), (strm_undef_cs Tsh v_b).
  forward_call (v_a, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tina touta] adla] dta] rsa]. simpl fst in *. simpl snd in *.
  forward_call (v_b, Tsh, Vundef, Vundef).
  Intros vv. destruct vv as [[[[tin tout] adl] dt] rs]. simpl fst in *. simpl snd in *.
  set (ra0 := rb_of tina touta adla dta rsa).
  match goal with |- context [@data_at ?cs Tsh t_strm ?v v_a] =>
    replace (@data_at cs Tsh t_strm v v_a) with (raw_strm gv Tsh v_a ra0 Vundef Vundef nullval nullval nullval)
      by reflexivity end.
  set (rb := rb_of tin tout adl dt rs).
  match goal with |- context [@data_at ?cs Tsh t_strm ?v v_b] =>
    replace (@data_at cs Tsh t_strm v v_b) with (braw gv v_b rb) by reflexivity end.
  assert_PROP (isptr (gv ___stringlit_x_inflate_reset_1)) as Pver by (unfold ir_hversion_lit; entailer!).
  replace_SEP 11 (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength ir_hver_vals)) ir_hver_vals
    (gv ___stringlit_x_inflate_reset_1)).
  { go_lower. apply ir_hver_to. }
  assert_PROP (isptr v_a) as Pa by entailer!.
  assert_PROP (isptr v_b) as Pb by (unfold braw, raw_strm; entailer!).
  forward_call (gv, Tsh, v_a, ra0, Vundef, Vundef, nullval, w, gv ___stringlit_x_inflate_reset_1,
                Ers, ir_hver_vals, 49, 112).
  { rewrite if_false by (destruct v_a; try contradiction; discriminate). cancel. }
  { repeat split; auto; try rep_lia; try reflexivity; try discriminate. }
  Intros vret. destruct vret as [alloc_ok sp]. simpl fst in *. simpl snd in *.
  replace_SEP 1 (ir_hversion_lit gv).
  { go_lower. apply ir_hver_back. }
  set (ret := init_ret v_a 49 112 w alloc_ok) in *.
  assert (Hret: ret = if alloc_ok then (if wbits_ok w then 0 else -2) else -4).
  { subst ret. unfold init_ret. simpl. rewrite if_false by (destruct v_a; try contradiction; discriminate).
    destruct alloc_ok; reflexivity. }
  clearbody ret.
  destruct alloc_ok; [destruct (wbits_ok w) eqn:WOK | ]; subst ret.
  2,3: forward_if; [ forward; Exists (Int.repr 0); entailer!;
         unfold init_mem, braw, raw_strm; rewrite if_false by (destruct v_a; try contradiction; discriminate);
         simpl; sep_apply strm_to_undef; sep_apply strm_to_undef; cancel
       | top_infeas ].
  forward_if.
  { top_infeas. }
  unfold init_mem.
  destruct (eq_dec v_a nullval) as [X|_]; [subst; contradiction | ].
  remember (init_live sp w) as L0 eqn:HL0. simpl.
  replace (istream_raw gv Tsh v_a (raw_after_init ra0 (l_s L0)) L0)
    with (istream gv Tsh v_a (z_init adla rsa L0) (Some L0)) by (symmetry; apply init_istream; auto).
  assert_PROP (live_ok L0 /\ zf_ok (z_init adla rsa L0)) as LZ by (unfold istream; entailer!).
  destruct LZ as [LOK ZOK].
  forward. forward. forward.
  assert_PROP (isptr srcp) as Psrc by entailer!.
  assert (GF: g_facts I1 I2 w srcp src rb).
  { refine (conj RF (conj WOK (conj Hw (conj E (conj Hsrcb (conj Psrc _)))))).
    exists tin, tout, adl, dt, rs. repeat split; first [reflexivity | lia]. }
  assert (HI0: I1 w src 0 (z_init adla rsa L0) L0).
  { subst L0. apply (rf_init _ _ RF); auto. }
  forward_loop (loop_inv I1 I2 gv v_a v_b v_sa v_sb w srcp src rb)
    break: (brk_inv I1 I2 gv v_a v_b v_sa v_sb w srcp src rb).
  { unfold loop_inv. Exists 1 0 w (z_init adla rsa L0) L0 (z_init adla rsa L0) L0.
    unfold inv_at, bmem, ph_inv. change (1 =? 1) with true. entailer!. }
  { unfold loop_inv at 1. Intros ph pos w2 za La zb Lb.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (proj1 (semax_seq_skip _ _ _ _)).
    eapply semax_pre; [ | apply (LS Espec I1 I2 gv v_a v_b v_sa v_sb w srcp src rb ph pos w2 za La zb Lb GF) ].
    apply andp_left2; apply derives_refl. }
  unfold brk_inv. Intros pos w2 za La zb Lb.
  unfold inv_at, bmem, ph_inv. change (2 =? 1) with false. Intros.
  forward_call (gv, Tsh, v_a, za, Some La).
  { rewrite ir_istream_opt by auto. cancel. }
  forward_call (gv, Tsh, v_b, zb, Some Lb).
  { rewrite !ir_istream_opt by auto. cancel. }
  forward. Exists (Int.repr 0). entailer!.
  rewrite ir_istream_opt by auto. sep_apply (istream_to_undef gv v_a). sep_apply (istream_to_undef gv v_b).
  cancel.
Qed.

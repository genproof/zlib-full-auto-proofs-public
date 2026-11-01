(* Law res_memory_inflate: main of harness/res_memory_inflate.c against main_core_spec at the law's
   compspecs.  main draws windowBits and assumes inflate_window_ok(windowBits) (laws_session.h: zlib.h's
   ranges, exactly the windowBits inflateInit2_ accepts: laws_session/Facts.v), draws the input (alloc_any_bytes
   of any length), makes the stream count through the harness's counting allocator (counted_stream) and calls
   inflateInit2_; it checks `code == Z_OK || (code == Z_MEM_ERROR && count.failed)` (with an accepted windowBits
   inflateInit2_ returns Z_OK, or Z_MEM_ERROR when the allocation of its state failed, the event ZFail) and
   returns unless Z_OK.  It then computes the harness's w (harness_w,
   ModelStmt.v) and runs the do-while of inflate() calls, whose body is ResIMemLoop.body_mem_loop, with the
   loop invariant ResIMemLoop.mem_inv: after inflateInit2_ the allocator holds the state (7160 bytes) and no
   window (ResIMemTheory.mem_init), the state satisfies res_inv (res_model_stmt) and swfW. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Import Zlib.proof.harness.res_inflate.ResICS.
Require Import Zlib.proof.harness.res_inflate.ResISpecs.
Require Import Zlib.proof.harness.res_inflate.ResIKit.
Require Import Zlib.proof.harness.res_inflate.ResITheory.
Require Import Zlib.proof.harness.res_inflate.ResIMemTheory.
Require Import Zlib.proof.harness.res_inflate.ResIMemLoop.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.res_memory_inflate.code.
Local Open Scope logic.

Ltac ret0 := forward; Exists (Int.repr 0); entailer!.

(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ discriminate
                              | match goal with H : _ <> _ |- _ => solve [apply H; reflexivity] end
                              | match goal with H : _ = _ |- _ => solve [discriminate H] end
                              | contradiction ].

(* forward_if whose join adds temp t = v to the current assertion *)
Ltac ifpost t v := match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end.

Module LS := Zlib.proof.harness.laws_session.Spec.

Lemma body_main_memory : res_model_stmt -> main_memory_stmt.
Proof.
  intros MODEL. unfold main_memory_stmt.
  start_function.
  unfold Ri. Intros.
  forward_call tt. Intros wb.
  rewrite (vint_signed wb). pose proof (Int.signed_range (Int.repr wb)) as Hw.
  set (w := Int.signed (Int.repr wb)) in *. clearbody w.
  (* gp_assume(inflate_window_ok(window_bits)) *)
  forward_call w.
  forward_call (Int.repr (if LS.inflate_window_valid w then 1 else 0)).
  { destruct (LS.inflate_window_valid w); entailer!. }
  assumed.
  rewrite Zlib.proof.harness.laws_session.Facts.inflate_window_valid_ok in E. rename E into Hwb.
  forward_call (9223372036854775807). Intros n.
  call_alone. forward_call (n, gv). Intros vret. destruct vret as [dp bs]. cbn [fst snd] in *. forward.
  subst n.
  destruct (eq_dec dp nullval) as [Ed | Nd].
  { subst dp. forward_if; [ ret0 | contradiction ]. }
  Intros.
  forward_if.
  { apply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS). cancel. }
  { contradiction. }
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
  assert_PROP (isptr (gv ___stringlit_res_memory_inflate_1)) as Pver by (unfold hversion_lit; entailer!).
  unfold hversion_lit.
  set (cp := v_count__1). set (za := gv HC._counted_alloc). set (zf := gv HC._counted_free).
  change (counted cp za zf) with (zai_a Ac (ix cp za zf false)).
  change (count_res cp gv []) with (@za_res (zai_a Ac (ix cp za zf false)) gv []).
  forward_call (ix cp za zf false,
                (gv, Tsh, v_strm,
                 RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef,
                 Vundef, Vundef, w, gv ___stringlit_res_memory_inflate_1, Ers, hver_vals, 49, 112, @nil zev)).
  { rewrite if_false by (destruct v_strm; try contradiction; discriminate). unfold zfuncs_za.
    simpl za_alloc. simpl za_free. simpl za_opaque. cancel. }
  { split; [unfold hver_vals; cbn; rep_lia | simpl za_cap; unfold ZEvents.state_size; rep_lia]. }
  Intros vret. destruct vret as [alloc_ok sp]. cbn [fst snd] in *.
  assert (Hret : init_ret v_strm 49 112 w alloc_ok = if alloc_ok then (if wbits_ok w then 0 else -2) else -4).
  { unfold init_ret. simpl. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    destruct alloc_ok; reflexivity. }
  rewrite Hret.
  destruct (eq_dec v_strm nullval) as [Esn | Hsn]; [subst v_strm; contradiction | ].
  unfold init_mem_za. rewrite if_false by exact Hsn.
  match goal with |- context [@za_res ?Z gv ?t] => change (@za_res Z gv t) with (count_res cp gv t) end.
  unfold ZEvents.init_ev. simpl andb. simpl orb. cbv iota beta.
  destruct alloc_ok; [rewrite Hwb | ]; simpl negb; cbv iota beta; simpl Z.eqb; cbv iota beta.
  2: { (* the allocation of the state failed: Z_MEM_ERROR, and count.failed is set *)
    unfold count_res. rewrite count_local. change (cnt_failed ([] ++ [ZFail])) with 1. Intros.
    ifpost _t'6 (Vint (Int.repr 1)).
    { infeas. }
    { forward_if; [ forward; forward; forward; entailer! | infeas ]. }
    forward_call (Int.repr 1).
    forward_if; [ | infeas].
    sep_apply (@data_at_data_at_ CSi). sep_apply raw_undef. ret0. }
  ifpost _t'6 (Vint (Int.repr 1)).
  { forward. entailer!. }
  { infeas. }
  forward_call (Int.repr 1).
  forward_if; [ infeas | ].
  (* inflateInit2_ returned Z_OK: the live stream with the fields of set_buffer(strm, Z_NULL, 0, Z_NULL, 0) *)
  change (RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef) with raw0.
  match goal with |- context [@istream_raw_za ?Z gv Tsh v_strm ?r ?L] =>
    change (@istream_raw_za Z gv Tsh v_strm r L) with (@istream_raw_za (counted cp za zf) gv Tsh v_strm r L) end.
  sep_apply (init_offer_pre gv cp za zf sp w v_strm). Intros.
  match goal with H : live_ok (init_live sp w) |- _ => rename H into HL end.
  sep_apply (offer_istream gv cp za zf sp w v_strm nullval 0 nullval 0 ltac:(rep_lia) ltac:(rep_lia) HL).
  rewrite app_nil_l.
  pose proof (harness_w_range w Hwb) as Hhw.
  assert (Wr : -15 <= w) by (unfold harness_w in Hhw; destruct (Z.ltb_spec w 0); lia).
  set (X := if w <? 0 then - w else Z.land w 15).
  assert (XR : 0 <= X <= 15).
  { subst X. destruct (Z.ltb_spec w 0); [lia | ].
    change (Z.land w 15) with (Z.land w (Z.ones 4)). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound w (2 ^ 4) ltac:(lia)). simpl in *. lia. }
  assert (HX : harness_w w = if X =? 0 then 15 else X) by (rewrite harness_w_c; reflexivity).
  forward.
  forward_if (temp _w (Vint (Int.repr X))).
  { forward.
    { entailer!. change (Int.signed Int.zero) with 0. rep_lia. }
    entailer!. subst X. destruct (Z.ltb_spec w 0); [ | lia]. try rewrite Int.neg_repr. reflexivity. }
  { forward. entailer!. subst X. destruct (Z.ltb_spec w 0); [lia | ]. try rewrite and_repr. reflexivity. }
  forward_if (temp _w (Vint (Int.repr (harness_w w)))).
  { forward. entailer!. rewrite HX.
    first [ match goal with H : (if w <? 0 then _ else _) = 0 |- _ => rewrite H; reflexivity end
          | match goal with H : Int.repr ?x = Int.repr 0 |- _ =>
              apply repr_inj_signed in H; [rewrite H; reflexivity | rep_lia | rep_lia] end ]. }
  { forward. entailer!. rewrite HX.
    match goal with H : ?x <> 0 |- context [?x =? 0] => rewrite (proj2 (Z.eqb_neq x 0) H); reflexivity end. }
  forward.
  (* the do-while, with the invariant mem_inv (ResIMemLoop.v) *)
  pose proof (proj1 MODEL w sp Hwb) as HI0.
  forward_loop (mem_inv gv w v_strm cp dp bs)
    continue: (mem_inv gv w v_strm cp dp bs)
    break: (mem_inv gv w v_strm cp dp bs).
  { unfold mem_inv. Exists 0 [ZAlloc ZEvents.state_size] (zinit nullval 0 nullval 0 w) (init_live sp w).
    unfold hversion_lit, zfuncs_za, mem_za. entailer!.
    - split; [apply init_swfW | apply mem_init; lia].
    - apply derives_refl. }
  2: { (* while (nondet_u8() != 0) *)
    unfold mem_inv. Intros read tr z L.
    forward_call tt. Intros c.
    forward_if.
    { forward. Exists read tr z L. entailer!. }
    { forward. Exists read tr z L. entailer!. } }
  2: { (* return 0 after the loop: main's locals back *)
    unfold mem_inv. Intros read tr z L.
    sep_apply (@live_local (mem_za gv cp) (init_cell w) gv Tsh v_strm z L).
    sep_apply count_back. ret0. }
  unfold mem_inv. Intros read tr z L.
  assert_PROP (isptr dp) as Pdp.
  { entailer!. destruct dp; try contradiction; auto. }
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (body_mem_loop MODEL gv w v_strm cp dp bs read tr z L); auto ].
  { entailer!. }
  lia.
Qed.

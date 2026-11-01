(* Law inflate_reset, main: the reset of a (inflateReset or inflateReset2 with wsel) and inflateInit2(&b, w2)
   (IRMainKit.seg_rst), from phase 1 to phase 2 (IRFacts.rf_reset). *)
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
Require Import Zlib.proof.inflate_api.ResetFacts.

(* a live stream as the reset functions take it, and back *)
Lemma ir_istream_rst gv shs vs z L:
  isptr vs -> istream gv shs vs z (Some L) |-- rstream_opt gv shs vs z (rst_of gv (Some L)).
Proof.
  intros P. unfold istream, rstream_opt, rstream, rst_of, state_mem.
  rewrite if_false by (intro; subst; contradiction).
  rewrite state_rep_v_eq. Intros.
  match goal with H: live_ok L |- _ => destruct H as (LP & LS & _) end.
  pose proof (sw_mode _ LS). pose proof (sw_wbits _ LS).
  entailer!.
Qed.

Lemma ir_rst_istream gv shs vs z L:
  isptr vs -> live_ok L -> rstream_opt gv shs vs z (rst_of gv (Some L)) |-- istream gv shs vs z (Some L).
Proof.
  intros P LOK. unfold istream, rstream_opt, rstream, rst_of, state_mem.
  rewrite if_false by (intro; subst; contradiction).
  rewrite state_rep_v_eq. Intros.
  entailer!.
Qed.

(* the fields the reset leaves: totals 0, msg NULL *)
Lemma ir_reset_z rst1 w2 z L:
  wbits_ok w2 = true ->
  zf_tin (snd3 (reset_out rst1 w2 z L)) = 0 /\ zf_tout (snd3 (reset_out rst1 w2 z L)) = 0 /\
  zf_msg (snd3 (reset_out rst1 w2 z L)) = None.
Proof.
  intros W. unfold reset_out. destruct rst1.
  - unfold reset_f, snd3. simpl. auto.
  - unfold reset2_f, wbits_ok in *. destruct (reset2_wb w2) as [[wr wb] | ]; [ | discriminate].
    unfold snd3. simpl. auto.
Qed.

(* a non-negative accepted windowBits has a wrapper *)
Lemma ir_wrap_pos sp w2:
  0 <= w2 -> wbits_ok w2 = true -> (i_wrap (l_s (init_live sp w2)) =? 0) = false.
Proof.
  intros P W. unfold wbits_ok in W. unfold init_live.
  destruct (reset2_wb w2) as [[wr wb] | ] eqn:E; [ | discriminate].
  assert (Wr: wr = Z.shiftr w2 4 + 5).
  { unfold reset2_wb in E. destruct (Z.ltb_spec w2 0); [lia | ].
    destruct (_ || _)%bool; inversion E; auto. }
  assert (Hs: 0 <= Z.shiftr w2 4) by (apply Z.shiftr_nonneg; lia).
  cbn [l_s]. destruct (init_s_wrap w2 wr wb E) as (A & _ & _ & D & _). rewrite A.
  apply Z.eqb_neq. intros Z. apply D in Z. lia.
Qed.

Lemma ir_reset2_none w2 z L: wbits_ok w2 = false -> reset2_f w2 z L = (Z_STREAM_ERROR, z, L).
Proof. unfold wbits_ok, reset2_f. destruct (reset2_wb w2) as [[? ?] | ]; [discriminate | auto]. Qed.

(* the end of seg_rst: loop_inv in phase 2 (the version literals abstracted: cancel would try to unify them) *)
Ltac ir_close gv HI :=
  change (Zlength (map (fun c : Z => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])) with 6;
  fold (ir_hversion_lit gv);
  go_lower;
  apply andp_right; [apply prop_right; rewrite !eqb_type_refl; repeat split; first [exact HI | lia] | ];
  match goal with |- context [istream ?gv _ ?vb ?zb (Some ?Lb)] =>
    generalize (istream gv Tsh vb zb (Some Lb)); intro end;
  match goal with |- context [istream ?gv _ ?vb ?zb (Some ?Lb)] =>
    generalize (istream gv Tsh vb zb (Some Lb)); intro end;
  match goal with |- context [version_lit ?gv] =>
    generalize (ir_hversion_lit gv); generalize (version_lit gv); intros end;
  cancel.

Lemma rst_proof : rst_stmt.
Proof.
  intros E I1 I2 gv va vb vsa vsb w srcp src rb pos wsel how za La G HI Hpos Hws Hhow Pva Pvb.
  pose proof G as G'. destruct G' as (RF & Wok & Wr & Hsrcl & Hsrcb & Psrc & RBok).
  unfold rst_pre, seg_rst, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  assert_PROP (zf_ok za /\ live_ok La) as ZL by (unfold istream; entailer!). destruct ZL as [ZOK LOK].
  forward_if (EX rst1: bool, EX w2: Z,
    PROP ((rst1 = true -> w2 = w); wbits_ok w2 = true; Int.min_signed <= w2 <= Int.max_signed)
    LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
           temp _w2 (Vint (Int.repr w2));
           lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
    SEP (istream gv Tsh va (snd3 (reset_out rst1 w2 za La)) (Some (thd3 (reset_out rst1 w2 za La)));
         braw gv vb rb; mem_mgr gv; zfuncs gv; tables_rep Ers gv;
         crc_table_at Ers gv; version_lit gv; ir_hversion_lit gv; ir_msg_lits gv;
         malloc_token Ews (tarray tuchar (Zlength src)) srcp;
         data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
         data_at_ Tsh (tptr tuchar) vsa; data_at_ Tsh (tptr tuchar) vsb)).
  { sep_apply (ir_istream_rst gv Tsh va za La Pva).
    forward_call (gv, Tsh, va, za, rst_of gv (Some La)).
    { unfold reset_pre, rs_live. rewrite if_false by (intro; subst; contradiction).
      intros _. destruct (rf_reset _ _ RF w src pos za La true w HI LOK ZOK (fun _ => eq_refl) Wok Wr) as (_ & X & _).
      exact X. }
    unfold reset_post, reset_ret, rs_live. rewrite !if_false by (intro; subst; contradiction). unfold rst_of.
    cbv iota. change (fst3 (reset_f za La)) with Z_OK. rewrite Z.eqb_refl. change Z_OK with 0.
    forward_call (Int.repr 1).
    Exists true w. entailer!. apply derives_refl. }
  { forward.
    sep_apply (ir_istream_rst gv Tsh va za La Pva).
    forward_call (gv, Tsh, va, za, rst_of gv (Some La), wsel).
    { unfold reset_pre, rs_live. rewrite if_false by (intro; subst; contradiction).
      unfold rst_of. cbv iota. destruct (wbits_ok wsel) eqn:WS.
      - intros _. destruct (rf_reset _ _ RF w src pos za La false wsel HI LOK ZOK ltac:(discriminate) WS Hws)
          as (_ & X & _). exact X.
      - rewrite ir_reset2_none by exact WS. discriminate. }
    unfold reset_ret, reset_post, rs_live. rewrite if_false by (intro; subst; contradiction).
    forward_call wsel.
    destruct (wbits_ok wsel) eqn:WS.
    - unfold rst_of. cbv iota.
      destruct (rf_reset _ _ RF w src pos za La false wsel HI LOK ZOK ltac:(discriminate) WS Hws) as (R0 & _ & _).
      unfold reset_out in R0. rewrite R0, Z.eqb_refl. change Z_OK with 0.
      forward_call (Int.repr 1).
      forward_if.
      { discriminate. }
      forward. Exists false wsel. entailer!. apply derives_refl.
    - unfold rst_of. cbv iota. rewrite ir_reset2_none by exact WS. unfold fst3; cbn [fst snd].
      change (Z_STREAM_ERROR =? Z_OK) with false. cbv iota.
      sep_apply (ir_rst_istream gv Tsh va za La Pva LOK).
      forward_call (Int.repr 1).
      forward_if.
      2: { discriminate. }
      forward. Exists (Int.repr 0). sep_apply (istream_to_undef gv va za (Some La)).
      unfold braw, raw_strm. sep_apply strm_to_undef. entailer!. }
  Intros rst1 w2.
  destruct (rf_reset _ _ RF w src pos za La rst1 w2 HI LOK ZOK) as (R0 & LOK2 & HI2); auto.
  pose proof (ir_reset_z rst1 w2 za La ltac:(assumption)) as (T0 & T1 & M0).
  set (z2 := snd3 (reset_out rst1 w2 za La)) in *. set (L2 := thd3 (reset_out rst1 w2 za La)) in *.
  clearbody z2 L2.
  destruct z2 as [ni ai tin no ao tout msg dt adl res]; cbn [zf_tin zf_tout zf_msg] in T0, T1, M0; subst tin tout msg.
  rewrite ir_istream_unfold. Intros. rename H2 into ZOK2. unfold ir_tup.
  cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res msg_val].
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'28 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
  { forward. forward. entailer!. }
  { exfalso. match goal with X: Int64.repr 0 <> _ |- _ => apply X; reflexivity end. }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx (temp _t'29 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
  { forward. forward. entailer!. }
  { exfalso. discriminate. }
  forward_call (Int.repr 1).
  unfold braw.
  assert_PROP (isptr (gv Zlib.harness.x_inflate_reset.code.___stringlit_x_inflate_reset_1)) as Pver
    by (unfold ir_hversion_lit; entailer!).
  unfold ir_hversion_lit.
  forward_call (gv, Tsh, vb, rb, Vundef, Vundef, nullval, w2,
                gv Zlib.harness.x_inflate_reset.code.___stringlit_x_inflate_reset_1, Ers,
                map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by (intro X; subst; contradiction). cancel. }
  { rewrite !Zlength_cons, Zlength_nil. rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp]. cbn [fst snd] in *.
  assert (IR: init_ret vb 49 112 w2 alloc_ok = if alloc_ok then Z_OK else Z_MEM_ERROR).
  { unfold init_ret. rewrite if_false by (intro X; subst; contradiction). rewrite H0. destruct alloc_ok; reflexivity. }
  rewrite IR. unfold init_mem. rewrite if_false by (intro X; subst; contradiction).
  destruct RBok as (tin & tout & adl0 & dt0 & rs & Rtin & Rtout & Radl & Rdt & Rrs & ERB).
  destruct alloc_ok.
  - change (Z_OK =? Z_VERSION_ERROR) with false. change (Z_OK =? Z_MEM_ERROR) with false.
    change (Z_OK =? Z_OK) with true. cbv iota.
    subst rb. rewrite init_istream by exact Radl.
    forward_if.
    { discriminate. }
    forward. forward.
    set (Lb := init_live sp w2).
    assert_PROP (live_ok Lb /\ zf_ok (z_init adl0 rs Lb)) as LZ by (unfold istream; entailer!).
    destruct LZ as [LOKb ZOKb].
    assert (Psp: isptr sp) by auto.
    set (za2 := ZF ni ai 0 no ao 0 None dt adl res) in *.
    forward_if.
    + forward.
      rewrite (ir_istream_unfold gv Tsh vb). Intros. unfold ir_tup.
      forward.
      set (zb := ZF nullval 0 0 nullval 0 0 None 0 adl (Vlong (Int64.repr rs))).
      assert (ZOKb': zf_ok zb).
      { destruct ZOK2 as (_ & _ & _ & _ & _ & A). unfold za2 in A; cbn [zf_adler] in A.
        unfold zb, zf_ok; cbn. rep_lia. }
      assert (HI2b: I2 w2 src 0 za2 L2 zb Lb).
      { apply HI2; auto; try reflexivity. intros; lia. }
      unfold loop_inv, inv_at. Exists 2 0 w2 za2 L2 zb Lb.
      unfold ph_inv, bmem. change (2 =? 1) with false. cbv iota.
      sep_apply (ir_istream_fold gv Tsh va za2 L2 ZOK2 H3 LOK2).
      sep_apply (ir_istream_fold gv Tsh vb zb Lb ZOKb' H3 LOKb).
      clear HI2. clearbody zb za2 Lb. ir_close gv HI2b.
    + forward.
      assert (HI2b: I2 w2 src 0 za2 L2 (z_init adl0 rs Lb) Lb).
      { apply HI2; auto; try reflexivity. intros; lia.
        intros P. unfold z_init. cbn [zf_adler]. unfold Lb. rewrite ir_wrap_pos by auto. reflexivity. }
      unfold loop_inv, inv_at. Exists 2 0 w2 za2 L2 (z_init adl0 rs Lb) Lb.
      unfold ph_inv, bmem. change (2 =? 1) with false. cbv iota.
      sep_apply (ir_istream_fold gv Tsh va za2 L2 ZOK2 H3 LOK2).
      clear HI2. clearbody za2 Lb. ir_close gv HI2b.
  - change (Z_MEM_ERROR =? Z_VERSION_ERROR) with false. change (Z_MEM_ERROR =? Z_MEM_ERROR) with true. cbv iota.
    forward_if.
    2: { discriminate. }
    forward. Exists (Int.repr 0).
    sep_apply (ir_istream_fold gv Tsh va
       (ZF ni ai 0 no ao 0 None dt adl res) L2 ZOK2 H3 LOK2).
    sep_apply (istream_to_undef gv va (ZF ni ai 0 no ao 0 None dt adl res) (Some L2)).
    unfold raw_strm. sep_apply strm_to_undef. entailer!.
Qed.

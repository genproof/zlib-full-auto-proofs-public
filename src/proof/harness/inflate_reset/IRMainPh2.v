(* Law inflate_reset, main: phase 2, the then-branch of `if (phase == 2)` (IRMainKit.seg_ph2): b's inflate()
   call on the same input and output space, `if (rb == Z_MEM_ERROR) return 0;`, and the asserts that both calls
   agree (IRFacts.rf_inflate2). *)
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

(* the bytes a call wrote at the start of an output object, as a slice for bytes_same (the bytes normalised
   by Int.unsigned o Int.repr: the stored values are bytes, the model's list need not be) *)
Lemma ph2_out_cbuf (c: list val) (ow: list Z) (n: Z) p:
  isptr p -> Zlength ow <= n -> Zlength c = n ->
  Forall (value_fits tuchar) (out_after c ow n) ->
  cbuf_ok false p Ews p 0 n (Zlength ow) (out_after c ow n) (map (fun x => Int.unsigned (Int.repr x)) ow).
Proof.
  intros Pp Hl Hc F. pose proof (Zlength_nonneg ow). unfold out_after in *. rewrite sublist_nil, app_nil_l in *.
  apply Forall_app in F. destruct F as [F _].
  unfold cbuf_ok. split; [destruct p; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto with share | ]. split; [lia | ]. split; [lia | ]. split; [rewrite Zlength_map; reflexivity | ].
  split.
  - unfold is_bytes, byte_vals in *. rewrite Forall_map in F. rewrite Forall_map.
    eapply Forall_impl; [ | exact F]. intros x Hx. simpl in Hx.
    specialize (Hx ltac:(discriminate)). simpl in Hx. pose proof (Int.unsigned_range (Int.repr x)). cbv beta delta [Basics.compose]. lia.
  - rewrite Z.add_0_l. rewrite sublist_app1 by (rewrite ?Zlength_byte_vals; lia).
    rewrite sublist_same by (rewrite ?Zlength_byte_vals; lia).
    unfold bytes_rep, byte_vals. rewrite map_map. apply map_ext. intros x. rewrite Int.repr_unsigned. reflexivity.
Qed.

(* hides an equation from entailer!'s substitutions *)
Definition ph2_hide (P: Prop) : Prop := P.

Lemma ph2_proof : ph2_stmt.
Proof.
  intros Espec I1 I2 gv va vb vsa vsb w srcp src rb w2 pos aout flush stop how wsel ain
         iap ibp oap obp qa qb bsa bsb za La zb Lb ra za' La' owa Fr PF.
  destruct PF as (GF & HI & HLa & Hza & HLb & Hzb & Hw2 & Hpos & Hain & Hpa & Haout & Hfl & Hwsel & Hstop & Hhow
                  & Hbsa & Bsa & Hbsb & Bsb & Pva & Pvb & Piap & Pibp & Poap & Pobp & Hrela & Hra).
  pose proof GF as GF'. destruct GF' as (RF & Hwok & Hw & Hsrc & Hsb & Psrc & Hrb).
  unfold ph2_pre, seg_ph2.
  rewrite (ir_istream_unfold gv Tsh vb zb Lb). Intros.
  forward. forward. forward. forward.
  set (sub := sublist pos (pos + ain) src) in *.
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  rewrite <- ir_tup_call.
  set (z1 := ir_call zb ibp ain obp aout).
  assert (Z1ok: zf_ok z1).
  { destruct Hzb as (? & ? & ? & ? & ? & ?). unfold z1, ir_call, zf_ok; simpl. rep_lia. }
  sep_apply (ir_istream_fold gv Tsh vb z1 Lb); auto.
  sep_apply (ir_bufs_pre Lb ibp obp ain aout (bytes_rep sub) (bytes_rep bsb)).
  { unfold bytes_rep. rewrite Zlength_map. auto. }
  destruct (rf_head2 _ _ RF _ _ _ _ _ _ _ HI) as [Hhda Hhdb].
  forward_call (gv, Tsh, vb, z1, Some Lb, ir_ib ibp ain (bytes_rep sub), sub,
                Some (ir_ob obp aout (bytes_rep bsb)), flush, Ers, Ers, true, true).
  { rewrite ir_istream_opt, ir_is_live by auto. simpl head_opt. unfold head_mem at 2; rewrite Hhdb. cancel. }
  { unfold z1, ir_call, ir_ib, ir_ob; simpl.
    assert (bytes_ok sub) by (apply Forall_sublist; exact Hsb).
    assert (Lr: Zlength (bytes_rep sub) = ain) by (unfold bytes_rep; rewrite Zlength_map; auto).
    assert (Lr2: Zlength (bytes_rep bsb) = aout) by (unfold bytes_rep; rewrite Zlength_map; auto).
    destruct ibp, obp; try contradiction. simpl offset_val. rewrite !Ptrofs.add_zero.
    rewrite Hsub, Z.add_0_l, sublist_same by lia.
    repeat match goal with |- _ /\ _ => split end; auto with share; try reflexivity; try rep_lia. }
  Intros vret. destruct vret as [[[rb' zb'] stb'] owb]. simpl fst; simpl snd.
  match goal with H: inflate_rel _ vb _ _ _ _ _ _ _ _ _ |- _ => rename H into Hrelb end.
  rewrite ir_istream_opt, !ir_is_live by auto.
  forward_if.
  { forward. Exists (Int.repr 0).
    sep_apply (istream_to_undef gv va za' (Some La')). sep_apply (istream_to_undef gv vb zb' stb'). unfold t_z.
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) qa vsa). sep_apply (data_at_data_at_ Tsh (tptr tuchar) qb vsb).
    entailer!. }
  match goal with H: Int.repr rb' <> _ |- _ => rename H into Hrb' end.
  assert (HrbM: rb' <> Z_MEM_ERROR) by (intro E; apply Hrb'; rewrite E; reflexivity).
  assert (Ez1: z1 = ir_call zb (in_ptr (ir_ib ibp ain (bytes_rep sub)) 0) ain
                      (out_ptr (ir_ob obp aout (bytes_rep bsb)) 0) aout)
    by (rewrite ir_in_ptr, ir_out_ptr by auto; reflexivity).
  rewrite Ez1 in Hrelb. cbv beta iota zeta delta [fst snd] in Hrelb.
  destruct (rf_inflate2 _ _ RF w2 src pos za La zb Lb va vb flush (ir_ib iap ain (bytes_rep sub)) (ir_ib ibp ain (bytes_rep sub)) sub (ir_ob oap aout (bytes_rep bsa)) (ir_ob obp aout (bytes_rep bsb)) ain aout ra za' _ owa rb' zb' stb' owb
              HI HLa HLb Hza Hzb ltac:(destruct va; try contradiction; discriminate)
              ltac:(destruct vb; try contradiction; discriminate) Hpos Hain Hpa Hsrc Hsb Haout Hfl
              ltac:(unfold ir_ib; discriminate) ltac:(unfold ir_ib; discriminate) eq_refl Hrela Hra Hrelb HrbM)
    as (La2 & Lb' & EA & EB & Er & Eai & Eao & Eow & Elow & Etin & Etout & Edt & Emsg & Eadl & Hai' & Hao' & HI').
  injection EA as <-. subst stb' rb' owb. clear Hrelb HrbM Hrb'.
  destruct (rf_head2 _ _ RF _ _ _ _ _ _ _ HI') as [Hha' Hhb'].
  simpl head_opt. unfold head_mem; rewrite Hha', Hhb'.
  sep_apply (ir_bufs_post Lb ibp obp ain aout (bytes_rep sub) (bytes_rep bsb) owa).
  rewrite (ir_istream_unfold gv Tsh va za' La'), (ir_istream_unfold gv Tsh vb zb' Lb'). Intros.
  assert (Etb: ir_tup gv zb' (l_sp Lb') =
    (zf_ni zb', (Vint (Int.repr (zf_ai za')), (Vlong (Int64.repr (zf_tin za')), (zf_no zb',
     (Vint (Int.repr (zf_ao za')), (Vlong (Int64.repr (zf_tout za')), (msg_val gv (zf_msg za'), (l_sp Lb',
     (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt za')),
     (Vlong (Int64.repr (zf_adler zb')), zf_res zb'))))))))))))))
    by (unfold ir_tup; rewrite <- Eai, <- Eao, <- Etin, <- Etout, <- Edt, <- Emsg; reflexivity).
  rewrite Etb. unfold ir_tup.
  forward_call (Int.repr 1).
  { entailer!. rewrite Int.eq_true. reflexivity. }
  forward. forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  forward.
  assert_PROP (Forall (value_fits tuchar) (out_after (bytes_rep bsa) owa aout)) as Fa by entailer!.
  assert_PROP (Forall (value_fits tuchar) (out_after (bytes_rep bsb) owa aout)) as Fb by entailer!.
  assert (Lbs: forall bs, Zlength bs = aout -> Zlength (bytes_rep bs) = aout)
    by (intros bs Hl; unfold bytes_rep; rewrite Zlength_map; auto).
  pose proof (ph2_out_cbuf (bytes_rep bsa) owa aout oap Poap ltac:(lia) (Lbs bsa Hbsa) Fa) as Ca.
  pose proof (ph2_out_cbuf (bytes_rep bsb) owa aout obp Pobp ltac:(lia) (Lbs bsb Hbsb) Fb) as Cb.
  rewrite Elow in Ca, Cb.
  rewrite <- (bytes_adler_cs Ews aout (out_after (bytes_rep bsa) owa aout) oap),
          <- (bytes_adler_cs Ews aout (out_after (bytes_rep bsb) owa aout) obp).
  forward_call (oap, Ews, oap, 0, aout, out_after (bytes_rep bsa) owa aout, map (fun x => Int.unsigned (Int.repr x)) owa,
                obp, Ews, obp, 0, aout, out_after (bytes_rep bsb) owa aout, map (fun x => Int.unsigned (Int.repr x)) owa,
                aout - zf_ao za').
  destruct (list_eq_dec Z.eq_dec (map (fun x => Int.unsigned (Int.repr x)) owa)
              (map (fun x => Int.unsigned (Int.repr x)) owa)) as [_ | NE]; [ | congruence].
  forward_call (Int.repr 1).
  rewrite (bytes_adler_cs Ews aout (out_after (bytes_rep bsa) owa aout) oap),
          (bytes_adler_cs Ews aout (out_after (bytes_rep bsb) owa aout) obp).
  forward. forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  forward. forward. forward. forward_call (Int.repr 1).
  { entailer!. rewrite Int64.eq_true. reflexivity. }
  forward. forward. apply semax_if_seq. forward_if.
  2: { exfalso. auto. }
  destruct (zf_msg za') as [m|] eqn:Em.
  - pose proof (ir_msg_ptr gv m) as MP. pose proof (ir_msg_valid gv m) as MV.
    unfold POSTCONDITION, abbreviate. change (msg_val gv (Some m)) with (gv (msg_ident m)) in *.
    set (mp := gv (msg_ident m)) in *.
    assert (Hid: ph2_hide (gv (msg_ident m) = mp)) by reflexivity. clearbody mp.
    rewrite (add_andp _ _ MP). Intros.
    forward. forward. forward.
    forward_call (Int.repr 1).
    forward_if.
    + forward. forward. forward_call (Int.repr 1).
      { entailer!. rewrite (Eadl ltac:(lia)), Int64.eq_true. reflexivity. }
      generalize POST_m; intros [Pn Pb Pc Pr]; simpl RA_normal.
      unfold ph2_post. Exists zb' Lb' (out_after (bytes_rep bsa) owa aout) (out_after (bytes_rep bsb) owa aout).
      rewrite (ir_istream_unfold gv Tsh va za' La'), (ir_istream_unfold gv Tsh vb zb' Lb'), Etb. unfold ir_tup.
      rewrite Em. change (msg_val gv (Some m)) with (gv (msg_ident m)). unfold ph2_hide in Hid. rewrite Hid.
      entailer!.
    + forward.
      generalize POST_m; intros [Pn Pb Pc Pr]; simpl RA_normal.
      unfold ph2_post. Exists zb' Lb' (out_after (bytes_rep bsa) owa aout) (out_after (bytes_rep bsb) owa aout).
      rewrite (ir_istream_unfold gv Tsh va za' La'), (ir_istream_unfold gv Tsh vb zb' Lb'), Etb. unfold ir_tup.
      rewrite Em. change (msg_val gv (Some m)) with (gv (msg_ident m)). unfold ph2_hide in Hid. rewrite Hid.
      entailer!.
  - change (msg_val gv None) with nullval.
    forward. forward. forward.
    forward_call (Int.repr 1).
    forward_if.
    + forward. forward. forward_call (Int.repr 1).
      { entailer!. rewrite (Eadl ltac:(lia)), Int64.eq_true. reflexivity. }
      generalize POST_m; intros [Pn Pb Pc Pr]; simpl RA_normal.
      unfold ph2_post. Exists zb' Lb' (out_after (bytes_rep bsa) owa aout) (out_after (bytes_rep bsb) owa aout).
      rewrite (ir_istream_unfold gv Tsh va za' La'), (ir_istream_unfold gv Tsh vb zb' Lb'), Etb. unfold ir_tup.
      rewrite Em. simpl msg_val. entailer!.
    + forward.
      generalize POST_m; intros [Pn Pb Pc Pr]; simpl RA_normal.
      unfold ph2_post. Exists zb' Lb' (out_after (bytes_rep bsa) owa aout) (out_after (bytes_rep bsb) owa aout).
      rewrite (ir_istream_unfold gv Tsh va za' La'), (ir_istream_unfold gv Tsh vb zb' Lb'), Etb. unfold ir_tup.
      rewrite Em. simpl msg_val. entailer!.
Qed.

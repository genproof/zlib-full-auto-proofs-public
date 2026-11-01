(* Law inflate_header: the bodies of the harness's own functions draw_nonzero, head_buf, field_ok against
   their specifications (IHHelpers.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS.
Require Import Zlib.proof.harness.inflate_header.IHHelpers.

Lemma ih_bytes_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_tok_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ih_ptr_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_ptr_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma body_draw_nonzero: semax_body Vprog_ih Gprog_draw_nonzero HH.f_draw_nonzero draw_nonzero_spec.
Proof.
  start_function.
  assert_PROP (isptr buf) as Pb by entailer!.
  forward_call (buf, n, sh).
  { rewrite if_false by (destruct buf; try contradiction; discriminate). cancel. }
  Intros bs. rewrite if_false by (destruct buf; try contradiction; discriminate).
  forward_for_simple_bound n (EX i: Z,
     PROP (Forall (fun b => 0 < b <= Byte.max_unsigned) (sublist 0 i bs))
     LOCAL (temp HH._buf buf; temp HH._n (Vint (Int.repr n)))
     SEP (data_at sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) buf)).
  - entailer!; rewrite sublist_nil; constructor.
  - assert (Hb: 0 <= Znth i bs <= Byte.max_unsigned) by (apply (sublist.Forall_Znth (fun b => 0 <= b <= Byte.max_unsigned)); auto; lia).
    forward.
    { entailer!; rewrite ?Znth_map by lia; simpl; rep_lia. }
    forward_call (Int.repr (if Z.eq_dec (Znth i bs) 0 then 0 else 1)).
    { entailer!.
      destruct (Z.eq_dec (Znth i bs) 0) as [E|E]; [rewrite E; reflexivity | ].
      rewrite Int.eq_false; [reflexivity | ]. intros X. apply repr_inj_unsigned in X; rep_lia. }
    entailer!.
    rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
    apply Forall_app. split; auto. constructor; [ | constructor].
    destruct (Z.eq_dec (Znth i bs) 0); [contradiction | lia].
  - Exists bs. rewrite sublist_same in * by lia. entailer!.
Qed.

Lemma body_head_buf: semax_body Vprog_ih Gprog_head_buf HH.f_head_buf head_buf_spec.
Proof.
  start_function.
  forward_if.
  - forward. forward. Exists nullval nullval (Zrepeat 0 max). entailer!.
    { split; [rewrite Zlength_Zrepeat; lia | ]. apply Forall_forall. intros x Hx.
      apply repeat_spec in Hx. subst. rep_lia. }
  - forward_call (max, snapp, ssh, gv).
    { rewrite ih_ptr_cs_. cancel. }
    Intros vret. destruct vret as [[r q] bs]. simpl fst in *. simpl snd in *.
    rewrite ih_ptr_cs.
    forward. Exists r q bs.
    destruct (eq_dec r nullval).
    + entailer!.
    + rewrite !ih_bytes_cs, !ih_tok_cs. entailer!.
Qed.

Lemma body_field_ok: semax_body Vprog_ih Gprog_field_ok HH.f_field_ok field_ok_spec.
Proof.
  start_function.
  set (k := Z.min (Zlength cf) (Zlength cb)).
  assert_PROP (isptr buf /\ isptr snap /\ isptr f) as Pp by entailer!. destruct Pp as (Pb & Ps & Pf).
  forward_if (PROP () LOCAL (temp HH._t'1 (Vint (Int.repr k)); temp HH._buf buf; temp HH._snap snap;
     temp HH._max (Vint (Int.repr (Zlength cb))); temp HH._f f; temp HH._len (Vint (Int.repr (Zlength cf))))
    SEP (data_at shb (tarray tuchar (Zlength cb)) (bytes_rep cb) buf;
         data_at shs (tarray tuchar (Zlength cb)) (bytes_rep cs) snap;
         data_at shf (tarray tuchar (Zlength cf)) (bytes_rep cf) f)).
  - forward. entailer!. subst k. rewrite Z.min_l by lia. auto.
  - forward. entailer!. subst k. rewrite Z.min_r by lia. auto.
  - forward.
    rewrite <- (ih_bytes_cs shb), <- (ih_bytes_cs shs), <- (ih_bytes_cs shf).
    forward_call (buf, shb, buf, 0, Zlength cb, bytes_rep cb, sublist 0 k cb,
                  f, shf, f, 0, Zlength cf, bytes_rep cf, sublist 0 k cf, k).
    { pose proof (Zlength_nonneg cb). pose proof (Zlength_nonneg cf).
      split; [pose proof (cbuf_ok_slice shb buf cb 0 k) as C | pose proof (cbuf_ok_slice shf f cf 0 k) as C];
        rewrite isptr_offset_val_zero in C by auto; apply C; auto; subst k; lia. }
    rewrite (ih_bytes_cs shb), (ih_bytes_cs shs), (ih_bytes_cs shf).
    forward_if (PROP () LOCAL (temp HH._t'3 (Vint (Int.repr (if field_okb cb cs cf then 1 else 0))))
      SEP (data_at shb (tarray tuchar (Zlength cb)) (bytes_rep cb) buf;
           data_at shs (tarray tuchar (Zlength cb)) (bytes_rep cs) snap;
           data_at shf (tarray tuchar (Zlength cf)) (bytes_rep cf) f)).
    + destruct (list_eq_dec Z.eq_dec (sublist 0 k cb) (sublist 0 k cf)) as [E|E]; [ | contradiction].
      rewrite <- (ih_bytes_cs shb), <- (ih_bytes_cs shs), <- (ih_bytes_cs shf).
      forward_call (offset_val k buf, shb, buf, k, Zlength cb, bytes_rep cb, sublist k (Zlength cb) cb,
                    offset_val k snap, shs, snap, k, Zlength cb, bytes_rep cs, sublist k (Zlength cb) cs,
                    Zlength cb - k).
      { assert (Hk: 0 <= k <= Zlength cb) by (pose proof (Zlength_nonneg cb); pose proof (Zlength_nonneg cf); subst k; lia).
        replace (Zlength cb) with (k + (Zlength cb - k)) at 3 6 by lia.
        split; [ | rewrite <- H0 at 1]; apply cbuf_ok_slice; auto; lia. }
      rewrite (ih_bytes_cs shb), (ih_bytes_cs shs), (ih_bytes_cs shf).
      forward. entailer!.
      unfold field_okb. cbv zeta. fold k. rewrite E. rewrite if_true by auto. simpl andb.
      destruct (list_eq_dec Z.eq_dec (sublist k (Zlength cb) cb) (sublist k (Zlength cb) cs)); reflexivity.
    + destruct (list_eq_dec Z.eq_dec (sublist 0 k cb) (sublist 0 k cf)) as [E|E].
      { match goal with H5: Int.repr 1 = Int.zero |- _ =>
          change Int.zero with (Int.repr 0) in H5; apply repr_inj_unsigned in H5; rep_lia end. }
      forward. entailer!. unfold field_okb. cbv zeta. fold k. rewrite if_false by auto. reflexivity.
    + forward.
Qed.

Lemma ih_helpers_bodies : ih_helpers_stmt.
Proof.
  split; [exact body_draw_nonzero | split; [exact body_head_buf | exact body_field_ok]].
Qed.

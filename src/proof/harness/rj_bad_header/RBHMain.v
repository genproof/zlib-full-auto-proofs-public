(* Law rj_bad_header: main of harness/rj_bad_header.c against main_core_spec R (statement in RBHMainStmt.v).
   main draws windowBits, the input and the output space, assumes the header breaks RFC 1950 2.2, initializes
   the stream, offers the input and the output space to one inflate() call and checks its outcome; the outcome
   comes from inflate_specW (the model run2) and RBHTheory.rbh_theory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rj_bad_header.RBHLawCS Zlib.proof.harness.rj_bad_header.RBHGlobals
               Zlib.proof.harness.rj_bad_header.RBHTheory Zlib.proof.harness.rj_bad_header.RBHMainStmt.
Require Import Zlib.harness.rj_bad_header.code.

(* The integer arithmetic of the harness's header tests on bytes and windowBits, as Z. *)
Lemma rbh_land15 w: 0 <= Z.land w 15 <= 15.
Proof.
  replace (Z.land w 15) with (w mod 16) by (symmetry; apply (Z.land_ones w 4); lia).
  pose proof (Z.mod_pos_bound w 16). lia.
Qed.

Lemma rbh_and a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.and (Int.repr a) (Int.repr b) = Int.repr (Z.land a b).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma rbh_land16 w: 0 <= w -> 0 <= Z.land w 16 < 32.
Proof.
  intros. assert (0 <= Z.land w 16) by (apply Z.land_nonneg; lia). split; auto.
  destruct (Z.eq_dec (Z.land w 16) 0) as [E | E]; [lia | ].
  pose proof (Z.log2_land w 16 ltac:(lia) ltac:(lia)).
  change 32 with (2 ^ 5). apply Z.log2_lt_pow2; [lia | ].
  change (Z.log2 16) with 4 in *. lia.
Qed.

Lemma rbh_shru a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.shru (Int.repr a) (Int.repr b) = Int.repr (Z.shiftr a b).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma rbh_modu a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.modu (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof. intros. unfold Int.modu. rewrite !Int.unsigned_repr by lia. reflexivity. Qed.

Lemma rbh_eq a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. unfold Int.eq. rewrite !Int.unsigned_repr by lia.
  destruct (zeq a b), (Z.eqb_spec a b); congruence.
Qed.

Lemma rbh_ltu a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.ltu (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros. unfold Int.ltu. rewrite !Int.unsigned_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

Lemma rbh_lt a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.lt (Int.repr a) (Int.repr b) = (a <? b).
Proof.
  intros. unfold Int.lt. rewrite !Int.signed_repr by lia.
  destruct (zlt a b), (Z.ltb_spec a b); try lia; reflexivity.
Qed.

Lemma rbh_shiftr4 b: 0 <= b <= 255 -> 0 <= Z.shiftr b 4 <= 15.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. split; [apply Z.div_pos; lia | ].
  assert (b / 16 < 16) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* the comparisons of the harness's header tests, as Z booleans *)
Ltac rbh_bool :=
  repeat match goal with H: context [Int.ltu (Int.repr _) (Int.repr _)] |- _ => rewrite rbh_ltu in H by rep_lia
                       | H: context [Int.eq (Int.repr _) (Int.repr _)] |- _ => rewrite rbh_eq in H by rep_lia
                       | H: context [Int.lt (Int.repr _) (Int.repr _)] |- _ => rewrite rbh_lt in H by rep_lia end;
  rewrite ?rbh_ltu, ?rbh_eq, ?rbh_lt by rep_lia; unfold bool2val in *;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b)
                       | |- context [zeq ?a ?b] => destruct (zeq a b)
                       | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
                       | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
                       | H: context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
                       | H: context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b) end;
  simpl in *; try lia; try discriminate; try reflexivity; try congruence.

(* two ints of unsigned values are equal exactly when the values are *)
Lemma rbh_repr_eq a b: 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  (Int.repr a = Int.repr b <-> a = b).
Proof.
  intros. split; [ | intros ->; reflexivity].
  intros E. apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by lia. exact E.
Qed.

(* Byte arrays and their malloc tokens are the same at the units' compspecs (the byte helpers are specified at
   the adler32 unit's, inflateInit2_'s version string at the inflate unit's) and at the law's. *)
Lemma rbh_bytes_a sh n (c: list val) p:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) c p = @data_at CS sh (tarray tuchar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_adler32 sh (tarray tuchar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma rbh_tok_a sh n p:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) p = @malloc_token CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CC_adler32) by reflexivity. reflexivity. Qed.

Lemma rbh_chars_i sh n (c: list val) p:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) c p = @data_at CS sh (tarray tschar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_inflate sh (tarray tschar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* struct z_stream: laws_common.h's view (compress unit) and inflate.c's (inflate unit) are the law's *)
Lemma rbh_zs_c sh (v: @reptype Zlib.units.Compress.CS t_zs) p:
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at CS sh (Tstruct _z_stream_s noattr) v p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_compress sh t_zs); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma rbh_zs_i sh (v: @reptype Zlib.units.Inflate.CS t_strm) p:
  @data_at Zlib.units.Inflate.CS sh t_strm v p = @data_at CS sh (Tstruct _z_stream_s noattr) v p.
Proof.
  erewrite (@data_at_change_composite _ _ CC_inflate sh t_strm); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* the local z_stream before new_stream: every member undefined *)
Lemma rbh_strm_undef p:
  @data_at_ CS Tsh (Tstruct _z_stream_s noattr) p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite rbh_zs_c. reflexivity. Qed.

(* raw_strm (inflate.c's view of struct z_stream) is laws_common.h's view *)
Lemma rbh_raw_zs gv sh p r msgv stv za zf opq:
  raw_strm gv sh p r msgv stv za zf opq =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val (rf_ni r) (rf_ai r) (rf_tin r) (rf_no r) (rf_ao r) (rf_tout r) msgv stv za zf opq
            (rf_dt r) (rf_adler r) (rf_res r)) p.
Proof. unfold raw_strm. rewrite rbh_zs_i, rbh_zs_c. reflexivity. Qed.

(* a stream left by a failed inflateInit2_ is the local variable's memory *)
Lemma rbh_init_fail_mem gv p r msgv stv opq ret sp w:
  isptr p -> ret <> Z_OK ->
  init_mem gv Tsh p r msgv stv opq ret sp w |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) p.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec p nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; rewrite rbh_zs_i; apply data_at_data_at_ | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; rewrite rbh_zs_i; apply data_at_data_at_ | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; rewrite rbh_zs_i; apply data_at_data_at_.
Qed.

Lemma rbh_init_ok gv p r msgv stv opq sp w: isptr p ->
  init_mem gv Tsh p r msgv stv opq Z_OK sp w =
  istream_raw gv Tsh p (raw_after_init r (l_s (init_live sp w))) (init_live sp w).
Proof. intros. unfold init_mem. rewrite if_false by (destruct p; try contradiction; discriminate). reflexivity. Qed.

(* the windowBits of the law: inflateInit2_ accepts them, with a zlib wrapper (wrap 5 or 7: adler = 1 after
   the init) and no gz_header *)
Lemma rbh_init_facts sp w: rbh_wbits w ->
  wbits_ok w = true /\ (i_wrap (l_s (init_live sp w)) =? 0) = false /\
  Z.land (i_wrap (l_s (init_live sp w))) 1 = 1 /\ i_head (l_s (init_live sp w)) = false.
Proof.
  intros [Hw0 [Hw16 Hw15]].
  assert (Hc: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15 \/ w = 16 \/ w = 17 \/ w = 18 \/ w = 19 \/ w = 20 \/ w = 21 \/ w = 22 \/ w = 23 \/ w = 24 \/ w = 25 \/ w = 26 \/ w = 27 \/ w = 28 \/ w = 29 \/ w = 30 \/ w = 31 \/ w = 32 \/ w = 33 \/ w = 34 \/ w = 35 \/ w = 36 \/ w = 37 \/ w = 38 \/ w = 39 \/ w = 40 \/ w = 41 \/ w = 42 \/ w = 43 \/ w = 44 \/ w = 45 \/ w = 46 \/ w = 47) by lia.
  repeat destruct Hc as [-> | Hc]; try (subst w); cbv in Hw16, Hw15;
    first [ discriminate Hw16 | exfalso; destruct Hw15 as [Hx | Hx]; [discriminate Hx | apply Hx; reflexivity]
          | split3; [reflexivity | reflexivity | split; reflexivity] ].
Qed.

Lemma rbh_init_ret p w a: isptr p -> rbh_wbits w ->
  init_ret p 49 112 w a = if a then Z_OK else Z_MEM_ERROR.
Proof.
  intros P Hw. destruct (rbh_init_facts nullval w Hw) as [Hok _].
  unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct p; try contradiction; discriminate). rewrite Hok. destruct a; reflexivity.
Qed.

(* the stream after inflateInit2_ and offer: an istream with the input and output space offered *)
Definition rbh_z (input: val) (inl: Z) (out: val) (room: Z) : zfields :=
  ZF input inl 0 out room 0 None 0 1 Vundef.

Lemma rbh_offer_istream gv p L input inl out room:
  live_ok L -> 0 <= inl <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val input (Vint (Int.repr inl)) (Vlong (Int64.repr 0)) out (Vint (Int.repr room)) (Vlong (Int64.repr 0))
            nullval (l_sp L) (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval
            (Vint (Int.repr 0)) (Vlong (Int64.repr 1)) Vundef) p * state_mem gv p L
  |-- istream gv Tsh p (rbh_z input inl out room) (Some L).
Proof.
  intros HL Hi Ho. unfold rbh_z.
  rewrite <- istream_raw_istream by (try reflexivity; unfold zf_ok; simpl; rep_lia).
  unfold istream_raw. rewrite rbh_raw_zs. simpl. entailer!.
Qed.

(* the stream after inflateInit2_ is wrapped (not raw) and in mode HEAD, which inflate_specW's swfW accepts *)
Lemma rbh_not_raw L: (i_wrap (l_s L) =? 0) = false -> raw_live (Some L) = false.
Proof. intros H. exact H. Qed.

Lemma rbh_swfW sp w: swfW (l_s (init_live sp w)).
Proof.
  assert (Hm: i_mode (l_s (init_live sp w)) = HEAD).
  { unfold init_live. destruct (reset2_wb w) as [[? ?] | ]; reflexivity. }
  unfold swfW. rewrite Hm. split; intro X; discriminate X.
Qed.

Lemma rbh_is_live p st: isptr p -> is_live p st = st.
Proof. intros. unfold is_live. rewrite if_false by (destruct p; try contradiction; discriminate). reflexivity. Qed.

(* the input and the output space as inflate()'s buffers, before the call and after a call that wrote nothing *)
Lemma rbh_bufs L input inl inp out room obs:
  Zlength obs = room ->
  bufs_opt (Some L) (InBuf Ews input 0 inl (bytes_rep inp)) (Some (OutBuf Ews out 0 room (bytes_rep obs))) []
    false true =
  (@data_at CS Ews (tarray tuchar inl) (bytes_rep inp) input *
   @data_at CS Ews (tarray tuchar room) (bytes_rep obs) out *
   @malloc_token CS Ews (tarray tuchar room) out)%logic.
Proof.
  intros Ho. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite sublist_nil, Zlength_nil, Z.add_0_r, sublist_same by (rewrite ?Zlength_bytes_rep; lia).
  simpl app. rewrite sepcon_emp.
  f_equal.
Qed.

(* q = any_bytes(len), as two steps: the call (its result in the temp t) and the assignment of t to the
   variable (a single forward_call stalls proving the type of the result, which is NULL or a pointer
   according to the if in the SEP) *)
Ltac rbh_new_bytes t len gv call :=
  repeat (apply -> seq_assoc);
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX q: val, EX bs: list Z,
             PROPx ((Zlength bs = len) :: is_bytes bs :: is_pointer_or_null q :: P)
             (LOCALx (temp t q :: Q)
             (SEPx ((if eq_dec q nullval then emp
                     else (malloc_token Ews (tarray tuchar len) q *
                           data_at Ews (tarray tuchar len) (bytes_rep bs) q)) :: R))))
  end;
  [ call; let v := fresh "v" in Intros v; rewrite ?rbh_bytes_a, ?rbh_tok_a;
    Exists (fst v) (snd v); destruct (eq_dec (fst v) nullval); entailer!
  | ].

(* the move of the byte helpers' arguments from the law's compspecs to the adler32 unit's (forward_call
   looks for it) *)
#[local] Instance CC_to_adler32 : change_composite_env CS Zlib.units.Adler32.CS.
  make_cs_preserve CS Zlib.units.Adler32.CS. Defined.

(* after gp_assume(c) with c a boolean of the harness: the boolean holds *)
Ltac rbh_assumed :=
  match goal with Hx: Int.repr (Z.b2z _) <> Int.zero |- _ => revert Hx end;
  rbh_bool; intros X; contradiction X; reflexivity.

Lemma body_main : rbh_main_stmt.
Proof.
  unfold rbh_main_stmt.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  (* window_bits = (int) upto(47): the call, then the cast *)
  apply -> seq_assoc. apply -> seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX wb: Z, PROPx ((0 <= wb <= 47) :: P) (LOCALx (temp _t'1 (Vlong (Int64.repr wb)) :: Q) (SEPx R)))
  end.
  { forward_call 47. Intros wb. Exists wb. entailer!. }
  Intros wb. forward. forward.
  rewrite Int64.unsigned_repr by rep_lia.
  set (low := Z.land wb 15).
  assert (Hlow: 0 <= low <= 15) by (unfold low; apply rbh_land15).
  rewrite !rbh_and by rep_lia. fold low.
  pose proof (rbh_land16 wb ltac:(lia)) as H16.
  ifpost _t'2 (Int.repr (if andb (Z.land wb 16 =? 0) (orb (low =? 0) (8 <=? low)) then 1 else 0)).
  { rewrite rbh_and in H0 by rep_lia. apply rbh_repr_eq in H0; try rep_lia. forward_if.
    + forward. entailer!. rewrite H0, H1. reflexivity.
    + forward. forward. entailer!. rewrite H0. destruct (Z.eqb_spec low 0); [lia | ].
      destruct (zlt low 8), (Z.leb_spec 8 low); try lia; reflexivity. }
  { forward. entailer!. rewrite rbh_and in H0 by rep_lia.
    destruct (Z.eqb_spec (Z.land wb 16) 0) as [E | ]; [rewrite E in H0; contradiction | ]. reflexivity. }
  forward_call (Int.repr (if andb (Z.land wb 16 =? 0) (orb (low =? 0) (8 <=? low)) then 1 else 0)).
  assumed.
  assert (Hwb: rbh_wbits wb).
  { apply andb_prop in E as [E1 E2]. apply orb_prop in E2. apply Z.eqb_eq in E1.
    destruct E2 as [E2 | E2]; [apply Z.eqb_eq in E2 | apply Z.leb_le in E2]; split3; auto. }
  clear E.
  (* input_len = 2 + upto(UINT_MAX - 2) *)
  forward_call (Int.max_unsigned - 2). Intros n.
  forward.
  (* room = nondet_u32(): the call, then the widening cast *)
  apply -> seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX r: Z, PROPx ((0 <= r <= Int.max_unsigned) :: P)
                       (LOCALx (temp _room (Vlong (Int64.repr r)) :: temp _t'4 (Vint (Int.repr r)) :: Q) (SEPx R)))
  end.
  { forward_call tt. Intros r. forward. Exists r. entailer!. }
  Intros room.
  replace (Int64.add (Int64.repr (Int.signed (Int.repr 2))) (Int64.repr n)) with (Int64.repr (2 + n))
    by (rewrite Int.signed_repr by rep_lia; rewrite Int64.add_signed, !Int64.signed_repr by rep_lia; reflexivity).
  (* input = any_bytes(input_len); out = any_bytes(room) *)
  rbh_new_bytes _t'5 (2 + n) gv ltac:(forward_call (2 + n, gv)).
  Intros input inp. forward.
  rbh_new_bytes _t'6 room gv ltac:(forward_call (room, gv)).
  Intros out obs. forward.
  (* if (input == NULL || out == NULL) return 0; *)
  destruct (eq_dec input nullval) as [PI | PI].
  { subst input.
    ifpost _t'7 (Int.repr 1).
    - forward. entailer!.
    - contradiction.
    - forward_if False; [ret0 | discriminate]. }
  Intros.
  destruct (eq_dec out nullval) as [PO | PO].
  { subst out.
    ifpost _t'7 (Int.repr 1).
    - congruence.
    - forward. entailer!.
    - forward_if False; [ret0 | discriminate]. }
  Intros.
  assert_PROP (isptr out) as Pout by entailer!.
  assert_PROP (isptr input) as Pin by entailer!.
  ifpost _t'7 (Int.repr 0).
  { congruence. }
  { forward. entailer!. destruct out; try contradiction; reflexivity. }
  forward_if True; [congruence | forward; entailer! | ].
  (* before = copy_of(out, room); if (before == NULL) return 0; *)
  assert (CBo: cbuf_ok false out Ews out 0 room room (bytes_rep obs) obs)
    by (subst room; apply cbuf_ok_whole; auto).
  repeat (apply -> seq_assoc).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX q: val,
             PROPx (is_pointer_or_null q :: P)
             (LOCALx (temp _t'8 q :: Q)
             (SEPx ((if eq_dec q nullval then emp
                     else (malloc_token Ews (tarray tuchar room) q *
                           data_at Ews (tarray tuchar room) (bytes_rep obs) q)) :: R))))
  end.
  { forward_call (out, Ews, out, 0, room, bytes_rep obs, room, obs, gv).
    Intros q. rewrite ?rbh_bytes_a, ?rbh_tok_a. Exists q. destruct (eq_dec q nullval); entailer!. }
  Intros before. forward.
  destruct (eq_dec before nullval) as [PB | PB].
  { subst before. forward_if False; [ret0 | congruence]. }
  Intros.
  forward_if True.
  { subst before. congruence. }
  { forward. entailer!. }
  (* the header bytes *)
  assert (Hb0: 0 <= Znth 0 inp <= 255) by (apply (is_bytes_Znth inp); auto; lia).
  assert (Hb1: 0 <= Znth 1 inp <= 255) by (apply (is_bytes_Znth inp); auto; lia).
  forward.
  { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite Znth_bytes_rep by lia.
  forward.
  { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite Znth_bytes_rep by lia.
  forward. forward. forward.
  set (b0 := Znth 0 inp) in *. set (b1 := Znth 1 inp) in *.
  rewrite rbh_shru, rbh_modu, rbh_and by rep_lia.
  pose proof (Z.mod_pos_bound (b0 * 256 + b1) 31 ltac:(lia)) as Hm31.
  pose proof (rbh_land15 b0) as Hcm.
  rewrite !rbh_eq by rep_lia.
  pose proof (rbh_shiftr4 b0 Hb0) as Hci.
  set (cinfo := Z.shiftr b0 4) in *.
  (* bad_window *)
  ifpost _t'9 (Int.repr (Z.b2z (orb (7 <? cinfo) (andb (negb (low =? 0)) (low <? cinfo + 8))))).
  { forward. entailer!. rbh_bool. }
  { forward_if.
    { forward. forward. entailer!. rbh_bool. }
    { forward. entailer!. rbh_bool. } }
  forward.
  (* gp_assume(bad_check || bad_method || bad_window) *)
  ifpost _t'10 (Int.repr (Z.b2z (orb (negb ((b0 * 256 + b1) mod 31 =? 0)) (negb (Z.land b0 15 =? 8))))).
  { forward. entailer!. rbh_bool. }
  { forward. entailer!. rbh_bool. }
  ifpost _t'11 (Int.repr (Z.b2z (orb (orb (negb ((b0 * 256 + b1) mod 31 =? 0)) (negb (Z.land b0 15 =? 8)))
                                     (orb (7 <? cinfo) (andb (negb (low =? 0)) (low <? cinfo + 8)))))).
  { forward. entailer!. rbh_bool. }
  { forward. entailer!. rbh_bool. }
  forward_call (Int.repr (Z.b2z (orb (orb (negb ((b0 * 256 + b1) mod 31 =? 0)) (negb (Z.land b0 15 =? 8)))
                                     (orb (7 <? cinfo) (andb (negb (low =? 0)) (low <? cinfo + 8)))))).
  assert (Hbad: rbh_bad low b0 b1).
  { unfold rbh_bad. rbh_assumed. }
  (* gp_assume(window_bits < 32 || cmf != 0x1f || flg != 0x8b) *)
  ifpost _t'12 (Int.repr (Z.b2z (orb (wb <? 32) (negb (b0 =? 31))))).
  { forward. entailer!. rbh_bool. }
  { forward. entailer!. rbh_bool. }
  ifpost _t'13 (Int.repr (Z.b2z (orb (orb (wb <? 32) (negb (b0 =? 31))) (negb (b1 =? 139))))).
  { forward. entailer!. rbh_bool. }
  { forward. entailer!. rbh_bool. }
  forward_call (Int.repr (Z.b2z (orb (orb (wb <? 32) (negb (b0 =? 31))) (negb (b1 =? 139))))).
  assert (Hgz: wb < 32 \/ b0 <> 31 \/ b1 <> 139).
  { rbh_assumed. }
  clear H6 H7.
  (* new_stream(&strm) *)
  rewrite rbh_strm_undef.
  forward_call (v_strm, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  unfold rbh_hversion_lit. rewrite <- rbh_chars_i.
  assert_PROP (isptr (gv ___stringlit_rj_bad_header_1)) as Pver by entailer!.
  assert_PROP (isptr v_strm) as Pstrm by entailer!.
  (* if (inflateInit2(&strm, window_bits) != Z_OK) return 0; *)
  forward_call (gv, Tsh, v_strm,
                RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef,
                Vundef, Vundef, nullval, wb, gv ___stringlit_rj_bad_header_1, Ers,
                map (fun c : Z => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by (destruct v_strm; try contradiction; discriminate). rewrite rbh_raw_zs. cancel. }
  { repeat split; auto; change (Zlength _) with 6; rep_lia. }
  Intros vret. destruct vret as [aok sp]. simpl fst in *; simpl snd in *.
  rewrite rbh_init_ret by auto.
  destruct aok.
  2: { forward_if False.
       { forward. Exists (Int.repr 0).
         sep_apply (rbh_init_fail_mem gv v_strm
           (RF nullval (Vint (Int.repr 0)) Vundef nullval (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef)
           Vundef Vundef nullval Z_MEM_ERROR sp wb Pstrm ltac:(discriminate)).
         entailer!. }
       { congruence. } }
  forward_if True.
  { congruence. }
  { forward. entailer!. }
  rewrite rbh_init_ok by auto.
  destruct (rbh_init_facts sp wb Hwb) as [_ [Hwr [Had Hhd]]].
  set (L := init_live sp wb) in *.
  unfold istream_raw. Intros.
  rewrite rbh_raw_zs. unfold raw_after_init. rewrite Hwr, Had.
  cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res].
  (* offer(&strm, input, input_len, out, room) *)
  forward_call (v_strm, Tsh, input, 2 + n, out, room, nullval, Vint (Int.repr 0), Vlong (Int64.repr 0), nullval,
                Vint (Int.repr 0), Vlong (Int64.repr 0), nullval, l_sp L, gv Zlib.inflate.code._zcalloc,
                gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr 0), Vlong (Int64.repr 1), Vundef).
  sep_apply (rbh_offer_istream gv v_strm L input (2 + n) out room ltac:(assumption) ltac:(rep_lia) ltac:(rep_lia)).
  (* code = inflate(&strm, (int) nondet_u32()) *)
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ib := InBuf Ews input 0 (2 + n) (bytes_rep inp)).
  set (ob := OutBuf Ews out 0 room (bytes_rep obs)).
  forward_call (gv, Tsh, v_strm, rbh_z input (2 + n) out room, Vundef, Some L, ib, inp, Some ob, flush, Ers, Ers,
                false, true).
  { unfold istreamA_opt. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
    rewrite istreamA_istream by (apply rbh_not_raw; exact Hwr).
    rewrite rbh_is_live by auto. unfold head_opt, head_mem. rewrite Hhd.
    unfold ib, ob. rewrite rbh_bufs by auto. cancel. }
  { unfold ib, ob, rbh_z, in_tok_ok, in_ok, out_ok, in_ptr, out_ptr. cbn [zf_ni zf_ai zf_no zf_ao].
    rewrite !Z.add_0_l, !isptr_offset_val_zero by auto.
    rewrite H2, sublist_same by (rewrite ?Zlength_bytes_rep; lia).
    rewrite !Zlength_bytes_rep.
    repeat match goal with |- _ /\ _ => split end; auto; try rep_lia; try lia; apply rbh_swfW. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into Hrel end.
  match goal with Hr: raw_live _ = raw_live _ |- _ => rename Hr into Hraw end.
  destruct Hrel as [[Hib _] | [_ [L' [o [res [winp [E1 [E2 [Hrun [_ [Er [Eow [Ez [_ Est]]]]]]]]]]]]]].
  { exfalso. unfold inflate_bad in Hib. rewrite rbh_is_live in Hib by auto.
    destruct Hib as [Hib | [Hib | [Hib _]]]; discriminate. }
  injection E1 as E1. injection E2 as E2. subst L' o.
  (* the call: RBHTheory.rbh_theory *)
  destruct (rbh_theory flush lenfix_list distfix_list (rbh_z input (2 + n) out room) sp wb inp res)
    as [Hret [How Htout]]; auto; try lia.
  subst r ow z' st'.
  rewrite How. rewrite !rbh_is_live by auto. unfold ib, ob. rewrite rbh_bufs by auto.
  unfold istreamA_opt. rewrite if_false by (destruct v_strm; try contradiction; discriminate).
  rewrite istreamA_istream by (rewrite Hraw; apply rbh_not_raw; exact Hwr).
  unfold istream. Intros. unfold zstrm_at, strm_rep. rewrite rbh_zs_i.
  change (zf_tout (z_after ?z ?ib ?o res)) with (m_tout (r_m res)). rewrite Htout.
  rewrite Hret.
  forward.
  assert_PROP (isptr before) as Pbef by entailer!.
  (* gp_assert(code == Z_DATA_ERROR && strm.total_out == 0 && bytes_eq(out, before, room)) *)
  ifpost _t'17 (Int.repr 1).
  { forward. forward. entailer!. }
  { exfalso. match goal with Hx: Int.repr _ <> Int.neg _ |- _ => apply Hx; reflexivity end. }
  ifpost _t'18 (Int.repr 1).
  { forward_call (out, Ews, out, 0, room, bytes_rep obs, obs, before, Ews, before, 0, room, bytes_rep obs, obs, room).
    { rewrite <- H4. apply cbuf_ok_whole; auto. }
    destruct (list_eq_dec Z.eq_dec obs obs) as [_ | Hne]; [ | contradiction Hne; reflexivity].
    forward. entailer!. }
  { exfalso. match goal with Hx: Int.repr 1 = _ |- _ => exact (Int.one_not_zero Hx) end. }
  forward_call (Int.repr 1).
  (* return 0: the local z_stream is given back, the rest goes to TT *)
  match goal with |- context [data_at Tsh (Tstruct _z_stream_s noattr) ?v v_strm] =>
    sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr) v v_strm) end.
  forward. Exists (Int.repr 0). entailer!.
Qed.

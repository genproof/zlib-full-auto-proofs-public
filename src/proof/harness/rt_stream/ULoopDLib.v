(* Law rt_stream (data of any length), main's deflate loop (UMainKit.loopD): the facts the proofs of its pieces
   use (ULoopDDraw, ULoopDPrep, ULoopDCall, ULoopDTest): the invariant after the draws, the compressor's fields at
   the law's compspecs, the pointer arithmetic of the harness, and cstream folded and unfolded. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDKit.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* the draws of offered and flush when flush was not Z_FINISH: the invariant's facts hold for the new values
   (fin is None, since a Z_FINISH would have stayed); Z_FINISH comes only with all the data offered and a rest
   that one call can take *)
Lemma dl_redraw J u l off fl :
  dl_ok J u l -> dl_flush l <> Z_FINISH -> dl_off l <= off <= Zlength (su_data u) -> 0 <= fl <= 5 ->
  (fl = Z_FINISH -> off = Zlength (su_data u) /\ Zlength (su_data u) - Zlength (dl_D l) <= 4294967295) ->
  dl_ok J u (mkDL (dl_D l) (dl_O l) (dl_fin l) off fl (dl_msg l) (dl_c l)).
Proof.
  intros (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno) Hnf Hoff Hfl' Hfin4'.
  unfold dl_ok; cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c].
  repeat split; auto; try lia;
    match goal with
    | E : dl_fin l = Some ?R |- _ => destruct (Hfin R E); contradiction
    | E : fl = _ |- _ => destruct (Hfin4' E); auto
    end.
Qed.

(* the fields of the compressor main reads and writes, as deflate.c's specifications hold them (DCS.CS) and
   at the law's compspecs *)
Lemma ld_next_in_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) v p = @field_at CS Ews t_z (DOT _next_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma ld_avail_in_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_in) v p = @field_at CS Ews t_z (DOT _avail_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma ld_next_out_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) v p = @field_at CS Ews t_z (DOT _next_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma ld_avail_out_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_out) v p = @field_at CS Ews t_z (DOT _avail_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes offered and the room left *)
Lemma ld_ptr_sub (p : val) k m : isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. destruct p; try contradiction. simpl.
  unfold sem_sub_pp, sem_sub_default. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma ld_sameblock_off (p : val) k : isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* compressed + capacity: the pointer arithmetic on a byte object *)
Lemma ld_add_ptr_long_tuchar (p : val) (n : Z) :
  isptr p -> 0 <= n <= Int64.max_unsigned -> force_val (sem_add_ptr_long tuchar p (vl n)) = offset_val n p.
Proof.
  intros Pp Hn. destruct p; try contradiction. unfold sem_add_ptr_long, vl. simpl.
  f_equal. f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by lia. reflexivity.
Qed.

(* two pointers into or one past a malloc'ed byte object are weakly valid, so comparing them is defined *)
Local Transparent denote_tc_test_eq.
Lemma ld_test_eq (R : mpred) (p : val) (lo1 lo2 n : Z) (contents : list val) :
  0 <= lo1 <= n -> 0 <= lo2 <= n -> isptr p ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
  |-- denote_tc_test_eq (offset_val lo1 p) (offset_val lo2 p).
Proof.
  intros Hlo1 Hlo2 Pp.
  assert (W : forall lo, 0 <= lo <= n ->
              (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
              |-- weak_valid_pointer (offset_val lo p)).
  { intros lo Hlo. apply sepcon_weak_valid_pointer1.
    apply (cbuf_weak_valid true Ews Ews p lo n contents); auto. }
  destruct p; try contradiction. unfold denote_tc_test_eq, offset_val, test_eq_ptrs.
  unfold sameblock. destruct (peq b b) as [E | NE]; [ | congruence]. cbn [proj_sumbool].
  apply andp_right; [apply (W lo1 Hlo1) | apply (W lo2 Hlo2)].
Qed.
Local Opaque denote_tc_test_eq.

(* next_out == compressed + capacity, cast to _Bool: a boolean *)
Lemma ld_cmp_bool (p : val) a n : isptr p ->
  exists b : bool,
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr tuchar) (tptr tuchar) (offset_val a p)
                                    (eval_binop Oadd (tptr tuchar) tulong p (vl n))))
  = Vint (if b then Int.one else Int.zero).
Proof.
  intros Pp. destruct p; try contradiction.
  simpl. unfold sem_cmp_pp; simpl. rewrite peq_true. simpl.
  destruct (Ptrofs.eq _ _); [exists true | exists false]; reflexivity.
Qed.

Section DCSView.
#[local] Existing Instance Zlib.proof.deflate.DCS.CS.

(* the compressor's fields, as main read them, back into cstream *)
Lemma ld_cstream_fold gv vc s ni ain tin no aout tout msgv adler :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  dstream 2 (Some s) vc nullval gv * field_at Ews t_strm (DOT DC._next_in) ni vc *
  field_at Ews t_strm (DOT DC._avail_in) (vi ain) vc * field_at Ews t_strm (DOT DC._total_in) (vl tin) vc *
  field_at Ews t_strm (DOT DC._next_out) no vc * field_at Ews t_strm (DOT DC._avail_out) (vi aout) vc *
  field_at Ews t_strm (DOT DC._total_out) (vl tout) vc * field_at Ews t_strm (DOT DC._msg) msgv vc *
  field_at Ews t_strm (DOT DC._adler) (vl adler) vc * srest vc
  |-- cstream gv vc (mkCS s ni ain tin no aout tout msgv adler).
Proof. intros. unfold cstream, api_fields. simpl. entailer!. Qed.

End DCSView.

(* at a return: the compressor's struct back to the stack frame *)
Lemma ld_cstream_frame gv vc c : cstream gv vc c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc nullval gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite DCS.CS LawCS.CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm) by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(* the end of the body, to the loop's test: DK with the deflate result [code] and the state [l] *)
Ltac ld_cont code l :=
  forward; Exists code l;
  unfold DK, su_locals, lv_locals; simpl app;
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler];
  entailer!.

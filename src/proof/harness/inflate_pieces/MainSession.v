(* The laws rj_any_input and api_untouched_output, mains: what the helpers of harness/laws_session.h add to the
   kit of MainKit.v (round 4 of the harnesses).
   - the specifications main calls besides MainKit.Gk_of's: gp_assume, inflate_window_ok, position_of, unmoved
     (and api_untouched_output's accounted, bytes_eq);
   - the six members a struct position records, of the stream (pz_of) and as set_buffer() left them
     (pz_offer); the struct z_stream and the struct position at the helpers' compspecs (CS_session) and at the
     law's (per law: modules AnyS, UntS);
   - what inflate() gives for the position (Facts.pf_inflate): the members accounted (accounted_b), and none
     moved for an empty piece and no output space (unmoved_b); the comparability that unmoved and accounted
     need, lent from the input and output objects;
   - the loop invariant pk_inv4: MainKit.pk_inv with the local struct position `at` (any contents). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.crc32.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Zlib.proof.harness.inflate_pieces.MainCntLoop.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* main's callees besides MainKit.Gk_of's: rj_any_input's, api_untouched_output's *)
Definition Gk_extra_any : funspecs :=
  [gp_assume_spec; LS.inflate_window_ok_spec; LS.position_of_spec; LS.unmoved_spec].
Definition Gk_extra_unt : funspecs :=
  [bytes_eq_spec; gp_assume_spec; LS.inflate_window_ok_spec; LS.position_of_spec; LS.accounted_spec;
   LS.unmoved_spec].

Definition t_posl : type := Tstruct HL._position noattr.

(* ---------------------------------------------------------------------------------------------- *)
(* The position                                                                                    *)

(* the six members of the stream z *)
Definition pz_of (z: zfields) : LS.posz :=
  LS.mk_posz (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z).

(* the eight other members, as istreamA holds them (MainKit.pk_tup) *)
Definition rest_of (gv: globals) (z: zfields) (adv sp: val) : LS.zs_rest :=
  (msg_val gv (zf_msg z), sp, gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval,
   Vint (Int.repr (zf_dt z)), adv, zf_res z).

(* the members after set_buffer(strm, piece, take, outp, room) on the stream z *)
Definition pz_offer (z: zfields) (piece: val) (take: Z) (outp: val) (room: Z) : LS.posz :=
  LS.mk_posz piece take (zf_tin z) outp room (zf_tout z).

Lemma pz_offer_ok z piece take outp room :
  zf_ok z -> isptr piece -> isptr outp -> 0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  LS.posz_ok (pz_offer z piece take outp room).
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & _) Pp Po Ht Hr. unfold LS.posz_ok, pz_offer; cbn.
  repeat split; auto; rep_lia.
Qed.

(* what inflate() gives (Facts.pf_inflate) for the members of the stream after the call *)
Definition after_call (z z': zfields) (piece: val) (take: Z) (outp: val) (room: Z) : Prop :=
  0 <= zf_ai z' <= take /\ 0 <= zf_ao z' <= room /\
  zf_ni z' = offset_val (take - zf_ai z') piece /\ zf_no z' = offset_val (room - zf_ao z') outp /\
  zf_tin z' = (zf_tin z + (take - zf_ai z')) mod 2 ^ 64 /\
  zf_tout z' = (zf_tout z + (room - zf_ao z')) mod 2 ^ 64.

Lemma after_call_of z z' piece take data outp room bs :
  Zlength data = take ->
  0 <= zf_ai z' <= Zlength data -> 0 <= zf_ao z' <= room ->
  zf_ni z' = in_ptr (ib_of piece take data) (Zlength data - zf_ai z') ->
  zf_no z' = out_ptr (ob_of outp room bs) (room - zf_ao z') ->
  zf_tin z' = (zf_tin z + (Zlength data - zf_ai z')) mod 2 ^ 64 ->
  zf_tout z' = (zf_tout z + (room - zf_ao z')) mod 2 ^ 64 ->
  after_call z z' piece take outp room.
Proof.
  intros Hl A1 A2 A3 A4 A5 A6. subst take. unfold after_call, ib_of, ob_of, in_ptr, out_ptr in *.
  rewrite !Z.add_0_l in *. auto 10.
Qed.

Lemma pz_of_ok z z' piece take outp room :
  zf_ok z' -> isptr piece -> isptr outp -> after_call z z' piece take outp room -> LS.posz_ok (pz_of z').
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & _) Pp Po (_ & _ & Hni & Hno & _). unfold LS.posz_ok, pz_of; cbn.
  rewrite Hni, Hno. destruct piece, outp; try contradiction. repeat split; auto; rep_lia.
Qed.

(* accounted(&strm, &at) after the call: next + avail is what was offered, on both sides *)
Lemma accounted_after z z' piece take outp room :
  isptr piece -> isptr outp -> after_call z z' piece take outp room ->
  LS.accounted_b (pz_of z') (pz_offer z piece take outp room) = true.
Proof.
  intros Pp Po (A1 & A2 & Hni & Hno & _).
  unfold LS.accounted_b, pz_of, pz_offer, LS.ptr_eqb; cbn. rewrite Hni, Hno.
  rewrite !offset_offset_val. replace (take - zf_ai z' + zf_ai z') with take by lia.
  replace (room - zf_ao z' + zf_ao z') with room by lia.
  destruct (Val.eq _ _) as [_|N]; [|contradiction N; reflexivity].
  destruct (Val.eq _ _) as [_|N]; [|contradiction N; reflexivity].
  rewrite !(proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

(* the pointers accounted compares *)
Lemma accounted_ptrs z z' piece take outp room :
  isptr piece -> isptr outp -> after_call z z' piece take outp room ->
  offset_val (LS.pz_avail_in (pz_of z')) (LS.pz_next_in (pz_of z')) = offset_val take piece /\
  offset_val (LS.pz_avail_out (pz_of z')) (LS.pz_next_out (pz_of z')) = offset_val room outp.
Proof.
  intros Pp Po (A1 & A2 & Hni & Hno & _). unfold pz_of; cbn. rewrite Hni, Hno, !offset_offset_val.
  split; f_equal; lia.
Qed.

(* an empty piece and no output space: the stream's members after the call are the offered ones *)
Lemma unmoved_after z z' piece outp :
  zf_ok z -> isptr piece -> isptr outp -> after_call z z' piece 0 outp 0 ->
  pz_of z' = pz_offer z piece 0 outp 0.
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & _) Pp Po (A1 & A2 & Hni & Hno & Hti & Hto).
  assert (E1: zf_ai z' = 0) by lia. assert (E2: zf_ao z' = 0) by lia.
  unfold pz_of, pz_offer. rewrite Hni, Hno, Hti, Hto, E1, E2.
  rewrite !Z.sub_0_r, !Z.add_0_r, !Z.mod_small by rep_lia.
  destruct piece, outp; try contradiction. cbn. rewrite !Ptrofs.add_zero. reflexivity.
Qed.

(* inflate()'s return code: not Z_OK when nothing was offered (Progress.v's pieces_progress, with
   pf_inflate's bounds 0 <= avail_in' <= 0, 0 <= avail_out' <= 0) *)
Lemma unmoved_true z : LS.unmoved_b (pz_of z) (pz_of z) = true.
Proof. apply (proj2 (Zlib.proof.harness.laws_session.Facts.unmoved_b_iff _ _)). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The comparability lent to unmoved and accounted                                                *)

(* the input and output objects of a call, as one SEP item lent to the helpers *)
Definition io_objs {cs: compspecs} (piece: val) (take: Z) (cin: list val) (outp: val) (room: Z) (cout: list val)
    : mpred :=
  (malloc_token Ews (tarray tuchar take) piece * data_at Ews (tarray tuchar take) cin piece *
   malloc_token Ews (tarray tuchar room) outp * data_at Ews (tarray tuchar room) cout outp)%logic.

Lemma io_cmp_in {cs: compspecs} piece take cin outp room cout k :
  0 <= k <= take -> io_objs piece take cin outp room cout |-- denote_tc_test_eq (offset_val k piece) (offset_val k piece).
Proof.
  intros Hk. apply (Zlib.proof.harness.inflate_pieces.MainCntLoop.test_eq_self _ take); [lia | ].
  unfold io_objs. sep_apply (data_at_data_at_ Ews (tarray tuchar take) cin piece). cancel.
Qed.

Lemma io_cmp_out {cs: compspecs} piece take cin outp room cout k :
  0 <= k <= room -> io_objs piece take cin outp room cout |-- denote_tc_test_eq (offset_val k outp) (offset_val k outp).
Proof.
  intros Hk. apply (Zlib.proof.harness.inflate_pieces.MainCntLoop.test_eq_self _ room); [lia | ].
  unfold io_objs. sep_apply (data_at_data_at_ Ews (tarray tuchar room) cout outp). cancel.
Qed.

(* unmoved(&strm, &at) for an empty piece and no output space *)
Lemma io_lend_unmoved {cs: compspecs} z piece cin outp cout :
  isptr piece -> isptr outp ->
  io_objs piece 0 cin outp 0 cout |--
  io_objs piece 0 cin outp 0 cout && LS.unmoved_cmp (pz_offer z piece 0 outp 0) (pz_offer z piece 0 outp 0).
Proof.
  intros Pp Po. apply Zlib.proof.harness.laws_session.Facts.lend_cmp. unfold LS.unmoved_cmp, pz_offer; cbn.
  apply andp_right.
  - eapply derives_trans; [apply (io_cmp_in _ _ _ _ _ _ 0); lia | ].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - eapply derives_trans; [apply (io_cmp_out _ _ _ _ _ _ 0); lia | ].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
Qed.

(* accounted(&strm, &at) after any call *)
Lemma io_lend_accounted {cs: compspecs} z z' piece take cin outp room cout :
  isptr piece -> isptr outp -> after_call z z' piece take outp room ->
  io_objs piece take cin outp room cout |--
  io_objs piece take cin outp room cout && LS.accounted_cmp (pz_of z') (pz_offer z piece take outp room).
Proof.
  intros Pp Po A. pose proof A as (A1 & A2 & _).
  destruct (accounted_ptrs z z' piece take outp room Pp Po A) as [E1 E2].
  apply Zlib.proof.harness.laws_session.Facts.lend_cmp. unfold LS.accounted_cmp. rewrite E1, E2.
  unfold pz_offer; cbn. apply andp_right; [apply io_cmp_in | apply io_cmp_out]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop invariant                                                                              *)

Section Inv.
Context {cs: compspecs}.

(* MainKit.pk_inv with the struct position `at` (va; any contents) *)
Definition pk_inv4 (P: zfields -> live -> Prop) (gv: globals) (vs va inp: val) (src: list Z) (Fr: mpred)
    : environ -> mpred :=
  EX z: zfields, EX L: live,
  PROP (P z L; zf_ok z; 0 <= zf_tin z <= Zlength src)
  LOCAL (temp HL._input_len (Vlong (Int64.repr (Zlength src))); temp HL._input inp;
         temp HL._read (Vlong (Int64.repr (zf_tin z))); lvar HL._strm t_zsl vs; lvar HL._at t_posl va;
         gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) inp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp; data_at_ Tsh t_posl va; Fr).

End Inv.

(* gp_assume(c) of a known boolean: the case c = 1 *)
Ltac assumed_b := match goal with H: Int.repr (if ?c then 1 else 0) <> Int.zero |- _ =>
  let E := fresh "E" in destruct c eqn:E; [clear H | exfalso; apply H; reflexivity] end.

(* ---------------------------------------------------------------------------------------------- *)
(* The moves of the two structs between the helpers' compspecs and the law's                     *)

Ltac ses_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Module AnyS.
#[local] Existing Instance Any.CS.
#[export] Instance CC_session : change_composite_env LS.CS_session Any.CS.
  make_cs_preserve LS.CS_session Any.CS. Defined.

(* the stream as set_buffer() leaves it (compress unit's compspecs), as the helpers take it *)
Lemma set_ses sh ni ai ti no ao to msg st za zf op dt ad rs q:
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr ti)) no (Vint (Int.repr ao)) (Vlong (Int64.repr to))
       msg st za zf op dt ad rs) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (LS.mk_posz ni ai ti no ao to) (msg, st, za, zf, op, dt, ad, rs)) q.
Proof.
  unfold LS.zs_of; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
  change t_zs with t_zsl. rewrite AnyK.strm_cs_c. symmetry. ses_tac CC_session.
Qed.

(* a live stream's struct (MainKit.istreamA_unfold), as the helpers take it *)
Lemma pk_ses sh gv z adv sp q:
  @data_at Any.CS sh t_zsl (pk_tup gv z adv sp) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (pz_of z) (rest_of gv z adv sp)) q.
Proof. symmetry. change t_zs with t_zsl. ses_tac CC_session. Qed.

(* the local struct position *)
Lemma pos_ses_ sh q: @data_at_ Any.CS sh t_posl q = @data_at_ LS.CS_session sh LS.t_pos q.
Proof. unfold data_at_. symmetry. ses_tac CC_session. Qed.

Lemma pos_back sh v q: @data_at LS.CS_session sh LS.t_pos v q |-- @data_at_ Any.CS sh t_posl q.
Proof. rewrite pos_ses_. apply data_at_data_at_. Qed.
End AnyS.

Module UntS.
#[local] Existing Instance Unt.CS.
#[export] Instance CC_session : change_composite_env LS.CS_session Unt.CS.
  make_cs_preserve LS.CS_session Unt.CS. Defined.

Lemma set_ses sh ni ai ti no ao to msg st za zf op dt ad rs q:
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val ni (Vint (Int.repr ai)) (Vlong (Int64.repr ti)) no (Vint (Int.repr ao)) (Vlong (Int64.repr to))
       msg st za zf op dt ad rs) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (LS.mk_posz ni ai ti no ao to) (msg, st, za, zf, op, dt, ad, rs)) q.
Proof.
  unfold LS.zs_of; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
  change t_zs with t_zsl. rewrite UntK.strm_cs_c. symmetry. ses_tac CC_session.
Qed.

Lemma pk_ses sh gv z adv sp q:
  @data_at Unt.CS sh t_zsl (pk_tup gv z adv sp) q =
  @data_at LS.CS_session sh t_zs (LS.zs_of (pz_of z) (rest_of gv z adv sp)) q.
Proof. symmetry. change t_zs with t_zsl. ses_tac CC_session. Qed.

Lemma pos_ses_ sh q: @data_at_ Unt.CS sh t_posl q = @data_at_ LS.CS_session sh LS.t_pos q.
Proof. unfold data_at_. symmetry. ses_tac CC_session. Qed.

Lemma pos_back sh v q: @data_at LS.CS_session sh LS.t_pos v q |-- @data_at_ Unt.CS sh t_posl q.
Proof. rewrite pos_ses_. apply data_at_data_at_. Qed.
End UntS.

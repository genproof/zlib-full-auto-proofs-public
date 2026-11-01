(* Law rj_bad_block, main: helpers shared by the segment proofs of main (BBWSetup.v, BBWLoop.v, BBWTail.v): the
   moves of objects between the units' compspecs and the law's (BB.CS), facts on main's values and on the
   stream after inflateInit2_, and tactics (round 1's helpers of BBMain.v, with the inputs of BBWDefs.bbw_ok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.

(* ---------------------------------------------------------------------------------------------- *)
(* Moves between the compspecs of the units and the law's                                         *)

(* byte arrays and their malloc tokens: the byte helpers and the bit writer are specified at the adler32 unit's
   compspecs *)
Lemma bb_bytes_a sh n (c: list val) p:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) c p = @data_at BB.CS sh (tarray tuchar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_adler32 sh (tarray tuchar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma bb_tok_a sh n p:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) p = @malloc_token BB.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ BB.CC_adler32) by reflexivity. reflexivity. Qed.

(* the bit position, a size_t object *)
Lemma bb_ulong_a sh v p:
  @data_at Zlib.units.Adler32.CS sh tulong v p = @data_at BB.CS sh tulong v p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_adler32 sh tulong); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* the move of the byte helpers' and the bit writer's arguments from the law's compspecs to the adler32 unit's
   (forward_call looks for it) *)
#[export] Instance CC_to_adler32 : change_composite_env BB.CS Zlib.units.Adler32.CS.
  make_cs_preserve BB.CS Zlib.units.Adler32.CS. Defined.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts on main's values                                                                         *)

(* btype[kind], the block type of the kind *)
Lemma bb_btype_range kind : 0 <= kind <= 4 -> 0 <= bb_btype kind <= 3.
Proof.
  intros. unfold bb_btype.
  assert (kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4) as C by lia.
  repeat destruct C as [-> | C]; subst; cbv; split; discriminate.
Qed.

(* the stream after main's three conditional writes of the bad element is BBFacts.bb_bytes *)
Lemma bb_bytes_eq S0 kind which lits : 0 <= kind <= 4 ->
  let S2 := put_lits (put_bits_m S0 1 (bb_btype kind) 2 0) 3 lits in
  let b := 3 + lits_len lits in
  let S3 := if kind =? 2 then put_bits_m S2 b (198 + which) 8 1 else S2 in
  let S4 := if kind =? 3 then put_bits_m (put_bits_m S3 b 1 7 1) (b + 7) (30 + which) 5 1 else S3 in
  (if kind =? 4 then put_bits_m S4 b (30 + which) 5 0 else S4) = bb_bytes S0 kind which lits.
Proof.
  intros. cbv zeta. unfold bb_bytes.
  destruct (Z.eqb_spec kind 2), (Z.eqb_spec kind 3), (Z.eqb_spec kind 4); subst; try lia; reflexivity.
Qed.

(* the int arithmetic of kind 0's gp_assume on the bytes stream[1..4], as Z *)
Lemma bb_or_shl a b :
  Int.or (Int.repr a) (Int.shl (Int.repr b) (Int.repr 8)) = Int.repr (Z.lor a (Z.shiftl b 8)).
Proof.
  apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_or, Int.bits_shl by lia. change (Int.unsigned (Int.repr 8)) with 8.
  rewrite (Int.testbit_repr a), (Int.testbit_repr (Z.lor a (Z.shiftl b 8))) by lia.
  rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (zlt i 8).
  - rewrite (Z.testbit_neg_r b) by lia. reflexivity.
  - rewrite Int.testbit_repr by (unfold Int.zwordsize in *; simpl in *; lia). reflexivity.
Qed.

Lemma bb_not_mask v :
  Int.and (Int.not (Int.repr v)) (Int.repr 65535) = Int.repr (Z.land (Z.lnot v) 65535).
Proof.
  apply Int.same_bits_eq; intros i Hi.
  rewrite Int.bits_and, Int.bits_not by lia.
  rewrite !Int.testbit_repr by lia. rewrite Z.land_spec, Z.lnot_spec by lia. reflexivity.
Qed.

Lemma bb_assume_z b1 b2 b3 b4 :
  (if Int.eq (Int.or (Int.repr b1) (Int.shl (Int.repr b2) (Int.repr 8)))
             (Int.and (Int.not (Int.or (Int.repr b3) (Int.shl (Int.repr b4) (Int.repr 8)))) (Int.repr 65535))
   then Int.zero else Int.one) <> Int.zero ->
  Z.lor b1 (Z.shiftl b2 8) <> Z.land (Z.lnot (Z.lor b3 (Z.shiftl b4 8))) 65535.
Proof.
  intros H E. apply H. rewrite !bb_or_shl, bb_not_mask, E, Int.eq_true. reflexivity.
Qed.


(* the version literal, inflate.c's struct z_stream (inflate unit) and laws_common.h's (compress unit) are the
   law's *)
Lemma bb_chars_i sh n (c: list val) p:
  @data_at Zlib.units.Inflate.CS sh (tarray tschar n) c p = @data_at BB.CS sh (tarray tschar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_inflate sh (tarray tschar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma bb_bytes_i sh n (c: list val) p:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) c p = @data_at BB.CS sh (tarray tuchar n) c p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_inflate sh (tarray tuchar n)); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma bb_tok_i sh n p:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) p = @malloc_token BB.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ BB.CC_inflate) by reflexivity. reflexivity. Qed.

Lemma bb_zs_c sh (v: @reptype Zlib.units.Compress.CS t_zs) p:
  @data_at Zlib.units.Compress.CS sh t_zs v p = @data_at BB.CS sh (Tstruct BBC._z_stream_s noattr) v p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_compress sh t_zs); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

Lemma bb_zs_i sh (v: @reptype Zlib.units.Inflate.CS t_strm) p:
  @data_at Zlib.units.Inflate.CS sh t_strm v p = @data_at BB.CS sh (Tstruct BBC._z_stream_s noattr) v p.
Proof.
  erewrite (@data_at_change_composite _ _ BB.CC_inflate sh t_strm); [reflexivity | apply JMeq_refl | reflexivity].
Qed.

(* main's local z_stream before new_stream: every member undefined *)
Lemma bb_strm_undef p:
  @data_at_ BB.CS Tsh (Tstruct BBC._z_stream_s noattr) p =
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef Vundef) p.
Proof. rewrite bb_zs_c. reflexivity. Qed.

(* raw_strm (inflate.c's view of struct z_stream) is laws_common.h's view *)
Lemma bb_raw_zs gv sh p r msgv stv za zf opq:
  raw_strm gv sh p r msgv stv za zf opq =
  @data_at Zlib.units.Compress.CS sh t_zs
    (zs_val (rf_ni r) (rf_ai r) (rf_tin r) (rf_no r) (rf_ao r) (rf_tout r) msgv stv za zf opq
            (rf_dt r) (rf_adler r) (rf_res r)) p.
Proof. unfold raw_strm. rewrite bb_zs_i, bb_zs_c. reflexivity. Qed.

(* a stream left by a failed inflateInit2_ is main's local variable *)
Lemma bb_init_fail_mem gv p r msgv stv opq ret sp w:
  isptr p -> ret <> Z_OK ->
  init_mem gv Tsh p r msgv stv opq ret sp w |-- @data_at_ BB.CS Tsh (Tstruct BBC._z_stream_s noattr) p.
Proof.
  intros P Hr. unfold init_mem.
  destruct (eq_dec p nullval); [subst; contradiction | ].
  destruct (ret =? Z_VERSION_ERROR); [unfold raw_strm; rewrite bb_zs_i; apply data_at_data_at_ | ].
  destruct (ret =? Z_MEM_ERROR); [unfold raw_strm; rewrite bb_zs_i; apply data_at_data_at_ | ].
  destruct (Z.eqb_spec ret Z_OK); [contradiction | ].
  unfold raw_strm; rewrite bb_zs_i; apply data_at_data_at_.
Qed.

Lemma bb_init_ok gv p r msgv stv opq sp w: isptr p ->
  init_mem gv Tsh p r msgv stv opq Z_OK sp w =
  istream_raw gv Tsh p (raw_after_init r (l_s (init_live sp w))) (init_live sp w).
Proof. intros. unfold init_mem. rewrite if_false by (destruct p; try contradiction; discriminate). reflexivity. Qed.

(* the windowBits of the law (-15..-8): inflateInit2_ accepts them, a raw stream (wrap 0) in mode HEAD without a
   gz_header *)
Lemma bb_init_facts sp w: -15 <= w <= -8 ->
  wbits_ok w = true /\ i_wrap (l_s (init_live sp w)) = 0 /\
  i_mode (l_s (init_live sp w)) = Zlib.proof.inflate.Model.HEAD /\ i_head (l_s (init_live sp w)) = false.
Proof.
  intros Hw.
  assert (Hc: w = -15 \/ w = -14 \/ w = -13 \/ w = -12 \/ w = -11 \/ w = -10 \/ w = -9 \/ w = -8) by lia.
  repeat destruct Hc as [-> | Hc]; try subst w; split3; try split; reflexivity.
Qed.

Lemma bb_init_ret p w a: isptr p -> -15 <= w <= -8 ->
  init_ret p 49 112 w a = if a then Z_OK else Z_MEM_ERROR.
Proof.
  intros P Hw. destruct (bb_init_facts nullval w Hw) as [Hok _].
  unfold init_ret, sizeof_z_stream. simpl.
  rewrite if_false by (destruct p; try contradiction; discriminate). rewrite Hok. destruct a; reflexivity.
Qed.

(* the stream after inflateInit2_ and offer: inflate()'s istreamA with strm->adler undefined, the input and the
   output space offered *)
Definition bb_z (input: val) (inl: Z) (out: val) (room: Z) : zfields :=
  ZF input inl 0 out room 0 None 0 0 Vundef.

Lemma bb_offer_istream gv p L input inl out room:
  live_ok L -> i_wrap (l_s L) = 0 -> 0 <= inl <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  @data_at Zlib.units.Compress.CS Tsh t_zs
    (zs_val input (Vint (Int.repr inl)) (Vlong (Int64.repr 0)) out (Vint (Int.repr room)) (Vlong (Int64.repr 0))
            nullval (l_sp L) (gv Zlib.inflate.code._zcalloc) (gv Zlib.inflate.code._zcfree) nullval
            (Vint (Int.repr 0)) Vundef Vundef) p * state_mem gv p L
  |-- istreamA gv Tsh p (bb_z input inl out room) Vundef (Some L).
Proof.
  intros HL Hw Hi Ho. unfold istreamA, zstrm_atA, adler_v, raw_live, bb_z. rewrite Hw. simpl.
  rewrite bb_zs_i, bb_zs_c. entailer!. unfold zf_ok; simpl; rep_lia.
Qed.

(* the input and the output space as inflate()'s buffers, before a call and after one that wrote nothing *)
Lemma bb_bufs L stream lo n S out room c:
  Zlength c = room ->
  bufs_opt (Some L) (InBuf Ews stream lo n (bytes_rep S)) (Some (OutBuf Ews out 0 room c)) [] true true =
  (@data_at BB.CS Ews (tarray tuchar n) (bytes_rep S) stream * @data_at BB.CS Ews (tarray tuchar room) c out *
   @malloc_token BB.CS Ews (tarray tuchar n) stream * @malloc_token BB.CS Ews (tarray tuchar room) out)%logic.
Proof.
  intros Ho. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite sublist_nil, Zlength_nil, Z.add_0_r, sublist_same by lia. simpl app.
  rewrite !bb_bytes_i, !bb_tok_i. reflexivity.
Qed.

(* main's local z_stream given back at return *)
Lemma bb_istreamA_undef gv p z av L:
  istreamA gv Tsh p z av (Some L) |-- @data_at_ BB.CS Tsh (Tstruct BBC._z_stream_s noattr) p * TT.
Proof.
  unfold istreamA, zstrm_atA. Intros. rewrite bb_zs_i. sep_apply data_at_data_at_. cancel.
Qed.

(* the bytes main offers to inflate(): as many as the arbitrary ones it drew *)
Lemma bb_bytes_ok S0 kind which lits : bbw_ok S0 kind which lits ->
  Zlength (bb_bytes S0 kind which lits) = Zlength S0 /\ is_bytes (bb_bytes S0 kind which lits).
Proof.
  intros (Hk & Hw & Hn & Hl & H0 & Hz & _).
  pose proof (lits_len_bounds lits) as Bl. pose proof (bb_btype_range kind Hk).
  destruct (put_bits_m_ok S0 1 (bb_btype kind) 2 0 H0 ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 B1].
  destruct (put_lits_ok lits _ 3 B1 ltac:(lia) ltac:(lia)) as [L2 B2].
  unfold bb_bytes; cbv zeta.
  destruct (kind =? 2); [ | destruct (kind =? 3); [ | destruct (kind =? 4)]].
  - destruct (put_bits_m_ok _ (3 + lits_len lits) (198 + which) 8 1 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L3 B3].
    split; [lia | exact B3].
  - destruct (put_bits_m_ok _ (3 + lits_len lits) 1 7 1 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L3 B3].
    destruct (put_bits_m_ok _ (3 + lits_len lits + 7) (30 + which) 5 1 B3 ltac:(lia) ltac:(lia) ltac:(lia))
      as [L4 B4].
    split; [lia | exact B4].
  - destruct (put_bits_m_ok _ (3 + lits_len lits) (30 + which) 5 0 B2 ltac:(lia) ltac:(lia) ltac:(lia)) as [L3 B3].
    split; [lia | exact B3].
  - split; [lia | exact B2].
Qed.

(* a pointer returned by an allocation, not NULL *)
Lemma bb_isptr p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. destruct p; simpl; intros; auto; subst; contradiction. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactics of main's proof                                                                        *)

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which takes minutes on main's
   LOCAL lists; the same list built syntactically, comparing the identifiers by vm_compute *)
Ltac bb_rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := bb_rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := bb_rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := bb_rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* [Q] without the binding of the temporary [t] *)
Ltac bb_rm_temp t Q :=
  lazymatch Q with
  | temp t _ :: ?Q' => Q'
  | ?a :: ?Q' => let r := bb_rm_temp t Q' in constr:(a :: r)
  | nil => constr:(@nil localdef)
  end.

(* forward over an [if] after which the temporary [t] is [v] *)
Ltac bb_if t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    let Q' := bb_rm_temp t Q in forward_if (PROPx P (LOCALx (temp t v :: Q') (SEPx R))) end.

(* a goal on comparisons of Z values, by cases on them *)
Ltac bb_zcase :=
  unfold bool2val in *;
  repeat match goal with
         | |- context [zeq ?a ?b] => destruct (zeq a b)
         | |- context [zlt ?a ?b] => destruct (zlt a b)
         | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
         | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
         | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
         | H: context [zeq ?a ?b] |- _ => destruct (zeq a b)
         | H: context [zlt ?a ?b] |- _ => destruct (zlt a b)
         | H: context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
         | H: context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b)
         | H: context [?a <=? ?b] |- _ => destruct (Z.leb_spec a b)
         end; simpl in *; try lia; try reflexivity; try congruence.

(* q = any_bytes(len) alone, its result in the temp t (a single forward_call stalls proving the type of the
   result, which is NULL or a pointer according to the if in the SEP) *)
Ltac bb_new_bytes t len gv :=
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
  [ forward_call (len, gv); let v := fresh "v" in Intros v; rewrite ?bb_bytes_a, ?bb_tok_a;
    Exists (fst v) (snd v); destruct (eq_dec (fst v) nullval); entailer!
  | ].

(* a branch that cannot be taken *)
Ltac bb_infeas :=
  exfalso;
  first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
        | match goal with H: _ |- _ => solve [discriminate H] end
        | solve [congruence] | contradiction ].

(* t = upto(m) alone (main casts or uses t in the next statement): the call, its result in the temp t *)
Ltac bb_upto t m :=
  repeat (apply -> seq_assoc);
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    eapply semax_seq' with
      (P' := EX v: Z, PROPx ((0 <= v <= m) :: P) (LOCALx (temp t (Vlong (Int64.repr v)) :: Q) (SEPx R)))
  end;
  [ forward_call m; let v := fresh "v" in Intros v; Exists v; entailer! | ].


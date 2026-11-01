(* Law rj_bad_block, main: the kit of the do-while of inflate() calls (statement 29, BBWLoop.v).
   - the loop's body and its test (the condition after `while`), cut out of BBWKit.bbw_seg29;
   - bbw_C, the assertion between them: the values of in_rest and out_rest the body computed and the code the
     call returned, with what the theory (BBWDefs.bbw_post) says of that call;
   - the moves of the stream and of the two objects at the law's compspecs (BB.CS) between main's view and
     inflate()'s (istreamA, bufs_opt), the pointer differences main computes;
   - bbl_run2_frame: a call that returns Z_OK or Z_BUF_ERROR leaves the input, the output space and the
     gz_header flag of the machine as they were (URunFrame.run2_frame, without its hypothesis on the mode: from
     a mode outside HEAD..BAD the call returns Z_MEM_ERROR or Z_STREAM_ERROR at once). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.
Require Zlib.proof.uncompr.URunFrame.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The body and the test of the do-while                                                         *)

Definition bbl_body : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bbw_seg29] in
          (match bbw_seg29 with Ssequence (Sloop b _) _ => b | _ => Sskip end) in exact x).
Definition bbl_test : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bbw_seg29] in
          (match bbw_seg29 with Ssequence (Sloop _ t) _ => t | _ => Sskip end) in exact x).

Lemma bbl_seg29_eq : bbw_seg29 = Ssequence (Sloop bbl_body bbl_test) bbw_seg30.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertion after the body                                                                   *)

(* the call was offered min(ir, 2^32 - 1) input bytes and min(or, 2^32 - 1) bytes of output space, ir and or
   the rest of the stream and of the room before it; it returned code: Z_DATA_ERROR, or Z_OK / Z_BUF_ERROR with
   the invariant at the new position pos and output ob, and when nothing was clipped Z_OK with Z_TREES, the
   fields of a call that was offered everything, and the next call's Z_DATA_ERROR *)
Definition bbw_cpost (J: bbw_J) (strp outp: val) (S0: list Z) (kind which: Z) (lits: list Z) (room flush: Z)
    (ir or code pos: Z) (ob: list Z) (z: zfields) (L: live) : Prop :=
  code = Z_DATA_ERROR \/
  ((code = Z_OK \/ code = Z_BUF_ERROR) /\
   J S0 kind which lits pos ob (l_s L) /\ swfW (l_s L) /\ i_head (l_s L) = false /\
   0 <= pos <= Zlength S0 /\ Zlength ob <= room /\
   zf_ni z = offset_val pos strp /\ zf_no z = offset_val (Zlength ob) outp /\
   (ir <= Int.max_unsigned -> or <= Int.max_unsigned ->
    code = Z_OK /\ flush = Z_TREES /\ zf_ai z = Zlength S0 - pos /\ zf_ao z = room - Zlength ob /\
    bbw_extra S0 kind which lits pos ob (l_s L) flush)).

Definition bbw_C (J: bbw_J) (gv: globals) (vs vbt vbit strp outp: val) (S0: list Z) (kind which: Z)
    (lits: list Z) (room flush: Z) : environ -> mpred :=
  EX ir: Z, EX or: Z, EX code: Z, EX pos: Z, EX ob: list Z, EX z: zfields, EX L: live, EX oc: list val,
  PROP (bbw_cpost J strp outp S0 kind which lits room flush ir or code pos ob z L;
        0 <= ir <= Int64.max_unsigned; 0 <= or <= Int64.max_unsigned; Zlength oc = room)
  LOCAL (temp BBC._in_rest (Vlong (Int64.repr ir)); temp BBC._out_rest (Vlong (Int64.repr or));
         temp BBC._code (Vint (Int.repr code));
         temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._out outp; temp BBC._flush (Vint (Int.repr flush));
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); zfuncs gv; mem_mgr gv; tables_rep Ers gv; crc_table_at Ers gv;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (bb_bytes S0 kind which lits)) strp;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at Ews (tarray tuchar room) oc outp; malloc_token Ews (tarray tuchar room) outp;
       data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT).

(* the post of the loop as the segment lemma needs it *)
Definition bbl_R (gv: globals) (vs vbt vbit strp outp: val) (S0: list Z) (kind which: Z) (lits: list Z)
    (room flush: Z) : ret_assert :=
  overridePost (bbw_AT gv vs vbt vbit strp outp S0 kind which lits room flush) POST_B.

(* the two halves of the loop *)
Definition bbl_body_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_facts J -> bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush) bbl_body
    (loop1_ret_assert (bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush)
       (bbl_R gv vs vbt vbit strp outp S0 kind which lits room flush)).

Definition bbl_test_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush) bbl_test
    (loop2_ret_assert (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush)
       (bbl_R gv vs vbt vbit strp outp S0 kind which lits room flush)).

(* ---------------------------------------------------------------------------------------------- *)
(* One call of the model                                                                          *)

Lemma bbl_step_off flush fx dx fs m:
  ~ URunFrame.vmode (i_mode (m_s m)) ->
  exists r, step2 flush fx dx fs m = IRet r m /\ (r = Z_MEM_ERROR \/ r = Z_STREAM_ERROR).
Proof.
  intros V. unfold step2, m_mode. cbv zeta. set (md := i_mode (m_s m)) in *. clearbody md.
  unfold URunFrame.vmode in V.
  cbv [Zlib.proof.inflate.Model.HEAD Zlib.proof.inflate.Model.FLAGS Zlib.proof.inflate.Model.TIME
       Zlib.proof.inflate.Model.OS Zlib.proof.inflate.Model.EXLEN Zlib.proof.inflate.Model.EXTRA
       Zlib.proof.inflate.Model.NAME Zlib.proof.inflate.Model.COMMENT Zlib.proof.inflate.Model.HCRC
       Zlib.proof.inflate.Model.DICTID Zlib.proof.inflate.Model.DICT Zlib.proof.inflate.Model.TYPE
       Zlib.proof.inflate.Model.TYPEDO Zlib.proof.inflate.Model.STORED Zlib.proof.inflate.Model.COPY_
       Zlib.proof.inflate.Model.COPY Zlib.proof.inflate.Model.TABLE Zlib.proof.inflate.Model.LENLENS
       Zlib.proof.inflate.Model.CODELENS Zlib.proof.inflate.Model.LEN_ Zlib.proof.inflate.Model.LEN
       Zlib.proof.inflate.Model.LENEXT Zlib.proof.inflate.Model.DIST Zlib.proof.inflate.Model.DISTEXT
       Zlib.proof.inflate.Model.MATCH Zlib.proof.inflate.Model.LIT Zlib.proof.inflate.Model.CHECK
       Zlib.proof.inflate.Model.LENGTH Zlib.proof.inflate.Model.DONE Zlib.proof.inflate.Model.BAD
       Zlib.proof.inflate.Model.MEM] in *.
  repeat match goal with |- context [md =? ?k] => destruct (Z.eqb_spec md k); [try (exfalso; lia) | ] end;
    eexists; (split; [reflexivity | auto]).
Qed.

Lemma bbl_run2_frame flush fx dx m0 res:
  run2 flush fx dx m0 res -> r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR ->
  m_inp (r_m res) = m_inp m0 /\ m_aout (r_m res) = m_aout m0 /\ i_head (m_s (r_m res)) = i_head (m_s m0).
Proof.
  intros R Hr.
  destruct (Z_le_dec Zlib.proof.inflate.Model.HEAD (i_mode (m_s m0)));
    [destruct (Z_le_dec (i_mode (m_s m0)) Zlib.proof.inflate.Model.BAD) | ].
  - destruct (URunFrame.run2_frame flush fx dx m0 res ltac:(unfold URunFrame.vmode; lia) R) as (A & B & _ & D & _).
    auto.
  - exfalso. destruct (bbl_step_off flush fx dx (fast fx dx) m0 ltac:(unfold URunFrame.vmode; lia)) as (r & S & Er).
    destruct R as (o & L & E). inversion L; subst; unfold stepf2 in *; rewrite S in *; try discriminate.
    match goal with H: IRet _ _ = IRet _ _ |- _ => injection H as <- <- end.
    try subst res; simpl in Hr. unfold Z_OK, Z_BUF_ERROR, Z_MEM_ERROR, Z_STREAM_ERROR in *. lia.
  - exfalso. destruct (bbl_step_off flush fx dx (fast fx dx) m0 ltac:(unfold URunFrame.vmode; lia)) as (r & S & Er).
    destruct R as (o & L & E). inversion L; subst; unfold stepf2 in *; rewrite S in *; try discriminate.
    match goal with H: IRet _ _ = IRet _ _ |- _ => injection H as <- <- end.
    try subst res; simpl in Hr. unfold Z_OK, Z_BUF_ERROR, Z_MEM_ERROR, Z_STREAM_ERROR in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream at the law's compspecs                                                              *)

(* the 14 members of struct z_stream *)
Definition bbl_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

(* the struct as istreamA holds it *)
Definition bbl_tup (gv: globals) (z: zfields) (adv sp: val) : bbl_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma bbl_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsb (bbl_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. rewrite bb_zs_i.
  apply pred_ext; entailer!.
Qed.

Lemma bbl_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma bbl_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma bbl_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite bbl_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* the stream given back to main's stack frame, at a return *)
Lemma bbl_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsb vs * TT.
Proof.
  intros Pv. rewrite bbl_istreamA_opt_ptr by auto. unfold istreamA, zstrm_atA. rewrite bb_zs_i.
  destruct st; Intros; sep_apply (data_at_data_at_ shs t_zsb); cancel.
Qed.

(* the fields main offers: next_in, avail_in, next_out, avail_out *)
Definition bbl_offer_z (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

(* the struct after main's stores into avail_in / avail_out: the stream inflate() takes *)
Lemma bbl_offer_fold gv vs z L ni no ai ao:
  isptr vs -> zf_ok z -> live_ok L -> i_head (l_s L) = false ->
  0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  data_at Tsh t_zsb
    (ni, (Vint (Int.repr ai), (Vlong (Int64.repr (zf_tin z)), (no, (Vint (Int.repr ao),
     (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
     (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
     (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))) vs * state_mem gv vs L
  |-- istreamA_opt gv Tsh vs (bbl_offer_z z ni ai no ao) Vundef (Some L) *
      head_opt (is_live vs (Some L)).
Proof.
  intros Pv Zo Lo Hh Hai Hao.
  rewrite bbl_head_none, bbl_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  rewrite bbl_istreamA_unfold. unfold bbl_tup, bbl_offer_z, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

Lemma bbl_zf_ok gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st |-- !! zf_ok z.
Proof.
  intros Pv. rewrite bbl_istreamA_opt_ptr by auto. unfold istreamA. destruct st; entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream object and the output object as inflate()'s buffers                                 *)

(* the input: the stream S (|S0| bytes at strp), offered from pos on; the output: the room bytes at outp,
   the first |ob| written *)
Definition bbl_ib (strp: val) (n pos: Z) (S: list Z) : inbuf := InBuf Ews strp pos n (bytes_rep S).
Definition bbl_ob (outp: val) (room lo: Z) (oc: list val) : outbuf := OutBuf Ews outp lo room oc.

(* the output object after ow was written from lo on *)
Definition bbl_oc (room lo: Z) (oc: list val) (ow: list Z) : list val :=
  sublist 0 lo oc ++ byte_vals ow ++ sublist (lo + Zlength ow) room oc.

Lemma bbl_oc_len room lo (oc: list val) ow: Zlength oc = room -> 0 <= lo -> lo + Zlength ow <= room ->
  Zlength (bbl_oc room lo oc ow) = room.
Proof.
  intros Ho Hl Hw. pose proof (Zlength_nonneg ow). unfold bbl_oc, byte_vals.
  rewrite !Zlength_app, Zlength_map, !Zlength_sublist by lia. lia.
Qed.

Lemma bbl_bufs_pre vs L strp n pos S outp room lo (oc: list val):
  isptr vs -> Zlength oc = room -> 0 <= lo <= room ->
  data_at Ews (tarray tuchar n) (bytes_rep S) strp * malloc_token Ews (tarray tuchar n) strp *
  data_at Ews (tarray tuchar room) oc outp * malloc_token Ews (tarray tuchar room) outp
  |-- bufs_opt (is_live vs (Some L)) (bbl_ib strp n pos S) (Some (bbl_ob outp room lo oc)) [] true true.
Proof.
  intros Pv Ho Hl. rewrite bbl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, bbl_ib, bbl_ob.
  rewrite app_nil_l, Zlength_nil, Z.add_0_r.
  rewrite (sublist_rejoin 0 lo room) by lia.
  rewrite sublist_same by lia.
  cancel; apply derives_refl.
Qed.

Lemma bbl_bufs_post vs L strp n pos S outp room lo (oc: list val) ow:
  isptr vs ->
  bufs_opt (is_live vs (Some L)) (bbl_ib strp n pos S) (Some (bbl_ob outp room lo oc)) ow true true
  |-- data_at Ews (tarray tuchar n) (bytes_rep S) strp * malloc_token Ews (tarray tuchar n) strp *
      data_at Ews (tarray tuchar room) (bbl_oc room lo oc ow) outp * malloc_token Ews (tarray tuchar room) outp.
Proof.
  intros Pv. rewrite bbl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, bbl_ib, bbl_ob, bbl_oc.
  cancel; apply derives_refl.
Qed.

Lemma bbl_in_ok strp n pos len S: isptr strp -> Zlength S = n -> n <= Ptrofs.max_unsigned -> is_bytes S ->
  0 <= pos -> 0 <= len -> pos + len <= n ->
  in_ok (bbl_ib strp n pos S) (sublist pos (pos + len) S).
Proof.
  intros Pc Hn Hm BS Hp Hl Hpl. unfold in_ok, bbl_ib.
  assert (Hs: Zlength (sublist pos (pos + len) S) = len) by (rewrite Zlength_sublist; lia).
  rewrite Hs.
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [unfold bytes_rep; rewrite Zlength_map; lia | ]. split; [lia | ]. split.
  - unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. exact BS.
Qed.

Lemma bbl_out_ok outp room lo (oc: list val) ao: isptr outp -> room <= Ptrofs.max_unsigned -> Zlength oc = room ->
  0 <= lo -> 0 <= ao -> lo + ao <= room ->
  out_ok (bbl_ob outp room lo oc) ao.
Proof.
  intros Po Hn Ho Hl Ha Hao. unfold out_ok, bbl_ob.
  split; [apply writable_Ews | ]. repeat split; auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The pointer differences main computes                                                          *)

(* m - (size_t) (p + k - p) *)
Lemma bbl_ptr_sub (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
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

Lemma bbl_sameblock (p: val) k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* m - (size_t) (p + k - p), as main computes in_rest and out_rest *)
Lemma bbl_rest (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr m))
     (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite <- (bbl_ptr_sub p k m Pp Hk Hm).
  destruct p; try contradiction. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The body cut before the call                                                                   *)

(* the body: the rests, the two clip() pieces stored; then the call and the test of Z_MEM_ERROR *)
Definition bbl_call : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [bbl_body] in
          (match bbl_body with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ e))) => e | _ => Sskip end)
        in exact x).

(* before the call: the stream with the fields main offers, in inflate()'s view, and the two objects as its
   buffers *)
Definition bbl_mid (J: bbw_J) (gv: globals) (vs vbt vbit strp outp: val) (S0: list Z) (kind which: Z)
    (lits: list Z) (room flush: Z) : environ -> mpred :=
  EX pos: Z, EX ob: list Z, EX z: zfields, EX L: live, EX oc: list val,
  PROP (J S0 kind which lits pos ob (l_s L); swfW (l_s L); i_head (l_s L) = false;
        0 <= pos <= Zlength S0; Zlength ob <= room; Zlength oc = room; zf_ok z; live_ok L)
  LOCAL (temp BBC._in_rest (Vlong (Int64.repr (Zlength S0 - pos)));
         temp BBC._out_rest (Vlong (Int64.repr (room - Zlength ob)));
         temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._out outp; temp BBC._flush (Vint (Int.repr flush));
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (istreamA_opt gv Tsh vs
         (bbl_offer_z z (offset_val pos strp) (Z.min (Zlength S0 - pos) Int.max_unsigned)
            (offset_val (Zlength ob) outp) (Z.min (room - Zlength ob) Int.max_unsigned)) Vundef (Some L);
       head_opt (is_live vs (Some L));
       bufs_opt (is_live vs (Some L)) (bbl_ib strp (Zlength S0) pos (bb_bytes S0 kind which lits))
         (Some (bbl_ob outp room (Zlength ob) oc)) [] true true;
       zfuncs gv; mem_mgr gv; tables_rep Ers gv; crc_table_at Ers gv;
       data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT).

Definition bbl_call_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_facts J -> bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbl_mid J gv vs vbt vbit strp outp S0 kind which lits room flush) bbl_call
    (loop1_ret_assert (bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush)
       (bbl_R gv vs vbt vbit strp outp S0 kind which lits room flush)).

(* the statements before the call, from the loop's invariant to bbl_mid *)
Definition bbl_pre_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbl_mid J gv vs vbt vbit strp outp S0 kind which lits room flush) bbl_call
    (loop1_ret_assert (bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush)
       (bbl_R gv vs vbt vbit strp outp S0 kind which lits room flush)) ->
  semax bbw_Delta (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush) bbl_body
    (loop1_ret_assert (bbw_C J gv vs vbt vbit strp outp S0 kind which lits room flush)
       (bbl_R gv vs vbt vbit strp outp S0 kind which lits room flush)).

(* The branches of the header cases FLAGS, TIME, OS that round 1 excluded by the header pass (RTHSpec.hpass),
   for the cases over RTH9WKit.case_ok9v (docs/port-hl/rth9h/fto.py patches the ported RTHFTO6 with them):
   - NEEDBITS runs out of input ([semax_leave9]): the case breaks with leave = 1 in the same header mode, its
     machine the model's, and the header stays the partial one (RTH9HDefs.hd9 in a header mode is hd6);
   - FLAGS finds a method other than 8 or reserved flag bits ([semax_seq_bad9] with [bad_brk9_method] /
     [bad_brk9_hflags]): the case breaks in mode BAD without passing the header; the header is the raw one with
     done = 0 ([hd6_hd9_raw]: RTH9HDefs.hd9a's second disjunct);
   - the fall-through into the next header mode after INITBITS keeps InvW.hdrW ([hdrW_initbits9]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate.HdrSame5.
Require Import Zlib.proof.inflate.Steps2.
Require Import Zlib.proof.roundtrip.RTHHdrKit5.
Require Import Zlib.proof.inflate.CaseFLAGS5.
Require Import Zlib.proof.roundtrip.RTHFTO6.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
Require Import Zlib.proof.roundtrip.RTH9WKit.
Require Import Zlib.proof.inflate.InvW.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* a statement that ends only by a break, in the loop state of machine m *)
Definition brk_ret9 (P: environ -> mpred) : ret_assert :=
  {| RA_normal := FF; RA_break := P; RA_continue := FF; RA_return := fun _ _ => FF |}.

(* ---------------------------------------------------------------------------------------------- *)
(* the header                                                                                     *)

(* the partial header as the raw one (done is 0: the header is not passed) *)
Lemma hd6_hraw: forall F m,
  hd6 F m |-- !! (h_done (m_h m) <> 1) && hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m).
Proof.
  intros F m. unfold hd6, head_rep6, head_rep6p, hraw6, bufok6.
  Intros vt vtm vxf vos vxl vhc lx ln lc.
  Exists vt vtm vxf vos vxl vhc (zv (h_done (m_h m))) lx ln lc.
  match goal with H: hinv6 _ _ |- _ => destruct H as [D _] end.
  entailer!.
Qed.

(* a machine past the header modes with the header of m: the raw header *)
Lemma hd6_hd9_raw: forall F m m', m_h m' = m_h m -> hdr_mode (m_mode m') = false -> hd6 F m |-- hd9 F m'.
Proof.
  intros F m m' E M. unfold hd9. rewrite M. unfold hd9a. apply orp_right2. rewrite E. apply hd6_hraw.
Qed.

(* InvW.hdrW after INITBITS into a header mode other than EXTRA *)
Lemma hdrW_initbits9: forall m md, md <> EXTRA -> hdrW (set_mode (initbits m) md).
Proof.
  intros m md N. split.
  - intros _. cbn. lia.
  - intros E. exfalso. apply N. exact E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS out of input                                                                          *)

(* NEEDBITS(n) then `if (leave) break;` when the bits run out: the case's break, in the same header mode *)
Lemma semax_leave9 {Espec: OracleKind} (F: frame) (m: mst) (n: Z) (NB c: statement) (R: ret_assert):
  semax Delta_cases5 (loop_stateH F m) NB (normal_ret_assert (loop_stateH F (needbits n m))) ->
  m_leave (needbits n m) = 1 -> hdr_mode (m_mode m) = true ->
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk (needbits n m) ->
  RA_break R = RA_normal (case_post9 F m) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hd6 F m))
    (Ssequence NB (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip) c)) R.
Proof.
  intros HNB HL HM HS HR.
  eapply semax_seq_frame6; [exact HNB | ].
  rewrite <- (hd6_needbits F n m).
  apply semax_seq with (Q := FF); [ | apply semax_pre with (P' := FF); [apply andp_left2, derives_refl | apply semax_ff]].
  rewrite lsH_hd. rewrite HL. abbreviate_semax.
  forward_if.
  - forward. destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
    change (RA_break _) with (RA_normal (case_post9 F m)).
    unfold case_post9. unfold RA_normal at 1. Exists (needbits n m).
    unfold post9. rewrite lsH_hd.
    assert (HD: hd9 F (needbits n m) = hd6 F (needbits n m)).
    { unfold hd9. rewrite hk_needbits_mode, HM. reflexivity. }
    rewrite HD, HL. entailer!.
  - exfalso. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the error blocks of FLAGS                                                                      *)

(* a statement that only breaks, in mode BAD: the case's break with the raw header *)
Lemma semax_seq_bad9 {Espec: OracleKind} (F: frame) (m0 m: mst) (e: msgid) (Hd: mpred) (c1 c2: statement)
    (R: ret_assert):
  semax Delta_cases5 (loop_stateH F m) c1 (brk_ret9 (loop_stateH F (set_bad m e))) ->
  RA_break R = RA_normal (case_post9 F m0) ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk (set_bad m e) ->
  Hd |-- hd9 F (set_bad m e) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => Hd)) (Ssequence c1 c2) R.
Proof.
  intros H1 HR HS HH. destruct R as [Rn Rb Rc Rr]. simpl in HR. subst Rb.
  apply semax_seq with (Q := FF); [ | apply semax_pre with (P' := FF); [apply andp_left2, derives_refl | apply semax_ff]].
  eapply semax_post; [ | | | | apply semax_frame with (F := fun _ => Hd); [apply closed_const | exact H1]].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. unfold case_post9. simpl.
    apply exp_right with (set_bad m e). apply andp_right; [apply prop_right; exact HS | ].
    unfold post9. simpl. apply sepcon_derives; [apply derives_refl | exact HH].
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
Qed.

Lemma head_partH_bad9: forall F m e, head_partH F (set_bad m e) = head_partH F m.
Proof. reflexivity. Qed.

Ltac bad_brk9_tac F :=
  let HWS := fresh "HWS" in let HWH := fresh "HWH" in let HRG := fresh "HRG" in let HRT := fresh "HRT" in
  let zca := fresh "zca" in let zcf := fresh "zcf" in let Hzca := fresh "Hzca" in let Hzcf := fresh "Hzcf" in
  intros FOK; destruct FOK as (HWS & HWH & HRG & HRT);
  unfold bad_block; cbn [msg_ident];
  rewrite loop_state_hsplitH; unfold loop_state_hH, strm_part, strm_rep;
  abbreviate_semax;
  remember (f_gv F _zcalloc) as zca eqn:Hzca; remember (f_gv F _zcfree) as zcf eqn:Hzcf;
  forward; forward; forward;
  unfold brk_ret9, RA_break;
  rewrite loop_state_hsplitH; unfold loop_state_hH, strm_part, strm_rep;
  rewrite mem_rep_h_bad, head_partH_bad9;
  cbn [set_bad set_mode upd_s set_m_s set_m_msg m_s m_msg i_mode set_i_mode i_wrap i_flags i_check i_head
       m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_snx m_sow m_tin m_tout m_adler m_have m_left];
  rewrite <- Hzca, <- Hzcf; entailer!.

(* `strm->msg = "unknown compression method"; state->mode = BAD; break;` *)
Lemma bad_brk9_method {Espec: OracleKind} (F: frame) (m: mst): frame_ok F ->
  semax Delta_cases5 (loop_stateH F m) (bad_block (msg_ident M_method) 27)
    (brk_ret9 (loop_stateH F (set_bad m M_method))).
Proof. bad_brk9_tac F. Qed.

(* `strm->msg = "unknown header flags set"; state->mode = BAD; break;` *)
Lemma bad_brk9_hflags {Espec: OracleKind} (F: frame) (m: mst): frame_ok F ->
  semax Delta_cases5 (loop_stateH F m) (bad_block (msg_ident M_hflags) 25)
    (brk_ret9 (loop_stateH F (set_bad m M_hflags))).
Proof. bad_brk9_tac F. Qed.

(* RT-H: common kit of the header cases EXLEN / EXTRA with the partial header hd6 framed next to
   the headless loop state: hd6 depends only on the mode, flags, length of the state and on the head; framing
   a closed SEP item through a loop_stateH step; NEEDBITS's leave branch contradicted by hpass. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Export Zlib.proof.roundtrip.RTHEx6Base.
Require Export Zlib.proof.roundtrip.RTHNeedKit5.
Require Import Zlib.proof.inflate.MwfLemmas.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* hd6 reads the mode, the flags and the length of the state, and the head *)
Lemma head_rep6_ext: forall hsh headp xb nb cb s s' h,
  i_mode s = i_mode s' -> i_flags s = i_flags s' -> i_length s = i_length s' ->
  head_rep6 hsh headp xb nb cb s h = head_rep6 hsh headp xb nb cb s' h.
Proof.
  intros hsh headp xb nb cb s s' h E1 E2 E3. unfold head_rep6, hinv6, hph, cx6, cn6, cc6, fextra.
  rewrite E1, E2, E3. reflexivity.
Qed.

Lemma hd6_ext: forall F m m',
  i_mode (m_s m) = i_mode (m_s m') -> i_flags (m_s m) = i_flags (m_s m') -> i_length (m_s m) = i_length (m_s m') ->
  m_h m = m_h m' -> hd6 F m = hd6 F m'.
Proof.
  intros F m m' E1 E2 E3 E4. unfold hd6. rewrite E4. apply head_rep6_ext; auto.
Qed.

(* a closed SEP item framed through a step of the headless loop state *)
Lemma semax_frame_lsH {Espec: OracleKind} (F: frame) (m m': mst) (X: mpred) (c: statement):
  semax Delta_cases5 (loop_stateH F m) c (normal_ret_assert (loop_stateH F m')) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => X)) c (normal_ret_assert (loop_stateH F m' * (fun _ => X))).
Proof.
  intros H.
  eapply semax_post; [ | | | | apply semax_frame; [ | exact H]].
  - intros rho. simpl. apply andp_left2. apply derives_refl.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros rho. simpl. apply andp_left2. normalize.
  - intros vl rho. simpl. apply andp_left2. normalize.
  - intros rho te _. reflexivity.
Qed.

(* the first pass of hpass *)
Lemma hpass_brk: forall flush n m m',
  hdr_mode (m_mode m) = true -> hpass flush (S n) m ->
  stepf2 flush lenfix_list distfix_list m = IBrk m' -> m_leave m' = 0.
Proof.
  intros flush n m m' H P E. cbn [hpass] in P. rewrite H, E in P. tauto.
Qed.

Lemma hpass_noret: forall flush n m r m',
  hdr_mode (m_mode m) = true -> hpass flush (S n) m ->
  stepf2 flush lenfix_list distfix_list m = IRet r m' -> False.
Proof.
  intros flush n m r m' H P E. cbn [hpass] in P. rewrite H, E in P. exact P.
Qed.

(* a closed SEP item at the end of a canonical assertion *)
Lemma PQR_tok: forall P Q S (X: mpred),
  PROPx P (LOCALx Q (SEPx S)) * (fun _ => X) = PROPx P (LOCALx Q (SEPx (S ++ [X]))).
Proof.
  intros. rewrite sepcon_comm. etransitivity; [apply (insert_SEP X) | ].
  f_equal. f_equal. unfold SEPx. extensionality rho. simpl. rewrite fold_right_sepcon_app. simpl.
  apply pred_ext; cancel.
Qed.

(* if (leave) break; with leave = 0 known to hold *)
Lemma semax_ifleave6 {Espec: OracleKind} (F: frame) (m1: mst) (X: mpred) (R: ret_assert):
  mwf m1 -> (m_leave m1 = 1 -> False) ->
  semax Delta_cases5 (loop_stateH F m1 * (fun _ => X)) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (overridePost (!! (m_leave m1 = 0) && (loop_stateH F m1 * (fun _ => X))) R).
Proof.
  intros W1 HN.
  pose proof (mw_leave _ W1) as HL1.
  assert (E: m_leave m1 = 0) by (destruct (Z.eq_dec (m_leave m1) 1) as [A | A]; [exfalso; auto | lia]); clear HN.
  unfold loop_stateH. rewrite E.
  rewrite PQR_tok.
  abbreviate_semax.
  forward_if.
  - exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end.
  - forward. destruct R as [Rn Rb Rc Rr]. unfold RA_normal at 1. simpl.
    intros rho. apply andp_right; [apply prop_right; reflexivity | ]. apply andp_left2. unfold PROPx. simpl.
    normalize.
Qed.

Lemma semax_needbits_seq6 {Espec: OracleKind} (F: frame) (m: mst) (n: Z) (X: mpred) (NB c: statement)
    (R: ret_assert):
  semax Delta_cases5 (loop_stateH F m) NB (normal_ret_assert (loop_stateH F (needbits n m))) ->
  mwf m -> n <= 32 ->
  (m_leave (needbits n m) = 1 -> False) ->
  semax Delta_cases5 (!! (m_leave (needbits n m) = 0) && (loop_stateH F (needbits n m) * (fun _ => X))) c R ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => X))
    (Ssequence (Ssequence NB (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)) c) R.
Proof.
  intros HNB W Hn HN Hc.
  apply semax_seq with (Q := !! (m_leave (needbits n m) = 0) && (loop_stateH F (needbits n m) * (fun _ => X)));
    [ | exact Hc].
  eapply semax_seq'; [ apply semax_frame_lsH; exact HNB | ].
  apply semax_ifleave6; auto. apply mwf_needbits; auto.
Qed.

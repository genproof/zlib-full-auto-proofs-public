(* Pure facts used by the allocator-generic proof of inflate()'s body (the generated
   src/proof/za/inflate_api/Body5*.v, patched by docs/port-za/inflate/body.py):

   - the allocator events of a call (ZEvents.v): updatewindow's event uw_ev on a successful update is the
     event win_ev of the call, which depends only on the window flags and modes of the states it compares
     and the wbits of the second; a failed update at the exit (the mode becomes MEM) is win_ev's ZFail;
   - the exit keeps the mode, wbits, the window flag, the extra length and stores the bit buffer in the
     saved state, so the gzip-extra facts InvW.swfW of the saved state follow from InvW.hdrW of the
     machine at inf_leave;
   - a return from inside the switch saves a state in neither EXLEN nor EXTRA (RetModeZ.v), so swfW holds
     for it too;
   - the store of the check value into strm->adler (UPDATE_CHECK at the exit) gives the stream's adler cell
     (ZAV.v: any contents when av_undef). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.inflate.Model2.
Require Import Zlib.proof.inflate.InvW.
Require Import Zlib.proof.inflate_api.Body5ExitKit.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.za.inflate_api.RetModeZ.
Require Import Zlib.proof.inflate_api.Spec5.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.inflate.Rep.
Require Import Zlib.proof.inflate.Inv.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The events                                                                                     *)

(* win_ev s s' depends only on the window flags of s and s', on whether s is in mode MEM, and on the mode
   and wbits of s' *)
Lemma win_ev_congr: forall s1 s2 s1' s2',
  i_win s1 = i_win s2 -> i_win s1' = i_win s2' -> i_wbits s1' = i_wbits s2' ->
  (i_mode s1 =? MEM) = (i_mode s2 =? MEM) -> i_mode s1' = i_mode s2' ->
  win_ev s1 s1' = win_ev s2 s2'.
Proof. intros s1 s2 s1' s2' A B C D G. unfold win_ev. rewrite A, B, C, D, G. reflexivity. Qed.

(* no event when the window flag does not change and the call does not enter MEM *)
Lemma win_ev_nomem: forall s s', i_win s' = i_win s -> (i_mode s' = MEM -> i_mode s = MEM) -> win_ev s s' = [].
Proof.
  intros s s' E M. unfold win_ev. rewrite E. destruct (i_win s); [reflexivity | ]. cbn [negb andb].
  destruct (Z.eqb_spec (i_mode s') MEM) as [H | H]; [rewrite (M H), Z.eqb_refl | ]; reflexivity.
Qed.

(* no event when the window flag and the mode do not change *)
Lemma win_ev_same: forall s s', i_win s' = i_win s -> i_mode s' = i_mode s -> win_ev s s' = [].
Proof. intros s s' E M. apply win_ev_nomem; [exact E | rewrite M; auto]. Qed.

(* a call that returns the state it was given (Z_STREAM_ERROR) allocates nothing *)
Lemma ev_self: forall st: option live,
  (match st, st with Some L, Some L' => win_ev (l_s L) (l_s L') | _, _ => [] end) = [].
Proof. intros [L|]; [apply win_ev_same; reflexivity | reflexivity]. Qed.

(* updatewindow changes only the window fields *)
Lemma updatewindow_keepW: forall s d,
  i_mode (updatewindow s d) = i_mode s /\ i_wbits (updatewindow s d) = i_wbits s /\
  i_win (updatewindow s d) = i_win s /\ i_length (updatewindow s d) = i_length s /\
  i_hold (updatewindow s d) = i_hold s /\ i_bits (updatewindow s d) = i_bits s /\
  i_flags (updatewindow s d) = i_flags s.
Proof.
  intros s d. unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; repeat split; reflexivity.
Qed.

(* a successful updatewindow (r = 0) on the state s allocates what the call's win_ev records *)
Lemma uw_ev_win_ev: forall s d,
  uw_ev s 0 = win_ev s (set_i_win (updatewindow s d) true).
Proof.
  intros s d. destruct (updatewindow_keepW s d) as (_ & W & _).
  unfold uw_ev, win_ev. simpl. rewrite W. destruct (i_win s); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The saved state at the exit                                                                    *)

(* the rest of leave_fin after the window update keeps the fields of the state but the counters and
   the check value *)
Lemma leave_tail_keepW: forall flush m,
  let s' := m_s (r_m (leave_tail flush m)) in
  i_mode s' = i_mode (m_s m) /\ i_wbits s' = i_wbits (m_s m) /\ i_win s' = i_win (m_s m) /\
  i_length s' = i_length (m_s m) /\ i_hold s' = i_hold (m_s m) /\ i_bits s' = i_bits (m_s m) /\
  i_flags s' = i_flags (m_s m).
Proof.
  intros flush m. unfold leave_tail. cbv zeta.
  match goal with |- context [m_s (if ?b then _ else _)] => destruct b end; simpl; repeat split; reflexivity.
Qed.

(* RESTORE and the window update store the bit buffer and keep the mode, wbits and the extra length *)
Lemma mwin_keepW: forall flush m,
  let s' := m_s (mwin flush m) in
  i_mode s' = i_mode (m_s m) /\ i_wbits s' = i_wbits (m_s m) /\
  i_win s' = (leave_ok flush m || i_win (m_s m))%bool /\
  i_length s' = i_length (m_s m) /\ i_hold s' = m_hold m /\ i_bits s' = m_bits m /\
  i_flags s' = i_flags (m_s m).
Proof.
  intros flush m. unfold mwin. cbv zeta. destruct (leave_ok flush m).
  - simpl.
    match goal with |- context [updatewindow ?s ?d] => destruct (updatewindow_keepW s d) as (A & B & C & D & E & G & H) end.
    rewrite A, B, D, E, G, H. simpl. repeat split; reflexivity.
  - simpl. repeat split; reflexivity.
Qed.

(* the call's event at the exit: the window allocated by the update *)
Lemma leave_fin_win_ev: forall flush m,
  win_ev (m_s m) (m_s (r_m (leave_fin flush m))) = win_ev (m_s m) (m_s (mwin flush m)).
Proof.
  intros flush m. rewrite leave_fin_eq.
  destruct (leave_tail_keepW flush (mwin flush m)) as (A & B & C & _).
  apply win_ev_congr; auto.
Qed.

(* the exit's window update failed (inf_leave's il_mem: the window was to be updated and there was none):
   the call entered MEM, win_ev records the failed allocation.  Without a window wsize is 0, so the update
   was asked for by a mode before BAD, not by MEM. *)
Lemma leave_mem_ev: forall flush m, swf (m_s m) -> leave_ok flush m = true -> i_win (m_s m) = false ->
  win_ev (m_s m) (m_s (set_mode (restore m) MEM)) = [ZFail].
Proof.
  intros flush m S HB HW.
  assert (WS: i_wsize (m_s m) = 0) by (destruct (sw_wsize _ S) as [? | [X _]]; [assumption | congruence]).
  unfold leave_ok in HB. rewrite WS in HB. cbn [Z.eqb negb orb] in HB.
  apply andb_prop in HB as [HB _]. apply andb_prop in HB as [_ HB]. apply Z.ltb_lt in HB.
  unfold win_ev.
  change (i_win (m_s (set_mode (restore m) MEM))) with (i_win (m_s m)).
  change (i_mode (m_s (set_mode (restore m) MEM))) with MEM.
  rewrite HW. cbn [negb andb]. rewrite Z.eqb_refl.
  replace (i_mode (m_s m) =? MEM) with false by (symmetry; apply Z.eqb_neq; unfold m_mode, BAD, MEM in *; lia).
  reflexivity.
Qed.

(* the saved state after inf_leave satisfies swfW when the machine satisfies hdrW *)
Lemma inf_leave_swfW: forall flush m res, hdrW m -> inf_leave flush m res -> swfW (m_s (r_m res)).
Proof.
  intros flush m res [H1 H2] IL. inversion IL; subst.
  - simpl. unfold swfW. simpl. unfold MEM, EXLEN, EXTRA. split; intro E; discriminate.
  - rewrite leave_fin_eq.
    destruct (leave_tail_keepW flush (mwin flush m)) as (A & _ & _ & D & E & G & H).
    destruct (mwin_keepW flush m) as (A' & _ & _ & D' & E' & G' & H').
    unfold swfW. rewrite A, D, E, G, H, A', D', E', G', H'.
    split; [exact H1 | exact H2].
Qed.

(* the saved state of a return from inside the switch satisfies swfW *)
Lemma stepf2_ret_swfW: forall fl fx dx m r m', stepf2 fl fx dx m = IRet r m' -> swfW (m_s m').
Proof.
  intros fl fx dx m r m' E. destruct (stepf2_ret_mode fl fx dx m r m' E) as [A B].
  unfold swfW. split; intro C; contradiction.
Qed.

(* the call's event of a return from inside the switch: none (the window flag is kept, and a return in mode
   MEM is MEM's own return, RetModeZ.stepf2_ret_mem) *)
Lemma win_ev_ret: forall s0 s s', i_win s = i_win s0 -> i_win s' = i_win s ->
  (i_mode s' = MEM -> i_mode s = MEM) -> (i_mode s = MEM -> i_mode s0 = MEM) -> win_ev s0 s' = [].
Proof. intros s0 s s' A B C D. apply win_ev_nomem; [congruence | auto]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The adler cell                                                                                 *)

Section SepFacts.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* a z_stream whose member adler holds the value c is a z_stream whose adler cell is c (any contents when
   av_undef) *)
Lemma strm_adler_weaken {AV: adler_cell}: forall sh p (ni ai ti no ao tout msg st za zf op dt vres: val) (c: Z),
  data_at sh t_strm (ni, (ai, (ti, (no, (ao, (tout, (msg, (st, (za, (zf, (op, (dt, (Vlong (Int64.repr c), vres))))))))))))) p
  |-- data_at sh t_strm (ni, (ai, (ti, (no, (ao, (tout, (msg, (st, (za, (zf, (op, (dt, (adler_val c, vres))))))))))))) p.
Proof.
  intros. unfold adler_val. destruct av_undef; [ | apply derives_refl].
  (* take the member out (the ramification of a store), weaken it to any contents, put it back *)
  unfold data_at.
  eapply derives_trans;
    [eapply (nested_field_ramif' sh t_strm [] (DOT _adler)); [apply JMeq_refl | split; [reflexivity | cbv; tauto]] | ].
  eapply derives_trans; [apply sepcon_derives; [apply field_at_field_at_ | apply derives_refl] | ].
  unfold field_at_.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | ] | ].
  { apply (allp_left _ (default_val _)); apply (allp_left _ (default_val _)).
    rewrite prop_imp by apply JMeq_refl. apply derives_refl. }
  eapply derives_trans; [apply modus_ponens_wand | ].
  apply derives_refl'. f_equal.
Qed.

(* the allocator's state as its own SEP item or inside the frame X *)
Lemma ENTAIL_sep_perm: forall Delta Q (A B C D E G: mpred) (R: environ -> mpred),
  ENTAIL Delta, PROPx [] (LOCALx Q (SEPx [A; B; C; E; (D * G)%logic])) |-- R ->
  ENTAIL Delta, PROPx [] (LOCALx Q (SEPx [A; B; C; D; E; G])) |-- R.
Proof.
  intros Delta Q A B C D E G R H. eapply derives_trans; [ | exact H].
  apply andp_derives; [apply derives_refl | ].
  unfold PROPx, LOCALx, SEPx. intro rho. simpl.
  apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  cancel.
Qed.

Lemma ENTAIL_sep_perm': forall Delta Q (A B C D E G: mpred) (R: environ -> mpred),
  ENTAIL Delta, PROPx [] (LOCALx Q (SEPx [A; B; C; D; E; G])) |-- R ->
  ENTAIL Delta, PROPx [] (LOCALx Q (SEPx [A; B; C; E; (D * G)%logic])) |-- R.
Proof.
  intros Delta Q A B C D E G R H. eapply derives_trans; [ | exact H].
  apply andp_derives; [apply derives_refl | ].
  unfold PROPx, LOCALx, SEPx. intro rho. simpl.
  apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  cancel.
Qed.

End SepFacts.

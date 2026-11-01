(* inflate()'s main loop over the machines of a call with their header RTH9HDefs.hd9 (RTH9AKit.loop9_stmt):
   header cases (RTH9HDefs.cases9h_all) from a header mode, headless cases (RTH9Defs.cases_nh9) on the machine
   with the small header RTH8W.mcanon past the header modes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Import Zlib.proof.roundtrip.RTH9ALoopH.
Require Import Zlib.proof.roundtrip.RTH9ALoopN.
Require Import Zlib.proof.inflate_api.Body5Loop.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the loop invariant: the real machine m at the loop head, reached from m0, with its header *)
Definition linv9 (F: frame) (X: mpred) (m0: mst) : environ -> mpred :=
  EX m: mst,
    !! ((forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) /\
        mwf3_9 m /\ hd_ok F m /\ m_leave m = 0 /\ i_head (m_s m) = true /\ pinv8 m0 m) &&
    lstateH F (X * hd9 F m) m.

(* `if (leave) break;` after a pass from m (leave is 0 or 1 by the machine invariant) *)
Lemma leave_if9 {Espec: OracleKind} (fast: funspec) (F: frame) (X: mpred) (m0 m: mst) (R: ret_assert):
  (forall o, loop2 (f_flush F) lenfix_list distfix_list m o -> loop2 (f_flush F) lenfix_list distfix_list m0 o) ->
  semax (Delta_inflate9 fast) (lmid9 F X m0 m) (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
    (loop1_ret_assert (linv9 F X m0) (overridePost (loop_exit9 F X m0) R)).
Proof.
  intros Reach. destruct R as [Rn Rb Rc Rr]. unfold lmid9, lstateH. Intros m'.
  apply semax_extract_prop. intros (E & W' & D' & I' & P').
  assert (HL: 0 <= m_leave m' <= 1).
  { destruct W' as [[Ww _] _]. pose proof (mwW_leave _ Ww) as HL. destruct m'. exact HL. }
  abbreviate_semax.
  forward_if.
  - forward. unfold loop_exit9, lstateH. Exists m'.
    assert (L1: m_leave m' = 1)
      by (destruct (zeq (m_leave m') 0) as [Z0 | Z0]; [rewrite Z0 in H; contradiction | lia]).
    entailer!.
    apply Reach. apply loop2_leave; auto.
  - forward. unfold linv9, lstateH. Exists m'.
    assert (L0: m_leave m' = 0).
    { apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. exact H. }
    entailer!.
    intros o Ho. apply Reach. eapply loop2_next; eauto. lia.
Qed.

Lemma loop9 : loop9_stmt.
Proof.
  intros fast FS HC HH HIv Espec F X m0 R HF HRet W0 L0 D0 I0 P0.
  destruct R as [Rn Rb Rc Rr].
  rewrite mainloop_eq.
  apply semax_pre with (P' := linv9 F X m0).
  { unfold linv9. apply andp_left2. Exists m0. apply andp_right; [apply prop_right | apply derives_refl].
    exact (conj (fun o Ho => Ho) (conj W0 (conj D0 (conj L0 (conj I0 P0))))). }
  apply semax_loop with (Q' := linv9 F X m0).
  - unfold linv9 at 1. apply extract_exists_pre. intros m.
    apply semax_extract_prop. intros (Reach & W & D & L & I & Pm).
    apply -> semax_skip_seq.
    apply semax_seq with (Q := lmid9 F X m0 m).
    + destruct (hdr_mode (m_mode m)) eqn:HM.
      * apply (pass_hdr9 fast F X m0 m); auto.
        simpl RA_normal. apply andp_left2. apply derives_refl.
      * apply (pass_nh9 fast F X m0 m {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |});
          auto.
        simpl RA_normal. apply andp_left2. apply derives_refl.
    + apply leave_if9; auto.
  - eapply semax_post; [ | | | | apply semax_skip]; simpl.
    + intros rho. apply andp_left2. apply derives_refl.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros rho. simpl. apply andp_left2. normalize.
    + intros vl rho. simpl. apply andp_left2. normalize.
Qed.

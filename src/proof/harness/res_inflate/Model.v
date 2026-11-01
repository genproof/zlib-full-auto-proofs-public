(* The model facts of res_free_inflate and res_memory_inflate (ModelStmt.v, res_model_stmt): the state between
   two inflate() calls (res_inv) after inflateInit2_ and after each call, the window kept once allocated, the
   mode MEM entered only without a window, and Z_MEM_ERROR returned only in MEM. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.inflate.Model2.
Require Zlib.proof.inflate_api.StepInv5Kit.

(* The invariant of state->wbits during the call: it is at most the harness's w, and it is 0 only when
   that w is 15 (windowBits & 15 = 0: the window size is then taken from the stream header, at most 15). *)
Definition wb_inv (hw: Z) (m: mst) : Prop :=
  i_wbits (m_s m) <= hw /\ (i_wbits (m_s m) = 0 -> hw = 15).

(* inflateInit2_'s state satisfies it *)
Lemma wb_inv_init : forall w z sp inp, wbits_ok w = true ->
  wb_inv (harness_w w) (m_init z (init_live sp w) inp).
Proof.
  intros w z sp inp Hok.
  unfold wbits_ok in Hok.
  destruct (reset2_wb w) as [[wrap wb]|] eqn:R; [|discriminate].
  (* with fix F8, wb = 0 sets bit 3 of wrap and inflateReset then sets wbits to 0 = wb again *)
  assert (E: i_wbits (m_s (m_init z (init_live sp w) inp)) = wb).
  { destruct (reset2_wrap_ok w wrap wb R) as (_ & B8 & _).
    unfold m_init, init_live; rewrite R; cbn [m_s l_s].
    assert (W: i_wbits (init_s wrap wb) = wb).
    { unfold init_s, reset2_s, reset_full_s, reset_hdr_s.
      cbn [zero_s i_win i_wbits andb negb set_i_wbits set_i_wrap set_i_win i_wrap].
      rewrite B8. destruct (Z.eqb_spec wb 0) as [-> | _]; reflexivity. }
    revert W; generalize (init_s wrap wb); intros s W.
    destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); [destruct s; exact W | exact W]. }
  unfold wb_inv, harness_w; rewrite E; clear E.
  unfold reset2_wb in R.
  destruct (w <? 0) eqn:N.
  - destruct (w <? -15); [discriminate|].
    destruct ((8 <=? - w) && (- w <=? 15))%bool eqn:B; [|discriminate].
    inversion R; subst; apply andb_prop in B; destruct B as [B1 B2];
      apply Z.leb_le in B1; split; lia.
  - destruct (w <? 48) eqn:L.
    + destruct ((Z.land w 15 =? 0) || ((8 <=? Z.land w 15) && (Z.land w 15 <=? 15)))%bool eqn:B; [|discriminate].
      inversion R; subst.
      destruct (Z.land w 15 =? 0) eqn:E0.
      * apply Z.eqb_eq in E0; rewrite E0; split; lia.
      * apply Z.eqb_neq in E0; split; lia.
    + apply Z.ltb_ge in L.
      destruct ((w =? 0) || ((8 <=? w) && (w <=? 15)))%bool eqn:B; [|discriminate].
      exfalso; apply orb_prop in B; destruct B as [B|B];
        [apply Z.eqb_eq in B; lia | apply andb_prop in B; destruct B as [_ B]; apply Z.leb_le in B; lia].
Qed.

(* the zlib/gzip header (case HEAD) keeps it: wbits is only set when it is 0, to 15 or to a checked
   window size of at most 15 *)
Lemma wb_inv_head : forall hw m, wb_inv hw m ->
  match c_HEAD2 m with IBrk m' => wb_inv hw m' | IRet _ m' => wb_inv hw m' end.
Proof.
  intros hw m Hi.
  unfold c_HEAD2.
  destruct (i_wrap (m_s m) =? 0); [exact Hi|].
  assert (Hi1: wb_inv hw (needbits 16 m)) by (unfold wb_inv; rewrite StepInv5Kit.needbits_s; exact Hi).
  clear Hi; revert Hi1; generalize (needbits 16 m); intros m1 Hi.
  destruct (m_leave m1 =? 1); [exact Hi|].
  destruct (negb (Z.land (i_wrap (m_s m1)) 2 =? 0) && (m_hold m1 =? 35615))%bool.
  { unfold wb_inv in *; cbn.
    destruct (i_wbits (m_s m1) =? 0) eqn:E0;
      [apply Z.eqb_eq in E0; specialize (proj2 Hi E0); lia | apply Z.eqb_neq in E0; exact Hi]. }
  set (m2 := if i_head (m_s m1) then upd_h m1 (fun h => set_h_done h (-1)) else m1).
  assert (H2: m_s m2 = m_s m1) by (subst m2; destruct (i_head (m_s m1)); reflexivity).
  assert (Hi2: wb_inv hw m2) by (unfold wb_inv; rewrite H2; exact Hi).
  clearbody m2; clear H2 Hi; rename Hi2 into Hi.
  destruct ((Z.land (i_wrap (m_s m1)) 1 =? 0) || _)%bool.
  { exact Hi. }
  destruct (negb (m_hold m2 mod 16 =? 8)).
  { exact Hi. }
  destruct ((15 <? m_hold (dropbits 4 m2) mod 16 + 8) ||
            (negb (i_wbits (m_s (dropbits 4 m2)) =? 0) &&
             (i_wbits (m_s (dropbits 4 m2)) <? m_hold (dropbits 4 m2) mod 16 + 8)))%bool eqn:B.
  { exact Hi. }
  apply orb_false_iff in B; destruct B as [B1 B2]; apply Z.ltb_ge in B1.
  unfold wb_inv in *; cbn in *.
  destruct (Z.land (m_hold (dropbits 4 m2)) 512 =? 0); cbn;
  destruct (i_wbits (m_s m2) =? 0) eqn:E0;
    try (apply Z.eqb_eq in E0; specialize (proj2 Hi E0); intros; split; [lia | intros; lia]);
    exact Hi.
Qed.

(* one pass of the switch keeps it: outside HEAD, wbits does not change *)
Lemma wb_inv_step : forall hw flush m, wb_inv hw m ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => wb_inv hw m' | IRet _ m' => wb_inv hw m' end.
Proof.
  intros hw flush m Hi.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply wb_inv_head; exact Hi.
  - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    unfold wb_inv in *.
    destruct (stepf2 flush lenfix_list distfix_list m); destruct G as (_ & G2 & _); rewrite G2; exact Hi.
Qed.

(* the loop keeps it *)
Lemma wb_inv_loop : forall hw flush m o, loop2 flush lenfix_list distfix_list m o -> wb_inv hw m ->
  match o with IBrk m' => wb_inv hw m' | IRet _ m' => wb_inv hw m' end.
Proof.
  intros hw flush m o L; induction L as [m r m' E | m m' E _ | m m' o E _ _ IH]; intros Hi.
  - pose proof (wb_inv_step hw flush m Hi) as S; rewrite E in S; exact S.
  - pose proof (wb_inv_step hw flush m Hi) as S; rewrite E in S; exact S.
  - pose proof (wb_inv_step hw flush m Hi) as S; rewrite E in S; exact (IH S).
Qed.

(* the exit (RESTORE, updatewindow, the counters and the check value) does not change wbits *)
Lemma updatewindow_wbits : forall s data, i_wbits (updatewindow s data) = i_wbits s.
Proof.
  intros s data; unfold updatewindow.
  destruct (i_wsize s =? 0); cbn;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma leave_fin_wbits : forall flush m, i_wbits (m_s (r_m (leave_fin flush m))) = i_wbits (m_s m).
Proof.
  intros flush m; unfold leave_fin.
  set (m1 := restore m).
  assert (H1: i_wbits (m_s m1) = i_wbits (m_s m)) by reflexivity.
  clearbody m1.
  set (m2 := if leave_ok flush m then _ else m1).
  assert (H2: i_wbits (m_s m2) = i_wbits (m_s m)).
  { subst m2; destruct (leave_ok flush m); [cbn; rewrite updatewindow_wbits; exact H1 | exact H1]. }
  clearbody m2.
  cbn; destruct (negb (Z.land (i_wrap _) 4 =? 0) && negb (_ =? 0))%bool; exact H2.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The window flag and the return code of a call from a state of the decoder proper                *)

Require Import Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.harness.inflate_buffers.IBStepKit.
Require Import Zlib.proof.harness.inflate_pieces.TheoryStep.
Require Zlib.proof.harness.inflate_codes.TheoryRun.
Require Zlib.proof.harness.inflate_buffers.IBRun.
Require Zlib.proof.inflate.StepW.

(* the zlib/gzip header (case HEAD) does not touch the window flag *)
Lemma win_head : forall m,
  match c_HEAD2 m with IBrk m' => i_win (m_s m') = i_win (m_s m) | IRet _ m' => i_win (m_s m') = i_win (m_s m) end.
Proof.
  intros m.
  unfold c_HEAD2.
  destruct (i_wrap (m_s m) =? 0); [reflexivity|].
  assert (H1: i_win (m_s (needbits 16 m)) = i_win (m_s m)) by (rewrite StepInv5Kit.needbits_s; reflexivity).
  revert H1; generalize (needbits 16 m); intros m1 H1.
  destruct (m_leave m1 =? 1); [exact H1|].
  destruct (negb (Z.land (i_wrap (m_s m1)) 2 =? 0) && (m_hold m1 =? 35615))%bool; [exact H1|].
  destruct (i_head (m_s m1));
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact H1.
Qed.

(* no pass of the switch changes the window flag (the window is only allocated at the exit) *)
Lemma win_step : forall flush m,
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => i_win (m_s m') = i_win (m_s m) | IRet _ m' => i_win (m_s m') = i_win (m_s m) end.
Proof.
  intros flush m.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply win_head.
  - pose proof (StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
    destruct (stepf2 flush lenfix_list distfix_list m); destruct G as (G1 & _); exact G1.
Qed.

Lemma win_loop : forall flush m o, loop2 flush lenfix_list distfix_list m o ->
  match o with IBrk m' => i_win (m_s m') = i_win (m_s m) | IRet _ m' => i_win (m_s m') = i_win (m_s m) end.
Proof.
  intros flush m o L; induction L as [m r m' E | m m' E _ | m m' o E _ _ IH].
  - pose proof (win_step flush m) as S; rewrite E in S; exact S.
  - pose proof (win_step flush m) as S; rewrite E in S; exact S.
  - pose proof (win_step flush m) as S; rewrite E in S.
    destruct o; rewrite IH; exact S.
Qed.

(* the exit keeps an allocated window *)
Lemma leave_fin_win : forall flush m, i_win (m_s m) = true -> i_win (m_s (r_m (leave_fin flush m))) = true.
Proof.
  intros flush m W; unfold leave_fin.
  set (m1 := restore m).
  assert (H1: i_win (m_s m1) = true) by exact W.
  clearbody m1.
  set (m2 := if leave_ok flush m then _ else m1).
  assert (H2: i_win (m_s m2) = true).
  { subst m2; destruct (leave_ok flush m); [reflexivity | exact H1]. }
  clearbody m2.
  cbn; destruct (negb (Z.land (i_wrap _) 4 =? 0) && negb (_ =? 0))%bool; exact H2.
Qed.

(* from a loop head of the decoder proper (Theory.v's pJ), the loop returns only Z_NEED_DICT (case DICT)
   and breaks (leave = 1) with the discipline of ret (TheoryStep.rk) *)
Lemma loop_ret flush z L inp : stepf2_mwf3W_stmt ->
  forall m o, loop2 flush lenfix_list distfix_list m o -> pJ z L inp m ->
  match o with IRet r _ => r = Z_NEED_DICT | IBrk m' => rk m' /\ m_leave m' = 1 end.
Proof.
  intros SW m o HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros J.
  - pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct (pc_step_pre z L inp m J) as [P1 P2].
    pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
    exact (proj1 G).
  - destruct (pc_brk flush z L inp SW m m' J E) as (_ & _ & _ & _ & Rk). split; [exact Rk | exact Hlv].
  - destruct (pc_brk flush z L inp SW m m' J E) as (T & W' & Hh & Hw & Rk).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (mwW_leave _ (proj1 W')) as Lv'.
    apply IH. unfold pJ.
    split; [exact W'|]. split; [lia|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split; [auto|].
    split; [intros Hd; destruct (T8 Hd) as (K1 & K2 & K3 & K4); destruct (J6 K1) as (L1 & L2 & L3);
            split; [congruence|]; split; congruence|].
    split; [congruence|]. split; [congruence|]. split; [exact T9|]. apply Rk.
Qed.

(* the exit's return code after such a loop is not Z_MEM_ERROR *)
Lemma leave_fin_not_mem flush m : rk m -> m_leave m = 1 -> r_ret (leave_fin flush m) <> Z_MEM_ERROR.
Proof.
  intros (R1 & R2 & R3) Lv.
  destruct (TheoryRun.rn_leave_fin flush m) as (E & _). rewrite E.
  unfold TheoryRun.rn_bufret.
  destruct (_ && _)%bool; [vm_compute; discriminate|].
  destruct (Z.eq_dec (m_mode m) BAD) as [B|B]; [rewrite (R3 Lv B); vm_compute; discriminate|].
  destruct (Z.eq_dec (m_mode m) DONE) as [D|D]; [rewrite (R2 Lv D); vm_compute; discriminate|].
  rewrite (R1 B D); vm_compute; discriminate.
Qed.

(* the machine at the loop head has the stream's state, but TYPE is entered as TYPEDO *)
Lemma m_init_s z L inp : m_s (m_init z L inp) = IBRun.ib_typedo (l_s L).
Proof. reflexivity. Qed.

Lemma typedo_fields s :
  i_win (IBRun.ib_typedo s) = i_win s /\ i_wbits (IBRun.ib_typedo s) = i_wbits s /\
  i_head (IBRun.ib_typedo s) = i_head s.
Proof. unfold IBRun.ib_typedo. destruct (_ =? _); repeat split. Qed.

(* inflateInit2_'s state: no gz_header request, mode HEAD *)
Lemma init_head sp w : i_head (l_s (init_live sp w)) = false.
Proof. unfold init_live. destruct (reset2_wb w) as [[a b] | ]; reflexivity. Qed.

Lemma init_mode sp w : i_mode (l_s (init_live sp w)) = HEAD.
Proof. unfold init_live. destruct (reset2_wb w) as [[a b] | ]; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                      *)

(* a call from the mode MEM returns Z_MEM_ERROR at once and changes nothing *)
Lemma res_call_mem flush z L inp res : i_mode (l_s L) = MEM ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  res = Res Z_MEM_ERROR (m_init z L inp) None /\ m_s (m_init z L inp) = l_s L.
Proof.
  intros Hm (o & HL & Ho).
  assert (S: m_s (m_init z L inp) = l_s L).
  { rewrite m_init_s. unfold IBRun.ib_typedo. rewrite Hm. reflexivity. }
  assert (E: stepf2 flush lenfix_list distfix_list (m_init z L inp) = IRet Z_MEM_ERROR (m_init z L inp)).
  { assert (M: m_mode (m_init z L inp) = MEM) by (unfold m_mode; rewrite S; exact Hm).
    unfold stepf2, step2. rewrite M. reflexivity. }
  inversion HL; subst; rewrite E in *; try discriminate.
  match goal with H: IRet _ _ = IRet _ _ |- _ => injection H as <- <- end.
  split; [exact Ho | exact S].
Qed.

Lemma res_model : res_model_stmt.
Proof.
  split.
  - intros w sp Hok.
    pose proof (wb_inv_init w (ZF nullval 0 0 nullval 0 0 None 0 0 nullval) sp [] Hok) as Wb.
    unfold wb_inv in Wb; rewrite m_init_s, (proj1 (proj2 (typedo_fields _))) in Wb.
    unfold res_inv. rewrite init_head, init_mode.
    split; [reflexivity|]. split; [right; wmodes; lia|]. exact Wb.
  - intros hw flush z L inp res Hinv Hsw HL Hz Hb Hn Hrun.
    destruct Hinv as (Ih & [Im | Im] & Iw1 & Iw2).
    + (* MEM *)
      destruct (res_call_mem flush z L inp res Im Hrun) as [-> S]; cbn [r_m r_ret m_s].
      rewrite S. split; [unfold res_inv; auto|].
      split; [auto|]. split; [auto|]. split; [intros N; contradiction|]. intros _; exact Im.
    + (* HEAD .. BAD *)
      assert (PI: pinv z L) by (split; [exact Ih | split; assumption]).
      pose proof (pc_J_init z L inp HL Hz Hb Hn PI) as J0.
      destruct (typedo_fields (l_s L)) as (T1 & T2 & T3).
      assert (Wb0: wb_inv hw (m_init z L inp)) by (unfold wb_inv; rewrite m_init_s, T2; split; assumption).
      destruct Hrun as (o & Hlo & Ho).
      pose proof (pc_loop flush z L inp StepW.stepf2_mwf3W Hz Hn _ _ Hlo J0) as P.
      pose proof (loop_ret flush z L inp StepW.stepf2_mwf3W _ _ Hlo J0) as R.
      pose proof (win_loop flush _ _ Hlo) as Wn.
      pose proof (wb_inv_loop hw flush _ _ Hlo Wb0) as Wb.
      rewrite m_init_s, T1 in Wn.
      assert (Hnm: i_mode (l_s L) <> MEM) by (wmodes; lia).
      (* the call ends in the decoder proper with a return code other than Z_MEM_ERROR *)
      assert (Fin: forall res, ppost z L inp res -> r_ret res <> Z_MEM_ERROR ->
                     wb_inv hw (r_m res) -> (i_win (l_s L) = true -> i_win (m_s (r_m res)) = true) ->
                     res_inv hw (m_s (r_m res)) /\
                     (i_win (l_s L) = true -> i_win (m_s (r_m res)) = true) /\
                     (i_mode (l_s L) = MEM -> m_s (r_m res) = l_s L) /\
                     (i_mode (l_s L) <> MEM -> i_mode (m_s (r_m res)) = MEM -> i_win (m_s (r_m res)) = false) /\
                     (r_ret res = Z_MEM_ERROR -> i_mode (m_s (r_m res)) = MEM)).
      { intros res0 (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7) Nr (B1 & B2) Hw.
        destruct (Q7 Nr) as (_ & _ & Md & _ & _). unfold m_mode in Md.
        split; [unfold res_inv; split; [congruence | split; [right; exact Md | split; assumption]]|].
        split; [exact Hw|]. split; [intros; contradiction|].
        split; [intros _ F; exfalso; rewrite F in Md; wmodes; lia|]. intros; contradiction. }
      destruct o as [m'|r m'].
      * (* the loop breaks: the exit *)
        specialize (P res Ho).
        inversion Ho as [Lok Wf E | E]; subst res.
        -- (* the window allocation failed: MEM *)
           destruct P as (_ & _ & _ & _ & Q5 & _).
           cbn [r_m r_ret m_s set_mode restore upd_s set_m_sow set_m_snx] in Q5 |- *.
           unfold wb_inv in Wb; cbn [m_s] in Wb.
           cbn [i_mode i_win i_wbits i_head set_i_mode set_i_bits set_i_hold] in Q5 |- *.
           split; [unfold res_inv; cbn [i_mode i_win i_wbits i_head set_i_mode set_i_bits set_i_hold];
                   split; [congruence | split; [left; reflexivity | exact Wb]]|].
           split; [intros W; congruence|]. split; [intros; contradiction|].
           split; [intros _ _; exact Wf|]. intros _; reflexivity.
        -- apply Fin; [exact P | | | ].
           ++ destruct R as [Rk Lv]. apply leave_fin_not_mem; assumption.
           ++ unfold wb_inv in *; rewrite leave_fin_wbits; exact Wb.
           ++ intros W; apply leave_fin_win; congruence.
      * (* the loop returns (case DICT) *)
        subst res. apply Fin; [exact P | cbn; rewrite R; vm_compute; discriminate | exact Wb |].
        intros W; cbn; congruence.
Qed.

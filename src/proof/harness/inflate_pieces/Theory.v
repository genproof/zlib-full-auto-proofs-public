(* The laws rj_any_input, api_counters and api_untouched_output, the theory: an invariant of the stream at the
   call boundaries with the facts of Facts.v (pieces_facts), from the intra-call invariant of the model for
   inputs and output spaces of up to 2^32-1 bytes (InvW.stepf2_mwf3W_stmt: one pass of the switch keeps
   mwf3W). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_pieces.Facts.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.harness.inflate_buffers.IBStepKit.
Require Zlib.proof.harness.inflate_buffers.IBRun.
Require Zlib.proof.harness.inflate_buffers.IBTheory.
Require Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.inflate.StepHd5.
Require Import Zlib.proof.harness.inflate_pieces.TheoryStep.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant at the call boundaries                                                           *)

(* no gz_header, a mode of the decoder proper (HEAD .. BAD: not MEM, not SYNC), and swfW (the gzip extra
   field's length and the bit buffer before it, which the wide inflate_specW requires) *)
Definition pinv (z: zfields) (L: live) : Prop :=
  i_head (l_s L) = false /\ HEAD <= i_mode (l_s L) <= BAD /\ swfW (l_s L).

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head                                                                   *)

Lemma pc_m_init_hdrW: forall z L inp, swfW (l_s L) -> hdrW (m_init z L inp).
Proof.
  intros z L inp [A B]. unfold hdrW, m_init, m_mode; cbn [m_s m_bits m_hold].
  destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [E|E]; cbn [i_mode i_bits i_hold i_length];
    [split; intros F; exfalso; vm_compute in F; discriminate F | split; assumption].
Qed.

Lemma pc_m_init_mwf3W: forall z L inp,
  live_ok L -> zf_ok z -> Zlength inp <= Int.max_unsigned -> bytes_ok inp -> swfW (l_s L) ->
  mwf3W (m_init z L inp).
Proof.
  intros z L inp (HP & HS & HM & HH & HS3 & _) HZ HI HB HW.
  destruct HZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  pose proof (Zlength_nonneg inp).
  split.
  - pose proof (sw_hold _ HS). pose proof (sw_bits _ HS).
    constructor; unfold m_init; simpl;
      try (fold (IBRun.ib_typedo (l_s L)));
      try (apply IBRun.ib_typedo_modewf; exact HM);
      try (apply IBRun.ib_typedo_swf; exact HS);
      try exact HH;
      unfold urange, lrange, Z_OK in *; rewrite ?Zlength_nil;
      try solve [lia | split; [lia | auto] | split; [lia | constructor] | left; reflexivity].
  - split; [apply IBRun.ib_typedo_swf3; exact HS3 | apply pc_m_init_hdrW; exact HW].
Qed.

Lemma pc_typedo_wrap s : i_wrap (IBRun.ib_typedo s) = i_wrap s.
Proof. unfold IBRun.ib_typedo. destruct (_ =? _); reflexivity. Qed.

Lemma pc_typedo_mode s : HEAD <= i_mode s <= BAD -> HEAD <= i_mode (IBRun.ib_typedo s) <= BAD.
Proof.
  unfold IBRun.ib_typedo. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE); [|auto].
  cbn. wmodes. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

Section Run.
Variables (flush: Z) (z: zfields) (L: live) (inp: list Z).

(* what the call gives (Res r m: the return value and the final machine) *)
Definition ppost (res: result) : Prop :=
  let m := r_m res in
  m_inp m = inp /\ m_aout m = zf_ao z /\
  m_sow m = Zlength (m_ow m) /\ Zlength (m_ow m) <= zf_ao z /\
  i_head (m_s m) = i_head (l_s L) /\ i_wrap (m_s m) = i_wrap (l_s L) /\
  (r_ret res <> Z_MEM_ERROR ->
     m_tin m = u64 (zf_tin z + m_snx m) /\ m_tout m = u64 (zf_tout z + m_sow m) /\
     HEAD <= m_mode m <= BAD /\ code_doc (r_ret res) /\ swfW (m_s m)).

(* the loop invariant *)
Definition pJ (m: mst) : Prop :=
  mwf3W m /\ m_leave m = 0 /\ m_inp m = inp /\ m_aout m = zf_ao z /\ m_tin m = zf_tin z /\
  (m_tout m + m_out m) mod 2 ^ 64 = (zf_tout z + zf_ao z) mod 2 ^ 64 /\ m_left m <= m_out m /\
  (hdr_md (m_mode m) -> Zlength (m_ow m) = 0 /\ m_out m = zf_ao z /\ m_tout m = zf_tout z) /\
  i_head (m_s m) = i_head (l_s L) /\ i_wrap (m_s m) = i_wrap (l_s L) /\ md_rng m /\
  (m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK).

Context (SW : stepf2_mwf3W_stmt).
Context (Hz : zf_ok z).
Context (Hinp : Zlength inp <= Int.max_unsigned).

Lemma pc_step_pre m : pJ m -> 0 <= m_left m <= m_out m /\ m_out m < 2 ^ 32.
Proof.
  intros ((W & _) & _ & _ & _ & _ & _ & J7 & _).
  pose proof (mwW_ow _ W) as [Ow _]. pose proof (mwW_out _ W) as O.
  unfold urange in O. unfold m_left in *. rep_lia.
Qed.

Lemma pc_brk m m' : pJ m -> stepf2 flush lenfix_list distfix_list m = IBrk m' ->
  trel m m' /\ mwf3W m' /\ i_head (m_s m') = i_head (m_s m) /\ i_wrap (m_s m') = i_wrap (m_s m) /\ rk m'.
Proof.
  intros J E. pose proof J as (W & Lv & _ & _ & _ & _ & _ & _ & _ & _ & Hr & Rt).
  destruct (pc_step_pre m J) as [P1 P2].
  pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
  pose proof (stepf2_pgood flush lenfix_list distfix_list m Hr Lv Rt) as G2. rewrite E in G2.
  pose proof (SW flush m W Lv) as W'. rewrite E in W'.
  pose proof (stepf2_hrel flush lenfix_list distfix_list m) as H. rewrite E in H.
  destruct G2 as [G2 G3].
  split; [exact G|]. split; [exact W'|]. split; [apply H|]. split; [exact G2 | exact G3].
Qed.

Lemma pc_mod_shift a b c M : a mod M = b mod M -> (a - c) mod M = (b - c) mod M.
Proof. intros H. rewrite Zminus_mod, H, <- Zminus_mod. reflexivity. Qed.

Lemma pc_u64_small x : 0 <= x <= Int64.max_unsigned -> u64 x = x.
Proof. intros H. unfold u64. apply Z.mod_small. unfold Int64.max_unsigned in H. rep_lia. Qed.

(* inf_leave changes none of the fields swfW looks at but restores hold and bits from the machine *)
Lemma pc_uw_length s d : i_length (updatewindow s d) = i_length s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; reflexivity.
Qed.

Lemma pc_leave_length fl m : i_length (m_s (r_m (leave_fin fl m))) = i_length (m_s m).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok fl m); cbn -[updatewindow u32 u64];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn -[updatewindow u32 u64]; rewrite ?pc_uw_length; reflexivity.
Qed.

Lemma pc_uw_flags s d : i_flags (updatewindow s d) = i_flags s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; reflexivity.
Qed.

Lemma pc_leave_flags fl m : i_flags (m_s (r_m (leave_fin fl m))) = i_flags (m_s m).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok fl m); cbn -[updatewindow u32 u64];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn -[updatewindow u32 u64]; rewrite ?pc_uw_flags; reflexivity.
Qed.

Lemma pc_leave_swf fl m : hdrW m -> swfW (m_s (r_m (leave_fin fl m))).
Proof.
  intros [A B].
  destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_leave_fin fl m)
    as (_ & _ & _ & _ & _ & _ & _ & R8 & R9 & R10 & _).
  unfold swfW. rewrite R8, R9, R10, pc_leave_length, pc_leave_flags. split; assumption.
Qed.

Lemma pc_loop m o : loop2 flush lenfix_list distfix_list m o -> pJ m ->
  match o with
  | IRet r m' => ppost (Res r m' None)
  | IBrk m' => forall res, inf_leave flush m' res -> ppost res
  end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros J.
  - pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct (pc_step_pre m J) as [P1 P2].
    pose proof (stepf2_tgood flush lenfix_list distfix_list m Hr P1 P2) as G. rewrite E in G.
    pose proof (stepf2_pgood flush lenfix_list distfix_list m Hr Lv Rt) as G2. rewrite E in G2.
    pose proof (SW flush m W Lv) as W'. rewrite E in W'.
    pose proof (stepf2_hrel flush lenfix_list distfix_list m) as H. rewrite E in H.
    destruct G as (Rr & Th & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    destruct G2 as (G2 & G3).
    destruct (J6 Th) as (K1 & K2 & K3).
    pose proof (mwW_nx _ (proj1 W')) as Nx. pose proof (mwW_in _ (proj1 W)) as In.
    destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
    unfold ppost; cbn [r_m r_ret].
    split; [congruence|]. split; [congruence|]. split; [exact T5|]. split; [lia|].
    split; [destruct H as (H & _); congruence|]. split; [congruence|].
    intros _. rewrite T9, J3, T4, In, J1.
    replace (Zlength inp - (Zlength inp - m_nx m')) with (m_nx m') by lia.
    unfold u32; rewrite (Z.mod_small (m_nx m')) by (rewrite T1, J1 in Nx; rep_lia).
    split; [reflexivity|]. split; [rewrite T8, K3, T5, T6, K1, Z.add_0_r, pc_u64_small by lia; reflexivity|].
    split; [unfold m_mode in *; rewrite G3; wmodes; lia|].
    subst r. split; [unfold code_doc; auto|].
    try unfold m_mode in G3. split; intros F; exfalso; rewrite G3 in F; vm_compute in F; discriminate F.
  - destruct (pc_brk m m' J E) as (T & W' & Hh & Hw & Rk).
    pose proof J as (W & Lv & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & Hr & Rt).
    destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (mwW_out _ (proj1 W')) as O'.
    pose proof (mwW_ow _ (proj1 W')) as [Ow' _]. pose proof (mwW_nx _ (proj1 W')) as Nx.
    pose proof (mwW_in _ (proj1 W')) as In'.
    destruct Hz as (Z1 & Z2 & Z3 & Z4 & _).
    intros res Hres. inversion Hres; subst.
    + unfold ppost; cbn. split; [congruence|]. split; [congruence|]. split; [reflexivity|].
      split; [lia|]. split; [congruence|]. split; [congruence|]. intros N; contradiction.
    + destruct (IBRun.ib_leave_fin flush m') as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_leave_fin flush m')
        as (R1 & _ & _ & _ & _ & _ & _ & R8 & _ & _ & R11 & _).
      unfold ppost. rewrite F1, F2, F3, F4, F5, F6, F7, F8, R1. unfold m_mode. rewrite R8, R11.
      split; [congruence|]. split; [congruence|]. split; [reflexivity|]. split; [lia|].
      split; [congruence|]. split; [congruence|]. intros _.
      unfold m_have, m_left in *. rewrite In', T4, J3.
      replace (Zlength (m_inp m') - (Zlength (m_inp m') - m_nx m')) with (m_nx m') by lia.
      unfold urange in O'.
      split; [unfold u32; rewrite (Z.mod_small (m_nx m')) by (rewrite T1, J1 in Nx; rep_lia); reflexivity|].
      specialize (T7 J5).
      split.
      { unfold u32; rewrite Z.mod_small by rep_lia.
        unfold u64. replace (m_tout m' + (m_out m' - (m_aout m' - Zlength (m_ow m'))))
          with (m_tout m' + m_out m' - (m_aout m' - Zlength (m_ow m'))) by lia.
        rewrite (pc_mod_shift _ _ _ _ T6), (pc_mod_shift _ _ _ _ J4), T2, J2. f_equal. lia. }
      split; [exact T9|].
      split; [| exact (pc_leave_swf flush m' (proj2 (proj2 W')))].
      destruct Rk as (Rk1 & Rk2 & Rk3).
      unfold Zlib.proof.harness.inflate_codes.TheoryRun.rn_bufret, code_doc.
      destruct (_ && _)%bool; [right; right; right; right; reflexivity|].
      destruct (Z.eq_dec (m_mode m') BAD) as [B|B]; [right; right; right; left; apply Rk3; auto|].
      destruct (Z.eq_dec (m_mode m') DONE) as [D|D]; [right; left; apply Rk2; auto|].
      left; apply Rk1; auto.
  - destruct (pc_brk m m' J E) as (T & W' & Hh & Hw & Rk).
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

End Run.

Lemma pc_J_init z L inp : live_ok L -> zf_ok z -> bytes_ok inp -> Zlength inp <= Int.max_unsigned ->
  pinv z L -> pJ z L inp (m_init z L inp).
Proof.
  intros HL Hz Hb Hn (P1 & P2 & P3).
  assert (W: mwf3W (m_init z L inp)) by (apply pc_m_init_mwf3W; auto).
  unfold pJ, m_left, md_rng, m_mode, m_init; cbn [m_leave m_inp m_aout m_tin m_tout m_out m_ow m_s m_ret].
  rewrite Zlength_nil. fold (IBRun.ib_typedo (l_s L)).
  rewrite IBRun.ib_typedo_head, pc_typedo_wrap.
  pose proof (pc_typedo_mode _ P2).
  split; [exact W|]. repeat split; try reflexivity; try lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The other functions                                                                            *)

Lemma pc_init_mode sp w : wbits_ok w = true -> i_mode (l_s (init_live sp w)) = HEAD.
Proof.
  unfold wbits_ok, init_live. destruct (reset2_wb w) as [[wrap wb]|]; [|discriminate]. intros _.
  unfold init_s, reset2_s, reset_s, reset_keep_s, zero_s. destruct (_ && _)%bool; reflexivity.
Qed.

Lemma pc_setdict_s s dict :
  i_head (setdict_s s dict) = i_head s /\ i_mode (setdict_s s dict) = i_mode s /\
  i_wrap (setdict_s s dict) = i_wrap s.
Proof.
  unfold setdict_s. destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_uw s dict) as (A & _ & _ & D & E & _).
  cbn -[updatewindow]. auto.
Qed.

Lemma pc_setdict_swf s dict : swfW s -> swfW (setdict_s s dict).
Proof.
  unfold setdict_s, swfW. destruct (Zlib.proof.harness.inflate_codes.TheoryRun.rn_uw s dict) as (A & B & C & _).
  cbn -[updatewindow]. rewrite A, B, C, pc_uw_length, pc_uw_flags. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                      *)

(* the facts hold of pinv (Progress.v proves more of the same invariant) *)
Lemma pinv_facts : stepf2_mwf3W_stmt -> pieces_facts pinv.
Proof.
  intros SW. constructor.
  - intros w z sp W _ _ _ _ _ _. split.
    + exact (proj1 (IBTheory.ib_init w sp W)).
    + split; [rewrite (pc_init_mode sp w W); wmodes; lia|].
      unfold swfW. rewrite (pc_init_mode sp w W). split; intros F; vm_compute in F; discriminate F.
  - intros z L [H _]. exact H.
  - intros z L (_ & _ & H). exact H.
  - intros z L dict alloc_ok winp (P1 & P2 & P3) _ _ _ _ N.
    unfold setdict_f in *. destruct (setdict_check (l_s L) dict); cbn in N |- *.
    + unfold pinv; intuition auto.
    + unfold pinv; intuition auto.
    + destruct (pc_setdict_s (l_s L) dict) as (S1 & S2 & S3).
      destruct (i_win (l_s L)); [|destruct alloc_ok; [|exfalso; apply N; reflexivity]];
        unfold fst3, snd3, thd3, pinv, wrap_of, set_l_s, set_l_winp; cbn -[setdict_s];
        rewrite S1, S2, S3; intuition auto using pc_setdict_swf.
  - intros z L strmp flush ib inp o aout r z' st' ow PI HL Hz Hs Hf Hib Hin Hout Hlen Haout Hrel Hr.
    destruct Hrel as [(Bad & _) | (NB & L0 & o0 & res & winp & Est & Eob & Run & Snx & Er & Eow & Ez & _ & Est')].
    + exfalso. unfold inflate_bad, is_live in Bad.
      destruct (eq_dec strmp nullval); [contradiction|].
      destruct Bad as [Bad | [Bad | (Bad & _)]]; discriminate || contradiction.
    + inversion Est; subst L0. inversion Eob; subst o0.
      assert (Ha0: 0 <= aout) by (destruct o; unfold out_ok in Hout; tauto).
      assert (Hb: bytes_ok inp) by (destruct ib; [contradiction | unfold in_ok in Hin; tauto]).
      set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
      assert (Hz0: zf_ok z0).
      { destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). pose proof (Zlength_nonneg inp).
        unfold zf_ok, z0, offer_z; cbn. repeat split; rep_lia. }
      destruct Run as (ol & Hlo & Hres).
      pose proof (pc_loop flush z0 L inp SW Hz0 Hlen _ _ Hlo (pc_J_init z0 L inp HL Hz0 Hb Hlen PI)) as H.
      assert (Hp: ppost z0 L inp res).
      { destruct ol as [m'|r' m']; [exact (H res Hres) | subst res; exact H]. }
      destruct Hp as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      subst r. destruct (Q7 Hr) as (Q8 & Q9 & Q10 & Q11 & Q12).
      destruct PI as (P1 & P2 & P3).
      eexists. split; [exact Est'|].
      subst z'. unfold z_after, pinv, wrap_of; cbn [l_s zf_ai zf_ao zf_ni zf_no zf_tin zf_tout].
      unfold z0, offer_z in Q2, Q4, Q8, Q9 |- *; cbn [zf_ao zf_tin zf_tout] in Q2, Q4, Q8, Q9 |- *.
      rewrite Q1, Q2. subst ow.
      split; [split; [congruence | split; [unfold m_mode in Q10; exact Q10 | exact Q12]]|].
      split; [exact Q6|]. split; [exact Q11|].
      pose proof (Zlength_nonneg (m_ow (r_m res))).
      split; [lia|]. split; [lia|].
      split; [f_equal; lia|]. split; [f_equal; lia|].
      split; [rewrite Q8; unfold u64; f_equal; lia|].
      split; [rewrite Q9; unfold u64; f_equal; lia|].
      lia.
Qed.

Lemma pieces_theory : stepf2_mwf3W_stmt -> exists P, pieces_facts P.
Proof. intros SW. exists pinv. exact (pinv_facts SW). Qed.

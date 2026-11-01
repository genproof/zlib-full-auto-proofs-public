(** * deflate_slow for wide streams: the loop invariant and the part statements

    Port of LTCSlowInv.v to [compress_pre2w] (DetCoreKit.v): [EIw] / [SIw] are LTCSlowInv.EI / SI with the
    wide precondition of the call's start, used only through [zwide_zall].  The split of deflate_slow
    ([dsl_*]), [msr], [rdy], [MID] and the facts that do not mention the invariant are LTCSlowInv's. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetCoreKit Zlib.proof.deflate.LTCSlowInv.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The invariant *)

(** What holds during the whole call: the call's precondition, the output state, the frame, the stream
    composed from the call's start, the bit chain and the events. *)
Definition EIw (s0 : dstate) (z0 : strm) (flush : Z) (s : dstate) (z : strm) (evs : list dev) : Prop :=
  compress_pre2w s0 z0 flush /\ fn_of s0 = 2 /\
  outok s /\ same_prm s0 s /\ api_eq s0 s /\ zall z /\ adler_ok (d_wrap s0) (z_adler z) /\
  (exists k x, zstep (d_wrap s0) z0 z k x /\ bytes x /\ k + ub s0 = sum_len evs + ub s) /\
  ev_chain (Gb s0 (z_total_out z0)) evs (Gb s (z_total_out z)) /\
  Forall (ev_ok s0 flush) evs.

(** The loop invariant (at the top of each iteration). *)
Definition SIw (s0 : dstate) (z0 : strm) (flush : Z) (s : dstate) (z : strm) (evs : list dev) : Prop :=
  W2 s /\ quiet s /\ Forall (fun e => ev_last e = 0) evs /\ EIw s0 z0 flush s z evs.

(** ** The result of one iteration's step: go on with the invariant and a smaller measure, or return *)
Definition step_okw (s0 : dstate) (z0 : strm) (flush : Z) (s : dstate) (z : strm)
    (r : (dstate * strm) + dexit) : Prop :=
  match r with
  | inl (s', z') => exists evs', SIw s0 z0 flush s' z' evs' /\ msr s' z' < msr s z
  | inr (s', z', Some bs) => exists evs', cpost W2 s0 z0 flush s' z' bs evs'
  | inr (_, _, None) => False
  end.

(** ** The parts *)

(** The refill (fill_window). *)
Definition refill_partw : Prop :=
  forall s0 z0 flush s z evs, SIw s0 z0 flush s z evs ->
  exists r, c_refill need_min_lookahead flush s z = Some r /\
  match r with
  | inl (s', z') => SIw s0 z0 flush s' z' evs /\ rdy s' /\ msr s' z' <= msr s z
  | inr (s', z', None) =>
      SIw s0 z0 flush s' z' evs /\ d_lookahead s' = 0 /\ z_avail_in z' = 0 /\ flush <> Z_NO_FLUSH /\
      d_strstart s' + MIN_LOOKAHEAD <= d_window_size s'
  | inr (s', z', Some bs) => exists evs', cpost W2 s0 z0 flush s' z' bs evs'
  end.

(** INSERT_STRING, longest_match and the filter. *)
Definition pre_partw : Prop :=
  forall s0 z0 flush s z evs, SIw s0 z0 flush s z evs -> rdy s ->
  exists s1, dsl_pre s = Some s1 /\ MID s s1.

(** The match branch (the previous match is emitted). *)
Definition match_partw : Prop :=
  forall s0 z0 flush s z evs s1, SIw s0 z0 flush s z evs -> rdy s -> MID s s1 ->
  MIN_MATCH <= d_prev_length s1 -> d_match_length s1 <= d_prev_length s1 ->
  exists r, dsl_match s1 z = Some r /\ step_okw s0 z0 flush s z r.

(** The pending-literal branch. *)
Definition lit_partw : Prop :=
  forall s0 z0 flush s z evs s1, SIw s0 z0 flush s z evs -> rdy s -> MID s s1 ->
  ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 <> 0 ->
  exists r, dsl_lit s1 z = Some r /\ step_okw s0 z0 flush s z r.

(** The new-candidate branch. *)
Definition cand_partw : Prop :=
  forall s0 z0 flush s z evs s1, SIw s0 z0 flush s z evs -> rdy s -> MID s s1 ->
  ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 = 0 ->
  exists r, dsl_cand s1 z = Some r /\ step_okw s0 z0 flush s z r.

(** After the loop's break. *)
Definition end_partw : Prop :=
  forall s0 z0 flush s z evs, SIw s0 z0 flush s z evs ->
  d_lookahead s = 0 -> z_avail_in z = 0 -> flush <> Z_NO_FLUSH ->
  d_strstart s + MIN_LOOKAHEAD <= d_window_size s ->
  exists s' z' bs evs', dsl_end s z flush = Some (s', z', bs) /\ cpost W2 s0 z0 flush s' z' bs evs'.

(** FLUSH_BLOCK_ONLY as an event (shared by the match / literal branches and the end). *)
Definition fboev_partw : Prop :=
  forall s0 z0 flush s z evs syms last,
    EIw s0 z0 flush s z evs -> fbo_pre s z syms last -> Forall (sym_ok s) syms ->
    (last = 1 -> flush = Z_FINISH) ->
    (last = 0 -> Zlength syms = d_L s - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) ->
    (d_block_start s < 0 -> MAX_DIST s < d_strstart s - d_block_start s) ->
    exists s' z' e,
      c_flush_block_only s z last = Some (s', z') /\ ev_last e = last /\
      EIw s0 z0 flush s' z' (evs ++ [e]) /\
      fbo_keep s' = fbo_keep s /\ d_block_start s' = d_strstart s /\
      tree_ok (d_tr s') (d_pbm s') [] /\ tr_cfg (d_tr s') = tr_cfg (d_tr s) /\ d_matches s' = 0 /\
      d_bi_valid s' <= 7 /\ (last = 1 -> d_bi_valid s' = 0) /\
      (d_pending s' = 0 \/ z_avail_out z' = 0) /\ z_avail_in z' = z_avail_in z.

(** ** Small proved facts *)

Lemma EIw_need_more s0 z0 flush s z evs :
  W2 s -> Forall (fun e => ev_last e = 0) evs -> EIw s0 z0 flush s z evs -> d_bi_valid s <= 7 ->
  (flush = Z_NO_FLUSH \/ z_avail_out z = 0) ->
  cpost W2 s0 z0 flush s z need_more evs.
Proof.
  intros HW HL (_ & _ & Ho & Hsp & Hapi & _ & _ & Hz & Hc & He) Hbv Hf.
  unfold cpost. split; [exact HW|]. split; [exact Ho|]. split; [exact Hsp|]. split; [exact Hapi|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact He|]. split; [exact HL|]. split; [exact Hbv|].
  destruct Hf as [Hf|Hf]; auto.
Qed.

Lemma SIw_need_more s0 z0 flush s z evs :
  SIw s0 z0 flush s z evs -> (flush = Z_NO_FLUSH \/ z_avail_out z = 0) ->
  cpost W2 s0 z0 flush s z need_more evs.
Proof. intros (HW & Hq & HL & HE) Hf. exact (EIw_need_more s0 z0 flush s z evs HW HL HE (proj2 (proj2 Hq)) Hf). Qed.

Lemma SIw_init s z flush : compress_pre2w s z flush -> fn_of s = 2 -> SIw s z flush s z [].
Proof.
  intros Hc Hf. pose proof Hc as (HW & Ho & Hq & Hfl & Hz & Hw & Ha).
  split; [exact HW|]. split; [exact Hq|]. split; [constructor|].
  split; [exact Hc|]. split; [exact Hf|]. split; [exact Ho|].
  split; [apply same_prm_refl|]. split; [apply api_eq_refl|].
  split; [apply zwide_zall; exact Hz|]. split; [exact Ha|].
  split; [|split; [reflexivity|constructor]].
  exists 0, []. split; [apply zstep_refl; [apply zwide_zall; exact Hz|exact Ha]|].
  split; [constructor|]. cbn. lia.
Qed.

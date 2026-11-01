(** * The compression functions consume input or write output when they ask for more

    deflate()'s compression stage returns Z_OK when the compression function (deflate_stored, deflate_fast,
    deflate_slow, deflate_rle, deflate_huff) returns need_more.  compress2_z's loop calls deflate() again after a
    Z_OK, so it ends only if every such call moves on: a compression function called with output space, and
    with input or Z_FINISH, that returns need_more has consumed input or written output.  (Level > 0: need_more
    comes from fill_window running out of input, or from a block flush that filled the output space; level 0:
    deflate_stored reads into the window when it has room, and otherwise has a full window, which it writes out
    as a stored block.) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWIface Zlib.proof.deflate.LTCore.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Reading the checked models backwards

    [mstep H] takes the first [let*], [if] or pair pattern of the hypothesis [H : run = Some r] apart; [mrun H]
    repeats it until the run is a constructor, dropping the branches where it is [None].  [bind] is reduced only
    on a constructor: a [match] on a call of the model (fill_window's loop, ...) left in [H] leads the kernel
    to evaluate that call when it checks the proof. *)
Ltac mstep H :=
  cbn [bind] in H;
  lazymatch type of H with
  | bind ?e _ = _ => first [is_var e; destruct e | let E := fresh "E" in destruct e eqn:E]
  | (match ?e with _ => _ end) = _ => first [is_var e; destruct e | let E := fresh "E" in destruct e eqn:E]
  end;
  cbn [bind] in H; try discriminate H.

Ltac mrun H := repeat mstep H.

(** [mrun] on every hypothesis [run = Some r] (the conditions of a [let*] land in their own equation). *)
Ltac mall := repeat match goal with H : _ = Some _ |- _ => progress (mrun H) end.

(** The tested conditions as propositions. *)
Ltac bnorm :=
  repeat match goal with
  | H : guard ?b = Some _ |- _ =>
      unfold guard in H; let B := fresh "B" in destruct b eqn:B; [clear H|discriminate H]
  | H : context [Z.gtb _ _] |- _ => rewrite Z.gtb_ltb in H
  | H : context [Z.geb _ _] |- _ => rewrite Z.geb_leb in H
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  | H : (_ || _) = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ && _) = false |- _ => apply andb_false_iff in H; destruct H
  | H : (_ || _) = true |- _ => apply orb_true_iff in H; destruct H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end.

Lemma bind_some {A B : Type} (e : option A) (f : A -> option B) r :
  bind e f = Some r -> exists x, e = Some x /\ f x = Some r.
Proof. destruct e as [x|]; cbn; [eauto|discriminate]. Qed.

(** The last iteration of a loop that returned [r]. *)
Lemma runs_last {A B : Type} (body : A -> option (A + B)) a r :
  runs body a r -> exists a', body a' = Some (inr r).
Proof. induction 1; eauto. Qed.

Lemma loop_last {A B : Type} d (body : A -> option (A + B)) a r :
  loop d body a = Some r -> exists a', body a' = Some (inr r).
Proof. intros H. exact (runs_last body a r (loop_runs d body a r H)). Qed.

(** ** Levels 1 to 9: [need_more] means the input ran out (Z_NO_FLUSH) or the output space is full *)

(** fill_window's do-while ends with [MIN_LOOKAHEAD] bytes of lookahead or without input. *)
Lemma fill_end s z s' z' :
  c_fill_window s z = Some (s', z') -> MIN_LOOKAHEAD <= d_lookahead s' \/ z_avail_in z' = 0.
Proof.
  unfold c_fill_window. intros H.
  destruct (loop FUEL fw_body (s, z)) as [[s1 z1]|] eqn:E; cbn [bind] in H; [|discriminate].
  destruct (c_fw_high_water s1) as [s2|] eqn:E2; cbn [bind] in H; [|discriminate].
  injection H as <- <-.
  assert (L : d_lookahead s2 = d_lookahead s1).
  { unfold c_fw_high_water in E2. mrun E2; injection E2 as <-; reflexivity. }
  rewrite L. clear E2 L.
  destruct (loop_last _ _ _ _ E) as [[s0 z0] B]. clear E.
  unfold fw_body in B. mrun B; injection B as <- <-.
  all: bnorm; auto.
Qed.

(** FLUSH_BLOCK returns [need_more] only with the output space full. *)
Lemma flush_block_nm s z last s' z' r :
  c_flush_block s z last = Some (s', z', Some r) -> r = need_more -> z_avail_out z' = 0.
Proof.
  unfold c_flush_block. intros H Hr. mrun H; injection H as <- <- <-; bnorm; auto.
Qed.

Lemma bflush_nm s z b s' z' :
  c_bflush s z b = Some (inr (s', z', Some need_more)) -> z_avail_out z' = 0.
Proof.
  unfold c_bflush. intros H. mrun H; injection H as <- <- ->.
  eapply flush_block_nm; [eassumption|reflexivity].
Qed.

Lemma tail_nm s z flush s' z' :
  c_deflate_tail s z flush = Some (s', z', need_more) -> z_avail_out z' = 0.
Proof.
  unfold c_deflate_tail. intros H. mrun H; injection H as <- <- Er; subst;
    try (eapply flush_block_nm; [eassumption|reflexivity]); discriminate.
Qed.

(** The refill at the top of the main loops: [need_more] when fill_window left too little lookahead at
    Z_NO_FLUSH, so without input. *)
Lemma refill_nm need flush s z s' z' :
  (forall t, need t = true -> d_lookahead t < MIN_LOOKAHEAD) ->
  c_refill need flush s z = Some (inr (s', z', Some need_more)) ->
  flush = Z_NO_FLUSH /\ z_avail_in z' = 0.
Proof.
  unfold c_refill. intros Hn H.
  destruct (need s); [|discriminate].
  destruct (c_fill_window s z) as [[s1 z1]|] eqn:F; cbn [bind] in H; [|discriminate].
  destruct (need s1) eqn:N; destruct (Z.eqb_spec flush Z_NO_FLUSH) as [Ef|Ef];
    cbv beta iota delta [andb] in H; try (destruct (d_lookahead s1 =? 0); discriminate).
  injection H as <- <-. split; [exact Ef|].
  destruct (fill_end _ _ _ _ F) as [L|L]; [pose proof (Hn _ N); lia|exact L].
Qed.

Lemma need_min_ok t : need_min_lookahead t = true -> d_lookahead t < MIN_LOOKAHEAD.
Proof. unfold need_min_lookahead. intros H. bnorm. exact H. Qed.

Lemma need_rle_ok t : need_rle t = true -> d_lookahead t < MIN_LOOKAHEAD.
Proof. unfold need_rle. intros H. bnorm. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. lia. Qed.

Definition nm_ok (flush : Z) (z' : strm) : Prop := (flush = Z_NO_FLUSH /\ z_avail_in z' = 0) \/ z_avail_out z' = 0.

Lemma df_step_nm s z s' z' : df_step s z = Some (inr (s', z', Some need_more)) -> z_avail_out z' = 0.
Proof. unfold df_step. intros H. mrun H; eapply bflush_nm; eassumption. Qed.

Lemma dsl_step_nm s z s' z' : dsl_step s z = Some (inr (s', z', Some need_more)) -> z_avail_out z' = 0.
Proof.
  unfold dsl_step. intros H. mrun H; try (eapply bflush_nm; eassumption);
    injection H as <- <-; bnorm; assumption.
Qed.

Lemma rle_step_nm s z s' z' : rle_step s z = Some (inr (s', z', Some need_more)) -> z_avail_out z' = 0.
Proof. unfold rle_step. intros H. mrun H; eapply bflush_nm; eassumption. Qed.

Lemma fast_nm s z flush s' z' : c_deflate_fast s z flush = Some (s', z', need_more) -> nm_ok flush z'.
Proof.
  unfold c_deflate_fast, nm_ok. intros H.
  destruct (loop FUEL (df_body flush) (s, z)) as [[[s1 z1] [r|]]|] eqn:E; cbn [bind] in H; try discriminate.
  - injection H as <- <- ->. destruct (loop_last _ _ _ _ E) as [[s0 z0] B]. unfold df_body in B.
    destruct (c_refill need_min_lookahead flush s0 z0) as [[[s2 z2]|e]|] eqn:R; cbn [bind] in B; try discriminate.
    + right. exact (df_step_nm _ _ _ _ B).
    + injection B as ->. left. exact (refill_nm _ _ _ _ _ _ need_min_ok R).
  - right. exact (tail_nm _ _ _ _ _ H).
Qed.

Lemma slow_nm s z flush s' z' : c_deflate_slow s z flush = Some (s', z', need_more) -> nm_ok flush z'.
Proof.
  unfold c_deflate_slow, nm_ok. intros H.
  destruct (loop FUEL (dsl_body flush) (s, z)) as [[[s1 z1] [r|]]|] eqn:E; cbn [bind] in H; try discriminate.
  - injection H as <- <- ->. destruct (loop_last _ _ _ _ E) as [[s0 z0] B]. unfold dsl_body in B.
    destruct (c_refill need_min_lookahead flush s0 z0) as [[[s2 z2]|e]|] eqn:R; cbn [bind] in B; try discriminate.
    + right. exact (dsl_step_nm _ _ _ _ B).
    + injection B as ->. left. exact (refill_nm _ _ _ _ _ _ need_min_ok R).
  - right. mrun H; exact (tail_nm _ _ _ _ _ H).
Qed.

Lemma rle_nm s z flush s' z' : c_deflate_rle s z flush = Some (s', z', need_more) -> nm_ok flush z'.
Proof.
  unfold c_deflate_rle, nm_ok. intros H.
  destruct (loop FUEL (rle_body flush) (s, z)) as [[[s1 z1] [r|]]|] eqn:E; cbn [bind] in H; try discriminate.
  - injection H as <- <- ->. destruct (loop_last _ _ _ _ E) as [[s0 z0] B]. unfold rle_body in B.
    destruct (c_refill need_rle flush s0 z0) as [[[s2 z2]|e]|] eqn:R; cbn [bind] in B; try discriminate.
    + right. exact (rle_step_nm _ _ _ _ B).
    + injection B as ->. left. exact (refill_nm _ _ _ _ _ _ need_rle_ok R).
  - right. exact (tail_nm _ _ _ _ _ H).
Qed.

Lemma huff_nm s z flush s' z' : c_deflate_huff s z flush = Some (s', z', need_more) -> nm_ok flush z'.
Proof.
  unfold c_deflate_huff, nm_ok. intros H.
  destruct (loop FUEL (huff_body flush) (s, z)) as [[[s1 z1] [r|]]|] eqn:E; cbn [bind] in H; try discriminate.
  - injection H as <- <- ->. destruct (loop_last _ _ _ _ E) as [[s0 z0] B]. unfold huff_body in B.
    mrun B; try (right; eapply bflush_nm; eassumption).
    injection B as ->.
    match goal with E0 : _ = Some (inr (s1, z1, Some need_more)) |- _ => mrun E0; injection E0 as <- <- end.
    bnorm. left. split; [assumption|].
    match goal with F : c_fill_window _ _ = Some _ |- _ =>
      destruct (fill_end _ _ _ _ F) as [L|L]; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L; lia|exact L] end.
  - right. exact (tail_nm _ _ _ _ _ H).
Qed.

(** The dispatch at levels 1 to 9. *)
Lemma dispatch_pos s z flush : prm s -> d_level s <> 0 ->
  c_compress_func s z flush = c_deflate_fast s z flush \/ c_compress_func s z flush = c_deflate_slow s z flush \/
  c_compress_func s z flush = c_deflate_huff s z flush \/ c_compress_func s z flush = c_deflate_rle s z flush.
Proof.
  intros Hp Hl.
  assert (Hr : 0 <= d_level s <= 9)
    by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  unfold c_compress_func. apply Z.eqb_neq in Hl. rewrite Hl.
  destruct (d_strategy s =? Z_HUFFMAN_ONLY); [auto|].
  destruct (d_strategy s =? Z_RLE); [auto|].
  apply Z.eqb_neq in Hl.
  destruct (Zlib.proof.deflate.LTCMisc.cfg_func_eq (d_level s) ltac:(lia)) as [E [E1|E1]]; rewrite E;
    cbn [bind]; rewrite E1; cbn [Z.eqb Pos.eqb]; auto.
Qed.

(** Levels 1 to 9. *)
Lemma compress_nm_pos s z flush s' z' :
  prm s -> d_level s <> 0 -> c_compress_func s z flush = Some (s', z', need_more) -> nm_ok flush z'.
Proof.
  intros Hp Hl H.
  destruct (dispatch_pos s z flush Hp Hl) as [E|[E|[E|E]]]; rewrite E in H.
  - exact (fast_nm _ _ _ _ _ H).
  - exact (slow_nm _ _ _ _ _ H).
  - exact (huff_nm _ _ _ _ _ H).
  - exact (rle_nm _ _ _ _ _ H).
Qed.

(** ** Level 0: deflate_stored

    The counters of the stream only move down: read_buf takes bytes from avail_in, flush_pending and the direct
    copies of the first loop take bytes from avail_out.  A stored block put into pending is written, at least
    in part, by the flush_pending that follows it when there is output space. *)

Lemma pb_byte om c om' : c_put_byte om c = Some om' ->
  0 <= o_pending (fst om) /\ o_pending (fst om') = o_pending (fst om) + 1.
Proof.
  destruct om as [o m]. unfold c_put_byte, wr, in_range. intros H. mall.
  injection H as <-. bnorm. cbn. lia.
Qed.

Lemma pb_short om w om' : c_put_short om w = Some om' ->
  0 <= o_pending (fst om) /\ o_pending (fst om') = o_pending (fst om) + 2.
Proof.
  unfold c_put_short. intros H.
  destruct (c_put_byte om (Z.land w 255)) as [om1|] eqn:E1; cbn [bind] in H; [|discriminate].
  apply pb_byte in E1. apply pb_byte in H. lia.
Qed.

Lemma pb_flush om om' : c_bi_flush om = Some om' -> o_pending (fst om) <= o_pending (fst om').
Proof.
  destruct om as [o m]. unfold c_bi_flush. intros H. mrun H; injection H as <-; cbn; try lia;
    match goal with
    | E : c_put_short _ _ = Some _ |- _ => apply pb_short in E
    | E : c_put_byte _ _ = Some _ |- _ => apply pb_byte in E
    end; cbn in *; lia.
Qed.

(** A stored block (header, LEN / NLEN, data) leaves bytes pending. *)
Lemma stored_block_pend om buf len last om' :
  c_tr_stored_block om buf len last = Some om' -> 0 < o_pending (fst om').
Proof.
  unfold c_tr_stored_block. intros H. mall; injection H as <-; cbn;
    repeat match goal with E : c_put_short _ _ = Some _ |- _ => apply pb_short in E end;
    cbn in *; bnorm; lia.
Qed.

Lemma pb_wr_pend s i v s' : c_pb_wr s i v = Some s' -> d_pending s' = d_pending s.
Proof. unfold c_pb_wr. intros H. mrun H. injection H as <-. reflexivity. Qed.

Lemma mb_read_len b lo n l : mb_read b lo n = Some l -> Zlength l = n /\ 0 <= n.
Proof.
  unfold mb_read, mb_definedb. intros H. mrun H. injection H as <-. bnorm.
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma out_put_ok z b z' : out_put z b = Some z' ->
  Zlength b <= z_avail_out z /\ z_avail_out z' = z_avail_out z /\ z_avail_in z' = z_avail_in z.
Proof. unfold out_put. intros H. mrun H. injection H as <-. bnorm. cbn. lia. Qed.

Lemma read_buf_ok s z n z' d : c_read_buf s z n = Some (z', d) ->
  z_avail_out z' = z_avail_out z /\ z_avail_in z' = z_avail_in z - Zlength d /\ 0 <= Zlength d /\
  (0 <= n -> 0 <= z_avail_in z -> Zlength d = Z.min n (z_avail_in z)).
Proof.
  unfold c_read_buf. intros H.
  set (len := if z_avail_in z >? n then n else z_avail_in z) in H.
  assert (Hl : 0 <= n -> 0 <= z_avail_in z -> len = Z.min n (z_avail_in z)).
  { unfold len. destruct (Z.gtb_spec (z_avail_in z) n); lia. }
  assert (Hl2 : len = n \/ len = z_avail_in z) by (unfold len; destruct (z_avail_in z >? n); auto).
  clearbody len.
  destruct (len =? 0) eqn:L0; bnorm.
  - injection H as <- <-. rewrite Zlength_nil. lia.
  - cbn [bind] in H. unfold rds in H. cbn [z_in z_next_in set_z_avail_in] in H.
    destruct ((0 <=? z_next_in z) && (0 <=? len) && (z_next_in z + len <=? Zlength (z_in z))) eqn:R;
      cbn [bind z_in z_next_in set_z_avail_in] in H; [|discriminate].
    bnorm. injection H as <- <-. rewrite Zlength_sublist by lia.
    destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; cbn; lia.
Qed.

(** flush_pending: avail_in kept, avail_out down, and strictly down when bytes are pending and there is room. *)
Lemma fp_ok s z s' z' : c_flush_pending s z = Some (s', z') -> 0 <= z_avail_out z <= 4294967295 ->
  z_avail_in z' = z_avail_in z /\ 0 <= z_avail_out z' <= z_avail_out z /\
  (0 < z_avail_out z -> 0 < d_pending s -> z_avail_out z' < z_avail_out z).
Proof.
  unfold c_flush_pending. intros H Ha.
  destruct (c_tr_flush_bits (d_out s)) as [o|] eqn:Eo; cbn [bind] in H; [|discriminate].
  apply pb_flush in Eo. change (o_pending (fst (d_out s))) with (d_pending s) in Eo.
  set (P := d_pending (set_d_out s o)) in H.
  assert (HP : P = o_pending (fst o)) by reflexivity.
  set (len := if P >? z_avail_out z then z_avail_out z else u32 P) in H.
  assert (Hlen : (len = z_avail_out z /\ z_avail_out z < P) \/ (len = P mod 4294967296 /\ P <= z_avail_out z)).
  { unfold len, u32. destruct (Z.gtb_spec P (z_avail_out z)); auto. }
  clearbody len.
  destruct (len =? 0) eqn:L0; bnorm.
  - injection H as <- <-. split; [reflexivity|split; [lia|]]. intros A B.
    destruct Hlen as [[-> _]|[L1 L2]]; [lia|].
    rewrite Z.mod_small in L1 by lia. lia.
  - cbn [bind] in H. mrun H. injection H as <- <-. cbn.
    repeat match goal with
    | E : mb_read _ _ _ = Some _ |- _ => apply mb_read_len in E; destruct E
    | E : out_put _ _ = Some _ |- _ => apply out_put_ok in E; destruct E as (? & ? & ?)
    end.
    split; [assumption|]. lia.
Qed.

(** The first loop of deflate_stored: a [break] leaves the state as it is; an iteration writes a stored block
    header (and its data) directly to next_out, so it takes output space when there is some. *)
Lemma ds_exit0 flush mb s z s' z' :
  ds_body flush mb (s, z) = Some (inr (s', z', 0)) -> s' = s /\ z' = z.
Proof.
  unfold ds_body. intros H. mall; injection H; intros; subst; first [split; reflexivity | bnorm; congruence].
Qed.

Lemma pend_out s o : d_pending (set_d_out s o) = o_pending (fst o). Proof. reflexivity. Qed.
Lemma pend_bs s x : d_pending (set_d_block_start s x) = d_pending s. Proof. reflexivity. Qed.

(** Equalities of results taken apart. *)
Ltac minj := repeat match goal with H : Some _ = Some _ |- _ => injection H; clear H; intros; subst end.

(** What each step of deflate_stored does to the counters and to pending (the lengths of the copied blocks are
    named by the lists the reads return). *)
Ltac mfacts :=
  repeat match goal with
  | E : mb_read _ _ _ = Some _ |- _ =>
      apply mb_read_len in E; let A := fresh "A" in let B := fresh "B" in
      destruct E as [A B]; try rewrite <- A in *
  | E : out_put _ _ = Some _ |- _ => apply out_put_ok in E; destruct E as (? & ? & ?)
  | E : c_read_buf _ _ _ = Some (_, _) |- _ => apply read_buf_ok in E; destruct E as (? & ? & ? & ?)
  | E : c_tr_stored_block _ _ _ _ = Some _ |- _ => apply stored_block_pend in E
  | E : c_pb_wr _ _ _ = Some _ |- _ => apply pb_wr_pend in E
  end;
  bnorm; rewrite ?pend_out, ?pend_bs in *.

(** flush_pending's facts, for a stream whose avail_out is known to be a uInt. *)
Ltac mfp :=
  repeat match goal with E : c_flush_pending _ _ = Some (_, _) |- _ =>
    let F := fresh "F" in pose proof (fp_ok _ _ _ _ E) as F; clear E; specialize (F ltac:(lia)) end.

(** The counters of the stream after the setters, and [u32] of a number known to be a uInt. *)
Ltac mfin :=
  cbn [z_avail_out z_avail_in set_z_total_out set_z_avail_out set_z_out set_z_avail_in set_z_total_in
       set_z_next_in set_z_adler] in *;
  unfold u32 in *;
  repeat match goal with H : Zlength ?l = ?x |- context [?x] => progress rewrite <- H end;
  repeat match goal with
  | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
  | H : context [?x mod 4294967296] |- _ => rewrite (Z.mod_small x 4294967296) in H by lia
  end.

(** One iteration of the first loop.  The block length [len] is abstracted: only the shape of the loop's
    break test is used, not the comparisons that compute [len] and [last]. *)
Lemma ds_step flush mb s z s' z' :
  ds_body flush mb (s, z) = Some (inl (s', z')) -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_avail_in z ->
  0 <= z_avail_in z' <= z_avail_in z /\ 0 <= z_avail_out z' <= z_avail_out z /\
  (0 < z_avail_out z -> z_avail_out z' < z_avail_out z).
Proof.
  unfold ds_body. intros H Ho Hi. cbn [bind] in H.
  match type of H with context [(?L <? mb) && _] => set (len := L) in H; clearbody len end.
  mall; minj; mfacts; mfp; mfin; lia.
Qed.

(** The whole first loop: it breaks at once, or takes output space (and never adds input or output space). *)
Lemma ds_loop flush mb : forall a r, runs (ds_body flush mb) a r ->
  forall s z s1 z1, a = (s, z) -> r = (s1, z1, 0) -> 0 <= z_avail_out z <= 4294967295 -> 0 <= z_avail_in z ->
  (s1 = s /\ z1 = z) \/
  (0 <= z_avail_in z1 <= z_avail_in z /\ 0 <= z_avail_out z1 <= z_avail_out z /\
   (0 < z_avail_out z -> z_avail_out z1 < z_avail_out z)).
Proof.
  induction 1 as [a r Hb|a a' r Hb Hr IH]; intros s z s1 z1 -> -> Ho Hi.
  - left. exact (ds_exit0 _ _ _ _ _ _ Hb).
  - destruct a' as [s2 z2]. destruct (ds_step _ _ _ _ _ _ Hb Ho Hi) as (A & B & C).
    right. destruct (IH s2 z2 s1 z1 eq_refl eq_refl ltac:(lia) ltac:(lia)) as [[-> ->]|(D & F & G)]; lia.
Qed.

(** The window positions through the bookkeeping of deflate_stored's second part. *)
Lemma uhw_ss t : d_strstart (upd_high_water t) = d_strstart t.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma uhw_bs t : d_block_start (upd_high_water t) = d_block_start t.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma uhw_ws t : d_window_size (upd_high_water t) = d_window_size t.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma uhw_w t : d_w_size (upd_high_water t) = d_w_size t.
Proof. unfold upd_high_water. destruct (_ <? _); reflexivity. Qed.
Lemma im_w t : d_w_size (incr_matches t) = d_w_size t.
Proof. unfold incr_matches. destruct (_ <? _); reflexivity. Qed.

(** Only the counters of the streams: the other hypotheses dropped (they slow [lia] down). *)
Ltac zonly :=
  repeat match goal with
  | E : c_read_buf _ _ _ = Some (_, _) |- _ => apply read_buf_ok in E; destruct E as (? & ? & ? & _)
  end;
  repeat match goal with
  | H : ?l = Some _ |- _ => lazymatch l with c_flush_pending _ _ => fail | _ => clear H end
  | H : _ = true |- _ => clear H
  | H : _ = false |- _ => clear H
  end;
  mfp.

(** The test of deflate_stored's last stored block ([left >= min_block || ...]) holds when more than a window
    of bytes is waiting, or at Z_FINISH without input. *)
Lemma block_taken left have2 w ai flush :
  0 <= ai -> (w < left \/ (ai = 0 /\ flush = Z_FINISH)) ->
  ((left >=? (if have2 >? w then w else have2)) ||
   ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) && (ai =? 0) && (left <=? have2)))
  = true.
Proof.
  intros Ha [Hl|[-> ->]].
  - apply orb_true_iff. left. rewrite Z.geb_le. destruct (Z.gtb_spec have2 w); lia.
  - apply orb_true_iff. destruct (Z.leb_spec left have2).
    + right. rewrite Z.eqb_refl, orb_true_r. reflexivity.
    + left. rewrite Z.geb_le. destruct (Z.gtb_spec have2 w); lia.
Qed.

Lemma u32_small x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.
Lemma u64_small x : 0 <= x < 18446744073709551616 -> u64 x = x.
Proof. intros H. unfold u64. apply Z.mod_small. exact H. Qed.

(** deflate_stored with output space, and with input or Z_FINISH, that returns need_more has taken input or
    written output. *)
Lemma stored_prog s z flush s' z' :
  Zlib.proof.deflate.LTCW.W s -> d_level s = 0 -> zin_okw z -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
  c_deflate_stored s z flush = Some (s', z', need_more) -> 0 < z_avail_out z ->
  (0 < z_avail_in z \/ flush = Z_FINISH) ->
  z_avail_in z' < z_avail_in z \/ z_avail_out z' < z_avail_out z.
Proof.
  intros HW Hl Hz Hf H Ho Hi.
  destruct HW as (Hp & (_ & _ & Hws & _) & (Hla & Hss & Hsl & Hbs & _) & _ & _ & _ & H0 & _).
  destruct (H0 Hl) as [Hla0 Hbs0]. clear H0.
  destruct Hp as (Hwb & Hw & _).
  assert (Hwr : 512 <= d_w_size s <= 32768).
  { rewrite Hw. split; [change 512 with (2 ^ 9)|change 32768 with (2 ^ 15)];
      apply Z.pow_le_mono_r; lia. }
  destruct Hz as (_ & _ & Hai & _ & Hao & _).
  (* c_deflate_stored through its pieces (an unfolding of it would have the kernel evaluate the first loop) *)
  rewrite Zlib.proof.deflate.LTCStoredKit.c_deflate_stored_eq in H. cbn zeta in H.
  apply bind_some in H. destruct H as [[[s1 z1] last] [EL H]]. cbv beta iota zeta in H.
  apply bind_some in H. destruct H as [s2 [EW H]]. cbv beta iota zeta in H.
  unfold Zlib.proof.deflate.LTCStoredKit.ds_fill2, Zlib.proof.deflate.LTCStoredKit.ds_blk2 in H.
  destruct (last =? 0) eqn:EL0; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in EL0. subst last.
  apply loop_runs in EL.
  destruct (ds_loop _ _ _ _ EL s z s1 z1 eq_refl eq_refl ltac:(lia) ltac:(lia)) as [[-> ->]|(P1 & P2 & P3)].
  (* the first loop wrote output: the rest only moves the counters down *)
  2:{ right. clear EL EW. mall; minj; zonly;
       repeat match goal with F : _ /\ _ /\ (_ -> _ -> _) |- _ => destruct F as (? & ? & _) end; lia. }
  rewrite Z.sub_diag in EW. replace (u32 0) with 0 in EW by reflexivity.
  unfold c_ds_window in EW. rewrite Z.eqb_refl in EW. injection EW as <-. clear EL.
  (* the first loop did nothing: the state and the stream are the call's *)
  set (s3 := upd_high_water s) in H.
  assert (S3 : d_strstart s3 = d_strstart s /\ d_block_start s3 = d_block_start s /\
               d_window_size s3 = d_window_size s /\ d_w_size s3 = d_w_size s)
    by (unfold s3; rewrite uhw_ss, uhw_bs, uhw_ws, uhw_w; auto).
  destruct S3 as (S3s & S3b & S3ws & S3w). clearbody s3.
  assert (Hh0 : u32 (u64 (d_window_size s3 - d_strstart s3)) = 2 * d_w_size s - d_strstart s)
    by (rewrite S3ws, S3s, Hws, u64_small, u32_small; lia).
  mstep H.
  (* the slide of the window: [hv] is the room in the window for input *)
  match type of H with bind ?X _ = _ => destruct X as [[s4 hv]|] eqn:EX; cbn [bind] in H; [|discriminate] end.
  assert (HX : (s4 = s3 /\ hv = 2 * d_w_size s - d_strstart s /\
                (z_avail_in z <= 2 * d_w_size s - d_strstart s \/ d_block_start s < d_w_size s)) \/
               (0 < z_avail_in z /\ 0 < hv)).
  { rewrite Hh0 in EX. revert EX. clear - Hwr Hss Hsl Hla0 Hws S3w S3b S3s Hai Hbs0 Hbs. intros EX.
    mrun EX; injection EX; intros; subst; bnorm; rewrite ?S3b, ?S3w in *;
      first [ left; split; [reflexivity|split; [reflexivity|lia]]
            | right; rewrite im_w; cbn [d_w_size set_d_window set_d_strstart set_d_block_start];
              rewrite S3w, u32_small by lia; lia ]. }
  clear EX.
  (* the bytes read into the window *)
  set (hp := if hv >? z_avail_in z then z_avail_in z else hv) in H.
  assert (Hhp : hp = Z.min hv (z_avail_in z)) by (unfold hp; destruct (Z.gtb_spec hv (z_avail_in z)); lia).
  clearbody hp.
  destruct (hp =? 0) eqn:Ehp; cbn [bind] in H.
  - (* nothing read: the window is full, or Z_FINISH without input; a stored block goes to pending *)
    apply Z.eqb_eq in Ehp.
    destruct HX as [(-> & -> & HX)|(HX1 & HX2)]; [|lia].
    right. mstep H.
    erewrite block_taken in H.
    2:{ lia. }
    2:{ rewrite uhw_ss, uhw_bs, uhw_w, S3s, S3b, S3w, u32_small by lia.
        destruct (Z.eq_dec (z_avail_in z) 0) as [A0|A0]; [right|left; lia].
        destruct Hi as [Hi|Hi]; [lia|split; [exact A0|exact Hi]]. }
    mall; minj;
    repeat match goal with
    | E : c_tr_stored_block _ _ _ _ = Some _ |- _ => apply stored_block_pend in E
    | H : ?l = Some _ |- _ => lazymatch l with c_flush_pending _ _ => fail | _ => clear H end
    | H : _ = true |- _ => clear H
    | H : _ = false |- _ => clear H
    end;
    mfp; rewrite ?pend_bs, ?pend_out in *; lia.
  - (* [hp] bytes read *)
    apply Z.eqb_neq in Ehp. left.
    assert (Hhp0 : 0 < hp) by (destruct HX as [(_ & -> & _)|(_ & HX)]; lia).
    mall; minj;
    repeat match goal with
    | E : c_read_buf _ _ _ = Some (_, _) |- _ =>
        let A := fresh "A" in apply read_buf_ok in E; destruct E as (? & ? & ? & A);
        specialize (A ltac:(lia) ltac:(lia))
    end;
    repeat match goal with
    | H : ?l = Some _ |- _ => lazymatch l with c_flush_pending _ _ => fail | _ => clear H end
    | H : _ = true |- _ => clear H
    | H : _ = false |- _ => clear H
    end;
    mfp;
    repeat match goal with F : _ /\ _ /\ (_ -> _ -> _) |- _ => destruct F as (? & ? & _) end; lia.
Qed.

Lemma compress_progress : forall s z flush s' z' bs,
  W3 s -> outok s -> quiet s -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> zin_okw z ->
  0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
  c_compress_func s z flush = Some (s', z', bs) -> bs = need_more ->
  0 < z_avail_out z -> (0 < z_avail_in z \/ flush = Z_FINISH) ->
  z_avail_in z' < z_avail_in z \/ z_avail_out z' < z_avail_out z.
Proof.
  intros s z flush s' z' bs [[HW _] _] _ _ Hf Hz _ _ Hc -> Hao Hai.
  assert (Hp : prm s) by (destruct HW as (Hp & _); exact Hp).
  destruct (Z.eq_dec (d_level s) 0) as [L0|L0].
  - assert (F : Zlib.proof.deflate.LTCW.fn_of s = 0)
      by (unfold Zlib.proof.deflate.LTCW.fn_of; rewrite L0; reflexivity).
    rewrite (dispatch_stored s z flush Hp F) in Hc.
    exact (stored_prog s z flush s' z' HW L0 Hz Hf Hc Hao Hai).
  - destruct (compress_nm_pos s z flush s' z' Hp L0 Hc) as [[Hf0 Hi0]|Ho0].
    + left. destruct Hai as [Hai|Hai]; [lia|].
      exfalso. rewrite Hf0 in Hai. discriminate Hai.
    + right. lia.
Qed.

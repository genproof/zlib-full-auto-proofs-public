(* Law api_deflate_any: the return codes of deflate() and deflateParams() in the model (DModel4.v), for the
   checks of main (AnyFacts.v says why main needs them).  These are facts of the model functions alone. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DetFacts2.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The return codes of the stages of deflate()

    [stage_ok r]: the stage result [r] is a return of deflate() only with Z_OK or Z_BUF_ERROR (it may fall
    through, [Some (s, z, None)], or be undefined, [None]).  Every stage after the entry checks has this property;
    so has the entry for a valid flush outside FINISH_STATE (or Z_FINISH in it).  The proofs take the stages
    apart by their conditions and destruct the results of the functions they call (the compressors, the loops of
    the gzip header) without unfolding them. *)
Definition stage_ok (r : option dres) : Prop :=
  forall s z c, r = Some (s, z, Some c) -> c = Z_OK \/ c = Z_BUF_ERROR.

Lemma stage_ok_None : stage_ok None.
Proof. intros s z c H; discriminate. Qed.

Lemma stage_ok_next : forall s z, stage_ok (Some (s, z, None)).
Proof. intros s0 z0 s z c H; discriminate. Qed.

Lemma stage_ok_OK : forall s z, stage_ok (Some (s, z, Some Z_OK)).
Proof. intros s0 z0 s z c H; inversion H; auto. Qed.

Lemma stage_ok_BUF : forall s z, stage_ok (Some (s, z, Some Z_BUF_ERROR)).
Proof. intros s0 z0 s z c H; inversion H; auto. Qed.

Lemma stage_ok_bind : forall {A : Type} (a : option A) (f : A -> option dres),
  (forall x, stage_ok (f x)) -> stage_ok (bind a f).
Proof. intros A a f H; destruct a as [x|]; [apply H | apply stage_ok_None]. Qed.

Lemma stage_ok_then : forall r k,
  stage_ok r -> (forall s z, stage_ok (k s z)) -> stage_ok (then_stage r k).
Proof.
  intros r k Hr Hk; unfold then_stage.
  destruct r as [[[s z] [c|]]|]; cbn [bind].
  - intros s' z' c' H; inversion H; subst; eapply Hr; reflexivity.
  - apply Hk.
  - apply stage_ok_None.
Qed.

(** A stage computed first and then chained ([let* r := a in then_stage (Some r) k]). *)
Lemma stage_ok_bind_then : forall a k,
  stage_ok a -> (forall s z, stage_ok (k s z)) -> stage_ok (bind a (fun r => then_stage (Some r) k)).
Proof.
  intros a k Ha Hk; destruct a as [r|]; cbn [bind]; [| apply stage_ok_None].
  apply stage_ok_then; auto.
Qed.

Ltac stage_ok_t :=
  repeat (cbv beta zeta;
    match goal with
    | |- stage_ok None => apply stage_ok_None
    | |- stage_ok (Some (_, _, None)) => apply stage_ok_next
    | |- stage_ok (Some (_, _, Some Z_OK)) => apply stage_ok_OK
    | |- stage_ok (Some (_, _, Some Z_BUF_ERROR)) => apply stage_ok_BUF
    | |- stage_ok (bind _ (fun r => then_stage (Some r) _)) => apply stage_ok_bind_then; [| intros ? ?]
    | |- stage_ok (bind _ _) => apply stage_ok_bind; intros ?
    | |- stage_ok (then_stage _ _) => apply stage_ok_then; [| intros ? ?]
    | |- stage_ok (if ?b then _ else _) => destruct b
    | |- stage_ok (match ?x with _ => _ end) => destruct x
    end).

Lemma flush_or_return_ok : forall s z, stage_ok (c_flush_or_return s z).
Proof. intros; unfold c_flush_or_return; stage_ok_t. Qed.

Lemma str_ok : forall h o b s z, stage_ok (c_deflate_str h o b s z).
Proof. intros; unfold c_deflate_str; stage_ok_t. Qed.

Lemma entry_ok : forall s z flush, (d_status s = FINISH_STATE -> flush = Z_FINISH) ->
  stage_ok (c_deflate_entry s z flush).
Proof.
  intros s z flush Hf; unfold c_deflate_entry.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:E.
  - exfalso; apply andb_true_iff in E; destruct E as [E1 E2].
    apply Z.eqb_eq in E1; apply negb_true_iff, Z.eqb_neq in E2; auto.
  - stage_ok_t.
Qed.

Lemma zlib_header_ok : forall s z, stage_ok (c_deflate_zlib_header s z).
Proof. intros; unfold c_deflate_zlib_header; stage_ok_t; apply flush_or_return_ok. Qed.

Lemma gzip_header_ok : forall s z, stage_ok (c_deflate_gzip_header s z).
Proof. intros; unfold c_deflate_gzip_header; stage_ok_t; apply flush_or_return_ok. Qed.

Lemma extra_ok : forall s z, stage_ok (c_deflate_extra s z).
Proof. intros; unfold c_deflate_extra; stage_ok_t. Qed.

Lemma name_ok : forall s z, stage_ok (c_deflate_name s z).
Proof. intros; unfold c_deflate_name; stage_ok_t; apply str_ok. Qed.

Lemma comment_ok : forall s z, stage_ok (c_deflate_comment s z).
Proof. intros; unfold c_deflate_comment; stage_ok_t; apply str_ok. Qed.

Lemma hcrc_ok : forall s z, stage_ok (c_deflate_hcrc s z).
Proof. intros; unfold c_deflate_hcrc; stage_ok_t; apply flush_or_return_ok. Qed.

Lemma compress_ok : forall s z flush, stage_ok (c_deflate_compress s z flush).
Proof. intros; unfold c_deflate_compress; stage_ok_t. Qed.

(** The trailer: Z_OK, or Z_STREAM_END for Z_FINISH only. *)
Lemma trailer_codes : forall s z flush s' z' code,
  c_deflate_trailer s z flush = Some (s', z', code) ->
  (code = Z_OK \/ code = Z_STREAM_END) /\ (code = Z_STREAM_END -> flush = Z_FINISH).
Proof.
  intros s z flush s' z' code H; unfold c_deflate_trailer in H.
  destruct (negb (flush =? Z_FINISH)) eqn:E.
  - inversion H; subst; split; [auto | discriminate].
  - apply negb_false_iff, Z.eqb_eq in E.
    destruct (d_wrap s <=? 0).
    + inversion H; subst; auto.
    + match type of H with bind ?a _ = _ => destruct a as [s1|]; [cbn [bind] in H | discriminate] end.
      destruct (c_flush_pending s1 z) as [[s2 z2]|]; [cbn [bind] in H | discriminate].
      destruct (negb (d_pending _ =? 0)); inversion H; subst; auto.
Qed.

(** The range tests of deflateParams' arguments, decided by cases on each comparison. *)
Ltac bool_range_t level :=
  destruct (Z.eqb_spec level (-1)); [subst |];
  repeat match goal with
         | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
         | |- context [?a >? ?b] => destruct (Z.gtb_spec a b)
         end;
  cbn [orb]; first [reflexivity | lia].

(** deflate(strm, flush) with a flush out of Z_NO_FLUSH..Z_BLOCK: Z_STREAM_ERROR, nothing changed. *)
Lemma deflate_bad_flush : forall s z flush,
  flush < 0 \/ 5 < flush -> c_deflate s z flush = Some (s, z, Z_STREAM_ERROR).
Proof.
  intros s z flush Hf; unfold c_deflate.
  replace (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)) with true; [reflexivity |].
  unfold Z_BLOCK; symmetry; rewrite !orb_true_iff, Z.gtb_lt, Z.ltb_lt; lia.
Qed.

(** deflate(strm, flush) with a valid flush on a stream that passes deflateStateCheck, not in FINISH_STATE unless
    the flush is Z_FINISH: Z_OK, Z_BUF_ERROR or Z_STREAM_END, the last only for Z_FINISH. *)
Lemma deflate_codes : forall s z flush s' z' code,
  bad_state s = false -> 0 <= flush <= 5 -> (d_status s = FINISH_STATE -> flush = Z_FINISH) ->
  c_deflate s z flush = Some (s', z', code) ->
  (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\ (code = Z_STREAM_END -> flush = Z_FINISH).
Proof.
  intros s z flush s' z' code Hb Hf Hfin H; unfold c_deflate in H.
  replace (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)) with false in H.
  2:{ rewrite Hb; unfold Z_BLOCK; symmetry; rewrite !orb_false_iff, Z.gtb_ltb, !Z.ltb_ge; lia. }
  match type of H with bind ?a _ = _ =>
    assert (Ha : stage_ok a);
    [ apply stage_ok_then; [apply entry_ok; exact Hfin | intros ? ?];
      apply stage_ok_then; [apply zlib_header_ok | intros ? ?];
      apply stage_ok_then; [apply gzip_header_ok | intros ? ?];
      apply stage_ok_then; [apply extra_ok | intros ? ?];
      apply stage_ok_then; [apply name_ok | intros ? ?];
      apply stage_ok_then; [apply comment_ok | intros ? ?];
      apply stage_ok_then; [apply hcrc_ok | intros ? ?];
      apply compress_ok
    | destruct a as [[[s1 z1] [c|]]|] eqn:E; cbn [bind] in H; [| | discriminate] ] end.
  - inversion H; subst.
    destruct (Ha _ _ _ eq_refl) as [-> | ->]; split; auto; discriminate.
  - destruct (trailer_codes _ _ _ _ _ _ H) as [[-> | ->] Hend]; auto.
Qed.

(** deflateParams(strm, level, strategy) with a level out of -1..9 or a strategy out of
    Z_DEFAULT_STRATEGY..Z_FIXED: Z_STREAM_ERROR, nothing changed. *)
Lemma params_bad : forall s z level strategy,
  ~ (-1 <= level <= 9 /\ 0 <= strategy <= 4) ->
  c_deflateParams s z level strategy = Some (s, z, Z_STREAM_ERROR).
Proof.
  intros s z level strategy Hl; unfold c_deflateParams.
  destruct (bad_state s); [reflexivity |].
  replace ((((if level =? Z_DEFAULT_COMPRESSION then 6 else level) <? 0) ||
            ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) >? 9) ||
            (strategy <? 0)) || (strategy >? Z_FIXED)) with true; [reflexivity |].
  unfold Z_DEFAULT_COMPRESSION, Z_FIXED.
  bool_range_t level.
Qed.

(** deflateParams(strm, level, strategy) with a valid level and strategy on a stream that passes
    deflateStateCheck and is not in FINISH_STATE: Z_OK or Z_BUF_ERROR (its deflate(strm, Z_BLOCK) does not fail). *)
Lemma params_codes : forall s z level strategy s' z' code,
  bad_state s = false -> d_status s <> FINISH_STATE -> -1 <= level <= 9 -> 0 <= strategy <= 4 ->
  c_deflateParams s z level strategy = Some (s', z', code) -> code = Z_OK \/ code = Z_BUF_ERROR.
Proof.
  intros s z level strategy s' z' code Hb Hst Hl Hs H; unfold c_deflateParams in H.
  rewrite Hb in H.
  replace ((((if level =? Z_DEFAULT_COMPRESSION then 6 else level) <? 0) ||
            ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) >? 9) ||
            (strategy <? 0)) || (strategy >? Z_FIXED)) with false in H.
  2:{ unfold Z_DEFAULT_COMPRESSION, Z_FIXED.
      bool_range_t level. }
  cbn [orb] in H.
  destruct (cfg_func (d_level s)) as [func|]; cbn [bind] in H; [| discriminate].
  match type of H with bind ?a _ = _ =>
    assert (Ha : forall s1 z1 c, a = Some (s1, z1, Some c) -> c = Z_BUF_ERROR);
    [ intros s1 z1 c Ea
    | destruct a as [[[s1 z1] [c|]]|] eqn:E; cbn [bind] in H; [| | discriminate] ] end.
  - match type of Ea with (if ?b then _ else _) = _ => destruct b end; [| discriminate].
    destruct (c_deflate s z Z_BLOCK) as [[[s2 z2] err]|] eqn:Ed; cbn [bind] in Ea; [| discriminate].
    destruct (Z.eqb_spec err Z_STREAM_ERROR).
    + exfalso; subst err.
      destruct (deflate_codes s z Z_BLOCK s2 z2 Z_STREAM_ERROR) as [Hc _]; auto.
      * unfold Z_BLOCK; lia.
      * intros Hf; contradiction.
      * unfold Z_STREAM_ERROR, Z_OK, Z_BUF_ERROR, Z_STREAM_END in Hc; lia.
    + destruct (negb (z_avail_in z2 =? 0)); [inversion Ea; auto |].
      destruct (in_long (d_strstart s2 - d_block_start s2)); cbn in Ea; [| discriminate].
      destruct (in_long (d_strstart s2 - d_block_start s2 + d_lookahead s2)); cbn in Ea; [| discriminate].
      destruct (negb (_ =? 0)); inversion Ea; auto.
  - inversion H; subst; right; eapply Ha; reflexivity.
  - match type of H with bind ?a _ = _ => destruct a; cbn [bind] in H; [| discriminate] end.
    inversion H; auto.
Qed.

(** deflate(strm, flush) with a valid flush and no output space (avail_out = 0) on a stream that passes
    deflateStateCheck, not in FINISH_STATE unless the flush is Z_FINISH: Z_BUF_ERROR, and only msg changes (the
    state, next_in, avail_in, total_in, next_out, avail_out and total_out are as they were). *)
Lemma deflate_no_room : forall s z flush,
  bad_state s = false -> 0 <= flush <= 5 -> (d_status s = FINISH_STATE -> flush = Z_FINISH) ->
  z_avail_out z = 0 ->
  c_deflate s z flush = Some (s, set_z_msg z (Some Z_BUF_ERROR), Z_BUF_ERROR).
Proof.
  intros s z flush Hb Hf Hfin Ho; unfold c_deflate.
  replace (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)) with false.
  2:{ rewrite Hb; unfold Z_BLOCK; symmetry; rewrite !orb_false_iff, Z.gtb_ltb, !Z.ltb_ge; lia. }
  replace (c_deflate_entry s z flush) with (Some (s, set_z_msg z (Some Z_BUF_ERROR), Some Z_BUF_ERROR)).
  { reflexivity. }
  unfold c_deflate_entry.
  destruct ((d_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:E.
  - exfalso; apply andb_true_iff in E; destruct E as [E1 E2].
    apply Z.eqb_eq in E1; apply negb_true_iff, Z.eqb_neq in E2; auto.
  - rewrite Ho. reflexivity.
Qed.

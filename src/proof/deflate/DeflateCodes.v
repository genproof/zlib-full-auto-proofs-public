(** * The return codes of deflate() on the model, whatever the state and the call

    Every stage of the model's deflate() ([DModel4.c_deflate]) returns either nothing (go on with the next
    stage) or one of the constants Z_OK, Z_BUF_ERROR and Z_STREAM_ERROR, and the trailer stage Z_OK or
    Z_STREAM_END; so a run that is defined returns one of these four codes.  A harness's loop `while (code ==
    Z_OK)` and its tests `code != Z_STREAM_END` compare the int that deflate() returned: this bounds it, so that
    the comparisons of the C (on Int.repr code) are those of the model's codes. *)
From Coq Require Import ZArith List Lia Bool.
Require Export Zlib.proof.deflate.DModel4.
Import ListNotations.
Local Open Scope Z_scope.

Definition code4 (c : Z) : Prop :=
  c = Z_OK \/ c = Z_STREAM_END \/ c = Z_BUF_ERROR \/ c = Z_STREAM_ERROR.

(* a stage's result stops deflate() only with one of the codes *)
Definition stage_ok (r : option dres) : Prop := forall s z c, r = Some (s, z, Some c) -> code4 c.

Lemma then_stage_ok r k : stage_ok r -> (forall s z, stage_ok (k s z)) -> stage_ok (then_stage r k).
Proof.
  intros H K s z c E. unfold then_stage in E. destruct r as [[[s1 z1] [c1|]]|]; cbn in E; try discriminate.
  - injection E as -> -> ->. exact (H _ _ _ eq_refl).
  - exact (K s1 z1 _ _ _ E).
Qed.

(* the case analysis of a stage: every match of the result, every constructor equation *)
Ltac stage_tac :=
  unfold stage_ok, code4; intros;
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : None = Some _ |- _ => discriminate H
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  | H : context [if ?x then _ else _] |- _ => destruct x eqn:?
  end;
  try discriminate; auto.

Lemma flush_or_return_ok s z : stage_ok (c_flush_or_return s z).
Proof. unfold c_flush_or_return, bind. stage_tac. Qed.

Lemma entry_ok s z f : stage_ok (c_deflate_entry s z f).
Proof. unfold c_deflate_entry, then_stage, bind. stage_tac. Qed.

Lemma zlib_header_ok s z : stage_ok (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header, c_flush_or_return, bind. stage_tac. Qed.

Lemma gzip_header_ok s z : stage_ok (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header, c_flush_or_return, bind. stage_tac. Qed.

Lemma extra_ok s z : stage_ok (c_deflate_extra s z).
Proof. unfold c_deflate_extra, then_stage, bind. stage_tac. Qed.

Lemma str_ok h o b s z : stage_ok (c_deflate_str h o b s z).
Proof. unfold c_deflate_str, bind. stage_tac. Qed.

Lemma name_ok s z : stage_ok (c_deflate_name s z).
Proof.
  unfold c_deflate_name. destruct (d_status s =? NAME_STATE); [|stage_tac].
  unfold bind. destruct (c_gzhead s) as [h|]; [|stage_tac].
  apply then_stage_ok; [apply str_ok | intros; stage_tac].
Qed.

Lemma comment_ok s z : stage_ok (c_deflate_comment s z).
Proof.
  unfold c_deflate_comment. destruct (d_status s =? COMMENT_STATE); [|stage_tac].
  unfold bind. destruct (c_gzhead s) as [h|]; [|stage_tac].
  apply then_stage_ok; [apply str_ok | intros; stage_tac].
Qed.

Lemma hcrc_ok s z : stage_ok (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc, then_stage, c_flush_or_return, bind. stage_tac. Qed.

Lemma compress_ok s z f : stage_ok (c_deflate_compress s z f).
Proof. unfold c_deflate_compress, bind. stage_tac. Qed.

Lemma trailer_code s z f s' z' c : c_deflate_trailer s z f = Some (s', z', c) -> code4 c.
Proof.
  unfold c_deflate_trailer, bind, code4. intros. stage_tac;
    match goal with |- context [if negb ?b then _ else _] => destruct b; cbn; auto end.
Qed.

Theorem c_deflate_code4 s z f s' z' c : c_deflate s z f = Some (s', z', c) -> code4 c.
Proof.
  unfold c_deflate. destruct (_ || _ || _).
  { intros E. injection E; intros; subst. unfold code4; auto. }
  unfold bind at 1. intros E.
  match type of E with context [match ?rr with _ => _ end] => destruct rr as [[[s1 z1] [c1|]]|] eqn:Er end;
    try discriminate.
  - injection E; intros; subst.
    refine (then_stage_ok _ _ (entry_ok s z f) _ _ _ _ Er). intros.
    repeat (apply then_stage_ok; [first [apply zlib_header_ok | apply gzip_header_ok | apply extra_ok
                                         | apply name_ok | apply comment_ok | apply hcrc_ok] | intros]).
    apply compress_ok.
  - exact (trailer_code _ _ _ _ _ _ E).
Qed.

(** * Pure facts for the body proof of deflate_stored: the output of a call only grows, and the bytes written plus
    the room left stay constant ([out_inv]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel4.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Definition out_inv (z z' : strm) : Prop :=
  (exists bs, z_out z' = z_out z ++ bs) /\
  Zlength (z_out z') + z_avail_out z' = Zlength (z_out z) + z_avail_out z /\ 0 <= z_avail_out z'.

Lemma out_inv_refl z : 0 <= z_avail_out z -> out_inv z z.
Proof. intros. split; [exists []; rewrite app_nil_r; auto | split; auto]. Qed.

Lemma out_inv_trans z1 z2 z3 : out_inv z1 z2 -> out_inv z2 z3 -> out_inv z1 z3.
Proof.
  intros [[b1 E1] [L1 P1]] [[b2 E2] [L2 P2]]. split; [|split; [lia|auto]].
  exists (b1 ++ b2). rewrite E2, E1, app_assoc. reflexivity.
Qed.

Lemma out_inv_le z z' : out_inv z z' -> 0 <= z_avail_out z' <= z_avail_out z.
Proof.
  intros [[b E] [L P]]. rewrite E, Zlength_app in L. pose proof (Zlength_nonneg b). lia.
Qed.

Lemma bind_some {A B} (a : option A) (f : A -> option B) r :
  bind a f = Some r -> exists x, a = Some x /\ f x = Some r.
Proof. destruct a; simpl; [eauto | discriminate]. Qed.

Ltac binv H := let x := fresh "x" in let Ha := fresh "Ha" in
  apply bind_some in H; destruct H as [x [Ha H]].

Lemma mb_read_len b lo n l : mb_read b lo n = Some l -> Zlength l = n.
Proof.
  unfold mb_read, mb_definedb. intros H.
  destruct ((0 <=? n) && ((0 <=? lo) && (lo + n <=? Zlength (mb_val b)) && _)) eqn:E; [|discriminate].
  inversion H; subst. apply andb_prop in E as [E1 E2]. apply andb_prop in E2 as [E2 _].
  apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E1, E2, E3.
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma out_put_inv z bs z1 : out_put z bs = Some z1 ->
  z_out z1 = z_out z ++ bs /\ Zlength bs <= z_avail_out z /\ z_avail_out z1 = z_avail_out z.
Proof.
  unfold out_put. destruct (Zlength bs <=? z_avail_out z) eqn:E; [|discriminate].
  intros H; inversion H; subst; clear H. apply Z.leb_le in E. cbn. auto.
Qed.

Lemma read_buf_out s z n z' d : c_read_buf s z n = Some (z', d) ->
  z_out z' = z_out z /\ z_avail_out z' = z_avail_out z.
Proof.
  unfold c_read_buf. destruct (_ =? 0).
  - intros H; inversion H; auto.
  - intros H. binv H. inversion H; subst. cbn.
    destruct (d_wrap s =? 1); [cbn; auto|]. destruct (d_wrap s =? 2); cbn; auto.
Qed.

Lemma flush_pending_inv s z s' z' : 0 <= z_avail_out z -> c_flush_pending s z = Some (s', z') -> out_inv z z'.
Proof.
  intros Hz. unfold c_flush_pending. intros H. binv H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:E0 end.
  - inversion H; subst. apply out_inv_refl; auto.
  - binv H. binv H. apply mb_read_len in Ha0. apply out_put_inv in Ha1. destruct Ha1 as [E1 [L1 A1]].
    inversion H; subst; clear H.
    rewrite <- Ha0. unfold out_inv; cbn.
    split; [exists x0; exact E1 | rewrite E1, Zlength_app, A1; lia].
Qed.

Lemma u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

(** One iteration of the first phase. *)
Lemma ds_body_inv flush mb s z res :
  0 <= z_avail_out z < 4294967296 -> ds_body flush mb (s, z) = Some res ->
  match res with inl (_, z') => out_inv z z' | inr (_, z', _) => out_inv z z' end.
Proof.
  intros Hz H. unfold ds_body in H.
  destruct (z_avail_out z <? stored_hdr s); [inversion H; subst; apply out_inv_refl; lia|].
  binv H.
  match type of H with context [if ?c then Some (inr (s, z, 0)) else _] => destruct c end;
    [inversion H; subst; apply out_inv_refl; lia|].
  binv H. binv H. binv H. binv H. binv H. binv H. destruct x5 as [s1 z1].
  assert (I1 : out_inv z z1) by (eapply flush_pending_inv; [|exact Ha5]; lia).
  apply bind_some in H; destruct H as [[[s2 z2] len2] [Hw H]].
  assert (I2 : out_inv z1 z2).
  { destruct (_ =? 0) in Hw; [inversion Hw; subst; apply out_inv_refl; apply (proj2 (proj2 I1))|].
    apply bind_some in Hw; destruct Hw as [bytes [Hr Hw]].
    apply bind_some in Hw; destruct Hw as [z1' [Hp Hw]].
    apply bind_some in Hw; destruct Hw as [[] [_ Hw]].
    apply mb_read_len in Hr. apply out_put_inv in Hp. destruct Hp as [E1 [L1 A1]].
    inversion Hw; subst; clear Hw. unfold out_inv; cbn [z_out z_avail_out set_z_total_out set_z_avail_out].
    rewrite <- Hr. pose proof (out_inv_le _ _ I1). pose proof (Zlength_nonneg bytes).
    rewrite u32_id by lia. split; [eexists; exact E1|]. rewrite E1, Zlength_app. lia. }
  apply bind_some in H; destruct H as [z3 [Hi H]].
  assert (I3 : out_inv z2 z3).
  { destruct (len2 =? 0) in Hi; [inversion Hi; subst; apply out_inv_refl; apply (proj2 (proj2 I2))|].
    apply bind_some in Hi; destruct Hi as [[z4 d] [Hr Hi]].
    apply bind_some in Hi; destruct Hi as [[] [Hg Hi]].
    apply bind_some in Hi; destruct Hi as [z5 [Hp Hi]].
    apply read_buf_out in Hr. destruct Hr as [Eo Ea].
    apply out_put_inv in Hp. destruct Hp as [E1 [L1 A1]].
    unfold guard in Hg. destruct (Zlength d =? len2) eqn:Ed; [|discriminate]. apply Z.eqb_eq in Ed.
    inversion Hi; subst; clear Hi. unfold out_inv; cbn [z_out z_avail_out set_z_total_out set_z_avail_out].
    pose proof (Zlength_nonneg d).
    pose proof (out_inv_le _ _ I1). pose proof (out_inv_le _ _ I2).
    rewrite u32_id by lia. split; [exists d; rewrite E1, Eo; auto|].
    rewrite E1, Eo, Zlength_app. lia. }
  pose proof (out_inv_trans _ _ _ (out_inv_trans _ _ _ I1 I2) I3) as I.
  revert H. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros H; inversion H; subst; exact I.
Qed.

(** The whole loop of the first phase. *)
Lemma ds_runs_inv flush mb a r :
  runs (ds_body flush mb) a r -> 0 <= z_avail_out (snd a) < 4294967296 ->
  out_inv (snd a) (snd (fst r)).
Proof.
  induction 1 as [[s z] [[s' z'] l] H | [s z] [s1 z1] [[s' z'] l] H _ IH]; cbn [fst snd]; intros Hz.
  - exact (ds_body_inv _ _ _ _ _ Hz H).
  - pose proof (ds_body_inv _ _ _ _ _ Hz H) as I. cbn in I.
    pose proof (out_inv_le _ _ I). eapply out_inv_trans; [exact I|]. apply IH. cbn. lia.
Qed.

Require Import Zlib.proof.deflate.StoredKit.

(** The second phase. *)
Lemma ds_phase2_inv s z flush r :
  ds_phase2 s z flush = Some r -> 0 <= z_avail_out z -> out_inv z (snd (fst r)).
Proof.
  intros H Hz. unfold ds_phase2 in H.
  apply bind_some in H; destruct H as [[s1 h1] [_ H]].
  apply bind_some in H; destruct H as [[s2 z2] [Hf H]].
  assert (I2 : out_inv z z2).
  { revert Hf. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros Hf.
    - inversion Hf; subst. apply out_inv_refl; auto.
    - apply bind_some in Hf; destruct Hf as [[z4 d] [Hr Hf]].
      apply bind_some in Hf; destruct Hf as [w [_ Hf]]. inversion Hf; subst.
      apply read_buf_out in Hr. destruct Hr as [E A].
      split; [exists []; rewrite E, app_nil_r; auto|]. rewrite E, A. lia. }
  apply bind_some in H; destruct H as [[] [_ H]].
  apply bind_some in H; destruct H as [[[s3 z3] l] [Hb H]].
  assert (I3 : out_inv z2 z3).
  { revert Hb. match goal with |- (if ?c then _ else _) = _ -> _ => destruct c end; intros Hb.
    - apply bind_some in Hb; destruct Hb as [b [_ Hb]].
      apply bind_some in Hb; destruct Hb as [o [_ Hb]].
      apply bind_some in Hb; destruct Hb as [[] [_ Hb]].
      apply bind_some in Hb; destruct Hb as [[s4 z4] [Hp Hb]]. inversion Hb; subst.
      eapply flush_pending_inv; [|exact Hp]. apply (out_inv_le _ _ I2).
    - inversion Hb; subst. apply out_inv_refl. apply (out_inv_le _ _ I2). }
  pose proof (out_inv_trans _ _ _ I2 I3) as I.
  destruct (l =? 0); inversion H; subst; exact I.
Qed.

(** The value of [last] when an iteration leaves the loop: 0 or 1. *)
Lemma ds_body_last flush mb a s z l :
  ds_body flush mb a = Some (inr (s, z, l)) -> l = 0 \/ l = 1.
Proof.
  destruct a as [s0 z0]. unfold ds_body. intros H.
  repeat match type of H with
  | Some _ = Some _ => inversion H; subst; clear H
  | (if ?c then _ else _) = _ => destruct c
  | bind ?x _ = _ => let E := fresh "E" in destruct x eqn:E; [cbn [bind] in H | discriminate]
  | (let '(_, _) := ?x in _) = _ => destruct x
  | (match ?x with (_, _) => _ end) = _ => destruct x
  end; auto; match goal with |- context [if ?c then 1 else 0] => destruct c; auto end.
Qed.

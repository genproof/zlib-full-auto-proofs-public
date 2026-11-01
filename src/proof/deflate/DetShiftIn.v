(** * A deflate() call does not depend on the bytes before next_in

    The deflate model reads the input object [z_in] only through [rds (z_in z) lo n] with [lo] counted from the
    start of the object (read_buf at next_in, the window update of deflate_stored at next_in - used), and only
    adds to [z_next_in].  Putting bytes [p] in front of the object and moving next_in by [Zlength p] ([zpre p])
    therefore gives the same run, shifted the same way.  The converse direction does not hold in general (a
    read before next_in would fail on the unshifted stream), so the statement is one-way: a defined call stays
    defined, with the same state and code.  The laws that call deflate() with next_in inside an input object
    (api_deterministic, rt_stream through RTK7Api) reduce such a call to one on the rest of the object from
    next_in 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel4.
Import ListNotations.
Local Open Scope Z_scope.

(** The stream [z] with the bytes [p] put in front of its input object, next_in after them. *)
Definition zpre (p : list Z) (z : strm) : strm :=
  mkST (p ++ z_in z) (Zlength p + z_next_in z) (z_avail_in z) (z_total_in z) (z_out z) (z_avail_out z)
       (z_total_out z) (z_adler z) (z_msg z).

(** ** One-way refinement

    [orf F o1 o2]: when [o2] is defined, so is [o1], with the value [F] of [o2]'s.  [o1] is a model function on
    the shifted stream, [o2] the same function on the original one, [F] the shift of its result.  A wrapper
    (not a definition) so that the hint search below treats it as an atom. *)
Inductive orf {A : Type} (F : A -> A) (o1 o2 : option A) : Prop :=
  orf_intro : (forall a, o2 = Some a -> o1 = Some (F a)) -> orf F o1 o2.

Lemma orf_None {A : Type} (F : A -> A) o : orf F o None.
Proof. constructor. discriminate. Qed.

Lemma orf_Some {A : Type} (F : A -> A) x y : x = F y -> orf F (Some x) (Some y).
Proof. intros ->. constructor. congruence. Qed.

Lemma orf_id {A : Type} (o : option A) : orf (fun x => x) o o.
Proof. constructor. auto. Qed.

Lemma orf_use {A : Type} (F : A -> A) o1 o2 a : orf F o1 o2 -> o2 = Some a -> o1 = Some (F a).
Proof. intros [H]. apply H. Qed.

Lemma bind_pre {A B : Type} (FA : A -> A) (FB : B -> B) (o1 o2 : option A) (k1 k2 : A -> option B) :
  orf FA o1 o2 -> (forall a, orf FB (k1 (FA a)) (k2 a)) -> orf FB (bind o1 k1) (bind o2 k2).
Proof.
  intros [H1] Hk. destruct o2 as [a|]; [|apply orf_None].
  rewrite (H1 a eq_refl). exact (Hk a).
Qed.

(** The shifts of the results: a (state, stream) pair, a (state, stream, x) triple, a (state, stream, x, y)
    quadruple, a (stream, bytes) pair (read_buf), and a sum of two shifted values. *)
Definition ppre (p : list Z) (a : dstate * strm) : dstate * strm := (fst a, zpre p (snd a)).
Definition tpre {C : Type} (p : list Z) (r : dstate * strm * C) : dstate * strm * C :=
  (fst (fst r), zpre p (snd (fst r)), snd r).
Definition qpre {C D : Type} (p : list Z) (r : dstate * strm * C * D) : dstate * strm * C * D :=
  (tpre p (fst r), snd r).
Definition bpre (p : list Z) (a : strm * list Z) : strm * list Z := (zpre p (fst a), snd a).
Definition smap {A B : Type} (f : A -> A) (g : B -> B) (x : A + B) : A + B :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

(** ** Loops *)

Lemma loop2_pre {A B : Type} (FA : A -> A) (FB : B -> B) (body : A -> option (A + B)) :
  (forall a, orf (smap FA FB) (body (FA a)) (body a)) ->
  forall n a, orf (smap FA FB) (loop2 n body (FA a)) (loop2 n body a).
Proof.
  intros H n; induction n as [|n IH]; intros a; simpl; [apply H|].
  constructor. intros r Hr.
  destruct (loop2 n body a) as [[a'|b]|] eqn:E; try discriminate.
  - rewrite (orf_use _ _ _ _ (IH a) E). simpl. exact (orf_use _ _ _ _ (IH a') Hr).
  - rewrite (orf_use _ _ _ _ (IH a) E). simpl. inversion Hr; subst. reflexivity.
Qed.

Lemma loop_pre {A B : Type} (FA : A -> A) (FB : B -> B) (body : A -> option (A + B)) :
  (forall a, orf (smap FA FB) (body (FA a)) (body a)) ->
  forall n a, orf FB (loop n body (FA a)) (loop n body a).
Proof.
  intros H n a. constructor. intros r Hr. unfold loop in *.
  destruct (loop2 n body a) as [[a'|b]|] eqn:E; try discriminate.
  rewrite (orf_use _ _ _ _ (loop2_pre FA FB body H n a) E). simpl. inversion Hr; subst. reflexivity.
Qed.

(** ** Getters, setters and the checked slice *)

Section Getters.
Variables (p : list Z) (z : strm).
Lemma zpre_in : z_in (zpre p z) = p ++ z_in z. Proof. reflexivity. Qed.
Lemma zpre_next_in : z_next_in (zpre p z) = Zlength p + z_next_in z. Proof. reflexivity. Qed.
Lemma zpre_avail_in : z_avail_in (zpre p z) = z_avail_in z. Proof. reflexivity. Qed.
Lemma zpre_total_in : z_total_in (zpre p z) = z_total_in z. Proof. reflexivity. Qed.
Lemma zpre_out : z_out (zpre p z) = z_out z. Proof. reflexivity. Qed.
Lemma zpre_avail_out : z_avail_out (zpre p z) = z_avail_out z. Proof. reflexivity. Qed.
Lemma zpre_total_out : z_total_out (zpre p z) = z_total_out z. Proof. reflexivity. Qed.
Lemma zpre_adler : z_adler (zpre p z) = z_adler z. Proof. reflexivity. Qed.
Lemma zpre_msg : z_msg (zpre p z) = z_msg z. Proof. reflexivity. Qed.

Lemma zpre_set_avail_in x : set_z_avail_in (zpre p z) x = zpre p (set_z_avail_in z x). Proof. reflexivity. Qed.
Lemma zpre_set_total_in x : set_z_total_in (zpre p z) x = zpre p (set_z_total_in z x). Proof. reflexivity. Qed.
Lemma zpre_set_out x : set_z_out (zpre p z) x = zpre p (set_z_out z x). Proof. reflexivity. Qed.
Lemma zpre_set_avail_out x : set_z_avail_out (zpre p z) x = zpre p (set_z_avail_out z x). Proof. reflexivity. Qed.
Lemma zpre_set_total_out x : set_z_total_out (zpre p z) x = zpre p (set_z_total_out z x). Proof. reflexivity. Qed.
Lemma zpre_set_adler x : set_z_adler (zpre p z) x = zpre p (set_z_adler z x). Proof. reflexivity. Qed.
Lemma zpre_set_msg x : set_z_msg (zpre p z) x = zpre p (set_z_msg z x). Proof. reflexivity. Qed.

(** The only update of next_in in the model: read_buf's [next_in + len]. *)
Lemma zpre_add_next_in a b : set_z_next_in (zpre p z) (Zlength p + a + b) = zpre p (set_z_next_in z (a + b)).
Proof. unfold zpre, set_z_next_in. simpl. f_equal. lia. Qed.
End Getters.

(** deflate_stored's window update reads at [next_in - used]. *)
Lemma zlength_add_sub (q : list Z) a b : Zlength q + a - b = Zlength q + (a - b).
Proof. lia. Qed.

(** The checked slice of the input object at [lo], read [Zlength p] bytes later in [p ++ l]. *)
Lemma rds_pre p l lo n : orf (fun x => x) (rds (p ++ l) (Zlength p + lo) n) (rds l lo n).
Proof.
  constructor. intros a. unfold rds. intros H.
  destruct ((0 <=? lo) && (0 <=? n) && (lo + n <=? Zlength l)) eqn:E; [|discriminate].
  inversion H; subst. rewrite !andb_true_iff, !Z.leb_le in E.
  pose proof (Zlength_nonneg p). rewrite Zlength_app.
  replace ((0 <=? Zlength p + lo) && (0 <=? n) && (Zlength p + lo + n <=? Zlength p + Zlength l)) with true
    by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
  f_equal. rewrite sublist_app2 by (split; lia). f_equal; lia.
Qed.

Create HintDb pre.
Hint Rewrite zpre_in zpre_next_in zpre_avail_in zpre_total_in zpre_out zpre_avail_out zpre_total_out zpre_adler
  zpre_msg zpre_set_avail_in zpre_set_total_in zpre_set_out zpre_set_avail_out zpre_set_total_out zpre_set_adler
  zpre_set_msg zpre_add_next_in zlength_add_sub : pre.
Hint Extern 1 (orf _ (rds _ _ _) _) => eapply rds_pre : pre.

(** ** The lockstep tactic

    The goal is [orf F lhs rhs] where [lhs] is [rhs] on the shifted stream.  Rewrite the shifted getters and
    setters ([pre] database), reduce the monad, and case on the first scrutinee of [lhs]: a shifted call (one with
    an [orf] lemma in the [pre] hints) is cased on through that lemma: when the original call fails, so does
    [rhs]; when it returns [b], the shifted call returns the shift of [b]; any other scrutinee without [zpre] is
    the same on both sides. *)
Ltac dpairs :=
  repeat match goal with
         | p : _ * _ |- _ => destruct p
         | p : ?T |- _ => let T' := eval hnf in T in lazymatch T' with prod _ _ => destruct p end
         end.

Ltac pre_red :=
  dpairs; unfold ppre, tpre, qpre, bpre; cbn [smap fst snd]; autorewrite with pre;
  unfold bind, then_stage, ppre, tpre, qpre, bpre; cbn [smap fst snd].

Ltac pre_close :=
  lazymatch goal with
  | |- orf _ _ None => apply orf_None
  | |- orf _ (Some _) (Some _) => apply orf_Some; unfold ppre, tpre, qpre, bpre; cbn [smap fst snd]; reflexivity
  | |- orf _ _ _ => solve [eauto 2 with pre nocore]
  end.

Ltac pre_call y :=
  let H := fresh "H" in
  eassert (H : orf _ y _) by (eauto 2 with pre nocore);
  lazymatch type of H with
  | orf _ _ ?y0 =>
      generalize (fun a => orf_use _ _ _ a H); clear H;
      let b := fresh "b" in
      destruct y0 as [b|]; intros H; [rewrite (H b eq_refl) |]; clear H
  end.

Ltac pre_case :=
  lazymatch goal with
  | |- orf _ ?L _ =>
      match L with
      | context [match smap _ _ ?y with _ => _ end] => destruct y
      | context [match ?y with _ => _ end] =>
          lazymatch y with
          | context [match _ with _ => _ end] => fail
          | _ => first [ pre_call y | lazymatch y with context [zpre] => fail | _ => destruct y end ]
          end
      end
  end.

Ltac pre_go := repeat (first [pre_close | progress pre_red | pre_case]).

(** ** read_buf, out_put, flush_pending, FLUSH_BLOCK *)

Lemma out_put_pre p z b : orf (zpre p) (out_put (zpre p z) b) (out_put z b).
Proof. unfold out_put. pre_go. Qed.
Hint Extern 1 (orf _ (out_put _ _) _) => eapply out_put_pre : pre.

Lemma read_buf_pre p s z n : orf (bpre p) (c_read_buf s (zpre p z) n) (c_read_buf s z n).
Proof. unfold c_read_buf. pre_go. Qed.
Hint Extern 1 (orf _ (c_read_buf _ _ _) _) => eapply read_buf_pre : pre.

Lemma flush_pending_pre p s z : orf (ppre p) (c_flush_pending s (zpre p z)) (c_flush_pending s z).
Proof. unfold c_flush_pending. pre_go. Qed.
Hint Extern 1 (orf _ (c_flush_pending _ _) _) => eapply flush_pending_pre : pre.

Lemma flush_block_only_pre p s z last :
  orf (ppre p) (c_flush_block_only s (zpre p z) last) (c_flush_block_only s z last).
Proof. unfold c_flush_block_only. pre_go. Qed.
Hint Extern 1 (orf _ (c_flush_block_only _ _ _) _) => eapply flush_block_only_pre : pre.

Lemma flush_block_pre p s z last : orf (tpre p) (c_flush_block s (zpre p z) last) (c_flush_block s z last).
Proof. unfold c_flush_block. pre_go. Qed.
Hint Extern 1 (orf _ (c_flush_block _ _ _) _) => eapply flush_block_pre : pre.

(** ** fill_window *)

Lemma fw_body_pre p a : orf (smap (ppre p) (ppre p)) (fw_body (ppre p a)) (fw_body a).
Proof. destruct a as [s z]. unfold fw_body. pre_go. Qed.

Lemma fw_loop_pre p s z :
  orf (ppre p) (loop FUEL fw_body (s, zpre p z)) (loop FUEL fw_body (s, z)).
Proof. exact (loop_pre (ppre p) (ppre p) _ (fw_body_pre p) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ fw_body _) _) => eapply fw_loop_pre : pre.

Lemma fill_window_pre p s z : orf (ppre p) (c_fill_window s (zpre p z)) (c_fill_window s z).
Proof. unfold c_fill_window. pre_go. Qed.
Hint Extern 1 (orf _ (c_fill_window _ _) _) => eapply fill_window_pre : pre.

(** ** The pieces of the compression functions *)

Lemma bflush_pre p s z b : orf (smap (ppre p) (tpre p)) (c_bflush s (zpre p z) b) (c_bflush s z b).
Proof. unfold c_bflush. pre_go. Qed.
Hint Extern 1 (orf _ (c_bflush _ _ _) _) => eapply bflush_pre : pre.

Lemma refill_pre p need flush s z : orf (smap (ppre p) (tpre p)) (c_refill need flush s (zpre p z)) (c_refill need flush s z).
Proof. unfold c_refill. pre_go. Qed.
Hint Extern 1 (orf _ (c_refill _ _ _ _) _) => eapply refill_pre : pre.

Lemma deflate_tail_pre p s z flush : orf (tpre p) (c_deflate_tail s (zpre p z) flush) (c_deflate_tail s z flush).
Proof. unfold c_deflate_tail. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_tail _ _ _) _) => eapply deflate_tail_pre : pre.

(** ** deflate_stored

    deflate_stored and its copy loop have [let*]s whose bound value is an [if]: casing on it would copy the rest of
    the function into each case.  [pre_bind] instead splits [let* x := o in k] into the refinement of [o] and that
    of [k] at every value ([bind_pre]), with the shift of the value chosen by its type. *)
Ltac pre_fa p T :=
  lazymatch T with
  | option (dstate * strm) => constr:(ppre p)
  | option (dstate * strm * ?C) => constr:(@tpre C p)
  | option strm => constr:(zpre p)
  | option (strm * list Z) => constr:(bpre p)
  | option ?A => constr:(fun x : A => x)
  end.

Ltac pre_bind p :=
  repeat (dpairs; unfold ppre, tpre, qpre, bpre; cbn [smap fst snd]; autorewrite with pre;
    first
    [ pre_close
    | apply orf_id
    | match goal with
      | |- orf ?FB (bind ?o1 ?k1) (bind ?o2 ?k2) =>
          let T := type of o2 in let FA := pre_fa p T in
          apply (bind_pre FA FB o1 o2 k1 k2); [|intros ?a]
      | |- orf _ _ (match ?x with _ => _ end) => destruct x
      end ]).

Lemma ds_body_pre p flush mb a :
  orf (smap (ppre p) (tpre p)) (ds_body flush mb (ppre p a)) (ds_body flush mb a).
Proof. destruct a as [s z]. unfold ds_body. pre_bind p. Qed.

Lemma ds_loop_pre p flush mb s z :
  orf (tpre p) (loop FUEL (ds_body flush mb) (s, zpre p z)) (loop FUEL (ds_body flush mb) (s, z)).
Proof. exact (loop_pre (ppre p) (tpre p) _ (ds_body_pre p flush mb) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ (ds_body _ _) _) _) => eapply ds_loop_pre : pre.

Lemma ds_window_pre p s z used : orf (fun x => x) (c_ds_window s (zpre p z) used) (c_ds_window s z used).
Proof. unfold c_ds_window. pre_bind p. Qed.
Hint Extern 1 (orf _ (c_ds_window _ _ _) _) => eapply ds_window_pre : pre.

Lemma deflate_stored_pre p s z flush :
  orf (tpre p) (c_deflate_stored s (zpre p z) flush) (c_deflate_stored s z flush).
Proof. unfold c_deflate_stored. pre_bind p. Qed.
Hint Extern 1 (orf _ (c_deflate_stored _ _ _) _) => eapply deflate_stored_pre : pre.

(** ** deflate_fast, deflate_slow, deflate_rle, deflate_huff *)

Lemma df_step_pre p s z : orf (smap (ppre p) (tpre p)) (df_step s (zpre p z)) (df_step s z).
Proof. unfold df_step. pre_go. Qed.
Hint Extern 1 (orf _ (df_step _ _) _) => eapply df_step_pre : pre.

Lemma df_body_pre p flush a : orf (smap (ppre p) (tpre p)) (df_body flush (ppre p a)) (df_body flush a).
Proof. destruct a as [s z]. unfold df_body. pre_go. Qed.

Lemma df_loop_pre p flush s z :
  orf (tpre p) (loop FUEL (df_body flush) (s, zpre p z)) (loop FUEL (df_body flush) (s, z)).
Proof. exact (loop_pre (ppre p) (tpre p) _ (df_body_pre p flush) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ (df_body _) _) _) => eapply df_loop_pre : pre.

Lemma deflate_fast_pre p s z flush : orf (tpre p) (c_deflate_fast s (zpre p z) flush) (c_deflate_fast s z flush).
Proof. unfold c_deflate_fast. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_fast _ _ _) _) => eapply deflate_fast_pre : pre.

Lemma dsl_step_pre p s z : orf (smap (ppre p) (tpre p)) (dsl_step s (zpre p z)) (dsl_step s z).
Proof. unfold dsl_step. pre_go. Qed.
Hint Extern 1 (orf _ (dsl_step _ _) _) => eapply dsl_step_pre : pre.

Lemma dsl_body_pre p flush a : orf (smap (ppre p) (tpre p)) (dsl_body flush (ppre p a)) (dsl_body flush a).
Proof. destruct a as [s z]. unfold dsl_body. pre_go. Qed.

Lemma dsl_loop_pre p flush s z :
  orf (tpre p) (loop FUEL (dsl_body flush) (s, zpre p z)) (loop FUEL (dsl_body flush) (s, z)).
Proof. exact (loop_pre (ppre p) (tpre p) _ (dsl_body_pre p flush) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ (dsl_body _) _) _) => eapply dsl_loop_pre : pre.

Lemma deflate_slow_pre p s z flush : orf (tpre p) (c_deflate_slow s (zpre p z) flush) (c_deflate_slow s z flush).
Proof. unfold c_deflate_slow. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_slow _ _ _) _) => eapply deflate_slow_pre : pre.

Lemma rle_step_pre p s z : orf (smap (ppre p) (tpre p)) (rle_step s (zpre p z)) (rle_step s z).
Proof. unfold rle_step. pre_go. Qed.
Hint Extern 1 (orf _ (rle_step _ _) _) => eapply rle_step_pre : pre.

Lemma rle_body_pre p flush a : orf (smap (ppre p) (tpre p)) (rle_body flush (ppre p a)) (rle_body flush a).
Proof. destruct a as [s z]. unfold rle_body. pre_go. Qed.

Lemma rle_loop_pre p flush s z :
  orf (tpre p) (loop FUEL (rle_body flush) (s, zpre p z)) (loop FUEL (rle_body flush) (s, z)).
Proof. exact (loop_pre (ppre p) (tpre p) _ (rle_body_pre p flush) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ (rle_body _) _) _) => eapply rle_loop_pre : pre.

Lemma deflate_rle_pre p s z flush : orf (tpre p) (c_deflate_rle s (zpre p z) flush) (c_deflate_rle s z flush).
Proof. unfold c_deflate_rle. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_rle _ _ _) _) => eapply deflate_rle_pre : pre.

Lemma huff_body_pre p flush a : orf (smap (ppre p) (tpre p)) (huff_body flush (ppre p a)) (huff_body flush a).
Proof. destruct a as [s z]. unfold huff_body. pre_go. Qed.

Lemma huff_loop_pre p flush s z :
  orf (tpre p) (loop FUEL (huff_body flush) (s, zpre p z)) (loop FUEL (huff_body flush) (s, z)).
Proof. exact (loop_pre (ppre p) (tpre p) _ (huff_body_pre p flush) FUEL (s, z)). Qed.
Hint Extern 1 (orf _ (loop _ (huff_body _) _) _) => eapply huff_loop_pre : pre.

Lemma deflate_huff_pre p s z flush : orf (tpre p) (c_deflate_huff s (zpre p z) flush) (c_deflate_huff s z flush).
Proof. unfold c_deflate_huff. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_huff _ _ _) _) => eapply deflate_huff_pre : pre.

Lemma compress_func_pre p s z flush : orf (tpre p) (c_compress_func s (zpre p z) flush) (c_compress_func s z flush).
Proof. unfold c_compress_func. pre_go. Qed.
Hint Extern 1 (orf _ (c_compress_func _ _ _) _) => eapply compress_func_pre : pre.

(** ** The stages of deflate() *)

Lemma deflate_compress_pre p s z flush : orf (tpre p) (c_deflate_compress s (zpre p z) flush) (c_deflate_compress s z flush).
Proof. unfold c_deflate_compress. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_compress _ _ _) _) => eapply deflate_compress_pre : pre.

Lemma flush_or_return_pre p s z : orf (tpre p) (c_flush_or_return s (zpre p z)) (c_flush_or_return s z).
Proof. unfold c_flush_or_return. pre_go. Qed.
Hint Extern 1 (orf _ (c_flush_or_return _ _) _) => eapply flush_or_return_pre : pre.

Lemma deflate_entry_pre p s z flush : orf (tpre p) (c_deflate_entry s (zpre p z) flush) (c_deflate_entry s z flush).
Proof. unfold c_deflate_entry. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_entry _ _ _) _) => eapply deflate_entry_pre : pre.

Lemma zlib_header_pre p s z : orf (tpre p) (c_deflate_zlib_header s (zpre p z)) (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_zlib_header _ _) _) => eapply zlib_header_pre : pre.

Lemma gzip_header_pre p s z : orf (tpre p) (c_deflate_gzip_header s (zpre p z)) (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_gzip_header _ _) _) => eapply gzip_header_pre : pre.

Lemma hcrc_update_pre p h s z beg : orf (zpre p) (c_hcrc_update h s (zpre p z) beg) (c_hcrc_update h s z beg).
Proof. unfold c_hcrc_update. pre_go. Qed.
Hint Extern 1 (orf _ (c_hcrc_update _ _ _ _) _) => eapply hcrc_update_pre : pre.

Lemma extra_body_pre p h x a :
  orf (smap (qpre p) (smap (qpre p) (ppre p))) (extra_body h x (qpre p a)) (extra_body h x a).
Proof. destruct a as [[[s z] beg] lft]. unfold extra_body. pre_go. Qed.

Lemma extra_loop_pre p h x s z beg lft :
  orf (smap (qpre p) (ppre p)) (loop FUEL (extra_body h x) (s, zpre p z, beg, lft)) (loop FUEL (extra_body h x) (s, z, beg, lft)).
Proof. exact (loop_pre (qpre p) (smap (qpre p) (ppre p)) _ (extra_body_pre p h x) FUEL (s, z, beg, lft)). Qed.
Hint Extern 1 (orf _ (loop _ (extra_body _ _) _) _) => eapply extra_loop_pre : pre.

Lemma deflate_extra_pre p s z : orf (tpre p) (c_deflate_extra s (zpre p z)) (c_deflate_extra s z).
Proof. unfold c_deflate_extra. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_extra _ _) _) => eapply deflate_extra_pre : pre.

Lemma str_body_pre p h str a :
  orf (smap (tpre p) (smap (tpre p) (ppre p))) (str_body h str (tpre p a)) (str_body h str a).
Proof. destruct a as [[s z] beg]. unfold str_body. pre_go. Qed.

Lemma str_loop_pre p h str s z beg :
  orf (smap (tpre p) (ppre p)) (loop FUEL (str_body h str) (s, zpre p z, beg)) (loop FUEL (str_body h str) (s, z, beg)).
Proof. exact (loop_pre (tpre p) (smap (tpre p) (ppre p)) _ (str_body_pre p h str) FUEL (s, z, beg)). Qed.
Hint Extern 1 (orf _ (loop _ (str_body _ _) _) _) => eapply str_loop_pre : pre.

Lemma deflate_str_pre p h o reset s z : orf (tpre p) (c_deflate_str h o reset s (zpre p z)) (c_deflate_str h o reset s z).
Proof. unfold c_deflate_str. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_str _ _ _ _ _) _) => eapply deflate_str_pre : pre.

Lemma deflate_name_pre p s z : orf (tpre p) (c_deflate_name s (zpre p z)) (c_deflate_name s z).
Proof. unfold c_deflate_name. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_name _ _) _) => eapply deflate_name_pre : pre.

Lemma deflate_comment_pre p s z : orf (tpre p) (c_deflate_comment s (zpre p z)) (c_deflate_comment s z).
Proof. unfold c_deflate_comment. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_comment _ _) _) => eapply deflate_comment_pre : pre.

Lemma deflate_hcrc_pre p s z : orf (tpre p) (c_deflate_hcrc s (zpre p z)) (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_hcrc _ _) _) => eapply deflate_hcrc_pre : pre.

Lemma deflate_trailer_pre p s z flush : orf (tpre p) (c_deflate_trailer s (zpre p z) flush) (c_deflate_trailer s z flush).
Proof. unfold c_deflate_trailer. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate_trailer _ _ _) _) => eapply deflate_trailer_pre : pre.

(** ** deflate() *)

Lemma deflate_pre_ref p s z flush : orf (tpre p) (c_deflate s (zpre p z) flush) (c_deflate s z flush).
Proof. unfold c_deflate. pre_go. Qed.
Hint Extern 1 (orf _ (c_deflate _ _ _) _) => eapply deflate_pre_ref : pre.

Theorem deflate_pre : forall p s z flush s' z' code,
  c_deflate s z flush = Some (s', z', code) -> c_deflate s (zpre p z) flush = Some (s', zpre p z', code).
Proof.
  intros p s z flush s' z' code H. exact (orf_use _ _ _ _ (deflate_pre_ref p s z flush) H).
Qed.

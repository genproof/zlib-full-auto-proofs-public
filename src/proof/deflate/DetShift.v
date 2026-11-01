(** * total_out is only counted: a call on a stream with total_out shifted is the same call, shifted ([tout_shift_stmt], DetWide.v)

    The deflate model never reads [z_total_out]; it only adds to it modulo 2^64 (flush_pending and the two
    direct copies of deflate_stored).  Since [u64 (u64 (a + d) + n) = u64 (u64 (a + n) + d)], every model
    function that threads a stream commutes with [zsh d]: one lemma per function, each of the form
    [f .. (zsh d z) .. = option_map (shift of the result) (f .. z ..)], proved by unfolding [f] and walking both
    sides in lockstep ([sh_go]); the loops by [loop_sh] from the commutation of their bodies. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetWide.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The shifts of the results *)

(** A (state, stream) pair, a (state, stream, x) triple, a (state, stream, x, y) quadruple, a (stream, bytes)
    pair (read_buf), and a sum of two shifted values. *)
Definition psh (d : Z) (p : dstate * strm) : dstate * strm := (fst p, zsh d (snd p)).
Definition tsh {C : Type} (d : Z) (r : dstate * strm * C) : dstate * strm * C :=
  (fst (fst r), zsh d (snd (fst r)), snd r).
Definition qsh {C D : Type} (d : Z) (r : dstate * strm * C * D) : dstate * strm * C * D := (tsh d (fst r), snd r).
Definition bsh (d : Z) (p : strm * list Z) : strm * list Z := (zsh d (fst p), snd p).
Definition smap {A B : Type} (f : A -> A) (g : B -> B) (x : A + B) : A + B :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

(** ** Arithmetic, getters and setters *)

Lemma u64_shift (a n d : Z) : u64 (u64 (a + d) + n) = u64 (u64 (a + n) + d).
Proof. unfold u64. rewrite !Zplus_mod_idemp_l. f_equal. lia. Qed.

Section Getters.
Variables (d : Z) (z : strm).
Lemma zsh_in : z_in (zsh d z) = z_in z. Proof. reflexivity. Qed.
Lemma zsh_next_in : z_next_in (zsh d z) = z_next_in z. Proof. reflexivity. Qed.
Lemma zsh_avail_in : z_avail_in (zsh d z) = z_avail_in z. Proof. reflexivity. Qed.
Lemma zsh_total_in : z_total_in (zsh d z) = z_total_in z. Proof. reflexivity. Qed.
Lemma zsh_out : z_out (zsh d z) = z_out z. Proof. reflexivity. Qed.
Lemma zsh_avail_out : z_avail_out (zsh d z) = z_avail_out z. Proof. reflexivity. Qed.
Lemma zsh_total_out : z_total_out (zsh d z) = u64 (z_total_out z + d). Proof. reflexivity. Qed.
Lemma zsh_adler : z_adler (zsh d z) = z_adler z. Proof. reflexivity. Qed.
Lemma zsh_msg : z_msg (zsh d z) = z_msg z. Proof. reflexivity. Qed.

Lemma zsh_set_in x : set_z_in (zsh d z) x = zsh d (set_z_in z x). Proof. reflexivity. Qed.
Lemma zsh_set_next_in x : set_z_next_in (zsh d z) x = zsh d (set_z_next_in z x). Proof. reflexivity. Qed.
Lemma zsh_set_avail_in x : set_z_avail_in (zsh d z) x = zsh d (set_z_avail_in z x). Proof. reflexivity. Qed.
Lemma zsh_set_total_in x : set_z_total_in (zsh d z) x = zsh d (set_z_total_in z x). Proof. reflexivity. Qed.
Lemma zsh_set_out x : set_z_out (zsh d z) x = zsh d (set_z_out z x). Proof. reflexivity. Qed.
Lemma zsh_set_avail_out x : set_z_avail_out (zsh d z) x = zsh d (set_z_avail_out z x). Proof. reflexivity. Qed.
Lemma zsh_set_adler x : set_z_adler (zsh d z) x = zsh d (set_z_adler z x). Proof. reflexivity. Qed.
Lemma zsh_set_msg x : set_z_msg (zsh d z) x = zsh d (set_z_msg z x). Proof. reflexivity. Qed.

(** The only update of total_out in the model: an addition modulo 2^64. *)
Lemma zsh_add_total_out n :
  set_z_total_out (zsh d z) (u64 (u64 (z_total_out z + d) + n)) = zsh d (set_z_total_out z (u64 (z_total_out z + n))).
Proof. unfold zsh, set_z_total_out. simpl. rewrite u64_shift. reflexivity. Qed.
End Getters.

Lemma option_map_Some {A B : Type} (f : A -> B) x : option_map f (Some x) = Some (f x).
Proof. reflexivity. Qed.
Lemma option_map_None {A B : Type} (f : A -> B) : option_map f None = None.
Proof. reflexivity. Qed.

Create HintDb zsh.
Hint Rewrite @option_map_Some @option_map_None : zsh.
Hint Rewrite zsh_in zsh_next_in zsh_avail_in zsh_total_in zsh_out zsh_avail_out zsh_total_out zsh_adler zsh_msg
  zsh_set_in zsh_set_next_in zsh_set_avail_in zsh_set_total_in zsh_set_out zsh_set_avail_out zsh_set_adler
  zsh_set_msg zsh_add_total_out : zsh.

(** ** Loops *)

Lemma loop2_sh {A B : Type} (FA : A -> A) (FB : B -> B) (body : A -> option (A + B)) :
  (forall a, body (FA a) = option_map (smap FA FB) (body a)) ->
  forall n a, loop2 n body (FA a) = option_map (smap FA FB) (loop2 n body a).
Proof.
  intros H n; induction n as [|n IH]; intros a; simpl; [apply H|].
  rewrite IH. destruct (loop2 n body a) as [[a'|b]|]; simpl; auto.
Qed.

Lemma loop_sh {A B : Type} (FA : A -> A) (FB : B -> B) (body : A -> option (A + B)) :
  (forall a, body (FA a) = option_map (smap FA FB) (body a)) ->
  forall n a, loop n body (FA a) = option_map FB (loop n body a).
Proof.
  intros H n a. unfold loop. rewrite (loop2_sh FA FB body H).
  destruct (loop2 n body a) as [[a'|b]|]; reflexivity.
Qed.

(** ** The lockstep tactic

    The goal is [lhs = option_map F rhs] where [lhs] is [rhs] with the stream shifted.  Rewrite the shifted
    getters, setters and calls ([zsh] database), reduce the monad, and case on the first scrutinee that is the
    same on both sides (one without [zsh]); the result of a shifted call is cased on through its [option_map]. *)
Ltac dpairs :=
  repeat match goal with
         | p : _ * _ |- _ => destruct p
         | p : ?T |- _ => let T' := eval hnf in T in lazymatch T' with prod _ _ => destruct p end
         end.

Ltac sh_red :=
  dpairs; unfold psh, tsh, qsh, bsh; cbn [smap fst snd]; autorewrite with zsh;
  unfold bind, then_stage, psh, tsh, qsh, bsh; cbn [smap fst snd].

Ltac sh_case :=
  match goal with
  | |- context [match option_map _ ?y with _ => _ end] =>
      lazymatch y with context [zsh] => fail | _ => destruct y end
  | |- context [match smap _ _ ?y with _ => _ end] =>
      lazymatch y with context [zsh] => fail | _ => destruct y end
  | |- context [match ?x with _ => _ end] =>
      lazymatch x with
      | context [zsh] => fail
      | context [smap] => fail
      | context [match _ with _ => _ end] => fail
      | _ => destruct x
      end
  end.

Ltac sh_refl :=
  lazymatch goal with
  | |- ?a = ?b =>
      first [ constr_eq a b; reflexivity
            | lazymatch goal with
              | |- context [match _ with _ => _ end] => fail
              | |- context [option_map] => fail
              | _ => reflexivity
              end ]
  end.

Ltac sh_go := repeat (first [sh_refl | progress sh_red | sh_case]).

(** ** read_buf, out_put, flush_pending, FLUSH_BLOCK *)

Lemma out_put_sh d z b : out_put (zsh d z) b = option_map (zsh d) (out_put z b).
Proof. unfold out_put. sh_go. Qed.
Hint Rewrite out_put_sh : zsh.

Lemma read_buf_sh d s z n : c_read_buf s (zsh d z) n = option_map (bsh d) (c_read_buf s z n).
Proof. unfold c_read_buf. sh_go. Qed.
Hint Rewrite read_buf_sh : zsh.

Lemma flush_pending_sh d s z : c_flush_pending s (zsh d z) = option_map (psh d) (c_flush_pending s z).
Proof. unfold c_flush_pending. sh_go. Qed.
Hint Rewrite flush_pending_sh : zsh.

Lemma flush_block_only_sh d s z last :
  c_flush_block_only s (zsh d z) last = option_map (psh d) (c_flush_block_only s z last).
Proof. unfold c_flush_block_only. sh_go. Qed.
Hint Rewrite flush_block_only_sh : zsh.

Lemma flush_block_sh d s z last :
  c_flush_block s (zsh d z) last = option_map (tsh d) (c_flush_block s z last).
Proof. unfold c_flush_block. sh_go. Qed.
Hint Rewrite flush_block_sh : zsh.

(** ** fill_window *)

Lemma fw_body_sh d a : fw_body (psh d a) = option_map (smap (psh d) (psh d)) (fw_body a).
Proof. destruct a as [s z]. unfold fw_body. sh_go. Qed.

Lemma fw_loop_sh d s z :
  loop FUEL fw_body (s, zsh d z) = option_map (psh d) (loop FUEL fw_body (s, z)).
Proof. exact (loop_sh (psh d) (psh d) fw_body (fw_body_sh d) FUEL (s, z)). Qed.
Hint Rewrite fw_loop_sh : zsh.

Lemma fill_window_sh d s z : c_fill_window s (zsh d z) = option_map (psh d) (c_fill_window s z).
Proof. unfold c_fill_window. sh_go. Qed.
Hint Rewrite fill_window_sh : zsh.

(** ** The pieces of the compression functions *)

Lemma bflush_sh d s z b :
  c_bflush s (zsh d z) b = option_map (smap (psh d) (tsh d)) (c_bflush s z b).
Proof. unfold c_bflush. sh_go. Qed.
Hint Rewrite bflush_sh : zsh.

Lemma refill_sh d need flush s z :
  c_refill need flush s (zsh d z) = option_map (smap (psh d) (tsh d)) (c_refill need flush s z).
Proof. unfold c_refill. sh_go. Qed.
Hint Rewrite refill_sh : zsh.

Lemma deflate_tail_sh d s z flush :
  c_deflate_tail s (zsh d z) flush = option_map (tsh d) (c_deflate_tail s z flush).
Proof. unfold c_deflate_tail. sh_go. Qed.
Hint Rewrite deflate_tail_sh : zsh.

(** ** deflate_stored *)

(** deflate_stored and its copy loop have [let*]s whose bound value is an [if]: casing on it would copy the rest of the
    function into each case.  [sh_bind] instead splits [let* x := o in k] into the commutation of [o] and that
    of [k] at every value, with the shift of the value chosen by its type. *)
Lemma bind_sh {A B : Type} (FA : A -> A) (FB : B -> B) (o1 o2 : option A) (k1 k2 : A -> option B) :
  o1 = option_map FA o2 -> (forall a, k1 (FA a) = option_map FB (k2 a)) ->
  bind o1 k1 = option_map FB (bind o2 k2).
Proof. intros -> H. destruct o2; simpl; auto. Qed.

Ltac sh_fa d T :=
  lazymatch T with
  | option (dstate * strm) => constr:(psh d)
  | option (dstate * strm * ?C) => constr:(@tsh C d)
  | option strm => constr:(zsh d)
  | option (strm * list Z) => constr:(bsh d)
  | option ?A => constr:(fun x : A => x)
  end.

Ltac sh_bind d :=
  repeat (dpairs; unfold psh, tsh, qsh, bsh; cbn [smap fst snd]; autorewrite with zsh;
          unfold psh, tsh, qsh, bsh; cbn [smap fst snd];
    first
    [ sh_refl
    | match goal with
      | |- bind ?o1 ?k1 = option_map ?FB (bind ?o2 ?k2) =>
          let T := type of o2 in let FA := sh_fa d T in
          apply (bind_sh FA FB o1 o2 k1 k2); [|intros ?a]
      | |- _ = option_map _ (match ?x with _ => _ end) => destruct x
      | |- _ = option_map _ ?o2 => destruct o2
      end ]).

Lemma ds_body_sh d flush mb a :
  ds_body flush mb (psh d a) = option_map (smap (psh d) (tsh d)) (ds_body flush mb a).
Proof. destruct a as [s z]. unfold ds_body. sh_bind d. Qed.

Lemma ds_loop_sh d flush mb s z :
  loop FUEL (ds_body flush mb) (s, zsh d z) = option_map (tsh d) (loop FUEL (ds_body flush mb) (s, z)).
Proof. exact (loop_sh (psh d) (tsh d) _ (ds_body_sh d flush mb) FUEL (s, z)). Qed.
Hint Rewrite ds_loop_sh : zsh.

Lemma ds_window_sh d s z used : c_ds_window s (zsh d z) used = c_ds_window s z used.
Proof. unfold c_ds_window. autorewrite with zsh. reflexivity. Qed.
Hint Rewrite ds_window_sh : zsh.

Lemma deflate_stored_sh d s z flush :
  c_deflate_stored s (zsh d z) flush = option_map (tsh d) (c_deflate_stored s z flush).
Proof. unfold c_deflate_stored. sh_bind d. Qed.
Hint Rewrite deflate_stored_sh : zsh.

(** ** deflate_fast, deflate_slow, deflate_rle, deflate_huff *)

Lemma df_step_sh d s z : df_step s (zsh d z) = option_map (smap (psh d) (tsh d)) (df_step s z).
Proof. unfold df_step. sh_go. Qed.
Hint Rewrite df_step_sh : zsh.

Lemma df_body_sh d flush a : df_body flush (psh d a) = option_map (smap (psh d) (tsh d)) (df_body flush a).
Proof. destruct a as [s z]. unfold df_body. sh_go. Qed.

Lemma df_loop_sh d flush s z :
  loop FUEL (df_body flush) (s, zsh d z) = option_map (tsh d) (loop FUEL (df_body flush) (s, z)).
Proof. exact (loop_sh (psh d) (tsh d) _ (df_body_sh d flush) FUEL (s, z)). Qed.
Hint Rewrite df_loop_sh : zsh.

Lemma deflate_fast_sh d s z flush :
  c_deflate_fast s (zsh d z) flush = option_map (tsh d) (c_deflate_fast s z flush).
Proof. unfold c_deflate_fast. sh_go. Qed.
Hint Rewrite deflate_fast_sh : zsh.

Lemma dsl_step_sh d s z : dsl_step s (zsh d z) = option_map (smap (psh d) (tsh d)) (dsl_step s z).
Proof. unfold dsl_step. sh_go. Qed.
Hint Rewrite dsl_step_sh : zsh.

Lemma dsl_body_sh d flush a : dsl_body flush (psh d a) = option_map (smap (psh d) (tsh d)) (dsl_body flush a).
Proof. destruct a as [s z]. unfold dsl_body. sh_go. Qed.

Lemma dsl_loop_sh d flush s z :
  loop FUEL (dsl_body flush) (s, zsh d z) = option_map (tsh d) (loop FUEL (dsl_body flush) (s, z)).
Proof. exact (loop_sh (psh d) (tsh d) _ (dsl_body_sh d flush) FUEL (s, z)). Qed.
Hint Rewrite dsl_loop_sh : zsh.

Lemma deflate_slow_sh d s z flush :
  c_deflate_slow s (zsh d z) flush = option_map (tsh d) (c_deflate_slow s z flush).
Proof. unfold c_deflate_slow. sh_go. Qed.
Hint Rewrite deflate_slow_sh : zsh.

Lemma rle_step_sh d s z : rle_step s (zsh d z) = option_map (smap (psh d) (tsh d)) (rle_step s z).
Proof. unfold rle_step. sh_go. Qed.
Hint Rewrite rle_step_sh : zsh.

Lemma rle_body_sh d flush a : rle_body flush (psh d a) = option_map (smap (psh d) (tsh d)) (rle_body flush a).
Proof. destruct a as [s z]. unfold rle_body. sh_go. Qed.

Lemma rle_loop_sh d flush s z :
  loop FUEL (rle_body flush) (s, zsh d z) = option_map (tsh d) (loop FUEL (rle_body flush) (s, z)).
Proof. exact (loop_sh (psh d) (tsh d) _ (rle_body_sh d flush) FUEL (s, z)). Qed.
Hint Rewrite rle_loop_sh : zsh.

Lemma deflate_rle_sh d s z flush :
  c_deflate_rle s (zsh d z) flush = option_map (tsh d) (c_deflate_rle s z flush).
Proof. unfold c_deflate_rle. sh_go. Qed.
Hint Rewrite deflate_rle_sh : zsh.

Lemma huff_body_sh d flush a :
  huff_body flush (psh d a) = option_map (smap (psh d) (tsh d)) (huff_body flush a).
Proof. destruct a as [s z]. unfold huff_body. sh_go. Qed.

Lemma huff_loop_sh d flush s z :
  loop FUEL (huff_body flush) (s, zsh d z) = option_map (tsh d) (loop FUEL (huff_body flush) (s, z)).
Proof. exact (loop_sh (psh d) (tsh d) _ (huff_body_sh d flush) FUEL (s, z)). Qed.
Hint Rewrite huff_loop_sh : zsh.

Lemma deflate_huff_sh d s z flush :
  c_deflate_huff s (zsh d z) flush = option_map (tsh d) (c_deflate_huff s z flush).
Proof. unfold c_deflate_huff. sh_go. Qed.
Hint Rewrite deflate_huff_sh : zsh.

Lemma compress_func_sh d s z flush :
  c_compress_func s (zsh d z) flush = option_map (tsh d) (c_compress_func s z flush).
Proof. unfold c_compress_func. sh_go. Qed.
Hint Rewrite compress_func_sh : zsh.

(** ** The stages of deflate() *)

Lemma deflate_compress_sh d s z flush :
  c_deflate_compress s (zsh d z) flush = option_map (tsh d) (c_deflate_compress s z flush).
Proof. unfold c_deflate_compress. sh_go. Qed.
Hint Rewrite deflate_compress_sh : zsh.

Lemma flush_or_return_sh d s z : c_flush_or_return s (zsh d z) = option_map (tsh d) (c_flush_or_return s z).
Proof. unfold c_flush_or_return. sh_go. Qed.
Hint Rewrite flush_or_return_sh : zsh.

Lemma deflate_entry_sh d s z flush :
  c_deflate_entry s (zsh d z) flush = option_map (tsh d) (c_deflate_entry s z flush).
Proof. unfold c_deflate_entry. sh_go. Qed.
Hint Rewrite deflate_entry_sh : zsh.

Lemma zlib_header_sh d s z : c_deflate_zlib_header s (zsh d z) = option_map (tsh d) (c_deflate_zlib_header s z).
Proof. unfold c_deflate_zlib_header. sh_go. Qed.
Hint Rewrite zlib_header_sh : zsh.

Lemma gzip_header_sh d s z : c_deflate_gzip_header s (zsh d z) = option_map (tsh d) (c_deflate_gzip_header s z).
Proof. unfold c_deflate_gzip_header. sh_go. Qed.
Hint Rewrite gzip_header_sh : zsh.

Lemma hcrc_update_sh d h s z beg : c_hcrc_update h s (zsh d z) beg = option_map (zsh d) (c_hcrc_update h s z beg).
Proof. unfold c_hcrc_update. sh_go. Qed.
Hint Rewrite hcrc_update_sh : zsh.

Lemma extra_body_sh d h x a :
  extra_body h x (qsh d a) = option_map (smap (qsh d) (smap (qsh d) (psh d))) (extra_body h x a).
Proof. destruct a as [[[s z] beg] lft]. unfold extra_body. sh_go. Qed.

Lemma extra_loop_sh d h x s z beg lft :
  loop FUEL (extra_body h x) (s, zsh d z, beg, lft) =
  option_map (smap (qsh d) (psh d)) (loop FUEL (extra_body h x) (s, z, beg, lft)).
Proof. exact (loop_sh (qsh d) (smap (qsh d) (psh d)) _ (extra_body_sh d h x) FUEL (s, z, beg, lft)). Qed.
Hint Rewrite extra_loop_sh : zsh.

Lemma deflate_extra_sh d s z : c_deflate_extra s (zsh d z) = option_map (tsh d) (c_deflate_extra s z).
Proof. unfold c_deflate_extra. sh_go. Qed.
Hint Rewrite deflate_extra_sh : zsh.

Lemma str_body_sh d h str a :
  str_body h str (tsh d a) = option_map (smap (tsh d) (smap (tsh d) (psh d))) (str_body h str a).
Proof. destruct a as [[s z] beg]. unfold str_body. sh_go. Qed.

Lemma str_loop_sh d h str s z beg :
  loop FUEL (str_body h str) (s, zsh d z, beg) =
  option_map (smap (tsh d) (psh d)) (loop FUEL (str_body h str) (s, z, beg)).
Proof. exact (loop_sh (tsh d) (smap (tsh d) (psh d)) _ (str_body_sh d h str) FUEL (s, z, beg)). Qed.
Hint Rewrite str_loop_sh : zsh.

Lemma deflate_str_sh d h o reset s z :
  c_deflate_str h o reset s (zsh d z) = option_map (tsh d) (c_deflate_str h o reset s z).
Proof. unfold c_deflate_str. sh_go. Qed.
Hint Rewrite deflate_str_sh : zsh.

Lemma deflate_name_sh d s z : c_deflate_name s (zsh d z) = option_map (tsh d) (c_deflate_name s z).
Proof. unfold c_deflate_name. sh_go. Qed.
Hint Rewrite deflate_name_sh : zsh.

Lemma deflate_comment_sh d s z : c_deflate_comment s (zsh d z) = option_map (tsh d) (c_deflate_comment s z).
Proof. unfold c_deflate_comment. sh_go. Qed.
Hint Rewrite deflate_comment_sh : zsh.

Lemma deflate_hcrc_sh d s z : c_deflate_hcrc s (zsh d z) = option_map (tsh d) (c_deflate_hcrc s z).
Proof. unfold c_deflate_hcrc. sh_go. Qed.
Hint Rewrite deflate_hcrc_sh : zsh.

Lemma deflate_trailer_sh d s z flush :
  c_deflate_trailer s (zsh d z) flush = option_map (tsh d) (c_deflate_trailer s z flush).
Proof. unfold c_deflate_trailer. sh_go. Qed.
Hint Rewrite deflate_trailer_sh : zsh.

(** ** deflate() and deflateParams() *)

Lemma deflate_sh d s z flush : c_deflate s (zsh d z) flush = option_map (tsh d) (c_deflate s z flush).
Proof. unfold c_deflate. sh_go. Qed.
Hint Rewrite deflate_sh : zsh.

Lemma deflateParams_sh d s z level strategy :
  c_deflateParams s (zsh d z) level strategy = option_map (tsh d) (c_deflateParams s z level strategy).
Proof. unfold c_deflateParams. sh_go. Qed.

Theorem tout_shift : tout_shift_stmt.
Proof.
  split; intros; [apply deflate_sh | apply deflateParams_sh].
Qed.

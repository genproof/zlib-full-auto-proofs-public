(** * deflate()'s model on a slice of its input object gives the call on the whole object

    The converse of InSlice.deflate_slice: when the model succeeds on the object cut down to the bytes
    [d, d + L) around the offered input ([zslice d L z]), it succeeds on the whole object with the same state,
    code and output, the stream being the sliced one with the whole object.  compress2_z's model runs deflate()
    on the whole source (up to 2^63-1 bytes), while the deflateBound accounting (LTWBWalk) runs a call on an
    object of its own offered from offset 0; this lemma moves the accounting's call to the source.  The simulation
    behind it, function by function, is InUnsliceKit.v (up to deflate_stored) and the lemmas [un_f] below. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel5 Zlib.proof.deflate.InSlice Zlib.proof.deflate.InUnsliceKit.
Import ListNotations.
Local Open Scope Z_scope.

Local Strategy opaque [loop loop2].
#[local] Ltac zwin_tac ::= uwin_tac.
#[local] Ltac sl_call ::= un_call.

(** ** deflate_fast, deflate_slow, deflate_rle, deflate_huff *)
Lemma un_df_step d L l s y x : df_step s y = Some x -> uwin d L l y -> step_un d L l (df_step s (zun d l y)) x.
Proof. un_tac df_step. Qed.

Lemma un_dsl_step d L l s y x : dsl_step s y = Some x -> uwin d L l y -> step_un d L l (dsl_step s (zun d l y)) x.
Proof. un_tac dsl_step. Qed.

Lemma un_rle_step d L l s y x : rle_step s y = Some x -> uwin d L l y -> step_un d L l (rle_step s (zun d l y)) x.
Proof. un_tac rle_step. Qed.

Ltac un_call9 ::=
  match goal with
  | Ha : df_step ?s ?y = Some _ |- context [df_step ?s (zun ?d ?l ?y)] => use_un un_df_step d l y Ha
  | Ha : dsl_step ?s ?y = Some _ |- context [dsl_step ?s (zun ?d ?l ?y)] => use_un un_dsl_step d l y Ha
  | Ha : rle_step ?s ?y = Some _ |- context [rle_step ?s (zun ?d ?l ?y)] => use_un un_rle_step d l y Ha
  end.

Lemma un_df_body d L l flush s y x : df_body flush (s, y) = Some x -> uwin d L l y ->
  step_un d L l (df_body flush (s, zun d l y)) x.
Proof. un_tac df_body. Qed.

Lemma un_dsl_body d L l flush s y x : dsl_body flush (s, y) = Some x -> uwin d L l y ->
  step_un d L l (dsl_body flush (s, zun d l y)) x.
Proof. un_tac dsl_body. Qed.

Lemma un_rle_body d L l flush s y x : rle_body flush (s, y) = Some x -> uwin d L l y ->
  step_un d L l (rle_body flush (s, zun d l y)) x.
Proof. un_tac rle_body. Qed.

Lemma un_huff_body d L l flush s y x : huff_body flush (s, y) = Some x -> uwin d L l y ->
  step_un d L l (huff_body flush (s, zun d l y)) x.
Proof. un_tac huff_body. Qed.

Lemma un_df_loop d L l flush s y s1 y1 r : loop FUEL (df_body flush) (s, y) = Some (s1, y1, r) -> uwin d L l y ->
  loop FUEL (df_body flush) (s, zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. loop_un un_df_body. Qed.

Lemma un_dsl_loop d L l flush s y s1 y1 r : loop FUEL (dsl_body flush) (s, y) = Some (s1, y1, r) -> uwin d L l y ->
  loop FUEL (dsl_body flush) (s, zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. loop_un un_dsl_body. Qed.

Lemma un_rle_loop d L l flush s y s1 y1 r : loop FUEL (rle_body flush) (s, y) = Some (s1, y1, r) -> uwin d L l y ->
  loop FUEL (rle_body flush) (s, zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. loop_un un_rle_body. Qed.

Lemma un_huff_loop d L l flush s y s1 y1 r : loop FUEL (huff_body flush) (s, y) = Some (s1, y1, r) -> uwin d L l y ->
  loop FUEL (huff_body flush) (s, zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. loop_un un_huff_body. Qed.

Ltac un_call10 ::=
  match goal with
  | Ha : loop _ (df_body ?f) (?s, ?y) = Some _ |- context [loop _ (df_body ?f) (?s, zun ?d ?l ?y)] =>
      use_un un_df_loop d l y Ha
  | Ha : loop _ (dsl_body ?f) (?s, ?y) = Some _ |- context [loop _ (dsl_body ?f) (?s, zun ?d ?l ?y)] =>
      use_un un_dsl_loop d l y Ha
  | Ha : loop _ (rle_body ?f) (?s, ?y) = Some _ |- context [loop _ (rle_body ?f) (?s, zun ?d ?l ?y)] =>
      use_un un_rle_loop d l y Ha
  | Ha : loop _ (huff_body ?f) (?s, ?y) = Some _ |- context [loop _ (huff_body ?f) (?s, zun ?d ?l ?y)] =>
      use_un un_huff_loop d l y Ha
  end.

Lemma un_deflate_fast d L l s y f s1 y1 r : c_deflate_fast s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_fast s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_deflate_fast. Qed.

Lemma un_deflate_slow d L l s y f s1 y1 r : c_deflate_slow s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_slow s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_deflate_slow. Qed.

Lemma un_deflate_rle d L l s y f s1 y1 r : c_deflate_rle s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_rle s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_deflate_rle. Qed.

Lemma un_deflate_huff d L l s y f s1 y1 r : c_deflate_huff s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_huff s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_deflate_huff. Qed.

Ltac un_call11 ::=
  match goal with
  | Ha : c_deflate_stored ?s ?y ?f = Some _ |- context [c_deflate_stored ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_stored d l y Ha
  | Ha : c_deflate_fast ?s ?y ?f = Some _ |- context [c_deflate_fast ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_fast d l y Ha
  | Ha : c_deflate_slow ?s ?y ?f = Some _ |- context [c_deflate_slow ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_slow d l y Ha
  | Ha : c_deflate_rle ?s ?y ?f = Some _ |- context [c_deflate_rle ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_rle d l y Ha
  | Ha : c_deflate_huff ?s ?y ?f = Some _ |- context [c_deflate_huff ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_huff d l y Ha
  end.

Lemma un_compress_func d L l s y f s1 y1 r : c_compress_func s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_compress_func s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_compress_func. Qed.

(** ** The stages of deflate() *)

(** The results of the stages: [(dstate * strm * option Z)]. *)
Notation stage_un d L l fs s1 y1 o :=
  (fs = Some (s1, zun d l y1, o) /\ uwin d L l y1) (only parsing).

Lemma un_hcrc_update d L l h s y beg y1 : c_hcrc_update h s y beg = Some y1 -> uwin d L l y ->
  c_hcrc_update h s (zun d l y) beg = Some (zun d l y1) /\ uwin d L l y1.
Proof. un_tac c_hcrc_update. Qed.

Lemma un_flush_or_return d L l s y s1 y1 o : c_flush_or_return s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_flush_or_return s (zun d l y)) s1 y1 o.
Proof. un_tac c_flush_or_return. Qed.

Ltac un_call12 ::=
  match goal with
  | Ha : c_compress_func ?s ?y ?f = Some _ |- context [c_compress_func ?s (zun ?d ?l ?y) ?f] =>
      use_un un_compress_func d l y Ha
  | Ha : c_hcrc_update ?h ?s ?y ?b = Some _ |- context [c_hcrc_update ?h ?s (zun ?d ?l ?y) ?b] =>
      use_un un_hcrc_update d l y Ha
  | Ha : c_flush_or_return ?s ?y = Some _ |- context [c_flush_or_return ?s (zun ?d ?l ?y)] =>
      use_un un_flush_or_return d l y Ha
  end.

Lemma un_extra_body d L l h xs s y beg lft e : extra_body h xs (s, y, beg, lft) = Some e -> uwin d L l y ->
  match e with
  | inl (s1, y1, b1, l1) => extra_body h xs (s, zun d l y, beg, lft) = Some (inl (s1, zun d l y1, b1, l1)) /\
                            uwin d L l y1
  | inr (inl (s1, y1, b1, l1)) =>
      extra_body h xs (s, zun d l y, beg, lft) = Some (inr (inl (s1, zun d l y1, b1, l1))) /\
      uwin d L l y1
  | inr (inr (s1, y1)) => extra_body h xs (s, zun d l y, beg, lft) = Some (inr (inr (s1, zun d l y1))) /\
                          uwin d L l y1
  end.
Proof. un_tac extra_body. Qed.

Lemma un_extra_loop d L l h xs s y beg lft e : loop FUEL (extra_body h xs) (s, y, beg, lft) = Some e -> uwin d L l y ->
  match e with
  | inl (s1, y1, b1, l1) => loop FUEL (extra_body h xs) (s, zun d l y, beg, lft) = Some (inl (s1, zun d l y1, b1, l1)) /\
                            uwin d L l y1
  | inr (s1, y1) => loop FUEL (extra_body h xs) (s, zun d l y, beg, lft) = Some (inr (s1, zun d l y1)) /\
                    uwin d L l y1
  end.
Proof.
  intros H W.
  set (fa := fun a : dstate * strm * Z * Z => let '(s, y, b, lf) := a in (s, zun d l y, b, lf)).
  set (P := fun a : dstate * strm * Z * Z => let '(_, y1, _, _) := a in uwin d L l y1).
  destruct (loop_sim (extra_body h xs) fa
              (fun e => match e with inl a => inl (fa a) | inr (s1, y1) => inr (s1, zun d l y1) end) P
              (fun e => match e with inl a => P a | inr (_, y1) => uwin d L l y1 end))
    with (3 := H) as [E Q].
  - intros [[[s0 y0] b0] l0] x W0 E. apply (un_extra_body d L l) in E; [|exact W0].
    destruct x as [[[[s2 y2] b2] l2]|[[[[s2 y2] b2] l2]|[s2 y2]]]; exact E.
  - exact W.
  - destruct e as [[[[s1 y1] b1] l1]|[s1 y1]]; cbn in E, Q; auto.
Qed.

Lemma un_str_body d L l h str s y beg e : str_body h str (s, y, beg) = Some e -> uwin d L l y ->
  match e with
  | inl (s1, y1, b1) => str_body h str (s, zun d l y, beg) = Some (inl (s1, zun d l y1, b1)) /\
                        uwin d L l y1
  | inr (inl (s1, y1, b1)) => str_body h str (s, zun d l y, beg) = Some (inr (inl (s1, zun d l y1, b1))) /\
                              uwin d L l y1
  | inr (inr (s1, y1)) => str_body h str (s, zun d l y, beg) = Some (inr (inr (s1, zun d l y1))) /\
                          uwin d L l y1
  end.
Proof. un_tac str_body. Qed.

Lemma un_str_loop d L l h str s y beg e : loop FUEL (str_body h str) (s, y, beg) = Some e -> uwin d L l y ->
  match e with
  | inl (s1, y1, b1) => loop FUEL (str_body h str) (s, zun d l y, beg) = Some (inl (s1, zun d l y1, b1)) /\
                        uwin d L l y1
  | inr (s1, y1) => loop FUEL (str_body h str) (s, zun d l y, beg) = Some (inr (s1, zun d l y1)) /\
                    uwin d L l y1
  end.
Proof.
  intros H W.
  set (fa := fun a : dstate * strm * Z => let '(s, y, b) := a in (s, zun d l y, b)).
  set (P := fun a : dstate * strm * Z => let '(_, y1, _) := a in uwin d L l y1).
  destruct (loop_sim (str_body h str) fa
              (fun e => match e with inl a => inl (fa a) | inr (s1, y1) => inr (s1, zun d l y1) end) P
              (fun e => match e with inl a => P a | inr (_, y1) => uwin d L l y1 end))
    with (3 := H) as [E Q].
  - intros [[s0 y0] b0] x W0 E. apply (un_str_body d L l) in E; [|exact W0].
    destruct x as [[[s2 y2] b2]|[[[s2 y2] b2]|[s2 y2]]]; exact E.
  - exact W.
  - destruct e as [[[s1 y1] b1]|[s1 y1]]; cbn in E, Q; auto.
Qed.

Ltac un_call13 ::=
  match goal with
  | Ha : loop _ (extra_body ?h ?x) (?s, ?y, ?b, ?lf) = Some _ |-
      context [loop _ (extra_body ?h ?x) (?s, zun ?d ?l ?y, ?b, ?lf)] => use_un un_extra_loop d l y Ha
  | Ha : loop _ (str_body ?h ?x) (?s, ?y, ?b) = Some _ |-
      context [loop _ (str_body ?h ?x) (?s, zun ?d ?l ?y, ?b)] => use_un un_str_loop d l y Ha
  end.

Lemma un_deflate_str d L l h o r s y s1 y1 x : c_deflate_str h o r s y = Some (s1, y1, x) -> uwin d L l y ->
  stage_un d L l (c_deflate_str h o r s (zun d l y)) s1 y1 x.
Proof. un_tac c_deflate_str. Qed.

Ltac un_call14 ::=
  match goal with
  | Ha : c_deflate_str ?h ?o ?r ?s ?y = Some _ |- context [c_deflate_str ?h ?o ?r ?s (zun ?d ?l ?y)] =>
      use_un un_deflate_str d l y Ha
  end.

Lemma un_entry d L l s y f s1 y1 o : c_deflate_entry s y f = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_entry s (zun d l y) f) s1 y1 o.
Proof. un_tac c_deflate_entry. Qed.

Lemma un_zlib_header d L l s y s1 y1 o : c_deflate_zlib_header s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_zlib_header s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_zlib_header. Qed.

Lemma un_gzip_header d L l s y s1 y1 o : c_deflate_gzip_header s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_gzip_header s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_gzip_header. Qed.

Lemma un_extra d L l s y s1 y1 o : c_deflate_extra s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_extra s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_extra. Qed.

Lemma un_name d L l s y s1 y1 o : c_deflate_name s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_name s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_name. Qed.

Lemma un_comment d L l s y s1 y1 o : c_deflate_comment s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_comment s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_comment. Qed.

Lemma un_hcrc d L l s y s1 y1 o : c_deflate_hcrc s y = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_hcrc s (zun d l y)) s1 y1 o.
Proof. un_tac c_deflate_hcrc. Qed.

Lemma un_compress d L l s y f s1 y1 o : c_deflate_compress s y f = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_compress s (zun d l y) f) s1 y1 o.
Proof. un_tac c_deflate_compress. Qed.

Lemma un_trailer d L l s y f s1 y1 o : c_deflate_trailer s y f = Some (s1, y1, o) -> uwin d L l y ->
  stage_un d L l (c_deflate_trailer s (zun d l y) f) s1 y1 o.
Proof. un_tac c_deflate_trailer. Qed.

Ltac un_call15 ::=
  match goal with
  | Ha : c_deflate_entry ?s ?y ?f = Some _ |- context [c_deflate_entry ?s (zun ?d ?l ?y) ?f] =>
      use_un un_entry d l y Ha
  | Ha : c_deflate_zlib_header ?s ?y = Some _ |- context [c_deflate_zlib_header ?s (zun ?d ?l ?y)] =>
      use_un un_zlib_header d l y Ha
  | Ha : c_deflate_gzip_header ?s ?y = Some _ |- context [c_deflate_gzip_header ?s (zun ?d ?l ?y)] =>
      use_un un_gzip_header d l y Ha
  | Ha : c_deflate_extra ?s ?y = Some _ |- context [c_deflate_extra ?s (zun ?d ?l ?y)] =>
      use_un un_extra d l y Ha
  | Ha : c_deflate_name ?s ?y = Some _ |- context [c_deflate_name ?s (zun ?d ?l ?y)] =>
      use_un un_name d l y Ha
  | Ha : c_deflate_comment ?s ?y = Some _ |- context [c_deflate_comment ?s (zun ?d ?l ?y)] =>
      use_un un_comment d l y Ha
  | Ha : c_deflate_hcrc ?s ?y = Some _ |- context [c_deflate_hcrc ?s (zun ?d ?l ?y)] =>
      use_un un_hcrc d l y Ha
  | Ha : c_deflate_compress ?s ?y ?f = Some _ |- context [c_deflate_compress ?s (zun ?d ?l ?y) ?f] =>
      use_un un_compress d l y Ha
  | Ha : c_deflate_trailer ?s ?y ?f = Some _ |- context [c_deflate_trailer ?s (zun ?d ?l ?y) ?f] =>
      use_un un_trailer d l y Ha
  end.

Lemma un_deflate d L l s y f s1 y1 e : c_deflate s y f = Some (s1, y1, e) -> uwin d L l y ->
  c_deflate s (zun d l y) f = Some (s1, zun d l y1, e) /\ uwin d L l y1.
Proof. un_tac c_deflate. Qed.

(** a call whose offered input [next_in, next_in + avail_in) lies in [d, d + L) and ends at d + L *)
Lemma deflate_unslice d L s z flush s' z1 e :
  0 <= d <= z_next_in z -> 0 <= z_avail_in z -> z_next_in z + z_avail_in z = d + L ->
  d + L <= Zlength (z_in z) ->
  c_deflate s (zslice d L z) flush = Some (s', z1, e) ->
  exists z', c_deflate s z flush = Some (s', z', e) /\ z1 = zslice d L z'.
Proof.
  intros Hd Ha Hs Hl H.
  assert (W : uwin d L (z_in z) (zslice d L z)) by (unfold uwin, zslice; cbn; repeat split; lia).
  destruct (un_deflate d L (z_in z) _ _ _ _ _ _ H W) as [E W1].
  replace (zun d (z_in z) (zslice d L z)) with z in E
    by (destruct z; unfold zun, zslice; cbn; f_equal; lia).
  exists (zun d (z_in z) z1). split; [exact E|].
  destruct W1 as (_ & _ & _ & W1). destruct z1; unfold zun, zslice; cbn in *. rewrite <- W1. f_equal; lia.
Qed.

(** The same, with the input object of the result: the call does not change it. *)
Lemma deflate_unslice_in d L s z flush s' z1 e :
  0 <= d <= z_next_in z -> 0 <= z_avail_in z -> z_next_in z + z_avail_in z = d + L ->
  d + L <= Zlength (z_in z) ->
  c_deflate s (zslice d L z) flush = Some (s', z1, e) ->
  exists z', c_deflate s z flush = Some (s', z', e) /\ z1 = zslice d L z' /\ z_in z' = z_in z.
Proof.
  intros Hd Ha Hs Hl H.
  assert (W : uwin d L (z_in z) (zslice d L z)) by (unfold uwin, zslice; cbn; repeat split; lia).
  destruct (un_deflate d L (z_in z) _ _ _ _ _ _ H W) as [E W1].
  replace (zun d (z_in z) (zslice d L z)) with z in E
    by (destruct z; unfold zun, zslice; cbn; f_equal; lia).
  exists (zun d (z_in z) z1). split; [exact E|]. split; [|reflexivity].
  destruct W1 as (_ & _ & _ & W1). destruct z1; unfold zun, zslice; cbn in *. rewrite <- W1. f_equal; lia.
Qed.

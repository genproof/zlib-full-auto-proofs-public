(** * The converse simulation of InSlice: a model call on a slice of the input object is the call on the whole object

    [zun d l y] puts a stream [y] whose input object is the slice [d, d + L) of [l] ([uwin d L l y]) back on [l],
    next_in moved by [d].  The model reads its input object only through [rds] (read_buf at next_in, deflate_stored's
    window update just before next_in); a read that succeeds on the slice reads the same bytes of [l], [d] further.
    So every model function that succeeds on [y] succeeds on [zun d l y] with the result put back on [l] ([un_f]
    below).  The proofs run the small call (the hypothesis, destructed with InSlice's [crunch]) and the whole call
    (the goal) in lockstep with InSlice's [lockstep], its tactics [zwin_tac] and [sl_call] redefined locally for
    the inverse map.  This file: the kit and the functions up to deflate_stored; InUnslice.v: the other
    compressors, the stages of deflate() and the result. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel5 Zlib.proof.deflate.InSlice.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope cmodel_scope.

(** [zun d l y]: the small stream [y] put back on the whole object [l], next_in moved by [d]: the inverse of
    [zslice d L] on the streams whose object is [sublist d (d + L) l]. *)
Definition zun (d : Z) (l : list Z) (y : strm) : strm :=
  mkST l (z_next_in y + d) (z_avail_in y) (z_total_in y) (z_out y) (z_avail_out y) (z_total_out y) (z_adler y)
    (z_msg y).

(** the small stream's object is the slice [d, d + L) of [l] *)
Definition uwin (d L : Z) (l : list Z) (y : strm) : Prop :=
  0 <= d /\ 0 <= L /\ d + L <= Zlength l /\ z_in y = sublist d (d + L) l.

Section ZU.
Variables (d : Z) (l : list Z) (y : strm).
Lemma zu_in : z_in (zun d l y) = l. Proof. reflexivity. Qed.
Lemma zu_avail_in : z_avail_in (zun d l y) = z_avail_in y. Proof. reflexivity. Qed.
Lemma zu_total_in : z_total_in (zun d l y) = z_total_in y. Proof. reflexivity. Qed.
Lemma zu_out : z_out (zun d l y) = z_out y. Proof. reflexivity. Qed.
Lemma zu_avail_out : z_avail_out (zun d l y) = z_avail_out y. Proof. reflexivity. Qed.
Lemma zu_total_out : z_total_out (zun d l y) = z_total_out y. Proof. reflexivity. Qed.
Lemma zu_adler : z_adler (zun d l y) = z_adler y. Proof. reflexivity. Qed.
Lemma zu_msg : z_msg (zun d l y) = z_msg y. Proof. reflexivity. Qed.
Lemma zu_set_avail_in x : set_z_avail_in (zun d l y) x = zun d l (set_z_avail_in y x).
Proof. reflexivity. Qed.
Lemma zu_set_total_in x : set_z_total_in (zun d l y) x = zun d l (set_z_total_in y x).
Proof. reflexivity. Qed.
Lemma zu_set_out x : set_z_out (zun d l y) x = zun d l (set_z_out y x).
Proof. reflexivity. Qed.
Lemma zu_set_avail_out x : set_z_avail_out (zun d l y) x = zun d l (set_z_avail_out y x).
Proof. reflexivity. Qed.
Lemma zu_set_total_out x : set_z_total_out (zun d l y) x = zun d l (set_z_total_out y x).
Proof. reflexivity. Qed.
Lemma zu_set_adler x : set_z_adler (zun d l y) x = zun d l (set_z_adler y x).
Proof. reflexivity. Qed.
Lemma zu_set_msg x : set_z_msg (zun d l y) x = zun d l (set_z_msg y x).
Proof. reflexivity. Qed.
End ZU.

#[export] Hint Rewrite zu_avail_in zu_total_in zu_out zu_avail_out zu_total_out zu_adler zu_msg zu_set_avail_in
  zu_set_total_in zu_set_out zu_set_avail_out zu_set_total_out zu_set_adler zu_set_msg : zsl.

Local Strategy opaque [loop loop2].

Ltac uwin_tac := unfold uwin in *; znorm; intuition (first [lia | congruence]).

(** InSlice's lockstep, with the roles of its tactics taken by the inverse map: [zwin_tac] proves [uwin], the
    called functions are simulated by the [un_*] lemmas below ([un_callN]). *)
#[local] Ltac zwin_tac ::= uwin_tac.

Ltac un_call1 := fail.
Ltac un_call2 := fail.
Ltac un_call3 := fail.
Ltac un_call4 := fail.
Ltac un_call5 := fail.
Ltac un_call6 := fail.
Ltac un_call7 := fail.
Ltac un_call8 := fail.
Ltac un_call9 := fail.
Ltac un_call10 := fail.
Ltac un_call11 := fail.
Ltac un_call12 := fail.
Ltac un_call13 := fail.
Ltac un_call14 := fail.
Ltac un_call15 := fail.
Ltac un_call16 := fail.
(** [un_call]: the lemma of a called function, filled in below as the lemmas are proved; InSlice's [sl_call] is
    redefined to it, locally, in each file of this simulation *)
Ltac un_call := first [un_call1 | un_call2 | un_call3 | un_call4 | un_call5 | un_call6 | un_call7 | un_call8 |
  un_call9 | un_call10 | un_call11 | un_call12 | un_call13 | un_call14 | un_call15 | un_call16].
#[local] Ltac sl_call ::= un_call.

(** Use the lemma [lem] of a called function: the small call [Ha] becomes the whole call in the goal. *)
Ltac use_un lem d l y Ha :=
  match goal with W0 : uwin d ?L l _ |- _ =>
    let Wy := fresh "Wy" in assert (Wy : uwin d L l y) by uwin_tac;
    let Hs := fresh "Hs" in let W' := fresh "W" in
    apply (lem d L l) in Ha; [|exact Wy]; destruct Ha as (Hs & W'); rewrite Hs; clear Hs Wy
  end.

Ltac un_tac f := intros H W; unfold f in *; crunch; lockstep.

(** ** The two reads of the input: a read inside the slice is the read of the whole object, [d] further *)
Lemma rds_unslice d L l lo n x :
  0 <= d -> 0 <= L -> d + L <= Zlength l -> rds (sublist d (d + L) l) lo n = Some x -> rds l (lo + d) n = Some x.
Proof.
  unfold rds. intros H0 HL H1 E.
  destruct ((0 <=? lo) && (0 <=? n) && (lo + n <=? Zlength (sublist d (d + L) l))) eqn:C; [|discriminate].
  inversion E; subst. rewrite !andb_true_iff, !Z.leb_le in C. rewrite Zlength_sublist in C by lia.
  replace ((0 <=? lo + d) && (0 <=? n) && (lo + d + n <=? Zlength l)) with true
    by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
  rewrite sublist_sublist by lia. f_equal. f_equal; lia.
Qed.

Lemma un_read_buf d L l s y n y1 data : c_read_buf s y n = Some (y1, data) -> uwin d L l y ->
  c_read_buf s (zun d l y) n = Some (zun d l y1, data) /\ uwin d L l y1.
Proof.
  intros H W. unfold c_read_buf in *. rewrite zu_avail_in.
  set (len := if z_avail_in y >? n then n else z_avail_in y) in *.
  destruct (len =? 0) eqn:E0.
  { inversion H; subst. split; [reflexivity | exact W]. }
  apply bind_some in H. destruct H as [x [Ha H]].
  rewrite zu_set_avail_in. cbn [z_in z_next_in zun set_z_avail_in] in Ha |- *.
  destruct W as (W1 & W0 & W2 & W3). rewrite W3 in Ha.
  rewrite (rds_unslice d L l _ _ _ W1 W0 W2 Ha). cbn [bind].
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; inversion H; subst;
    (split; [unfold zun, set_z_total_in, set_z_next_in, set_z_adler, set_z_avail_in; cbn; do 3 f_equal; lia
            | unfold uwin; cbn; repeat split; auto]).
Qed.

Lemma un_out_put d L l y b y1 : out_put y b = Some y1 -> uwin d L l y ->
  out_put (zun d l y) b = Some (zun d l y1) /\ uwin d L l y1.
Proof. un_tac out_put. Qed.

Ltac un_call1 ::=
  match goal with
  | Ha : c_read_buf ?s ?y ?n = Some _ |- context [c_read_buf ?s (zun ?d ?l ?y) ?n] => use_un un_read_buf d l y Ha
  | Ha : out_put ?y ?b = Some _ |- context [out_put (zun ?d ?l ?y) ?b] => use_un un_out_put d l y Ha
  end.

Lemma un_flush_pending d L l s y s1 y1 : c_flush_pending s y = Some (s1, y1) -> uwin d L l y ->
  c_flush_pending s (zun d l y) = Some (s1, zun d l y1) /\ uwin d L l y1.
Proof. un_tac c_flush_pending. Qed.

Lemma un_fw_body d L l s y x : fw_body (s, y) = Some x -> uwin d L l y ->
  match x with
  | inl (s1, y1) => fw_body (s, zun d l y) = Some (inl (s1, zun d l y1)) /\ uwin d L l y1
  | inr (s1, y1) => fw_body (s, zun d l y) = Some (inr (s1, zun d l y1)) /\ uwin d L l y1
  end.
Proof. un_tac fw_body. Qed.

Lemma un_fw_loop d L l s y s1 y1 : loop FUEL fw_body (s, y) = Some (s1, y1) -> uwin d L l y ->
  loop FUEL fw_body (s, zun d l y) = Some (s1, zun d l y1) /\ uwin d L l y1.
Proof.
  intros H W.
  destruct (loop_sim fw_body (fun a => (fst a, zun d l (snd a))) (fun a => (fst a, zun d l (snd a)))
              (fun a => uwin d L l (snd a)) (fun a => uwin d L l (snd a))) with (3 := H) as [E Q];
    [| exact W | split; [exact E | exact Q]].
  intros [s0 y0] x W0 E. cbn [fst snd] in W0 |- *. apply (un_fw_body d L l) in E; [|exact W0].
  destruct x as [[s2 y2]|[s2 y2]]; exact E.
Qed.

Ltac un_call2 ::=
  match goal with
  | Ha : c_flush_pending ?s ?y = Some _ |- context [c_flush_pending ?s (zun ?d ?l ?y)] =>
      use_un un_flush_pending d l y Ha
  | Ha : loop _ fw_body (?s, ?y) = Some _ |- context [loop _ fw_body (?s, zun ?d ?l ?y)] =>
      use_un un_fw_loop d l y Ha
  end.

Lemma un_fill_window d L l s y s1 y1 : c_fill_window s y = Some (s1, y1) -> uwin d L l y ->
  c_fill_window s (zun d l y) = Some (s1, zun d l y1) /\ uwin d L l y1.
Proof. un_tac c_fill_window. Qed.

Lemma un_flush_block_only d L l s y b s1 y1 : c_flush_block_only s y b = Some (s1, y1) -> uwin d L l y ->
  c_flush_block_only s (zun d l y) b = Some (s1, zun d l y1) /\ uwin d L l y1.
Proof. un_tac c_flush_block_only. Qed.

Ltac un_call3 ::=
  match goal with
  | Ha : c_fill_window ?s ?y = Some _ |- context [c_fill_window ?s (zun ?d ?l ?y)] =>
      use_un un_fill_window d l y Ha
  | Ha : c_flush_block_only ?s ?y ?b = Some _ |- context [c_flush_block_only ?s (zun ?d ?l ?y) ?b] =>
      use_un un_flush_block_only d l y Ha
  end.

Lemma un_flush_block d L l s y b s1 y1 r : c_flush_block s y b = Some (s1, y1, r) -> uwin d L l y ->
  c_flush_block s (zun d l y) b = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_flush_block. Qed.

Ltac un_call4 ::=
  match goal with
  | Ha : c_flush_block ?s ?y ?b = Some _ |- context [c_flush_block ?s (zun ?d ?l ?y) ?b] =>
      use_un un_flush_block d l y Ha
  end.

(** The step functions of the main loops: results [(dstate * strm) + (dstate * strm * _)]. *)
Notation step_un d L l fs x :=
  (match x with
   | inl (s1, y1) => fs = Some (inl (s1, zun d l y1)) /\ uwin d L l y1
   | inr (s1, y1, r) => fs = Some (inr (s1, zun d l y1, r)) /\ uwin d L l y1
   end) (only parsing).

Lemma un_bflush d L l s y b x : c_bflush s y b = Some x -> uwin d L l y -> step_un d L l (c_bflush s (zun d l y) b) x.
Proof. un_tac c_bflush. Qed.

Lemma un_refill d L l need flush s y x : c_refill need flush s y = Some x -> uwin d L l y ->
  step_un d L l (c_refill need flush s (zun d l y)) x.
Proof. un_tac c_refill. Qed.

Lemma un_deflate_tail d L l s y f s1 y1 r : c_deflate_tail s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_tail s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac c_deflate_tail. Qed.

(** A main loop whose iterations are simulated by [body_lemma] (in the form [step_un]). *)
Ltac loop_un body_lemma :=
  intros H W;
  match type of H with loop _ ?body (_, _) = _ => match goal with |- context [zun ?d ?l _] =>
  match type of W with uwin _ ?L _ _ =>
  let E := fresh "E" in let Q := fresh "Q" in
  destruct (loop_sim body (fun a => (fst a, zun d l (snd a))) (fun e => (fst (fst e), zun d l (snd (fst e)), snd e))
              (fun a => uwin d L l (snd a)) (fun e => uwin d L l (snd (fst e)))) with (3 := H) as [E Q];
  [ let s0 := fresh "s" in let y0 := fresh "y" in let x := fresh "x" in let W0 := fresh "W" in
    let E0 := fresh "E" in
    intros [s0 y0] x W0 E0; cbn [fst snd] in W0 |- *; apply (body_lemma d L l) in E0; [|exact W0];
    let s2 := fresh "s" in let y2 := fresh "y" in let o2 := fresh "o" in
    destruct x as [[s2 y2]|[[s2 y2] o2]]; exact E0
  | exact W
  | split; [exact E | exact Q] ]
  end end end.

(** deflate_stored's window update: a read of the small object is the read of the whole object at [d] further. *)
Lemma un_ds_window d L l s y used s1 : c_ds_window s y used = Some s1 -> uwin d L l y ->
  c_ds_window s (zun d l y) used = Some s1.
Proof.
  intros H W. unfold c_ds_window in *. destruct (used =? 0); [exact H|].
  destruct W as (W1 & W0 & W2 & W3). cbn [zun z_in z_next_in]. rewrite W3 in H.
  apply bind_some in H. destruct H as [s2 [Ha H]].
  match goal with |- bind ?e _ = _ => assert (Hs : e = Some s2); [| rewrite Hs; exact H] end. clear H.
  destruct (used >=? d_w_size s) eqn:E1.
  - apply bind_some in Ha. destruct Ha as [b [Hb Ha]].
    replace (z_next_in y + d - d_w_size (set_d_matches s 2)) with (z_next_in y - d_w_size (set_d_matches s 2) + d)
      by lia.
    rewrite (rds_unslice d L l _ _ _ W1 W0 W2 Hb). exact Ha.
  - apply bind_some in Ha. destruct Ha as [s3 [Hs3 Ha]]. rewrite Hs3. cbn [bind].
    apply bind_some in Ha. destruct Ha as [b [Hb Ha]].
    replace (z_next_in y + d - used) with (z_next_in y - used + d) by lia.
    rewrite (rds_unslice d L l _ _ _ W1 W0 W2 Hb). exact Ha.
Qed.

Ltac un_call5 ::=
  match goal with
  | Ha : c_bflush ?s ?y ?b = Some _ |- context [c_bflush ?s (zun ?d ?l ?y) ?b] => use_un un_bflush d l y Ha
  | Ha : c_refill ?n ?f ?s ?y = Some _ |- context [c_refill ?n ?f ?s (zun ?d ?l ?y)] => use_un un_refill d l y Ha
  | Ha : c_deflate_tail ?s ?y ?f = Some _ |- context [c_deflate_tail ?s (zun ?d ?l ?y) ?f] =>
      use_un un_deflate_tail d l y Ha
  | Ha : c_ds_window ?s ?y ?u = Some _ |- context [c_ds_window ?s (zun ?d ?l ?y) ?u] =>
      match goal with W0 : uwin d ?L l _ |- _ =>
        rewrite (un_ds_window d L l _ _ _ _ Ha ltac:(uwin_tac)); clear Ha end
  end.

(** ** deflate_stored's first phase: the loop of [ds_body] *)
Lemma un_ds_body d L l flush mb s y x : ds_body flush mb (s, y) = Some x -> uwin d L l y ->
  step_un d L l (ds_body flush mb (s, zun d l y)) x.
Proof. un_tac ds_body. Qed.

Lemma un_ds_loop d L l flush mb s y s1 y1 r : loop FUEL (ds_body flush mb) (s, y) = Some (s1, y1, r) ->
  uwin d L l y -> loop FUEL (ds_body flush mb) (s, zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. loop_un un_ds_body. Qed.

Ltac un_call6 ::=
  match goal with
  | Ha : loop _ (ds_body ?f ?m) (?s, ?y) = Some _ |- context [loop _ (ds_body ?f ?m) (?s, zun ?d ?l ?y)] =>
      use_un un_ds_loop d l y Ha
  end.

(** ** deflate_stored

    Its body after the first phase has many paths; run whole, the lockstep is slow.  It is cut into three phases,
    each a definition below whose text is the corresponding part of [c_deflate_stored] (DModel2): [ds_emit] (the
    stored block from the window), [ds_read] (the copy of the remaining input into the window, then [ds_emit]) and
    the head of the function, which calls [ds_read]; [c_deflate_stored_split] checks by conversion that the three
    put together are [c_deflate_stored]. *)

(** the stored block from the window into pending *)
Definition ds_emit (flush : Z) (s : dstate) (z : strm) : option (dstate * strm * bstate) :=
  let have := stored_hdr s in
  let have := u32 (let a := u64 (d_pending_buf_size s - have) in if a >? MAX_STORED then MAX_STORED else a) in
  let min_block := if have >? d_w_size s then d_w_size s else have in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let* (s, z, last) :=
    (if (left >=? min_block) ||
        ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
         (z_avail_in z =? 0) && (left <=? have)) then
       let len := if left >? have then have else left in
       let last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0 in
       let* buf := (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) in
       let* o := c_tr_stored_block (d_out s) buf len last in
       let s := set_d_out s o in
       let* _ := guard (in_long (d_block_start s + len)) in
       let s := set_d_block_start s (d_block_start s + len) in
       let* (s, z) := c_flush_pending s z in
       Some (s, z, last)
     else Some (s, z, 0)) in
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started).

(** the copy of the remaining input ([have] bytes) into the window, then [ds_emit] *)
Definition ds_read (flush : Z) (s : dstate) (z : strm) (have : Z) : option (dstate * strm * bstate) :=
  let* (s, z) :=
    (if have =? 0 then Some (s, z) else
     let* (z, data) := c_read_buf s z have in
     let* win := mb_write (d_window s) (d_strstart s) data in
     let s := set_d_window s win in
     let s := set_d_strstart s (u32 (d_strstart s + have)) in
     Some (add_insert s have, z)) in
  let s := upd_high_water s in
  ds_emit flush s z.

Lemma c_deflate_stored_split s z flush : c_deflate_stored s z flush =
  let min_block := u32 (let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a) in
  let used := z_avail_in z in
  let* (s, z, last) := loop FUEL (ds_body flush min_block) (s, z) in
  let used := u32 (used - z_avail_in z) in
  let* s := c_ds_window s z used in
  let s := upd_high_water s in
  if negb (last =? 0) then Some (set_d_bi_used s 8, z, finish_done) else
  if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z =? 0) &&
     (d_strstart s =? d_block_start s)
  then Some (s, z, block_done) else
  (* fill the window with any remaining input *)
  let have := u32 (u64 (d_window_size s - d_strstart s)) in
  let* (s, have) :=
    (if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
       let s := set_d_block_start s (d_block_start s - d_w_size s) in
       let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
       let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
       let s := set_d_window s win in
       let s := incr_matches s in
       let have := u32 (have + d_w_size s) in
       Some (clamp_insert s, have)
     else Some (s, have)) in
  let have := if have >? z_avail_in z then z_avail_in z else have in
  ds_read flush s z have.
Proof. reflexivity. Qed.

Lemma un_ds_emit d L l flush s y s1 y1 r : ds_emit flush s y = Some (s1, y1, r) -> uwin d L l y ->
  ds_emit flush s (zun d l y) = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac ds_emit. Qed.

Ltac un_call7 ::=
  match goal with
  | Ha : ds_emit ?f ?s ?y = Some _ |- context [ds_emit ?f ?s (zun ?d ?l ?y)] => use_un un_ds_emit d l y Ha
  end.

Lemma un_ds_read d L l flush s y have s1 y1 r : ds_read flush s y have = Some (s1, y1, r) -> uwin d L l y ->
  ds_read flush s (zun d l y) have = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. un_tac ds_read. Qed.

Ltac un_call8 ::=
  match goal with
  | Ha : ds_read ?f ?s ?y ?h = Some _ |- context [ds_read ?f ?s (zun ?d ?l ?y) ?h] => use_un un_ds_read d l y Ha
  end.

Lemma un_deflate_stored d L l s y f s1 y1 r : c_deflate_stored s y f = Some (s1, y1, r) -> uwin d L l y ->
  c_deflate_stored s (zun d l y) f = Some (s1, zun d l y1, r) /\ uwin d L l y1.
Proof. rewrite !c_deflate_stored_split. intros H W; cbv beta iota zeta in H; crunch; lockstep. Qed.

(** * deflate()'s model reads its input only inside the bytes offered by the call

    The model [c_deflate s z flush] (DModel4) sees the input object [z_in z] with next_in at offset
    [z_next_in z].  It reads that object only through [rds] at read_buf (bytes [next_in, next_in + len) with
    len <= avail_in) and at deflate_stored's window update (the [used] bytes consumed by the call, just before
    next_in): always inside [next_in, next_in + avail_in) of the call's start.  So the call gives the same result
    on the object cut down to these bytes, next_in moved by the cut ([zslice]).

    compress2_z (RTCBodiesW.v) needs it: its model runs deflate on the whole source (up to 2^64-1 bytes), while
    DSpec.deflate_spec takes an input object of at most 2^32-1 bytes (strm_ranges); the caller presents the
    slice [d, d + L) = [next_in, next_in + avail_in) of the source as that object. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel5.
Import ListNotations.
Local Open Scope Z_scope.

(** the stream [z] with its input object cut down to the bytes [d, d + L) of [z_in z] *)
Definition zslice (d L : Z) (z : strm) : strm :=
  mkST (sublist d (d + L) (z_in z)) (z_next_in z - d) (z_avail_in z) (z_total_in z) (z_out z) (z_avail_out z)
    (z_total_out z) (z_adler z) (z_msg z).

(** ** The simulation: every model function run on [zslice d L z] does what it does on [z]

    [zwin d L z]: the bytes offered [next_in, next_in + avail_in) lie in [d, d + L) of the input object and end at
    [d + L].  Each lemma [sl_f] below says: when [f] succeeds on a stream [z] with [zwin d L z], it succeeds on
    [zslice d L z] with the sliced result, keeps [zwin] and does not increase avail_in.  The proofs run the big
    call (the hypothesis, destructed with [crunch]) and the small call (the goal) in lockstep ([lockstep]). *)

Definition zwin (d L : Z) (z : strm) : Prop :=
  0 <= d <= z_next_in z /\ 0 <= z_avail_in z /\ z_next_in z + z_avail_in z = d + L /\ d + L <= Zlength (z_in z).

Lemma bind_some {A B} (a : option A) (f : A -> option B) r :
  bind a f = Some r -> exists x, a = Some x /\ f x = Some r.
Proof. destruct a; cbn; [eauto | discriminate]. Qed.

(** zslice commutes with the fields it does not change *)
Section ZS.
Variables (d L : Z) (z : strm).
Lemma zs_avail_in : z_avail_in (zslice d L z) = z_avail_in z. Proof. reflexivity. Qed.
Lemma zs_total_in : z_total_in (zslice d L z) = z_total_in z. Proof. reflexivity. Qed.
Lemma zs_out : z_out (zslice d L z) = z_out z. Proof. reflexivity. Qed.
Lemma zs_avail_out : z_avail_out (zslice d L z) = z_avail_out z. Proof. reflexivity. Qed.
Lemma zs_total_out : z_total_out (zslice d L z) = z_total_out z. Proof. reflexivity. Qed.
Lemma zs_adler : z_adler (zslice d L z) = z_adler z. Proof. reflexivity. Qed.
Lemma zs_msg : z_msg (zslice d L z) = z_msg z. Proof. reflexivity. Qed.
Lemma zs_set_avail_in x : set_z_avail_in (zslice d L z) x = zslice d L (set_z_avail_in z x).
Proof. reflexivity. Qed.
Lemma zs_set_total_in x : set_z_total_in (zslice d L z) x = zslice d L (set_z_total_in z x).
Proof. reflexivity. Qed.
Lemma zs_set_out x : set_z_out (zslice d L z) x = zslice d L (set_z_out z x).
Proof. reflexivity. Qed.
Lemma zs_set_avail_out x : set_z_avail_out (zslice d L z) x = zslice d L (set_z_avail_out z x).
Proof. reflexivity. Qed.
Lemma zs_set_total_out x : set_z_total_out (zslice d L z) x = zslice d L (set_z_total_out z x).
Proof. reflexivity. Qed.
Lemma zs_set_adler x : set_z_adler (zslice d L z) x = zslice d L (set_z_adler z x).
Proof. reflexivity. Qed.
Lemma zs_set_msg x : set_z_msg (zslice d L z) x = zslice d L (set_z_msg z x).
Proof. reflexivity. Qed.
End ZS.

#[local] Hint Rewrite zs_avail_in zs_total_in zs_out zs_avail_out zs_total_out zs_adler zs_msg zs_set_avail_in
  zs_set_total_in zs_set_out zs_set_avail_out zs_set_total_out zs_set_adler zs_set_msg : zsl.

Ltac znorm := cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg
  set_z_in set_z_next_in set_z_avail_in set_z_total_in set_z_out set_z_avail_out set_z_total_out set_z_adler
  set_z_msg fst snd] in *.

Ltac zwin_tac := unfold zwin in *; znorm; lia.

(** The big call: destruct the hypothesis along the path it took, keeping every test and every intermediate
    result as an equation. *)
(** Injections that do not reduce their arguments (inversion would, and the two calls would no longer be
    written alike). *)
Lemma some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.
Lemma pair_inj {A B} (a c : A) (b e : B) : (a, b) = (c, e) -> a = c /\ b = e.
Proof. intros H; inversion H; auto. Qed.
Lemma inl_inj {A B} (a b : A) : @inl A B a = inl b -> a = b.
Proof. congruence. Qed.
Lemma inr_inj {A B} (a b : B) : @inr A B a = inr b -> a = b.
Proof. congruence. Qed.

(** [t] is replaced by its value in [H] only: the equations kept so far stay as they are. *)
Ltac case_in H t :=
  first [ is_var t; destruct t
        | let v := fresh "v" in let E := fresh "E" in remember t as v eqn:E in H; destruct v; symmetry in E ].

Ltac crunch_step :=
  match goal with
  | H : Some _ = Some _ |- _ => apply some_inj in H
  | H : None = Some _ |- _ => discriminate H
  | H : (_, _) = (_, _) |- _ => apply pair_inj in H; destruct H
  | H : inl _ = inl _ |- _ => apply inl_inj in H
  | H : inr _ = inr _ |- _ => apply inr_inj in H
  | H : ?a = ?b |- _ => is_var b; subst b
  | H : ?a = ?b |- _ => is_var a; subst a
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : (if ?b then _ else _) = Some _ |- _ => case_in H b
  | H : match ?x with None => _ | Some _ => _ end = Some _ |- _ => case_in H x
  | H : match ?x with inl _ => _ | inr _ => _ end = Some _ |- _ => case_in H x
  | H : match ?x with (_, _) => _ end = Some _ |- _ => destruct x
  | H : match ?x with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end = Some _ |- _ =>
      case_in H x
  | H : then_stage _ _ = Some _ |- _ => unfold then_stage in H
  | H : bind _ _ = Some _ |- _ =>
      let x := fresh "x" in let Ha := fresh "Ha" in apply bind_some in H; destruct H as [x [Ha H]]
  | H : _ = _ |- _ => discriminate H
  end.

Ltac crunch := repeat (crunch_step; cbv beta iota zeta in * |-; cbn [andb orb negb] in * |-).

(** The small call: one step of the goal.  [sl_call] uses the lemma of a called function; its parts [sl_callN] are
    filled in below as the lemmas are proved. *)
Ltac sl_call1 := fail.
Ltac sl_call2 := fail.
Ltac sl_call3 := fail.
Ltac sl_call4 := fail.
Ltac sl_call5 := fail.
Ltac sl_call6 := fail.
Ltac sl_call7 := fail.
Ltac sl_call8 := fail.
Ltac sl_call9 := fail.
Ltac sl_call10 := fail.
Ltac sl_call11 := fail.
Ltac sl_call12 := fail.
Ltac sl_call13 := fail.
Ltac sl_call := first [sl_call1 | sl_call2 | sl_call3 | sl_call4 | sl_call5 | sl_call6 | sl_call7 | sl_call8 |
  sl_call9 | sl_call10 | sl_call11 | sl_call12 | sl_call13].

Ltac gnorm := cbn [bind negb andb orb]; cbv beta iota zeta; autorewrite with zsl.

(** The value of a test [t] of the small call: the big call's equation for it, or a case split on a variable. *)
Ltac hcase t :=
  first [ match goal with E : t = _ |- _ => rewrite E end | is_var t; destruct t ];
  cbn [bind negb andb orb]; cbv beta iota.

(** One step of the small call [e], at its head. *)
Ltac hred e :=
  lazymatch e with
  | bind ?e2 _ =>
      lazymatch e2 with
      | Some _ => cbn [bind]; cbv beta iota zeta
      | _ => hred e2
      end
  | (if ?b then _ else _) => hcase b
  | match ?x with (_, _) => _ end => destruct x
  | match ?x with inl _ => _ | inr _ => _ end => hcase x
  | match ?x with Some _ => _ | None => _ end => hcase x
  | match ?x with need_more => _ | block_done => _ | finish_started => _ | finish_done => _ end => hcase x
  | _ => first [ sl_call; gnorm | match goal with E : e = _ |- _ => rewrite E end ]
  end.

Ltac lstep :=
  lazymatch goal with
  | |- Some _ = _ /\ _ => fail
  | |- ?lhs = _ /\ _ => first [hred lhs | progress gnorm]
  | |- match ?x with inl _ => _ | inr _ => _ end => destruct x; cbv beta iota
  | |- match ?x with (_, _) => _ end => destruct x; cbv beta iota
  end.

Ltac lfinish := repeat split; first [reflexivity | zwin_tac].

Ltac lockstep := try unfold then_stage; gnorm; repeat lstep; gnorm; lfinish.

Ltac sl_tac f := intros H W; unfold f in *; crunch; lockstep.

(** Use the lemma [lem] of a called function: the big call [Ha] becomes the small call in the goal. *)
Ltac use_sl lem d L z Ha :=
  let Wz := fresh "Wz" in assert (Wz : zwin d L z) by zwin_tac;
  let Hs := fresh "Hs" in let W' := fresh "W" in let A := fresh "A" in
  apply (lem d L) in Ha; try exact Wz; destruct Ha as (Hs & W' & A); rewrite Hs; clear Hs Wz.

(** ** Loops

    A loop whose iterations are simulated one by one ([fa] maps the big state to the small one, [fb] the exit
    values; [P], [Q] the invariant along the big run) is simulated as a whole, for any fuel. *)
Lemma loop2_sim {A B} (body : A -> option (A + B)) (fa : A -> A) (fb : B -> B) (P : A -> Prop) (Q : B -> Prop) :
  (forall a x, P a -> body a = Some x ->
     match x with
     | inl a' => body (fa a) = Some (inl (fa a')) /\ P a'
     | inr b => body (fa a) = Some (inr (fb b)) /\ Q b
     end) ->
  forall n a x, P a -> loop2 n body a = Some x ->
     match x with
     | inl a' => loop2 n body (fa a) = Some (inl (fa a')) /\ P a'
     | inr b => loop2 n body (fa a) = Some (inr (fb b)) /\ Q b
     end.
Proof.
  intros Hb n. induction n as [|n IH]; intros a x Pa E; cbn [loop2] in *.
  - exact (Hb a x Pa E).
  - destruct (loop2 n body a) as [[a1|b1]|] eqn:E1; [| | discriminate].
    + destruct (IH a (inl a1) Pa E1) as [E1' P1]. rewrite E1'. exact (IH a1 x P1 E).
    + inversion E; subst. destruct (IH a (inr b1) Pa E1) as [E1' Q1]. rewrite E1'. auto.
Qed.

Lemma loop_sim {A B} (body : A -> option (A + B)) (fa : A -> A) (fb : B -> B) (P : A -> Prop) (Q : B -> Prop) :
  (forall a x, P a -> body a = Some x ->
     match x with
     | inl a' => body (fa a) = Some (inl (fa a')) /\ P a'
     | inr b => body (fa a) = Some (inr (fb b)) /\ Q b
     end) ->
  forall n a r, P a -> loop n body a = Some r -> loop n body (fa a) = Some (fb r) /\ Q r.
Proof.
  intros Hb n a r Pa E. unfold loop in *.
  destruct (loop2 n body a) as [[a1|b1]|] eqn:E1; try discriminate. inversion E; subst.
  destruct (loop2_sim body fa fb P Q Hb n a (inr r) Pa E1) as [-> Qr]. auto.
Qed.

(** The kernel must not compute [loop FUEL] (2^40 iterations) when it checks an unfolding of a model function. *)
Local Strategy opaque [loop loop2].

(** ** The two reads of the input *)
Lemma rds_slice d L l lo n x :
  0 <= d -> d + L <= Zlength l -> d <= lo -> lo + n <= d + L -> rds l lo n = Some x ->
  rds (sublist d (d + L) l) (lo - d) n = Some x.
Proof.
  unfold rds. intros H0 H1 H2 H3 E.
  destruct ((0 <=? lo) && (0 <=? n) && (lo + n <=? Zlength l)) eqn:C; [|discriminate]. inversion E; subst.
  rewrite !andb_true_iff, !Z.leb_le in C.
  rewrite Zlength_sublist by lia.
  replace ((0 <=? lo - d) && (0 <=? n) && (lo - d + n <=? d + L - d)) with true
    by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
  rewrite sublist_sublist by lia. f_equal. f_equal; lia.
Qed.

Lemma sl_read_buf d L s z n z1 data : c_read_buf s z n = Some (z1, data) -> zwin d L z ->
  c_read_buf s (zslice d L z) n = Some (zslice d L z1, data) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof.
  intros H W. unfold c_read_buf in *. rewrite zs_avail_in.
  set (len := if z_avail_in z >? n then n else z_avail_in z) in *.
  assert (Hl : len <= z_avail_in z) by (subst len; destruct (Z.gtb_spec (z_avail_in z) n); lia).
  destruct (len =? 0) eqn:E0.
  { inversion H; subst. split; [reflexivity | split; [exact W | lia]]. }
  apply bind_some in H. destruct H as [x [Ha H]].
  rewrite zs_set_avail_in. cbn [z_in z_next_in zslice set_z_avail_in] in Ha |- *.
  assert (Hr : 0 <= len /\ z_next_in z + len <= Zlength (z_in z)).
  { unfold rds in Ha. destruct ((0 <=? z_next_in z) && (0 <=? len) && (z_next_in z + len <=? Zlength (z_in z)))
      eqn:C; [|discriminate]. rewrite !andb_true_iff, !Z.leb_le in C. lia. }
  unfold zwin in W.
  erewrite rds_slice by (try exact Ha; lia). cbn [bind].
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; inversion H; subst;
    (split; [unfold zslice, set_z_total_in, set_z_next_in, set_z_adler, set_z_avail_in; cbn; do 3 f_equal; lia
            | unfold zwin; cbn; lia]).
Qed.

Lemma sl_out_put d L z b z1 : out_put z b = Some z1 -> zwin d L z ->
  out_put (zslice d L z) b = Some (zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac out_put. Qed.

Ltac sl_call1 ::=
  match goal with
  | Ha : c_read_buf ?s ?z ?n = Some _ |- context [c_read_buf ?s (zslice ?d ?L ?z) ?n] => use_sl sl_read_buf d L z Ha
  | Ha : out_put ?z ?b = Some _ |- context [out_put (zslice ?d ?L ?z) ?b] => use_sl sl_out_put d L z Ha
  end.

Lemma sl_flush_pending d L s z s1 z1 : c_flush_pending s z = Some (s1, z1) -> zwin d L z ->
  c_flush_pending s (zslice d L z) = Some (s1, zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_flush_pending. Qed.

Lemma sl_fw_body d L s z x : fw_body (s, z) = Some x -> zwin d L z ->
  match x with
  | inl (s1, z1) => fw_body (s, zslice d L z) = Some (inl (s1, zslice d L z1)) /\ zwin d L z1 /\
                    z_avail_in z1 <= z_avail_in z
  | inr (s1, z1) => fw_body (s, zslice d L z) = Some (inr (s1, zslice d L z1)) /\ zwin d L z1 /\
                    z_avail_in z1 <= z_avail_in z
  end.
Proof. sl_tac fw_body. Qed.

Lemma sl_fw_loop d L s z s1 z1 : loop FUEL fw_body (s, z) = Some (s1, z1) -> zwin d L z ->
  loop FUEL fw_body (s, zslice d L z) = Some (s1, zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof.
  intros H W.
  destruct (loop_sim fw_body (fun a => (fst a, zslice d L (snd a))) (fun a => (fst a, zslice d L (snd a)))
              (fun a => zwin d L (snd a) /\ z_avail_in (snd a) <= z_avail_in z)
              (fun a => zwin d L (snd a) /\ z_avail_in (snd a) <= z_avail_in z)) with (3 := H) as [E Q];
    [| cbn; split; [exact W | lia] | split; [exact E | exact Q]].
  intros [s0 z0] x [W0 A0] E. cbn [fst snd] in W0, A0 |- *. apply (sl_fw_body d L) in E; [|exact W0].
  destruct x as [[s2 z2]|[s2 z2]]; destruct E as (E & W1 & A1); (split; [exact E | cbn; split; [exact W1 | lia]]).
Qed.

Ltac sl_call2 ::=
  match goal with
  | Ha : c_flush_pending ?s ?z = Some _ |- context [c_flush_pending ?s (zslice ?d ?L ?z)] =>
      use_sl sl_flush_pending d L z Ha
  | Ha : loop _ fw_body (?s, ?z) = Some _ |- context [loop _ fw_body (?s, zslice ?d ?L ?z)] =>
      use_sl sl_fw_loop d L z Ha
  end.

Lemma sl_fill_window d L s z s1 z1 : c_fill_window s z = Some (s1, z1) -> zwin d L z ->
  c_fill_window s (zslice d L z) = Some (s1, zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_fill_window. Qed.

Lemma sl_flush_block_only d L s z l s1 z1 : c_flush_block_only s z l = Some (s1, z1) -> zwin d L z ->
  c_flush_block_only s (zslice d L z) l = Some (s1, zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_flush_block_only. Qed.

Ltac sl_call3 ::=
  match goal with
  | Ha : c_fill_window ?s ?z = Some _ |- context [c_fill_window ?s (zslice ?d ?L ?z)] =>
      use_sl sl_fill_window d L z Ha
  | Ha : c_flush_block_only ?s ?z ?l = Some _ |- context [c_flush_block_only ?s (zslice ?d ?L ?z) ?l] =>
      use_sl sl_flush_block_only d L z Ha
  end.

Lemma sl_flush_block d L s z l s1 z1 r : c_flush_block s z l = Some (s1, z1, r) -> zwin d L z ->
  c_flush_block s (zslice d L z) l = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_flush_block. Qed.

Ltac sl_call4 ::=
  match goal with
  | Ha : c_flush_block ?s ?z ?l = Some _ |- context [c_flush_block ?s (zslice ?d ?L ?z) ?l] =>
      use_sl sl_flush_block d L z Ha
  end.

(** The step functions of the main loops: results [(dstate * strm) + (dstate * strm * _)]. *)
Notation step_sl d L z fs x :=
  (match x with
   | inl (s1, z1) => fs = Some (inl (s1, zslice d L z1)) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
   | inr (s1, z1, r) => fs = Some (inr (s1, zslice d L z1, r)) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
   end) (only parsing).

Lemma sl_bflush d L s z b x : c_bflush s z b = Some x -> zwin d L z ->
  step_sl d L z (c_bflush s (zslice d L z) b) x.
Proof. sl_tac c_bflush. Qed.

Lemma sl_refill d L need flush s z x : c_refill need flush s z = Some x -> zwin d L z ->
  step_sl d L z (c_refill need flush s (zslice d L z)) x.
Proof. sl_tac c_refill. Qed.

Lemma sl_deflate_tail d L s z f s1 z1 r : c_deflate_tail s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_tail s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_tail. Qed.

(** A main loop whose iterations are simulated by [body_lemma] (in the form [step_sl]). *)
Ltac loop_sl body_lemma :=
  intros H W;
  match type of H with loop _ ?body (_, ?z) = _ => match goal with |- context [zslice ?d ?L _] =>
  let E := fresh "E" in let Q := fresh "Q" in
  destruct (loop_sim body (fun a => (fst a, zslice d L (snd a))) (fun e => (fst (fst e), zslice d L (snd (fst e)), snd e))
              (fun a => zwin d L (snd a) /\ z_avail_in (snd a) <= z_avail_in z)
              (fun e => zwin d L (snd (fst e)) /\ z_avail_in (snd (fst e)) <= z_avail_in z)) with (3 := H) as [E Q];
  [ let s0 := fresh "s" in let z0 := fresh "z" in let x := fresh "x" in let W0 := fresh "W" in
    let A0 := fresh "A" in let E0 := fresh "E" in
    intros [s0 z0] x [W0 A0] E0; cbn [fst snd] in W0, A0 |- *; apply (body_lemma d L) in E0; [|exact W0];
    let s2 := fresh "s" in let z2 := fresh "z" in let o2 := fresh "o" in let W1 := fresh "W" in let A1 := fresh "A" in
    destruct x as [[s2 z2]|[[s2 z2] o2]]; destruct E0 as (E0 & W1 & A1);
    (split; [exact E0 | cbn [fst snd]; split; [exact W1 | lia]])
  | cbn [fst snd]; split; [exact W | lia]
  | split; [exact E | exact Q] ]
  end end.

(** deflate_stored's window update reads the [used] bytes before next_in: [used] (a u32 of the bytes the call
    consumed) is at most the distance from [d], since next_in started at or after [d]. *)
Lemma u32_le x : 0 <= x -> 0 <= u32 x <= x.
Proof. intros. unfold u32. pose proof (Z.mod_pos_bound x 4294967296). pose proof (Z.mod_le x 4294967296). lia. Qed.

Lemma sl_ds_window d L s z used s1 : c_ds_window s z used = Some s1 -> zwin d L z -> 0 <= used <= z_next_in z - d ->
  c_ds_window s (zslice d L z) used = Some s1.
Proof.
  intros H W U. unfold c_ds_window in *. destruct (used =? 0); [exact H|].
  unfold zwin in W. cbn [zslice z_in z_next_in].
  apply bind_some in H. destruct H as [s2 [Ha H]].
  match goal with |- bind ?e _ = _ => assert (Hs : e = Some s2); [| rewrite Hs; exact H] end. clear H.
  destruct (used >=? d_w_size s) eqn:E1.
  - apply bind_some in Ha. destruct Ha as [b [Hb Ha]].
    change (d_w_size (set_d_matches s 2)) with (d_w_size s) in *.
    assert (Hw : 0 <= d_w_size s) by (unfold rds in Hb; destruct (_ && _ && _) eqn:C; [|discriminate];
      rewrite !andb_true_iff, !Z.leb_le in C; lia).
    apply Z.geb_le in E1.
    replace (z_next_in z - d - d_w_size s) with (z_next_in z - d_w_size s - d) by lia.
    erewrite rds_slice by (try exact Hb; lia). exact Ha.
  - apply bind_some in Ha. destruct Ha as [s3 [Hs3 Ha]]. rewrite Hs3. cbn [bind].
    apply bind_some in Ha. destruct Ha as [b [Hb Ha]].
    replace (z_next_in z - d - used) with (z_next_in z - used - d) by lia.
    erewrite rds_slice by (try exact Hb; lia). exact Ha.
Qed.

Ltac sl_call5 ::=
  match goal with
  | Ha : c_bflush ?s ?z ?b = Some _ |- context [c_bflush ?s (zslice ?d ?L ?z) ?b] => use_sl sl_bflush d L z Ha
  | Ha : c_refill ?n ?f ?s ?z = Some _ |- context [c_refill ?n ?f ?s (zslice ?d ?L ?z)] => use_sl sl_refill d L z Ha
  | Ha : c_deflate_tail ?s ?z ?f = Some _ |- context [c_deflate_tail ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_tail d L z Ha
  | Ha : c_ds_window ?s ?z ?u = Some _ |- context [c_ds_window ?s (zslice ?d ?L ?z) ?u] =>
      let U := fresh "U" in
      assert (U : 0 <= u <= z_next_in z - d)
        by (match u with u32 ?a => pose proof (u32_le a ltac:(zwin_tac)) end; zwin_tac);
      rewrite (sl_ds_window d L _ _ _ _ Ha ltac:(zwin_tac) U); clear Ha U
  end.

(** ** deflate_stored *)
Lemma sl_ds_body d L flush mb s z x : ds_body flush mb (s, z) = Some x -> zwin d L z ->
  step_sl d L z (ds_body flush mb (s, zslice d L z)) x.
Proof. sl_tac ds_body. Qed.

Lemma sl_ds_loop d L flush mb s z s1 z1 r : loop FUEL (ds_body flush mb) (s, z) = Some (s1, z1, r) -> zwin d L z ->
  loop FUEL (ds_body flush mb) (s, zslice d L z) = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\
  z_avail_in z1 <= z_avail_in z.
Proof. loop_sl sl_ds_body. Qed.

Ltac sl_call6 ::=
  match goal with
  | Ha : loop _ (ds_body ?f ?m) (?s, ?z) = Some _ |- context [loop _ (ds_body ?f ?m) (?s, zslice ?d ?L ?z)] =>
      use_sl sl_ds_loop d L z Ha
  end.

Lemma sl_deflate_stored d L s z f s1 z1 r : c_deflate_stored s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_stored s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_stored. Qed.

(** ** deflate_fast, deflate_slow, deflate_rle, deflate_huff *)
Lemma sl_df_step d L s z x : df_step s z = Some x -> zwin d L z -> step_sl d L z (df_step s (zslice d L z)) x.
Proof. sl_tac df_step. Qed.

Lemma sl_dsl_step d L s z x : dsl_step s z = Some x -> zwin d L z -> step_sl d L z (dsl_step s (zslice d L z)) x.
Proof. sl_tac dsl_step. Qed.

Lemma sl_rle_step d L s z x : rle_step s z = Some x -> zwin d L z -> step_sl d L z (rle_step s (zslice d L z)) x.
Proof. sl_tac rle_step. Qed.

Ltac sl_call7 ::=
  match goal with
  | Ha : df_step ?s ?z = Some _ |- context [df_step ?s (zslice ?d ?L ?z)] => use_sl sl_df_step d L z Ha
  | Ha : dsl_step ?s ?z = Some _ |- context [dsl_step ?s (zslice ?d ?L ?z)] => use_sl sl_dsl_step d L z Ha
  | Ha : rle_step ?s ?z = Some _ |- context [rle_step ?s (zslice ?d ?L ?z)] => use_sl sl_rle_step d L z Ha
  end.

Lemma sl_df_body d L flush s z x : df_body flush (s, z) = Some x -> zwin d L z ->
  step_sl d L z (df_body flush (s, zslice d L z)) x.
Proof. sl_tac df_body. Qed.

Lemma sl_dsl_body d L flush s z x : dsl_body flush (s, z) = Some x -> zwin d L z ->
  step_sl d L z (dsl_body flush (s, zslice d L z)) x.
Proof. sl_tac dsl_body. Qed.

Lemma sl_rle_body d L flush s z x : rle_body flush (s, z) = Some x -> zwin d L z ->
  step_sl d L z (rle_body flush (s, zslice d L z)) x.
Proof. sl_tac rle_body. Qed.

Lemma sl_huff_body d L flush s z x : huff_body flush (s, z) = Some x -> zwin d L z ->
  step_sl d L z (huff_body flush (s, zslice d L z)) x.
Proof. sl_tac huff_body. Qed.

Lemma sl_df_loop d L flush s z s1 z1 r : loop FUEL (df_body flush) (s, z) = Some (s1, z1, r) -> zwin d L z ->
  loop FUEL (df_body flush) (s, zslice d L z) = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\
  z_avail_in z1 <= z_avail_in z.
Proof. loop_sl sl_df_body. Qed.

Lemma sl_dsl_loop d L flush s z s1 z1 r : loop FUEL (dsl_body flush) (s, z) = Some (s1, z1, r) -> zwin d L z ->
  loop FUEL (dsl_body flush) (s, zslice d L z) = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\
  z_avail_in z1 <= z_avail_in z.
Proof. loop_sl sl_dsl_body. Qed.

Lemma sl_rle_loop d L flush s z s1 z1 r : loop FUEL (rle_body flush) (s, z) = Some (s1, z1, r) -> zwin d L z ->
  loop FUEL (rle_body flush) (s, zslice d L z) = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\
  z_avail_in z1 <= z_avail_in z.
Proof. loop_sl sl_rle_body. Qed.

Lemma sl_huff_loop d L flush s z s1 z1 r : loop FUEL (huff_body flush) (s, z) = Some (s1, z1, r) -> zwin d L z ->
  loop FUEL (huff_body flush) (s, zslice d L z) = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\
  z_avail_in z1 <= z_avail_in z.
Proof. loop_sl sl_huff_body. Qed.

Ltac sl_call8 ::=
  match goal with
  | Ha : loop _ (df_body ?f) (?s, ?z) = Some _ |- context [loop _ (df_body ?f) (?s, zslice ?d ?L ?z)] =>
      use_sl sl_df_loop d L z Ha
  | Ha : loop _ (dsl_body ?f) (?s, ?z) = Some _ |- context [loop _ (dsl_body ?f) (?s, zslice ?d ?L ?z)] =>
      use_sl sl_dsl_loop d L z Ha
  | Ha : loop _ (rle_body ?f) (?s, ?z) = Some _ |- context [loop _ (rle_body ?f) (?s, zslice ?d ?L ?z)] =>
      use_sl sl_rle_loop d L z Ha
  | Ha : loop _ (huff_body ?f) (?s, ?z) = Some _ |- context [loop _ (huff_body ?f) (?s, zslice ?d ?L ?z)] =>
      use_sl sl_huff_loop d L z Ha
  end.

Lemma sl_deflate_fast d L s z f s1 z1 r : c_deflate_fast s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_fast s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_fast. Qed.

Lemma sl_deflate_slow d L s z f s1 z1 r : c_deflate_slow s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_slow s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_slow. Qed.

Lemma sl_deflate_rle d L s z f s1 z1 r : c_deflate_rle s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_rle s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_rle. Qed.

Lemma sl_deflate_huff d L s z f s1 z1 r : c_deflate_huff s z f = Some (s1, z1, r) -> zwin d L z ->
  c_deflate_huff s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate_huff. Qed.

Ltac sl_call9 ::=
  match goal with
  | Ha : c_deflate_stored ?s ?z ?f = Some _ |- context [c_deflate_stored ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_stored d L z Ha
  | Ha : c_deflate_fast ?s ?z ?f = Some _ |- context [c_deflate_fast ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_fast d L z Ha
  | Ha : c_deflate_slow ?s ?z ?f = Some _ |- context [c_deflate_slow ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_slow d L z Ha
  | Ha : c_deflate_rle ?s ?z ?f = Some _ |- context [c_deflate_rle ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_rle d L z Ha
  | Ha : c_deflate_huff ?s ?z ?f = Some _ |- context [c_deflate_huff ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_deflate_huff d L z Ha
  end.

Lemma sl_compress_func d L s z f s1 z1 r : c_compress_func s z f = Some (s1, z1, r) -> zwin d L z ->
  c_compress_func s (zslice d L z) f = Some (s1, zslice d L z1, r) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_compress_func. Qed.

(** ** The stages of deflate() *)

(** The results of the stages: [(dstate * strm * option Z)]. *)
Notation stage_sl d L z fs s1 z1 o :=
  (fs = Some (s1, zslice d L z1, o) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z) (only parsing).

Lemma sl_hcrc_update d L h s z beg z1 : c_hcrc_update h s z beg = Some z1 -> zwin d L z ->
  c_hcrc_update h s (zslice d L z) beg = Some (zslice d L z1) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_hcrc_update. Qed.

Lemma sl_flush_or_return d L s z s1 z1 o : c_flush_or_return s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_flush_or_return s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_flush_or_return. Qed.

Ltac sl_call10 ::=
  match goal with
  | Ha : c_compress_func ?s ?z ?f = Some _ |- context [c_compress_func ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_compress_func d L z Ha
  | Ha : c_hcrc_update ?h ?s ?z ?b = Some _ |- context [c_hcrc_update ?h ?s (zslice ?d ?L ?z) ?b] =>
      use_sl sl_hcrc_update d L z Ha
  | Ha : c_flush_or_return ?s ?z = Some _ |- context [c_flush_or_return ?s (zslice ?d ?L ?z)] =>
      use_sl sl_flush_or_return d L z Ha
  end.

Lemma sl_extra_body d L h xs s z beg lft e : extra_body h xs (s, z, beg, lft) = Some e -> zwin d L z ->
  match e with
  | inl (s1, z1, b1, l1) => extra_body h xs (s, zslice d L z, beg, lft) = Some (inl (s1, zslice d L z1, b1, l1)) /\
                            zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (inl (s1, z1, b1, l1)) =>
      extra_body h xs (s, zslice d L z, beg, lft) = Some (inr (inl (s1, zslice d L z1, b1, l1))) /\
      zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (inr (s1, z1)) => extra_body h xs (s, zslice d L z, beg, lft) = Some (inr (inr (s1, zslice d L z1))) /\
                          zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  end.
Proof. sl_tac extra_body. Qed.

Lemma sl_extra_loop d L h xs s z beg lft e : loop FUEL (extra_body h xs) (s, z, beg, lft) = Some e -> zwin d L z ->
  match e with
  | inl (s1, z1, b1, l1) => loop FUEL (extra_body h xs) (s, zslice d L z, beg, lft) = Some (inl (s1, zslice d L z1, b1, l1)) /\
                            zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (s1, z1) => loop FUEL (extra_body h xs) (s, zslice d L z, beg, lft) = Some (inr (s1, zslice d L z1)) /\
                    zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  end.
Proof.
  intros H W.
  set (fa := fun a : dstate * strm * Z * Z => let '(s, z, b, l) := a in (s, zslice d L z, b, l)).
  set (P := fun a : dstate * strm * Z * Z => let '(_, z1, _, _) := a in zwin d L z1 /\ z_avail_in z1 <= z_avail_in z).
  destruct (loop_sim (extra_body h xs) fa
              (fun e => match e with inl a => inl (fa a) | inr (s1, z1) => inr (s1, zslice d L z1) end) P
              (fun e => match e with inl a => P a | inr (_, z1) => zwin d L z1 /\ z_avail_in z1 <= z_avail_in z end))
    with (3 := H) as [E Q].
  - intros [[[s0 z0] b0] l0] x [W0 A0] E. apply (sl_extra_body d L) in E; [|exact W0].
    destruct x as [[[[s2 z2] b2] l2]|[[[[s2 z2] b2] l2]|[s2 z2]]]; destruct E as (E & W1 & A1); cbn;
      (split; [exact E | split; [exact W1 | lia]]).
  - cbn. split; [exact W | lia].
  - destruct e as [[[[s1 z1] b1] l1]|[s1 z1]]; cbn in E, Q; destruct Q; auto.
Qed.

Lemma sl_str_body d L h str s z beg e : str_body h str (s, z, beg) = Some e -> zwin d L z ->
  match e with
  | inl (s1, z1, b1) => str_body h str (s, zslice d L z, beg) = Some (inl (s1, zslice d L z1, b1)) /\
                        zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (inl (s1, z1, b1)) => str_body h str (s, zslice d L z, beg) = Some (inr (inl (s1, zslice d L z1, b1))) /\
                              zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (inr (s1, z1)) => str_body h str (s, zslice d L z, beg) = Some (inr (inr (s1, zslice d L z1))) /\
                          zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  end.
Proof. sl_tac str_body. Qed.

Lemma sl_str_loop d L h str s z beg e : loop FUEL (str_body h str) (s, z, beg) = Some e -> zwin d L z ->
  match e with
  | inl (s1, z1, b1) => loop FUEL (str_body h str) (s, zslice d L z, beg) = Some (inl (s1, zslice d L z1, b1)) /\
                        zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  | inr (s1, z1) => loop FUEL (str_body h str) (s, zslice d L z, beg) = Some (inr (s1, zslice d L z1)) /\
                    zwin d L z1 /\ z_avail_in z1 <= z_avail_in z
  end.
Proof.
  intros H W.
  set (fa := fun a : dstate * strm * Z => let '(s, z, b) := a in (s, zslice d L z, b)).
  set (P := fun a : dstate * strm * Z => let '(_, z1, _) := a in zwin d L z1 /\ z_avail_in z1 <= z_avail_in z).
  destruct (loop_sim (str_body h str) fa
              (fun e => match e with inl a => inl (fa a) | inr (s1, z1) => inr (s1, zslice d L z1) end) P
              (fun e => match e with inl a => P a | inr (_, z1) => zwin d L z1 /\ z_avail_in z1 <= z_avail_in z end))
    with (3 := H) as [E Q].
  - intros [[s0 z0] b0] x [W0 A0] E. apply (sl_str_body d L) in E; [|exact W0].
    destruct x as [[[s2 z2] b2]|[[[s2 z2] b2]|[s2 z2]]]; destruct E as (E & W1 & A1); cbn;
      (split; [exact E | split; [exact W1 | lia]]).
  - cbn. split; [exact W | lia].
  - destruct e as [[[s1 z1] b1]|[s1 z1]]; cbn in E, Q; destruct Q; auto.
Qed.

Ltac sl_call11 ::=
  match goal with
  | Ha : loop _ (extra_body ?h ?x) (?s, ?z, ?b, ?l) = Some _ |-
      context [loop _ (extra_body ?h ?x) (?s, zslice ?d ?L ?z, ?b, ?l)] => use_sl sl_extra_loop d L z Ha
  | Ha : loop _ (str_body ?h ?x) (?s, ?z, ?b) = Some _ |-
      context [loop _ (str_body ?h ?x) (?s, zslice ?d ?L ?z, ?b)] => use_sl sl_str_loop d L z Ha
  end.

Lemma sl_deflate_str d L h o r s z s1 z1 x : c_deflate_str h o r s z = Some (s1, z1, x) -> zwin d L z ->
  stage_sl d L z (c_deflate_str h o r s (zslice d L z)) s1 z1 x.
Proof. sl_tac c_deflate_str. Qed.

Ltac sl_call12 ::=
  match goal with
  | Ha : c_deflate_str ?h ?o ?r ?s ?z = Some _ |- context [c_deflate_str ?h ?o ?r ?s (zslice ?d ?L ?z)] =>
      use_sl sl_deflate_str d L z Ha
  end.

Lemma sl_entry d L s z f s1 z1 o : c_deflate_entry s z f = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_entry s (zslice d L z) f) s1 z1 o.
Proof. sl_tac c_deflate_entry. Qed.

Lemma sl_zlib_header d L s z s1 z1 o : c_deflate_zlib_header s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_zlib_header s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_zlib_header. Qed.

Lemma sl_gzip_header d L s z s1 z1 o : c_deflate_gzip_header s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_gzip_header s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_gzip_header. Qed.

Lemma sl_extra d L s z s1 z1 o : c_deflate_extra s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_extra s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_extra. Qed.

Lemma sl_name d L s z s1 z1 o : c_deflate_name s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_name s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_name. Qed.

Lemma sl_comment d L s z s1 z1 o : c_deflate_comment s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_comment s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_comment. Qed.

Lemma sl_hcrc d L s z s1 z1 o : c_deflate_hcrc s z = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_hcrc s (zslice d L z)) s1 z1 o.
Proof. sl_tac c_deflate_hcrc. Qed.

Lemma sl_compress d L s z f s1 z1 o : c_deflate_compress s z f = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_compress s (zslice d L z) f) s1 z1 o.
Proof. sl_tac c_deflate_compress. Qed.

Lemma sl_trailer d L s z f s1 z1 o : c_deflate_trailer s z f = Some (s1, z1, o) -> zwin d L z ->
  stage_sl d L z (c_deflate_trailer s (zslice d L z) f) s1 z1 o.
Proof. sl_tac c_deflate_trailer. Qed.

Ltac sl_call13 ::=
  match goal with
  | Ha : c_deflate_entry ?s ?z ?f = Some _ |- context [c_deflate_entry ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_entry d L z Ha
  | Ha : c_deflate_zlib_header ?s ?z = Some _ |- context [c_deflate_zlib_header ?s (zslice ?d ?L ?z)] =>
      use_sl sl_zlib_header d L z Ha
  | Ha : c_deflate_gzip_header ?s ?z = Some _ |- context [c_deflate_gzip_header ?s (zslice ?d ?L ?z)] =>
      use_sl sl_gzip_header d L z Ha
  | Ha : c_deflate_extra ?s ?z = Some _ |- context [c_deflate_extra ?s (zslice ?d ?L ?z)] =>
      use_sl sl_extra d L z Ha
  | Ha : c_deflate_name ?s ?z = Some _ |- context [c_deflate_name ?s (zslice ?d ?L ?z)] =>
      use_sl sl_name d L z Ha
  | Ha : c_deflate_comment ?s ?z = Some _ |- context [c_deflate_comment ?s (zslice ?d ?L ?z)] =>
      use_sl sl_comment d L z Ha
  | Ha : c_deflate_hcrc ?s ?z = Some _ |- context [c_deflate_hcrc ?s (zslice ?d ?L ?z)] =>
      use_sl sl_hcrc d L z Ha
  | Ha : c_deflate_compress ?s ?z ?f = Some _ |- context [c_deflate_compress ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_compress d L z Ha
  | Ha : c_deflate_trailer ?s ?z ?f = Some _ |- context [c_deflate_trailer ?s (zslice ?d ?L ?z) ?f] =>
      use_sl sl_trailer d L z Ha
  end.

Lemma sl_deflate d L s z f s1 z1 e : c_deflate s z f = Some (s1, z1, e) -> zwin d L z ->
  c_deflate s (zslice d L z) f = Some (s1, zslice d L z1, e) /\ zwin d L z1 /\ z_avail_in z1 <= z_avail_in z.
Proof. sl_tac c_deflate. Qed.

(** a call whose offered input [next_in, next_in + avail_in) lies in [d, d + L) and ends at d + L *)
Lemma deflate_slice d L s z flush s' z' e :
  0 <= d <= z_next_in z -> 0 <= z_avail_in z -> z_next_in z + z_avail_in z = d + L ->
  d + L <= Zlength (z_in z) ->
  c_deflate s z flush = Some (s', z', e) ->
  c_deflate s (zslice d L z) flush = Some (s', zslice d L z', e).
Proof.
  intros Hd Ha Hs Hl H. apply (sl_deflate d L) in H; [exact (proj1 H) | unfold zwin; lia].
Qed.

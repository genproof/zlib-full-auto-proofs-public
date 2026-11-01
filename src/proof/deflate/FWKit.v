(** * Kit for the body proof of fill_window (Body_fill_window.v): the function's context, its statement split
    into fragments, the shapes of the fragment triples, and model facts.

    The body of fill_window (deflate.c) is

      wsize = s->w_size;
      do {
        more = (unsigned)(s->window_size - (ulg)s->lookahead - (ulg)s->strstart);
        if (sizeof(int) <= 2) { ... }                       [dead: sizeof(int) = 4]
        if (s->strstart >= wsize + MAX_DIST(s)) { ... }     [S_slide: model c_fw_slide]
        if (s->strm->avail_in == 0) break;
        n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more);
        s->lookahead += n;                                  [S_read: c_read_buf, mb_write, lookahead]
        if (s->lookahead + s->insert >= MIN_MATCH) { ... }  [S_ins: model c_fw_insert]
      } while (s->lookahead < MIN_LOOKAHEAD && s->strm->avail_in != 0);
      if (s->high_water < s->window_size) { ... }           [S_high: model c_fw_high_water]

    The fragment triples are proved in FWSlide.v, FWRead.v, FWIns.v, FWHigh.v; Body_fill_window.v puts them
    together (the do-while loop against DLoop.runs fw_body).  Every fragment keeps the whole stream without the
    output side [dfull_in] (DSpec.v) in its pre- and postcondition. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Export Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Export Zlib.proof.deflate.Obligations.
Require Export Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The context of the body *)
Definition Delta_fw : tycontext := func_tycontext f_fill_window Vprog Gprog_fill_window nil.

(** ** Sub-statements of the body, by path: Ssequence a b: 0 = a, 1 = b; Sloop body incr: 0 = body, 1 = incr;
    Sifthenelse e a b: 1 = a, 2 = b. *)
Fixpoint fw_sub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => fw_sub a path'
    | Ssequence _ b, S O => fw_sub b path'
    | Sloop a _, O => fw_sub a path'
    | Sloop _ b, S O => fw_sub b path'
    | Sifthenelse _ a _, S O => fw_sub a path'
    | Sifthenelse _ _ b, S (S O) => fw_sub b path'
    | _, _ => Sskip
    end
  end.

(** [t'58 = s->strstart; t'59 = s->w_size; if (t'58 >= wsize + (t'59 - 262)) { zmemcpy ...; slide_hash(s);
    more += wsize; }] *)
Definition S_slide : statement := fw_sub (fn_body f_fill_window) [1;0;0;1;1;0]%nat.
(** [n = read_buf(s->strm, s->window + s->strstart + s->lookahead, more); s->lookahead += n;] *)
Definition S_read : statement :=
  Ssequence (fw_sub (fn_body f_fill_window) [1;0;0;1;1;1;1;0]%nat)
            (fw_sub (fn_body f_fill_window) [1;0;0;1;1;1;1;1;0]%nat).
(** [if (s->lookahead + s->insert >= MIN_MATCH) { str = ...; ins_h = ...; UPDATE_HASH; while (s->insert) ... }] *)
Definition S_ins : statement := fw_sub (fn_body f_fill_window) [1;0;0;1;1;1;1;1;1]%nat.
(** [if (s->high_water < s->window_size) { ... }] (after the loop, the end of the function). *)
Definition S_high : statement := fw_sub (fn_body f_fill_window) [1;1]%nat.

(** Show a fragment's statement concretely. *)
Ltac show_fw_stmt := cbv [S_slide S_read S_ins S_high fw_sub f_fill_window fn_body].

(** ** The fragment triples (proved in FWSlide.v, FWRead.v, FWIns.v, FWHigh.v) *)

(** The slide: [c_fw_slide s more = Some (s', more')]. *)
Definition fw_slide_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (more : Z) (s' : dstate) (more' : Z),
  0 <= more <= Int.max_unsigned ->
  c_fw_slide s more = Some (s', more') ->
  semax Delta_fw
    (PROP () LOCAL (temp _wsize (vi (d_w_size s)); temp _more (vi more); temp _s (p_s p); gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv))
    S_slide
    (normal_ret_assert
      (PROP () LOCAL (temp _wsize (vi (d_w_size s)); temp _more (vi more'); temp _s (p_s p); gvars gv)
       SEP (dfull_in s' z p pin ish msgv gv; deflate_globals gv))).

(** The read: [c_read_buf s z more = Some (z', data)], the window written at strstart + lookahead. *)
Definition fw_read_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (w more : Z) (z' : strm) (data : list Z) (win : mbuf),
  0 <= more <= Int.max_unsigned ->
  c_read_buf s z more = Some (z', data) ->
  mb_write (d_window s) (d_strstart s + d_lookahead s) data = Some win ->
  semax Delta_fw
    (PROP () LOCAL (temp _wsize (vi w); temp _more (vi more); temp _s (p_s p); gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv))
    S_read
    (normal_ret_assert
      (PROP () LOCAL (temp _wsize (vi w); temp _s (p_s p); gvars gv)
       SEP (dfull_in (set_d_lookahead (set_d_window s win) (u32 (d_lookahead s + Zlength data))) z' p pin ish
              msgv gv;
            deflate_globals gv))).

(** The hash insertion: [c_fw_insert s = Some s']. *)
Definition fw_ins_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (w : Z) (s' : dstate),
  c_fw_insert s = Some s' ->
  semax Delta_fw
    (PROP () LOCAL (temp _wsize (vi w); temp _s (p_s p); gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv))
    S_ins
    (normal_ret_assert
      (PROP () LOCAL (temp _wsize (vi w); temp _s (p_s p); gvars gv)
       SEP (dfull_in s' z p pin ish msgv gv; deflate_globals gv))).

(** The high-water zeroing after the loop: [c_fw_high_water s = Some s']. *)
Definition fw_high_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (w : Z) (s' : dstate),
  c_fw_high_water s = Some s' ->
  semax Delta_fw
    (PROP () LOCAL (temp _wsize (vi w); temp _s (p_s p); gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv))
    S_high
    (normal_ret_assert
      (PROP () LOCAL (temp _s (p_s p); gvars gv)
       SEP (dfull_in s' z p pin ish msgv gv; deflate_globals gv))).

(** ** The window as a masked buffer *)

Lemma Zlength_mb_vals b : Zlength (mb_def b) = Zlength (mb_val b) -> Zlength (mb_vals b) = Zlength (mb_val b).
Proof. intros. unfold mb_vals. apply Zlength_pb_vals. auto. Qed.

Lemma pb_vals_app b1 b2 m1 m2 : Zlength m1 = Zlength b1 ->
  pb_vals (b1 ++ b2) (m1 ++ m2) = pb_vals b1 m1 ++ pb_vals b2 m2.
Proof.
  intros H. unfold pb_vals. rewrite combine_app' by lia.
  apply map_app.
Qed.

Lemma pb_vals_sublist lo hi b m : Zlength m = Zlength b ->
  pb_vals (sublist lo hi b) (sublist lo hi m) = sublist lo hi (pb_vals b m).
Proof.
  intros H. unfold pb_vals. rewrite sublist_map, sublist_combine. reflexivity.
Qed.

Lemma pb_vals_all_true b : pb_vals b (repeat true (Z.to_nat (Zlength b))) = map vi b.
Proof.
  unfold pb_vals. rewrite Zlength_correct, Nat2Z.id.
  induction b as [|x b IH]; [reflexivity|]. cbn. f_equal. exact IH.
Qed.

(** The contents of the window after [mb_write]: the old contents with [src] in place. *)
Lemma mb_vals_write b lo src b' :
  Zlength (mb_def b) = Zlength (mb_val b) ->
  mb_write b lo src = Some b' ->
  mb_vals b' = sublist 0 lo (mb_vals b) ++ map vi src ++
               sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_vals b) /\
  Zlength (mb_val b') = Zlength (mb_val b) /\ Zlength (mb_def b') = Zlength (mb_val b') /\
  0 <= lo /\ lo + Zlength src <= Zlength (mb_val b).
Proof.
  intros Hl H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  unfold mb_vals; cbn [mb_val mb_def].
  assert (Hlen : Zlength (sublist 0 lo (mb_val b) ++ src ++
                  sublist (lo + Zlength src) (Zlength (mb_val b)) (mb_val b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
  assert (Hlen' : Zlength (sublist 0 lo (mb_def b) ++ repeat true (Z.to_nat (Zlength src)) ++
                  sublist (lo + Zlength src) (Zlength (mb_def b)) (mb_def b)) = Zlength (mb_val b)).
  { rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia. }
  split; [|split; [exact Hlen|split; [lia|split; lia]]].
  rewrite !pb_vals_app.
  2: { rewrite Zlength_repeat; lia. }
  2: { rewrite !Zlength_sublist by lia. lia. }
  rewrite pb_vals_all_true. rewrite Hl.
  rewrite !pb_vals_sublist by auto. reflexivity.
Qed.

Lemma mb_ok_write b lo src b' :
  mb_ok b -> Forall (fun x => 0 <= x < 256) src -> mb_write b lo src = Some b' -> mb_ok b'.
Proof.
  intros [Hl Hd] Hs H. unfold mb_write in H.
  destruct (andb (0 <=? lo) (lo + Zlength src <=? Zlength (mb_val b))) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  inversion H; subst; clear H. pose proof (Zlength_nonneg src).
  split; cbn [mb_val mb_def].
  - rewrite !Zlength_app, Zlength_repeat, !Zlength_sublist by lia. lia.
  - intros i Hi Hdi. rewrite !Zlength_app, !Zlength_sublist in Hi by lia.
    destruct (Z_lt_dec i lo).
    + rewrite app_Znth1 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia.
      apply Hd; [lia|]. rewrite Z.add_0_r in *. auto.
    + rewrite app_Znth2 in Hdi by (rewrite Zlength_sublist; lia).
      rewrite app_Znth2 by (rewrite Zlength_sublist; lia).
      rewrite Zlength_sublist in Hdi by lia. rewrite Zlength_sublist by lia.
      destruct (Z_lt_dec (i - (lo - 0)) (Zlength src)).
      * rewrite app_Znth1 by lia. rewrite Forall_forall in Hs. apply Hs. apply Znth_In. lia.
      * rewrite app_Znth2 in Hdi by (rewrite ?Zlength_repeat; lia).
        rewrite app_Znth2 by (rewrite ?Zlength_repeat; lia).
        rewrite Zlength_repeat in Hdi by lia.
        rewrite Znth_sublist in Hdi by lia. rewrite Znth_sublist by lia. apply Hd; [lia|]. auto.
Qed.

(** ** Model facts *)

Ltac destr_if_in H := match type of H with context [if ?b then _ else _] => destruct b end.

Lemma fw_slide_w_size s more s' more' :
  c_fw_slide s more = Some (s', more') -> d_w_size s' = d_w_size s.
Proof.
  unfold c_fw_slide. destruct (_ >=? _).
  - intros H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
    unfold c_slide_hash in Ha3. inv_bind Ha3. inversion Ha3; subst; clear Ha3.
    destruct (_ >? _); inversion H; subst; reflexivity.
  - intros H; inversion H; reflexivity.
Qed.

Lemma fw_insert_body_w_size a r :
  runs fw_insert_body a r -> d_w_size r = d_w_size (fst a).
Proof.
  induction 1 as [[s str] r H|[s str] a' r H _ IH].
  - unfold fw_insert_body in H. destruct (d_insert s =? 0); [inversion H; reflexivity|].
    inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
    destr_if_in H; inversion H; subst; reflexivity.
  - rewrite IH. unfold fw_insert_body in H. destruct (d_insert s =? 0); [discriminate|].
    inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
    destr_if_in H; inversion H; subst; reflexivity.
Qed.

Lemma fw_insert_w_size s s' : c_fw_insert s = Some s' -> d_w_size s' = d_w_size s.
Proof.
  unfold c_fw_insert. destruct (_ >=? _).
  - intros H. inv_bind H. inv_bind H. inv_bind H.
    apply loop_runs, fw_insert_body_w_size in H. rewrite H. reflexivity.
  - intros H; inversion H; reflexivity.
Qed.

(** One iteration of the loop keeps w_size. *)
Lemma fw_body_w_size a r :
  fw_body a = Some r -> d_w_size (fst (match r with inl x => x | inr x => x end)) = d_w_size (fst a).
Proof.
  destruct a as [s z]. unfold fw_body. intros H.
  inv_bind H. destruct x as [s1 more1]. apply fw_slide_w_size in Ha.
  destruct (z_avail_in z =? 0); [inversion H; subst; exact Ha|].
  inv_bind H. destruct x as [z2 data]. inv_bind H. inv_bind H.
  apply fw_insert_w_size in Ha2. destr_if_in H; inversion H; subst; cbn; rewrite Ha2; cbn; exact Ha.
Qed.

Lemma runs_fw_body_w_size a r : runs fw_body a r -> d_w_size (fst r) = d_w_size (fst a).
Proof.
  induction 1 as [a r H|a a' r H _ IH].
  - exact (fw_body_w_size _ _ H).
  - rewrite IH. exact (fw_body_w_size _ _ H).
Qed.

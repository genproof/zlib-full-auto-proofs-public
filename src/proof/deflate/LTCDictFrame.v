(** * deflateSetDictionary: fill_window does not look at head, prev or the output side of the stream
    when nothing is to be inserted (insert = 0) and the window does not slide. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCDictKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop simulated through a map of its states *)
Lemma loop2_sim {A B : Type} (body : A -> option (A + B)) (f : A -> A) (g : B -> B) (I : A -> Prop)
    (J : B -> Prop) :
  (forall a, I a ->
     body (f a) = match body a with Some (inl a') => Some (inl (f a')) | Some (inr b) => Some (inr (g b))
                  | None => None end /\
     (forall a', body a = Some (inl a') -> I a') /\ (forall b, body a = Some (inr b) -> J b)) ->
  forall d a, I a ->
     loop2 d body (f a) = match loop2 d body a with Some (inl a') => Some (inl (f a'))
                          | Some (inr b) => Some (inr (g b)) | None => None end /\
     (forall a', loop2 d body a = Some (inl a') -> I a') /\ (forall b, loop2 d body a = Some (inr b) -> J b).
Proof.
  intros Hb d. induction d as [|d IH]; intros a Ha.
  - simpl. apply Hb; assumption.
  - simpl. destruct (IH a Ha) as [E1 [I1 J1]]. rewrite E1.
    destruct (loop2 d body a) as [[a'|b]|] eqn:E.
    + destruct (IH a' (I1 a' eq_refl)) as [E2 [I2 J2]]. split; [exact E2|]. split; assumption.
    + split; [reflexivity|]. split; [intros; discriminate|]. intros b' Hb'. inversion Hb'; subst. auto.
    + split; [reflexivity|]. split; intros; discriminate.
Qed.

Lemma loop2_exit {A B : Type} (body : A -> option (A + B)) a r :
  body a = Some (inr r) -> forall d, loop2 d body a = Some (inr r).
Proof. intros E d. induction d as [|d IH]; simpl; [exact E|]. rewrite IH. reflexivity. Qed.

(** ** The frame: head and prev replaced *)
Definition fr (H P : list Z) (s : dstate) : dstate := set_d_head (set_d_prev s P) H.

Lemma fr_window H P s : d_window (fr H P s) = d_window s. Proof. reflexivity. Qed.
Lemma fr_window_size H P s : d_window_size (fr H P s) = d_window_size s. Proof. reflexivity. Qed.
Lemma fr_lookahead H P s : d_lookahead (fr H P s) = d_lookahead s. Proof. reflexivity. Qed.
Lemma fr_strstart H P s : d_strstart (fr H P s) = d_strstart s. Proof. reflexivity. Qed.
Lemma fr_w_size H P s : d_w_size (fr H P s) = d_w_size s. Proof. reflexivity. Qed.
Lemma fr_insert H P s : d_insert (fr H P s) = d_insert s. Proof. reflexivity. Qed.
Lemma fr_wrap H P s : d_wrap (fr H P s) = d_wrap s. Proof. reflexivity. Qed.
Lemma fr_hash_shift H P s : d_hash_shift (fr H P s) = d_hash_shift s. Proof. reflexivity. Qed.
Lemma fr_hash_mask H P s : d_hash_mask (fr H P s) = d_hash_mask s. Proof. reflexivity. Qed.
Lemma fr_ins_h H P s : d_ins_h (fr H P s) = d_ins_h s. Proof. reflexivity. Qed.
Lemma fr_high_water H P s : d_high_water (fr H P s) = d_high_water s. Proof. reflexivity. Qed.
Lemma fr_set_window H P s w : set_d_window (fr H P s) w = fr H P (set_d_window s w).
Proof. destruct s; reflexivity. Qed.
Lemma fr_set_lookahead H P s w : set_d_lookahead (fr H P s) w = fr H P (set_d_lookahead s w).
Proof. destruct s; reflexivity. Qed.
Lemma fr_set_ins_h H P s w : set_d_ins_h (fr H P s) w = fr H P (set_d_ins_h s w).
Proof. destruct s; reflexivity. Qed.
Lemma fr_set_high_water H P s w : set_d_high_water (fr H P s) w = fr H P (set_d_high_water s w).
Proof. destruct s; reflexivity. Qed.

Lemma ins_h_insert s w : d_insert (set_d_ins_h s w) = d_insert s. Proof. reflexivity. Qed.

Lemma update_hash_fr H P s h c : update_hash (fr H P s) h c = update_hash s h c.
Proof. reflexivity. Qed.

Hint Rewrite fr_window fr_window_size fr_lookahead fr_strstart fr_w_size fr_insert fr_wrap fr_hash_shift
  fr_hash_mask fr_ins_h fr_high_water fr_set_window fr_set_lookahead fr_set_ins_h fr_set_high_water
  update_hash_fr : frdb.

Lemma read_buf_frame H P s z o ao to n :
  c_read_buf (fr H P s) (zframe z o ao to) n =
    match c_read_buf s z n with Some (z', d) => Some (zframe z' o ao to, d) | None => None end.
Proof.
  destruct z. unfold c_read_buf, zframe, set_z_avail_in, set_z_adler, set_z_next_in, set_z_total_in. simpl.
  try rewrite fr_wrap.
  destruct (_ =? 0); [reflexivity|].
  unfold bind. destruct (rds _ _ _); [|reflexivity].
  destruct (d_wrap s =? 1); [reflexivity|]. destruct (d_wrap s =? 2); reflexivity.
Qed.

Lemma fw_insert_frame H P s :
  d_insert s = 0 ->
  c_fw_insert (fr H P s) = match c_fw_insert s with Some s' => Some (fr H P s') | None => None end /\
  (forall s', c_fw_insert s = Some s' -> d_insert s' = 0 /\ d_strstart s' = d_strstart s /\
     d_w_size s' = d_w_size s).
Proof.
  intros Hi. unfold c_fw_insert. autorewrite with frdb.
  destruct (_ >=? MIN_MATCH).
  - unfold bind. destruct (mb_rd _ _) as [c0|]; [|split; [reflexivity|intros; discriminate]].
    autorewrite with frdb. destruct (guard _) as [[]|]; [|split; [reflexivity|intros; discriminate]].
    destruct (mb_rd _ _) as [c1|]; [|split; [reflexivity|intros; discriminate]].
    autorewrite with frdb.
    set (s1 := set_d_ins_h (set_d_ins_h s c0) _).
    assert (Hi1 : d_insert s1 = 0) by exact Hi.
    set (str := u32 (d_strstart s - d_insert s)).
    assert (E1 : fw_insert_body (s1, str) = Some (inr s1)).
    { unfold fw_insert_body. rewrite Hi1. reflexivity. }
    assert (E2 : fw_insert_body (fr H P s1, str) = Some (inr (fr H P s1))).
    { unfold fw_insert_body. rewrite fr_insert, Hi1. reflexivity. }
    unfold loop. rewrite (loop2_exit _ _ _ E1), (loop2_exit _ _ _ E2).
    split; [reflexivity|]. intros s' Hs'. injection Hs' as <-. split; [exact Hi1|split; reflexivity].
  - split; [reflexivity|]. intros s' Hs'. inversion Hs'; subst. auto.
Qed.

Lemma zf_avail_in z o ao to : z_avail_in (zframe z o ao to) = z_avail_in z. Proof. reflexivity. Qed.

Definition FI (a : dstate * strm) : Prop :=
  262 <= d_w_size (fst a) <= 1073741824 /\ d_insert (fst a) = 0 /\
  d_strstart (fst a) < d_w_size (fst a) + MAX_DIST (fst a).

Lemma fw_slide_none s more :
  262 <= d_w_size s <= 1073741824 -> d_strstart s < d_w_size s + MAX_DIST s ->
  c_fw_slide s more = Some (s, more).
Proof.
  intros Hw Hs. unfold c_fw_slide, MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
  unfold u32. rewrite (Z.mod_small (d_w_size s - _)) by lia. rewrite Z.mod_small by lia.
  destruct (_ >=? _) eqn:E; [lia|reflexivity].
Qed.

Lemma fw_body_frame H P o ao to :
  let f := fun a : dstate * strm => (fr H P (fst a), zframe (snd a) o ao to) in
  forall a, FI a ->
     fw_body (f a) = match fw_body a with Some (inl a') => Some (inl (f a')) | Some (inr b) => Some (inr (f b))
                     | None => None end /\
     (forall a', fw_body a = Some (inl a') -> FI a') /\
     (forall b, fw_body a = Some (inr b) -> d_insert (fst b) = 0).
Proof.
  intros f [s z] [Hw [Hi Hs]]. cbn [fst snd] in *. subst f. cbn [fst snd].
  unfold fw_body. autorewrite with frdb.
  rewrite (fw_slide_none s) by assumption.
  rewrite (fw_slide_none (fr H P s)) by (autorewrite with frdb; unfold MAX_DIST in *; autorewrite with frdb; lia).
  cbn [bind]. rewrite zf_avail_in.
  destruct (z_avail_in z =? 0).
  { split; [reflexivity|]. split; [intros; discriminate|]. intros b Hb. injection Hb as <-. exact Hi. }
  rewrite read_buf_frame.
  destruct (c_read_buf s z _) as [[z' d]|]; [|split; [reflexivity|split; intros; discriminate]].
  cbn [bind]. autorewrite with frdb.
  destruct (mb_write _ _ _) as [win|]; [|split; [reflexivity|split; intros; discriminate]].
  cbn [bind]. autorewrite with frdb.
  set (s1 := set_d_lookahead (set_d_window s win) _).
  assert (Hi1 : d_insert s1 = 0) by exact Hi.
  destruct (fw_insert_frame H P s1 Hi1) as [E F]. rewrite E.
  destruct (c_fw_insert s1) as [s2|]; [|split; [reflexivity|split; intros; discriminate]].
  destruct (F s2 eq_refl) as [Hi2 [Hs2 Hw2]].
  cbn [bind]. autorewrite with frdb. rewrite zf_avail_in.
  assert (FI2 : FI (s2, z')).
  { unfold FI, MAX_DIST in *. cbn [fst]. rewrite Hi2, Hs2, Hw2. split; [exact Hw|]. split; [reflexivity|exact Hs]. }
  destruct (_ && _).
  - split; [reflexivity|]. split; [|intros; discriminate]. intros a' Ha'. injection Ha' as <-. exact FI2.
  - split; [reflexivity|]. split; [intros; discriminate|]. intros b Hb. injection Hb as <-. exact Hi2.
Qed.

Lemma high_water_frame H P s :
  c_fw_high_water (fr H P s) = match c_fw_high_water s with Some s' => Some (fr H P s') | None => None end /\
  (forall s', c_fw_high_water s = Some s' -> d_insert s' = d_insert s).
Proof.
  unfold c_fw_high_water. autorewrite with frdb.
  destruct (_ <? _); [|split; [reflexivity|intros s' E; injection E as <-; reflexivity]].
  destruct (_ <? _).
  - unfold bind. destruct (mb_write _ _ _); [|split; [reflexivity|intros; discriminate]].
    autorewrite with frdb. split; [reflexivity|intros s' E; injection E as <-; reflexivity].
  - destruct (_ <? _); [|split; [reflexivity|intros s' E; injection E as <-; reflexivity]].
    unfold bind. destruct (mb_write _ _ _); [|split; [reflexivity|intros; discriminate]].
    autorewrite with frdb. split; [reflexivity|intros s' E; injection E as <-; reflexivity].
Qed.

Lemma fill_frame : forall s z H P o ao to,
  262 <= d_w_size s <= 1073741824 -> d_insert s = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
  c_fill_window (set_d_head (set_d_prev s P) H) (zframe z o ao to) =
    match c_fill_window s z with
    | Some (s', z') => Some (set_d_head (set_d_prev s' P) H, zframe z' o ao to)
    | None => None
    end /\
  (forall s' z', c_fill_window s z = Some (s', z') -> d_insert s' = 0).
Proof.
  intros s z H P o ao to Hw Hi Hs.
  set (f := fun a : dstate * strm => (fr H P (fst a), zframe (snd a) o ao to)).
  destruct (loop2_sim fw_body f f FI (fun b => d_insert (fst b) = 0) (fw_body_frame H P o ao to) FUEL (s, z))
    as [E [_ J]]; [unfold FI; cbn [fst]; auto|].
  unfold c_fill_window, loop. change (set_d_head (set_d_prev s P) H, zframe z o ao to) with (f (s, z)).
  rewrite E.
  destruct (loop2 FUEL fw_body (s, z)) as [[a|[s1 z1]]|]; cbn [bind];
    [split; [reflexivity|intros; discriminate]| |split; [reflexivity|intros; discriminate]].
  specialize (J (s1, z1) eq_refl). cbn [fst] in J. subst f. cbn [fst snd].
  destruct (high_water_frame H P s1) as [E2 F2]. rewrite E2.
  destruct (c_fw_high_water s1) as [s2|]; cbn [bind].
  - split; [reflexivity|]. intros s' z' Hs'. injection Hs' as <- <-. rewrite (F2 s2 eq_refl). exact J.
  - split; [reflexivity|intros; discriminate].
Qed.

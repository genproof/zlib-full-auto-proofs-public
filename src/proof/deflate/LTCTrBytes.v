(** * TREES part, sub-part BYTES: see LTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCTrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** pending_buf after an output function: same length, only bytes written, only in [lo, hi) *)

Definition buf_after (b b' : list Z) (lo hi : Z) : Prop :=
  lo <= hi /\ Zlength b' = Zlength b /\ (lo = hi \/ (0 <= lo /\ hi <= Zlength b)) /\
  (forall i, i < lo \/ hi <= i -> Znth i b' = Znth i b) /\
  (forall i, lo <= i < hi -> 0 <= Znth i b' < 256).

Lemma buf_after_refl b p : buf_after b b p p.
Proof.
  split; [lia|]. split; [reflexivity|]. split; [left; reflexivity|].
  split; [intros; reflexivity | intros; lia].
Qed.

Lemma buf_after_trans b1 b2 b3 a b c :
  buf_after b1 b2 a b -> buf_after b2 b3 b c -> buf_after b1 b3 a c.
Proof.
  intros [Hab [L1 [R1 [F1 B1]]]] [Hbc [L2 [R2 [F2 B2]]]].
  split; [lia|]. split; [lia|]. split.
  { destruct R1 as [R1|R1], R2 as [R2|R2]; [left; lia|right; lia|right; lia|right; lia]. }
  split.
  - intros i Hi. rewrite F2 by lia. apply F1. lia.
  - intros i Hi. destruct (Z_lt_ge_dec i b).
    + rewrite F2 by lia. apply B1. lia.
    + apply B2. lia.
Qed.

Lemma Znth_upd_Znth_other {A} {d : Inhabitant A} (l : list A) p v i :
  i <> p -> Znth i (upd_Znth p l v) = Znth i l.
Proof.
  intros Hne.
  destruct (Z_le_gt_dec 0 p); [destruct (Z_lt_ge_dec p (Zlength l))|].
  - destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
    + apply upd_Znth_diff; lia.
    + rewrite !Znth_overflow; auto; rewrite ?Zlength_upd_Znth_any; lia.
    + rewrite !Znth_underflow; auto; lia.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
  - rewrite upd_Znth_out_of_range by lia. reflexivity.
Qed.

Lemma buf_after_upd b p v : 0 <= p < Zlength b -> 0 <= v < 256 -> buf_after b (upd_Znth p b v) p (p + 1).
Proof.
  intros Hp Hv. split; [lia|]. split; [apply Zlength_upd_Znth_any|]. split; [right; lia|]. split.
  - intros i Hi. apply Znth_upd_Znth_other. lia.
  - intros i Hi. replace i with p by lia. rewrite upd_Znth_same by lia. exact Hv.
Qed.

Lemma buf_after_copy b p src :
  0 <= p -> p + Zlength src <= Zlength b -> bytes src ->
  buf_after b (copy_bytes b p src) p (p + Zlength src).
Proof.
  intros H0 H1 Hs. pose proof (Zlength_nonneg src) as Hn. unfold copy_bytes.
  assert (Lp : Zlength (sublist 0 p b) = p) by (rewrite Zlength_sublist; lia).
  split; [lia|]. split.
  { rewrite !Zlength_app, Zlength_sublist, Zlength_sublist by lia. lia. }
  split; [right; lia|]. split.
  - intros i Hi. destruct Hi as [Hi|Hi].
    + destruct (Z_lt_ge_dec i 0).
      * rewrite !Znth_underflow by lia. reflexivity.
      * rewrite app_Znth1 by lia. rewrite Znth_sublist by lia. f_equal; lia.
    + destruct (Z_lt_ge_dec i (Zlength b)).
      * rewrite app_Znth2 by lia. rewrite Lp. rewrite app_Znth2 by lia.
        rewrite Znth_sublist by lia. f_equal; lia.
      * rewrite !Znth_overflow; auto.
        rewrite !Zlength_app, Zlength_sublist, Zlength_sublist by lia. lia.
  - intros i Hi. rewrite app_Znth2 by lia. rewrite Lp. rewrite app_Znth1 by lia.
    unfold bytes in Hs. rewrite Forall_forall in Hs. apply Hs. apply Znth_In. lia.
Qed.

Lemma c_put_short_pos o m w o' m' :
  c_put_short (o, m) w = Some (o', m') -> 0 <= o_pending o /\ o_pending o' = o_pending o + 2.
Proof.
  intros H. unfold c_put_short, c_put_byte in H.
  destruct (wr (o_buf o) (o_pending o) _) as [b|] eqn:E; cbv beta iota zeta delta [bind] in H; [|discriminate H].
  apply wr_Some in E. destruct E as [_ E].
  cbn [o_buf o_pending] in H.
  destruct (wr b (o_pending o + 1) _) as [b2|] eqn:E2; [|discriminate H].
  apply some_inj in H. inversion H; subst. cbn [o_pending]. lia.
Qed.

Class CBytes (b : list Z) (p : Z) (c : option cout) : Prop :=
  cbytes : forall o' m', c = Some (o', m') -> buf_after b (o_buf o') p (o_pending o').

Ltac bstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cout |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply some_inj in H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : false = true |- _ => discriminate H
  | H : true = false |- _ => discriminate H
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | Q : (_, _) = (_, _) |- _ => apply pair_inj in Q; destruct Q; subst
  | E : guard _ = Some _ |- _ => apply guard_Some in E
  | E : c_put_short (_, _) _ = Some (_, _) |- _ =>
      let A := fresh "A" in pose proof (c_put_short_pos _ _ _ _ _ E); pose proof (cbytes _ _ E) as A; clear E
  | E : _ = Some (_, _) |- _ => let A := fresh "A" in pose proof (cbytes _ _ E) as A; clear E
  | E : _ = Some ?r |- _ =>
      lazymatch type of r with Z => clear E | unit => clear E | bool => clear E | list Z => clear E end
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac bchain :=
  repeat match goal with
  | A1 : buf_after ?m1 ?m2 ?a ?b, A2 : buf_after ?m2 ?m3 ?b ?c |- _ =>
      pose proof (buf_after_trans _ _ _ _ _ _ A1 A2); clear A1 A2
  end.

Ltac brun :=
  repeat (bstep; cbv beta iota zeta delta [andb orb negb fst snd] in *);
  cbn [o_pending o_buf set_bits fst snd] in *; bchain;
  try assumption; try apply buf_after_refl.

Ltac bstart := intros ? ? ?.

#[export] Instance cb_put_byte o m c : CBytes (o_buf o) (o_pending o) (c_put_byte (o, m) c).
Proof.
  bstart. unfold c_put_byte in *.
  destruct (wr (o_buf o) (o_pending o) (u8 c)) as [b|] eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H;
    [|discriminate H].
  apply wr_Some in E. destruct E as [-> E]. apply some_inj in H. inversion H; subst. cbn [o_buf o_pending].
  apply buf_after_upd; [lia|]. unfold u8. apply Z.mod_pos_bound. lia.
Qed.

#[export] Instance cb_put_short o m w : CBytes (o_buf o) (o_pending o) (c_put_short (o, m) w).
Proof. bstart. unfold c_put_short in *. brun. Qed.

#[export] Instance cb_send_bits o m v l : CBytes (o_buf o) (o_pending o) (c_send_bits (o, m) v l).
Proof. bstart. unfold c_send_bits in *. brun. Qed.

#[export] Instance cb_send_code o m c codes lens : CBytes (o_buf o) (o_pending o) (c_send_code (o, m) c codes lens).
Proof. bstart. unfold c_send_code in *. brun. Qed.

#[export] Instance cb_bi_windup o m : CBytes (o_buf o) (o_pending o) (c_bi_windup (o, m)).
Proof. bstart. unfold c_bi_windup in *. brun. Qed.

#[export] Instance cb_send_codes : forall fuel o m c codes lens count,
  CBytes (o_buf o) (o_pending o) (c_send_codes fuel (o, m) c codes lens count).
Proof. induction fuel; intros; bstart; cbn [c_send_codes] in *; brun. Qed.

#[export] Instance cb_send_tree_loop : forall fuel t max_code blc bll o m n prevlen nextlen count max_count min_count,
  CBytes (o_buf o) (o_pending o)
    (c_send_tree_loop fuel t max_code blc bll (o, m) n prevlen nextlen count max_count min_count).
Proof. induction fuel; intros; bstart; cbn [c_send_tree_loop] in *; brun. Qed.

#[export] Instance cb_send_tree o m t max_code bl : CBytes (o_buf o) (o_pending o) (c_send_tree (o, m) t max_code bl).
Proof. bstart. unfold c_send_tree in *. brun. Qed.

#[export] Instance cb_send_bl_lens : forall fuel bl o m rank blcodes,
  CBytes (o_buf o) (o_pending o) (c_send_bl_lens fuel bl (o, m) rank blcodes).
Proof. induction fuel; intros; bstart; cbn [c_send_bl_lens] in *; brun. Qed.

#[export] Instance cb_send_all_trees o m lt dt bl lcodes dcodes blcodes :
  CBytes (o_buf o) (o_pending o) (c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes).
Proof. bstart. unfold c_send_all_trees in *. brun. Qed.

#[export] Instance cb_send_symbol o m lcodes llens dcodes dlens dist lc :
  CBytes (o_buf o) (o_pending o) (c_send_symbol (o, m) lcodes llens dcodes dlens dist lc).
Proof. bstart. unfold c_send_symbol in *. brun. Qed.

#[export] Instance cb_compress_loop : forall fuel lit_bufsize sym_next lcodes llens dcodes dlens o m sx,
  CBytes (o_buf o) (o_pending o) (c_compress_loop fuel lit_bufsize sym_next lcodes llens dcodes dlens (o, m) sx).
Proof. induction fuel; intros; bstart; cbn [c_compress_loop] in *; brun. Qed.

#[export] Instance cb_compress_block o m lit_bufsize sym_next lcodes llens dcodes dlens :
  CBytes (o_buf o) (o_pending o) (c_compress_block (o, m) lit_bufsize sym_next lcodes llens dcodes dlens).
Proof. bstart. unfold c_compress_block in *. brun. Qed.

Lemma cb_tr_stored_block o m buf stored_len last :
  bytes buf -> CBytes (o_buf o) (o_pending o) (c_tr_stored_block (o, m) buf stored_len last).
Proof.
  intros Hb. bstart. unfold c_tr_stored_block in *. brun.
  all: repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H end.
  all: repeat match goal with
       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
       | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
       end.
  - eapply buf_after_trans; [eassumption|].
    match goal with A : buf_after _ _ _ _ |- _ => pose proof A as A' end.
    destruct A' as [_ [_ [R _]]].
    assert (Ls : Zlength (sublist 0 stored_len buf) = stored_len) by (rewrite Zlength_sublist; lia).
    rewrite <- Ls at 2. apply buf_after_copy.
    + lia.
    + rewrite Ls. lia.
    + apply bytes_sublist. exact Hb.
  - subst stored_len. rewrite Z.add_0_r. assumption.
Qed.

Lemma c_tr_flush_block_bytes s m buf stored_len last s' m' k :
  c_tr_flush_block (s, m) buf stored_len last = Some ((s', m'), k) ->
  (forall b, buf = Some b -> bytes b) ->
  buf_after (o_buf (tr_out s)) (o_buf (tr_out s')) (o_pending (tr_out s)) (o_pending (tr_out s')).
Proof.
  intros H Hbuf. unfold c_tr_flush_block in H.
  destruct (if tr_level s >? 0 then _ else _) as [[[[s1 ol] sl] mb]|] eqn:E1;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (O1 : tr_out s1 = tr_out s).
  { destruct (tr_level s >? 0); [|apply some_inj in E1; inversion E1; reflexivity].
    repeat match goal with
    | E : bind ?a _ = Some _ |- _ =>
        let E' := fresh "E" in
        destruct a eqn:E'; unfold bind at 1 in E; cbv beta iota zeta in E; [| discriminate E]
    | x : (_ * _)%type |- _ => destruct x
    | E : (if ?b then _ else _) = Some _ |- _ => destruct b
    end.
    all: repeat match goal with E : Some _ = Some _ |- _ => apply some_inj in E end.
    all: repeat match goal with E : (_, _) = (_, _) |- _ => apply pair_inj in E; destruct E end.
    all: subst.
    all: repeat match goal with E : c_build_bl_tree _ = Some _ |- _ => apply c_build_bl_tree_out in E end.
    all: match goal with E : tr_out _ = tr_out _ |- _ => rewrite E; reflexivity end. }
  rewrite <- O1. clear E1 O1.
  destruct (match buf with Some _ => _ | None => _ end) as [[[o2 m2] kd]|] eqn:E2;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (A2 : buf_after (o_buf (tr_out s1)) (o_buf o2) (o_pending (tr_out s1)) (o_pending o2)).
  { clear H. destruct buf as [b|].
    - assert (Hb : bytes b) by (apply Hbuf; reflexivity).
      destruct (u64 (stored_len + 4) <=? ol).
      + destruct (guard (0 <? Zlength b)); cbv beta iota zeta delta [bind] in E2; [|discriminate E2].
        destruct (c_tr_stored_block (tr_out s1, m) b stored_len last) as [[o3 m3]|] eqn:E3;
          [|discriminate E2].
        apply some_inj in E2. inversion E2; subst.
        apply (cb_tr_stored_block _ _ _ _ _ Hb) in E3. exact E3.
      + repeat bstep. all: cbn [o_pending o_buf set_bits fst snd] in *; bchain; assumption.
    - repeat bstep. all: cbn [o_pending o_buf set_bits fst snd] in *; bchain; assumption. }
  destruct (c_init_block (set_out s1 o2)) as [s3|] eqn:E3;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  apply c_init_block_out in E3. cbn [tr_out set_out] in E3.
  destruct (negb (last =? 0)).
  - destruct (c_bi_windup (tr_out s3, m2)) as [[o4 m4]|] eqn:E4;
      cbv beta iota zeta delta [bind] in H; [|discriminate H].
    apply some_inj in H. inversion H; subst. apply cbytes in E4.
    cbn [tr_out set_out]. eapply buf_after_trans; eassumption.
  - cbv beta iota zeta delta [bind] in H.
    apply some_inj in H. inversion H; subst. cbn [tr_out set_out]. assumption.
Qed.

Theorem bytes_some : bytes_statement.
Proof.
  intros s m buf sl last s' m' k H Hb.
  destruct (c_tr_flush_block_bytes _ _ _ _ _ _ _ _ H Hb) as [_ [L [_ [F B]]]].
  split; [exact L|]. split; [exact F|exact B].
Qed.

(** * deflate() leaves strm->adler a 64-bit value (model)

    In the checked model of deflate.c (DModel4.c_deflate) strm->adler changes only in read_buf (adler32 or crc32
    of the bytes read from next_in: below 2^32 for bytes), in the zlib and gzip header stages (the constants 1
    and 0), in HCRC_UPDATE (crc32 of pending_buf bytes: excluded here by [d_gzhead s = None], the only case the
    clip()-stream laws need) and after the gzip trailer (0).  So it stays within the 64 bits of the z_stream
    field: what the mains of rt_partial, rj_truncated, rj_bad_checksum and rfc_trailing_bytes need from one
    deflate() call to the next (DFacts.cd_range). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.DModel4.
Require Zlib.proof.adler32.Model Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Loops: an invariant [P] of the loop state that [body] keeps, and a property [Q] of the exit value that
    [body] establishes from [P]. *)
Lemma ak_loop {A B} d (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) :
  (forall a x, body a = Some x -> P a -> match x with inl a' => P a' | inr r => Q r end) ->
  forall a r, loop d body a = Some r -> P a -> Q r.
Proof.
  intros Hb a r H. apply loop_runs in H. induction H as [a r E|a a' r E _ IH]; intros Ha.
  - exact (Hb _ _ E Ha).
  - apply IH. exact (Hb _ _ E Ha).
Qed.

Lemma ak_some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.

(** The kernel must never unfold the loops (binary fuel 2^40). *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

(** Splitting the model functions along their memory accesses and case distinctions (as in GrowCompressR). *)
Ltac astep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply ak_some_inj in H
  | H : None = Some _ |- _ => discriminate H
  | H : inl _ = inl _ |- _ => injection H as H
  | H : inr _ = inr _ |- _ => injection H as H
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : (_, _) = (_, _) |- _ => injection H as; subst
  | H : ?x = _ |- _ => is_var x; subst x
  | H : _ = ?x |- _ => is_var x; subst x
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | H : (if ?b then _ else _) = Some _ |- _ => destruct b eqn:?
  | H : match ?x with _ => _ end = Some _ |- _ => destruct x eqn:?
  end.

Ltac adec := repeat (astep; cbv beta iota zeta in *).

Ltac aconj := repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac znorm := cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg set_z_in
  set_z_next_in set_z_avail_in set_z_total_in set_z_out set_z_avail_out set_z_total_out set_z_adler set_z_msg
  fst snd] in *.

(** The stream of a step of a main loop: the loop state or the exit value. *)
Definition xz (x : (dstate * strm) + dexit) : strm :=
  match x with inl (_, z) => z | inr (_, z, _) => z end.

Section Keep.

(** The input of the call: bytes. *)
Context (inp : list Z) (Hinp : Forall (fun b => 0 <= b < 256) inp).

(** The invariant of the stream during the call: its input is [inp] and its adler field a 64-bit value. *)
Definition zok (z : strm) : Prop := z_in z = inp /\ 0 <= z_adler z <= 18446744073709551615.

Ltac zclose :=
  cbn [xz] in *; cbv beta iota in *; unfold zok in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  znorm; aconj; (split; [congruence | lia]).

Lemma ak_bytes d : (exists lo n, rds inp lo n = Some d) -> Zlib.proof.adler32.Bytes.is_bytes d.
Proof.
  intros (lo & n & E). unfold rds in E. destruct (_ && _ && _); [|discriminate].
  injection E as <-. apply Forall_sublist. unfold Zlib.proof.adler32.Bytes.is_bytes.
  eapply Forall_impl; [|exact Hinp]. intros b Hb. change (0 <= b <= 255). cbv beta in Hb. lia.
Qed.

Lemma ak_read_buf s z n z' d : c_read_buf s z n = Some (z', d) -> zok z -> zok z'.
Proof.
  unfold c_read_buf. intros H Hz. adec; [zclose|].
  match goal with E : rds _ _ _ = Some ?l |- _ =>
    assert (B : Zlib.proof.adler32.Bytes.is_bytes l)
      by (apply ak_bytes; destruct Hz as [Hi _]; cbn [z_in set_z_avail_in] in E; rewrite Hi in E; eauto) end.
  unfold zok in *. destruct Hz as [Hi Ha].
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)]; znorm; (split; [exact Hi|]).
  - pose proof (Zlib.proof.adler32.Model.adler32_z_val_range (z_adler z) _ B). lia.
  - pose proof (Zlib.proof.crc32.Combine.ref_crc32_range (z_adler z) _ B).
    unfold Zlib.proof.crc32.GF2.is32 in *. lia.
  - exact Ha.
Qed.

Lemma ak_out_put z b z' : out_put z b = Some z' -> zok z -> zok z'.
Proof. unfold out_put. intros H Hz. adec. zclose. Qed.

(** The facts of the callees, applied to their results; [zf] is extended after each group of lemmas. *)
Ltac zf E := first [apply ak_read_buf in E | apply ak_out_put in E].
Ltac zfacts := repeat match goal with E : _ = Some _ |- _ => zf E; [|zclose] end.

Lemma ak_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') -> zok z -> zok z'.
Proof.
  unfold c_flush_pending. intros H Hz. adec; zfacts; zclose.
Qed.

Ltac zf E ::= first [apply ak_read_buf in E | apply ak_out_put in E | apply ak_flush_pending in E].

(** *** fill_window *)
Lemma ak_fw_body a x : fw_body a = Some x -> zok (snd a) ->
  match x with inl a' => zok (snd a') | inr r => zok (snd r) end.
Proof. destruct a as [s z]. unfold fw_body. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_fill_window s z s' z' : c_fill_window s z = Some (s', z') -> zok z -> zok z'.
Proof.
  unfold c_fill_window. intros H Hz. adec.
  match goal with E : loop _ _ _ = Some _ |- _ =>
    exact (ak_loop _ _ (fun a => zok (snd a)) (fun r => zok (snd r)) ak_fw_body _ _ E Hz) end.
Qed.

(** *** FLUSH_BLOCK and the common pieces of the main loops *)
Lemma ak_flush_block_only s z last s' z' : c_flush_block_only s z last = Some (s', z') -> zok z -> zok z'.
Proof. unfold c_flush_block_only. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_flush_block s z last s' z' r : c_flush_block s z last = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_flush_block. intros H Hz. adec.
  all: apply ak_flush_block_only in E; [zclose | exact Hz].
Qed.

Ltac zf E ::= first [apply ak_read_buf in E | apply ak_out_put in E | apply ak_flush_pending in E
  | apply ak_fill_window in E | apply ak_flush_block_only in E | apply ak_flush_block in E].

Lemma ak_bflush s z b x : c_bflush s z b = Some x -> zok z -> zok (xz x).
Proof. unfold c_bflush. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_refill need flush s z x : c_refill need flush s z = Some x -> zok z -> zok (xz x).
Proof. unfold c_refill. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_deflate_tail s z f s' z' r : c_deflate_tail s z f = Some (s', z', r) -> zok z -> zok z'.
Proof. unfold c_deflate_tail. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_main_loop (body : dstate * strm -> option ((dstate * strm) + dexit)) :
  (forall a x, body a = Some x -> zok (snd a) -> zok (xz x)) ->
  forall a s' z' r, loop FUEL body a = Some (s', z', r) -> zok (snd a) -> zok z'.
Proof.
  intros Hb a s' z' r H Ha.
  refine (ak_loop _ _ (fun a => zok (snd a)) (fun r => zok (snd (fst r))) _ a _ H Ha).
  intros a1 x E Ha1. specialize (Hb _ _ E Ha1). destruct x as [[s2 z2]|[[s2 z2] r2]]; exact Hb.
Qed.

Ltac zf E ::= first [apply ak_read_buf in E | apply ak_out_put in E | apply ak_flush_pending in E
  | apply ak_fill_window in E | apply ak_flush_block_only in E | apply ak_flush_block in E
  | apply ak_deflate_tail in E].

(** The facts of c_bflush and c_refill (whose results are loop steps) applied to their results. *)
Ltac zx :=
  repeat match goal with
  | E : c_bflush _ _ _ = Some _ |- _ => apply ak_bflush in E; [|zclose]
  | E : c_refill _ _ _ _ = Some _ |- _ => apply ak_refill in E; [|zclose]
  end; cbn [xz] in *.

(** *** deflate_fast, deflate_slow, deflate_rle, deflate_huff *)
Lemma ak_df_step s z x : df_step s z = Some x -> zok z -> zok (xz x).
Proof. unfold df_step. intros H Hz. adec; zfacts; zx; zclose. Qed.

Lemma ak_df_body flush a x : df_body flush a = Some x -> zok (snd a) -> zok (xz x).
Proof.
  destruct a as [s z]. unfold df_body. intros H Hz. adec; zfacts; zx;
  repeat match goal with E : df_step _ _ = Some _ |- _ => apply ak_df_step in E; [|zclose] end; zclose.
Qed.

Lemma ak_deflate_fast s z f s' z' r : c_deflate_fast s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_deflate_fast. intros H Hz. adec;
  match goal with E : loop FUEL _ _ = Some _ |- _ => apply (ak_main_loop _ (ak_df_body f)) in E; [|zclose] end;
  zfacts; zclose.
Qed.

Lemma ak_dsl_step s z x : dsl_step s z = Some x -> zok z -> zok (xz x).
Proof. unfold dsl_step. intros H Hz. adec; zfacts; zx; zclose. Qed.

Lemma ak_dsl_body flush a x : dsl_body flush a = Some x -> zok (snd a) -> zok (xz x).
Proof.
  destruct a as [s z]. unfold dsl_body. intros H Hz. adec; zfacts; zx;
  repeat match goal with E : dsl_step _ _ = Some _ |- _ => apply ak_dsl_step in E; [|zclose] end; zclose.
Qed.

Lemma ak_deflate_slow s z f s' z' r : c_deflate_slow s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_deflate_slow. intros H Hz. adec;
  match goal with E : loop FUEL _ _ = Some _ |- _ => apply (ak_main_loop _ (ak_dsl_body f)) in E; [|zclose] end;
  zfacts; zclose.
Qed.

Lemma ak_rle_step s z x : rle_step s z = Some x -> zok z -> zok (xz x).
Proof. unfold rle_step. intros H Hz. adec; zfacts; zx; zclose. Qed.

Lemma ak_rle_body flush a x : rle_body flush a = Some x -> zok (snd a) -> zok (xz x).
Proof.
  destruct a as [s z]. unfold rle_body. intros H Hz. adec; zfacts; zx;
  repeat match goal with E : rle_step _ _ = Some _ |- _ => apply ak_rle_step in E; [|zclose] end; zclose.
Qed.

Lemma ak_deflate_rle s z f s' z' r : c_deflate_rle s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_deflate_rle. intros H Hz. adec;
  match goal with E : loop FUEL _ _ = Some _ |- _ => apply (ak_main_loop _ (ak_rle_body f)) in E; [|zclose] end;
  zfacts; zclose.
Qed.

Lemma ak_huff_body flush a x : huff_body flush a = Some x -> zok (snd a) -> zok (xz x).
Proof. destruct a as [s z]. unfold huff_body. intros H Hz. adec; zfacts; zx; zclose. Qed.

Lemma ak_deflate_huff s z f s' z' r : c_deflate_huff s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_deflate_huff. intros H Hz. adec;
  match goal with E : loop FUEL _ _ = Some _ |- _ => apply (ak_main_loop _ (ak_huff_body f)) in E; [|zclose] end;
  zfacts; zclose.
Qed.

(** *** deflate_stored *)
Lemma ak_ds_body flush mb a x : ds_body flush mb a = Some x -> zok (snd a) ->
  match x with inl a' => zok (snd a') | inr r => zok (snd (fst r)) end.
Proof. destruct a as [s z]. unfold ds_body. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_deflate_stored s z f s' z' r : c_deflate_stored s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_deflate_stored. intros H Hz. adec;
  match goal with E : loop FUEL _ _ = Some _ |- _ =>
    apply (ak_loop _ _ (fun a => zok (snd a)) (fun r => zok (snd (fst r))) (ak_ds_body _ _)) in E; [|zclose] end;
  zfacts; zclose.
Qed.

(** *** The dispatch, the compression stage and the trailer of deflate() *)
Lemma ak_compress_func s z f s' z' r : c_compress_func s z f = Some (s', z', r) -> zok z -> zok z'.
Proof.
  unfold c_compress_func. intros H Hz. adec.
  all: first [ apply ak_deflate_stored in H | apply ak_deflate_fast in H | apply ak_deflate_slow in H
             | apply ak_deflate_rle in H | apply ak_deflate_huff in H ]; [exact H | exact Hz].
Qed.

Ltac zf E ::= first [apply ak_read_buf in E | apply ak_out_put in E | apply ak_flush_pending in E
  | apply ak_fill_window in E | apply ak_flush_block_only in E | apply ak_flush_block in E
  | apply ak_deflate_tail in E | apply ak_compress_func in E].

Lemma ak_deflate_compress s z f s' z' o : c_deflate_compress s z f = Some (s', z', o) -> zok z -> zok z'.
Proof. unfold c_deflate_compress. intros H Hz. adec; zfacts; zclose. Qed.

Lemma ak_deflate_trailer s z f s' z' c : c_deflate_trailer s z f = Some (s', z', c) -> zok z -> zok z'.
Proof. unfold c_deflate_trailer. intros H Hz. adec; zfacts; zclose. Qed.

End Keep.

(** ** The header stages keep the gz_header pointer (here NULL) *)
Ltac gnorm := cbn [d_gzhead set_d_status set_d_po set_d_wrap set_d_gzindex set_d_method set_d_last_flush
  set_d_tr set_d_pbm set_d_out fst snd] in *.

Lemma dg_dput_byte s c s' : c_dput_byte s c = Some s' -> d_gzhead s' = d_gzhead s.
Proof. unfold c_dput_byte. intros H. adec. gnorm. reflexivity. Qed.

Lemma dg_dput_bytes l : forall s s', c_dput_bytes s l = Some s' -> d_gzhead s' = d_gzhead s.
Proof.
  induction l as [|c l IH]; intros s s' H; cbn [c_dput_bytes] in H; adec; [reflexivity|].
  match goal with E : c_dput_byte _ _ = Some _ |- _ => apply dg_dput_byte in E end.
  apply IH in H. congruence.
Qed.

Lemma dg_putShortMSB s b s' : c_putShortMSB s b = Some s' -> d_gzhead s' = d_gzhead s.
Proof.
  unfold c_putShortMSB. intros H. adec.
  repeat match goal with E : c_dput_byte _ _ = Some _ |- _ => apply dg_dput_byte in E end. congruence.
Qed.

Lemma dg_flush_pending s z s' z' : c_flush_pending s z = Some (s', z') -> d_gzhead s' = d_gzhead s.
Proof.
  unfold c_flush_pending. intros H. adec.
  all: repeat match goal with |- context [if ?b then _ else _] => destruct b end; gnorm; reflexivity.
Qed.

(** The facts of the header stages: the stream stays fine and the gz_header pointer is kept. *)
Ltac dgf :=
  repeat match goal with
  | E : c_dput_bytes _ _ = Some _ |- _ => apply dg_dput_bytes in E
  | E : c_dput_byte _ _ = Some _ |- _ => apply dg_dput_byte in E
  | E : c_putShortMSB _ _ = Some _ |- _ => apply dg_putShortMSB in E
  | E : c_flush_pending _ _ = Some (?s, ?z) |- _ =>
      let D := fresh "D" in
      lazymatch goal with _ : d_gzhead s = _ |- _ => fail | _ => idtac end;
      pose proof (dg_flush_pending _ _ _ _ E) as D
  end.

Ltac zfp inp :=
  repeat match goal with
  | E : c_flush_pending _ _ = Some _ |- _ => apply (ak_flush_pending inp) in E; [|zclose_g inp]
  end
with zclose_g inp :=
  cbv beta iota in *; unfold zok in *;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  znorm; aconj; (split; [congruence | lia]).

Ltac gclose :=
  gnorm;
  repeat match goal with
  | H : context [d_gzhead (if ?b then _ else _)] |- _ => destruct b
  | |- context [d_gzhead (if ?b then _ else _)] => destruct b
  end; gnorm; congruence.

(** After a header stage: the stream invariant and a NULL gz_header pointer. *)
Definition sok (inp : list Z) (r : dres) : Prop :=
  zok inp (snd (fst r)) /\ d_gzhead (fst (fst r)) = None.

Lemma ak_entry inp s z f r : c_deflate_entry s z f = Some r -> zok inp z -> d_gzhead s = None -> sok inp r.
Proof.
  unfold c_deflate_entry, then_stage, sok. intros H Hz Hg. adec; dgf; zfp inp;
    (split; [zclose_g inp | gclose]).
Qed.

Lemma ak_zlib_header inp s z r : c_deflate_zlib_header s z = Some r -> zok inp z -> d_gzhead s = None -> sok inp r.
Proof.
  unfold c_deflate_zlib_header, c_flush_or_return, sok. intros H Hz Hg. adec; dgf; zfp inp;
    (split; [zclose_g inp | gclose]).
Qed.

Lemma ak_gzip_header inp s z r : c_deflate_gzip_header s z = Some r -> zok inp z -> d_gzhead s = None -> sok inp r.
Proof.
  unfold c_deflate_gzip_header, c_flush_or_return, sok. intros H Hz Hg. adec; dgf; gnorm; try congruence; zfp inp;
    (split; [zclose_g inp | gclose]).
Qed.

(** With a NULL gz_header the states EXTRA .. HCRC are a NULL dereference ([None]); otherwise these stages
    do nothing. *)
Lemma ak_null_stage (st : dstate -> strm -> option dres) s z r :
  (forall s z, d_gzhead s = None -> st s z = None \/ st s z = Some (s, z, None)) ->
  st s z = Some r -> d_gzhead s = None -> r = (s, z, None).
Proof. intros Hst H Hg. destruct (Hst s z Hg) as [E|E]; rewrite E in H; congruence. Qed.

Lemma null_extra s z : d_gzhead s = None -> c_deflate_extra s z = None \/ c_deflate_extra s z = Some (s, z, None).
Proof. intros Hg. unfold c_deflate_extra, c_gzhead. rewrite Hg. destruct (_ =? _); auto. Qed.
Lemma null_name s z : d_gzhead s = None -> c_deflate_name s z = None \/ c_deflate_name s z = Some (s, z, None).
Proof. intros Hg. unfold c_deflate_name, c_gzhead. rewrite Hg. destruct (_ =? _); auto. Qed.
Lemma null_comment s z : d_gzhead s = None ->
  c_deflate_comment s z = None \/ c_deflate_comment s z = Some (s, z, None).
Proof. intros Hg. unfold c_deflate_comment, c_gzhead. rewrite Hg. destruct (_ =? _); auto. Qed.
Lemma null_hcrc s z : d_gzhead s = None -> c_deflate_hcrc s z = None \/ c_deflate_hcrc s z = Some (s, z, None).
Proof. intros Hg. unfold c_deflate_hcrc, c_gzhead. rewrite Hg. destruct (_ =? _); auto. Qed.


(** A chain of stages: [P] holds after the first stage, gives [Q] when the chain stops there, and [Q] holds after
    the rest when it continues. *)
Lemma then_stage_ok (P Q : dres -> Prop) r k x :
  then_stage r k = Some x -> (forall y, r = Some y -> P y) -> (forall y, P y -> Q y) ->
  (forall s z x, P (s, z, None) -> k s z = Some x -> Q x) -> Q x.
Proof.
  unfold then_stage. intros H HP HPQ Hk. destruct r as [[[s z] o]|]; [|discriminate].
  cbn [bind] in H. specialize (HP _ eq_refl). destruct o as [c|].
  - injection H as <-. apply HPQ. exact HP.
  - exact (Hk _ _ _ HP H).
Qed.

(** After any stage: the stream invariant. *)
Definition zq (inp : list Z) (r : dres) : Prop := zok inp (snd (fst r)).

Lemma sok_zq inp r : sok inp r -> zq inp r.
Proof. intros [A _]. exact A. Qed.

Lemma null_sok inp (st : dstate -> strm -> option dres) s z r :
  (forall s z, d_gzhead s = None -> st s z = None \/ st s z = Some (s, z, None)) ->
  st s z = Some r -> sok inp (s, z, None) -> sok inp r.
Proof. intros Hst H [Hz Hg]. cbn [fst snd] in *. rewrite (ak_null_stage st s z r Hst H Hg). split; assumption. Qed.

Lemma c_deflate_adler_range : forall s z flush s' z' code,
  d_gzhead s = None -> Forall (fun b => 0 <= b < 256) (z_in z) ->
  0 <= z_adler z <= 18446744073709551615 ->
  c_deflate s z flush = Some (s', z', code) ->
  0 <= z_adler z' <= 18446744073709551615.
Proof.
  intros s z flush s' z' code Hg Hin Ha H.
  set (inp := z_in z) in *.
  assert (Hz : zok inp z) by (split; [reflexivity | exact Ha]).
  enough (zok inp z') by (destruct H0; assumption).
  unfold c_deflate in H.
  destruct (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)).
  { injection H as <- <- <-. exact Hz. }
  destruct (then_stage (c_deflate_entry s z flush) _) as [[[s1 z1] o]|] eqn:R; [|discriminate].
  cbn [bind] in H.
  assert (Z1 : zq inp (s1, z1, o)).
  { refine (then_stage_ok (sok inp) (zq inp) _ _ _ R _ (sok_zq inp) _).
    { intros y Ey. exact (ak_entry inp _ _ _ _ Ey Hz Hg). }
    intros s2 z2 x2 S2 E2. destruct S2 as [Hz2 Hg2]; cbn [fst snd] in *.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E2 _ (sok_zq inp) _).
    { intros y Ey. exact (ak_zlib_header inp _ _ _ Ey Hz2 Hg2). }
    intros s3 z3 x3 S3 E3. destruct S3 as [Hz3 Hg3]; cbn [fst snd] in *.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E3 _ (sok_zq inp) _).
    { intros y Ey. exact (ak_gzip_header inp _ _ _ Ey Hz3 Hg3). }
    intros s4 z4 x4 S4 E4.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E4 _ (sok_zq inp) _).
    { intros y Ey. exact (null_sok inp _ _ _ _ null_extra Ey S4). }
    intros s5 z5 x5 S5 E5.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E5 _ (sok_zq inp) _).
    { intros y Ey. exact (null_sok inp _ _ _ _ null_name Ey S5). }
    intros s6 z6 x6 S6 E6.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E6 _ (sok_zq inp) _).
    { intros y Ey. exact (null_sok inp _ _ _ _ null_comment Ey S6). }
    intros s7 z7 x7 S7 E7.
    refine (then_stage_ok (sok inp) (zq inp) _ _ _ E7 _ (sok_zq inp) _).
    { intros y Ey. exact (null_sok inp _ _ _ _ null_hcrc Ey S7). }
    intros s8 z8 [[s9 z9] o9] [Hz8 _] E8. cbn [fst snd] in Hz8.
    exact (ak_deflate_compress inp Hin _ _ _ _ _ _ E8 Hz8). }
  unfold zq in Z1; cbn [fst snd] in Z1.
  destruct o as [c|].
  - injection H as <- <- <-. exact Z1.
  - exact (ak_deflate_trailer inp _ _ _ _ _ _ H Z1).
Qed.

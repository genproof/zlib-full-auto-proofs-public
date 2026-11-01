(** * deflate() on [Iapi] without its size limits: stages 2..7, the headers

    [LTApiHdrSt.hdr_stage_ok] for [MidW] (DetApiMid.v), by [hf_run_wide] (DetWide.v) instead of hf_run; and the
    header stages keep strm->adler below 2^32 (they set it to 1 / 0 or to a CRC-32). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetApiMid.
Require Import Zlib.proof.deflate.LTApiHdrSt.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.


(** ** The header stages keep strm->adler a 32-bit value

    The stages set strm->adler to 1 (zlib), to 0 (gzip), or to a CRC-32 of bytes read from pending_buf (the
    gzip header CRC, HCRC_UPDATE).  A CRC-32 is below 2^32 when it is computed over bytes, so the invariant
    carried through the stages is that the defined bytes of pending_buf are bytes ([pbq]); the gzip extra
    field, which the EXTRA stage copies into pending_buf, is bytes too. *)
Definition pbq (s : dstate) : Prop :=
  mb_ok (d_pb s) /\ (forall h x, d_gzhead s = Some h -> gz_extra h = Some x -> bytes x).

Definition adq (z : strm) : Prop := 0 <= z_adler z < 4294967296.

(** [mb_ok] of the pending buffer held in a bit-output state. *)
Definition cok (om : cout) : Prop := mb_ok (mkMB (o_buf (fst om)) (snd om)).

Lemma cok_put_byte : forall om c om', c_put_byte om c = Some om' -> cok om -> cok om'.
Proof.
  intros [o m] c om' H [L B]. unfold c_put_byte, wr, in_range, bind in H. cbn in L, B.
  destruct ((0 <=? o_pending o) && (o_pending o <? Zlength (o_buf o))) eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  inversion H; subst; clear H. unfold cok, mb_ok; simpl. split.
  - rewrite !Zlength_upd_Znth_any. exact L.
  - intros i Hi Hd. rewrite Zlength_upd_Znth_any in Hi.
    destruct (Z.eq_dec i (o_pending o)) as [->|Hne].
    + rewrite upd_Znth_same by lia. apply hs_u8.
    + rewrite upd_Znth_diff in Hd by lia. rewrite upd_Znth_diff by lia. apply B; auto.
Qed.

Lemma cok_put_short : forall om w om', c_put_short om w = Some om' -> cok om -> cok om'.
Proof.
  intros om w om' H C. unfold c_put_short, bind in H.
  destruct (c_put_byte om _) as [om1|] eqn:E; [|discriminate].
  eapply cok_put_byte; [exact H|]. eapply cok_put_byte; [exact E|exact C].
Qed.

Lemma cok_flush_bits : forall om om', c_tr_flush_bits om = Some om' -> cok om -> cok om'.
Proof.
  intros [o m] om' H C. unfold c_tr_flush_bits, c_bi_flush, bind in H.
  destruct (o_bi_valid o =? 16).
  - destruct (c_put_short (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
    inversion H; subst. exact (cok_put_short _ _ _ E C).
  - destruct (o_bi_valid o >=? 8).
    + destruct (c_put_byte (o, m) (o_bi_buf o)) as [[o1 m1]|] eqn:E; [|discriminate].
      inversion H; subst. exact (cok_put_byte _ _ _ E C).
    + inversion H; subst. exact C.
Qed.

Lemma pbq_ext : forall s s', pbq s -> d_pb s' = d_pb s -> d_gzhead s' = d_gzhead s -> pbq s'.
Proof. intros s s' [A B] E1 E2. split; [rewrite E1; exact A|rewrite E2; exact B]. Qed.

Lemma pbq_out : forall s o, pbq s -> cok o -> pbq (set_d_out s o).
Proof. intros s [o m] [_ B] C. split; [exact C|exact B]. Qed.

Lemma pbq_dput_byte : forall s c s', c_dput_byte s c = Some s' -> pbq s -> pbq s'.
Proof.
  intros s c s' H P. unfold c_dput_byte, bind in H.
  destruct (c_put_byte (d_out s) c) as [o|] eqn:E; [|discriminate]. inversion H; subst.
  apply pbq_out; [exact P|]. eapply cok_put_byte; [exact E|]. apply P.
Qed.

Lemma pbq_dput_bytes : forall l s s', c_dput_bytes s l = Some s' -> pbq s -> pbq s'.
Proof.
  induction l as [|c l IH]; intros s s' H P; cbn in H; [inversion H; subst; exact P|].
  unfold bind in H. destruct (c_dput_byte s c) as [s1|] eqn:E; [|discriminate].
  exact (IH _ _ H (pbq_dput_byte _ _ _ E P)).
Qed.

Lemma pbq_putShortMSB : forall s b s', c_putShortMSB s b = Some s' -> pbq s -> pbq s'.
Proof.
  intros s b s' H P. unfold c_putShortMSB, bind in H.
  destruct (c_dput_byte s _) as [s1|] eqn:E; [|discriminate].
  exact (pbq_dput_byte _ _ _ H (pbq_dput_byte _ _ _ E P)).
Qed.

Lemma pbq_flush : forall s z s' z', c_flush_pending s z = Some (s', z') -> pbq s -> pbq s' /\ z_adler z' = z_adler z.
Proof.
  intros s z s' z' H P. unfold c_flush_pending, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|] eqn:E; [|discriminate].
  assert (P1 : pbq (set_d_out s o)) by (apply pbq_out; [exact P|]; eapply cok_flush_bits; [exact E|apply P]).
  cbv zeta in H.
  match type of H with context [if ?c =? 0 then _ else _] => destruct (c =? 0) end.
  { inversion H; subst. split; [exact P1|reflexivity]. }
  match type of H with context [mb_read ?b ?lo ?len] => destruct (mb_read b lo len) as [l|] end;
    [|discriminate].
  unfold out_put in H.
  match type of H with context [Zlength ?l <=? ?a] => destruct (Zlength l <=? a) end; [|discriminate].
  match type of H with context [if ?c =? 0 then _ else _] => destruct (c =? 0) end;
    inversion H; subst; split; try reflexivity; eapply pbq_ext; try exact P1; reflexivity.
Qed.

Lemma pbq_mb_read : forall s lo len l, mb_read (d_pb s) lo len = Some l -> pbq s -> bytes l.
Proof.
  intros s lo len l H [A _]. unfold mb_read in H.
  destruct ((0 <=? len) && mb_definedb (d_pb s) lo (lo + len)) eqn:E; [|discriminate].
  inversion H; subst; clear H. apply andb_prop in E as [_ E].
  unfold mb_definedb in E. apply andb_prop in E as [E E2]. apply andb_prop in E as [E0 E1].
  apply Z.leb_le in E0, E1.
  apply (fp_bytes (d_pb s)); [exact A|]. split; [lia|split; [lia|]].
  intros i Hi. rewrite forallb_forall in E2. specialize (E2 (lo + Z.of_nat (Z.to_nat (i - lo)))).
  rewrite Z2Nat.id in E2 by lia. replace (lo + (i - lo)) with i in E2 by lia. apply E2.
  apply in_map_iff. exists (Z.to_nat (i - lo)). split; [rewrite Z2Nat.id by lia; lia|].
  apply in_seq. lia.
Qed.

Lemma crc_adq : forall c l, bytes l -> 0 <= Zlib.proof.crc32.Model.ref_crc32 c l < 4294967296.
Proof.
  intros c l B. apply Zlib.proof.crc32.Combine.ref_crc32_range. apply bytes_is_bytes. exact B.
Qed.

Lemma adq_hcrc : forall h s z beg z', c_hcrc_update h s z beg = Some z' -> pbq s -> adq z -> adq z'.
Proof.
  intros h s z beg z' H P A. unfold c_hcrc_update, bind in H.
  destruct (_ && _); [|inversion H; subst; exact A].
  destruct (mb_read (d_pb s) beg (d_pending s - beg)) as [l|] eqn:E; [|discriminate].
  inversion H; subst. unfold adq; cbn. apply crc_adq. exact (pbq_mb_read _ _ _ _ E P).
Qed.

Lemma mb_ok_write : forall b lo bs b', mb_write b lo bs = Some b' -> bytes bs -> mb_ok b -> mb_ok b'.
Proof.
  intros [v d] lo bs b' H Hb [L B]. unfold mb_write in H; cbn [mb_val mb_def] in *.
  destruct ((0 <=? lo) && (lo + Zlength bs <=? Zlength v)) eqn:E; [|discriminate].
  apply andb_prop in E as [E0 E1]. apply Z.leb_le in E0, E1. inversion H; subst; clear H.
  pose proof (Zlength_nonneg bs).
  assert (Lr : Zlength (repeat true (Z.to_nat (Zlength bs))) = Zlength bs)
    by (rewrite Zlength_repeat; lia).
  unfold mb_ok; cbn [mb_val mb_def]; split.
  - rewrite !Zlength_app, !Zlength_sublist, Lr by lia. lia.
  - intros i Hi Hd. rewrite !Zlength_app, !Zlength_sublist in Hi by lia.
    destruct (Z_lt_le_dec i lo).
    + rewrite app_Znth1 in Hd by (rewrite Zlength_sublist; lia). rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist in Hd by lia. rewrite Znth_sublist by lia.
      apply B; [lia|]. rewrite Z.add_0_r in Hd. rewrite Z.add_0_r. exact Hd.
    + rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      destruct (Z_lt_le_dec (i - (lo - 0)) (Zlength bs)).
      * rewrite app_Znth1 by lia. apply Forall_Znth; [lia|exact Hb].
      * rewrite app_Znth2 in Hd by (rewrite ?Zlength_sublist, ?Lr; lia).
        rewrite app_Znth2 in Hd by (rewrite ?Zlength_sublist, ?Lr; lia).
        rewrite app_Znth2 by lia. rewrite Zlength_sublist, Lr in Hd by lia.
        rewrite Znth_sublist in Hd by lia. rewrite Znth_sublist by lia. apply B; [lia|].
        replace (i - (lo - 0) - Zlength bs + (lo + Zlength bs)) with i in * by lia. exact Hd.
Qed.

Lemma pbq_write : forall s lo bs pb, mb_write (d_pb s) lo bs = Some pb -> bytes bs -> pbq s -> pbq (set_d_pb s pb).
Proof.
  intros s lo bs [v d] H Hb P. unfold set_d_pb. apply pbq_out; [exact P|].
  unfold cok; cbn. exact (mb_ok_write _ _ _ _ H Hb (proj1 P)).
Qed.

Lemma rds_bytes : forall x lo n l, rds x lo n = Some l -> bytes x -> bytes l.
Proof.
  intros x lo n l H B. unfold rds in H. destruct (_ && _); inversion H; subst. apply Forall_sublist. exact B.
Qed.


Lemma adq_flush : forall s z s' z', c_flush_pending s z = Some (s', z') -> pbq s -> adq z -> adq z'.
Proof. intros s z s' z' H P A. unfold adq. rewrite (proj2 (pbq_flush _ _ _ _ H P)). exact A. Qed.

Lemma pbq_extra : forall s h x, pbq s -> c_gzhead s = Some h -> gz_extra h = Some x -> bytes x.
Proof. intros s h x [_ B] E1 E2. exact (B h x E1 E2). Qed.

Definition pa4 (a : dstate * strm * Z * Z) : Prop := let '(s, z, _, _) := a in pbq s /\ adq z.
Definition pa3 (a : dstate * strm * Z) : Prop := let '(s, z, _) := a in pbq s /\ adq z.

(* the kernel otherwise unfolds these when checking the case analyses below *)
Local Strategy opaque [c_flush_pending c_hcrc_update mb_write mb_read rds c_dput_byte c_dput_bytes c_putShortMSB loop loop2].

(** One step back from [pbq s'] / [adq z'] after a case analysis of a stage ([hs_go]): through a setter or an
    operation the stage made. *)
Ltac hq_base :=
  first
  [ assumption
  | match goal with
    | |- _ /\ _ => split
    | |- pbq (set_d_status ?s _) => apply (pbq_ext s); [|reflexivity|reflexivity]
    | |- pbq (set_d_last_flush ?s _) => apply (pbq_ext s); [|reflexivity|reflexivity]
    | |- pbq (set_d_gzindex ?s _) => apply (pbq_ext s); [|reflexivity|reflexivity]
    | |- pbq (set_d_pending ?s _) => apply (pbq_ext s); [|reflexivity|reflexivity]
    | E : mb_write (d_pb ?s) _ ?bs = Some ?pb |- pbq (set_d_pb ?s ?pb) => apply (pbq_write s _ bs pb E)
    | E : rds _ _ _ = Some ?l |- bytes ?l => eapply rds_bytes; [exact E|]
    | E : c_dput_byte _ _ = Some ?s |- pbq ?s => apply (pbq_dput_byte _ _ _ E)
    | E : c_dput_bytes _ _ = Some ?s |- pbq ?s => apply (pbq_dput_bytes _ _ _ E)
    | E : c_putShortMSB _ _ = Some ?s |- pbq ?s => apply (pbq_putShortMSB _ _ _ E)
    | E : c_flush_pending _ _ = Some (?s, _) |- pbq ?s => eapply proj1; apply (pbq_flush _ _ _ _ E)
    | E : c_flush_pending _ _ = Some (_, ?z) |- adq ?z => apply (adq_flush _ _ _ _ E)
    | E : c_hcrc_update _ _ _ _ = Some ?z |- adq ?z => apply (adq_hcrc _ _ _ _ _ E)
    | |- adq (set_z_adler _ (Zlib.proof.crc32.Model.ref_crc32 _ ?l)) =>
        unfold adq; cbn [z_adler set_z_adler]; apply crc_adq;
        match goal with E : mb_read (d_pb _) _ _ = Some l |- _ => apply (pbq_mb_read _ _ _ _ E) end
    | |- adq (set_z_adler _ _) => unfold adq; cbn [z_adler set_z_adler]; lia
    | E1 : c_gzhead ?s = Some ?h, E2 : gz_extra ?h = Some ?x |- bytes ?x =>
        apply (pbq_extra s h x); [|exact E1|exact E2]
    end ].

Lemma hq_extra_body : forall h x s z beg lft r, extra_body h x (s, z, beg, lft) = Some r ->
  bytes x -> pbq s -> adq z ->
  match r with inl a => pa4 a | inr (inl a) => pa4 a | inr (inr (s, z)) => pbq s /\ adq z end.
Proof.
  intros h x s z beg lft r H Hx P A. unfold extra_body in H.
  hs_go H; inversion H; subst; cbv beta iota delta [pa4]; repeat hq_base.
Qed.

Lemma hq_str_body : forall h x s z beg r, str_body h x (s, z, beg) = Some r -> pbq s -> adq z ->
  match r with inl a => pa3 a | inr (inl a) => pa3 a | inr (inr (s, z)) => pbq s /\ adq z end.
Proof.
  intros h x s z beg r H P A. unfold str_body in H.
  hs_go H; inversion H; subst; cbv beta iota delta [pa3]; repeat hq_base.
Qed.

Lemma hq_extra_loop : forall h x a r, loop FUEL (extra_body h x) a = Some r -> bytes x -> pa4 a ->
  match r with inl a' => pa4 a' | inr (s, z) => pbq s /\ adq z end.
Proof.
  intros h x a r L Hx. apply loop_runs in L. revert a r L.
  apply (hs_runs _ pa4 (fun r => match r with inl a' => pa4 a' | inr (s, z) => pbq s /\ adq z end)).
  - intros [[[s z] beg] lft] a' [P A] H. exact (hq_extra_body _ _ _ _ _ _ _ H Hx P A).
  - intros [[[s z] beg] lft] r [P A] H. exact (hq_extra_body _ _ _ _ _ _ _ H Hx P A).
Qed.

Lemma hq_str_loop : forall h x a r, loop FUEL (str_body h x) a = Some r -> pa3 a ->
  match r with inl a' => pa3 a' | inr (s, z) => pbq s /\ adq z end.
Proof.
  intros h x a r L. apply loop_runs in L. revert a r L.
  apply (hs_runs _ pa3 (fun r => match r with inl a' => pa3 a' | inr (s, z) => pbq s /\ adq z end)).
  - intros [[s z] beg] a' [P A] H. exact (hq_str_body _ _ _ _ _ _ H P A).
  - intros [[s z] beg] r [P A] H. exact (hq_str_body _ _ _ _ _ _ H P A).
Qed.

(** [hq_base] and the loops of the EXTRA / NAME / COMMENT stages. *)
Ltac hq_close :=
  repeat first
  [ hq_base
  | match goal with
    | E : loop FUEL (extra_body _ _) _ = Some _ |- _ =>
        let L := fresh "L" in pose proof (hq_extra_loop _ _ _ _ E) as L; cbv beta iota delta [pa4] in L; clear E
    | E : loop FUEL (str_body _ _) _ = Some _ |- _ =>
        let L := fresh "L" in pose proof (hq_str_loop _ _ _ _ E) as L; cbv beta iota delta [pa3] in L; clear E
    | L : _ -> _ -> pbq ?s /\ _ |- pbq ?s => eapply proj1; apply L
    | L : _ -> _ -> _ /\ adq ?z |- adq ?z => eapply proj2; apply L
    | L : _ -> pbq ?s /\ _ |- pbq ?s => eapply proj1; apply L
    | L : _ -> _ /\ adq ?z |- adq ?z => eapply proj2; apply L
    end ].

Lemma hq_zlib : forall s z s' z' o, c_deflate_zlib_header s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof. intros s z s' z' o H P A. unfold c_deflate_zlib_header in H. hs_go H; inversion H; subst; hq_close. Qed.

Lemma hq_gzip : forall s z s' z' o, c_deflate_gzip_header s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof. intros s z s' z' o H P A. unfold c_deflate_gzip_header in H. hs_go H; inversion H; subst; hq_close. Qed.

Lemma hq_extra : forall s z s' z' o, c_deflate_extra s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof. intros s z s' z' o H P A. unfold c_deflate_extra in H. hs_go H; inversion H; subst; hq_close. Qed.

Lemma hq_str : forall h x b s z s' z' o, c_deflate_str h x b s z = Some (s', z', o) -> pbq s -> adq z ->
  pbq s' /\ adq z'.
Proof.
  intros h x b s z s' z' o H P A. unfold c_deflate_str in H.
  hs_go H; inversion H; subst; try destruct b; hq_close.
Qed.

Lemma hq_name : forall s z s' z' o, c_deflate_name s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof.
  intros s z s' z' o H P A. unfold c_deflate_name in H. hs_go H; inversion H; subst; try (split; assumption).
  all: match goal with E : c_deflate_str _ _ _ _ _ = Some _ |- _ => destruct (hq_str _ _ _ _ _ _ _ _ E P A) end.
  all: hq_close.
Qed.

Lemma hq_comment : forall s z s' z' o, c_deflate_comment s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof.
  intros s z s' z' o H P A. unfold c_deflate_comment in H. hs_go H; inversion H; subst; try (split; assumption).
  all: match goal with E : c_deflate_str _ _ _ _ _ = Some _ |- _ => destruct (hq_str _ _ _ _ _ _ _ _ E P A) end.
  all: hq_close.
Qed.

Lemma hq_hcrc : forall s z s' z' o, c_deflate_hcrc s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof. intros s z s' z' o H P A. unfold c_deflate_hcrc in H. hs_go H; inversion H; subst; hq_close. Qed.

Lemma hq_then : forall r f s' z' o,
  (forall s1 z1 o1, r = Some (s1, z1, o1) -> pbq s1 /\ adq z1) ->
  (forall s z s' z' o, f s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z') ->
  then_stage r f = Some (s', z', o) -> pbq s' /\ adq z'.
Proof.
  intros r f s' z' o H1 H2 H. unfold then_stage, bind in H.
  destruct r as [[[s1 z1] [c|]]|]; try discriminate.
  - inversion H; subst. eapply H1; reflexivity.
  - destruct (H1 _ _ _ eq_refl) as [P A]. exact (H2 _ _ _ _ _ H P A).
Qed.

(** The header stages keep the pending buffer bytes and strm->adler below 2^32. *)
Lemma hdr_stages_adq : forall s z s' z' o, hdr_stages s z = Some (s', z', o) -> pbq s -> adq z -> pbq s' /\ adq z'.
Proof.
  intros s z s' z' o H P A. unfold hdr_stages in H.
  refine (hq_then _ _ _ _ _ (fun _ _ _ E => hq_zlib _ _ _ _ _ E P A) _ H).
  intros s1 z1 s1' z1' o1 H1 P1 A1.
  refine (hq_then _ _ _ _ _ (fun _ _ _ E => hq_gzip _ _ _ _ _ E P1 A1) _ H1).
  intros s2 z2 s2' z2' o2 H2 P2 A2.
  refine (hq_then _ _ _ _ _ (fun _ _ _ E => hq_extra _ _ _ _ _ E P2 A2) _ H2).
  intros s3 z3 s3' z3' o3 H3 P3 A3.
  refine (hq_then _ _ _ _ _ (fun _ _ _ E => hq_name _ _ _ _ _ E P3 A3) _ H3).
  intros s4 z4 s4' z4' o4 H4 P4 A4.
  refine (hq_then _ _ _ _ _ (fun _ _ _ E => hq_comment _ _ _ _ _ E P4 A4) _ H4).
  intros s5 z5 s5' z5' o5 H5 P5 A5.
  exact (hq_hcrc _ _ _ _ _ H5 P5 A5).
Qed.

(** ** The stages under [MidW] *)

(** The pending buffer of the in-call invariant holds bytes, and so does the gzip extra field. *)
Lemma midw_pbq : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z -> pbq s.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z (_ & _ & _ & _ & _ & IA).
  destruct IA as (_ & Hout & _ & _ & _ & _ & _ & Hgz & _).
  split; [apply Hout|]. intros h x E1 E2.
  destruct (Hgz h E1) as (_ & _ & _ & _ & _ & Hex & _). exact (proj2 (Hex x E2)).
Qed.

(** [LTApiHdrSt.hdr_tail] for [MidW]: from [hdr_post] back to the invariant. *)
Lemma hdrw_tail : forall W HI dict wrap D O inb nin aout tin tout flush s z H k s' z' r,
  core_facts W -> hdr_facts HI -> MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  d_wrap s = wrap -> d_bi_valid s = 0 -> d_sym_next s = 0 -> hdr_good dict wrap H -> 0 <= k ->
  D ++ sublist nin (z_next_in z) inb = [] -> O ++ z_out z = sublist 0 k H ->
  hdr_stages s z = Some (s', z', r) -> hdr_post HI s z H k s' z' r ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_gzhead s2 = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s2 z2 /\ z_next_in z2 = z_next_in z /\
    match r with
    | Some c => c = Z_OK
    | None => d_pending s2 = 0 /\
              (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z H k s' z' r CF HF M Hpend Hlf Hfl Hao
    Hwr Hbv Hsym HG Hk0 HD HO HS HP.
  destruct M as (ZR & Hn0 & Hsz1 & Ha & Hsz2 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & Htin & HF6 & Hdz & Hph).
  destruct ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  destruct HP as (Hce & Hout' & Hwr' & Hgz' & Hbv' & x & k' & Hk & Hx & ZS & Hr).
  destruct ZS as (Zin' & Zni' & Zai' & Zti' & Zo' & Zao' & Zto' & Zad' & Zmsg').
  pose proof (hdr_stages_ao _ _ _ _ _ HS ltac:(lia)) as Hao2.
  pose proof (hs_sym _ _ Hce) as CEF.
  assert (HbH : bytes H) by apply HG.
  assert (Hbx : bytes x).
  { assert (B : bytes (x ++ pend s')) by (rewrite Hx; apply Forall_sublist; exact HbH).
    apply Forall_app in B. apply B. }
  assert (Hlx : Zlength x <= z_avail_out z) by lia.
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Zto'. unfold u64. apply Z.mod_small. rewrite Hto, Zlength_app. 
    pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg x). lia. }
  assert (HO2 : O ++ z_out z' = sublist 0 k H ++ x) by (rewrite Zo', app_assoc, HO; reflexivity).
  assert (Hfin : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Zni'; reflexivity).
  assert (HJ : sublist 0 k H ++ x ++ pend s' = sublist 0 k' H) by (rewrite Hx; apply sublist_rejoin; lia).
  assert (Hst : d_status s' = BUSY_STATE \/ (exists H1 k1, HI s' (z_adler z') H1 k1)).
  { destruct r as [c|]; [|left; apply Hr]. destruct Hr as (_ & _ & _ & _ & [[A _]|A]); [left; exact A|].
    right; eauto. }
  exists s', z', r. split; [exact HS|]. split; [exact Hgz'|].
  split; [|split; [exact Zni'|]].
  2:{ destruct r as [c|]; [apply Hr|]. destruct Hr as (_ & A & B & _). split; [exact B|left; exact A]. }
  unfold MidW. rewrite Zni', Hfin.
  split; [|split; [exact Hn0|split; [exact Hsz1|split; [exact Ha|split; [exact Hsz2|]]]]].
  { unfold zrunw. rewrite Zin', Zni', Zai', Zti', Zo', Hto', Zlength_app. repeat split; try lia.
    - exact Zin.
    - apply Forall_app; split; assumption. }
  rewrite HD, HO2, Zti', Hto'.
  rewrite HD in Htin, HbD.
  assert (HlO : Zlength (sublist 0 k H) = Zlength (O ++ z_out z)) by (rewrite HO; reflexivity).
  unfold Iapi.
  split; [eapply (cf_frame _ CF); eauto|].
  split; [exact Hout'|].
  split; [exact Hwr0|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
  split; [destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                               destruct Hr as (_ & _ & _ & _ & _ & ->); lia]|].
  split; [rewrite Hgz'; exact Hgz|].
  split; [rewrite Hto, (Zlength_app _ (sublist 0 k H)), HlO; lia|].
  split; [apply Forall_app; split; [rewrite <- HO; exact HbO|exact Hbx]|].
  split; [exact HbD|]. split; [exact Htin|].
  split.
  { intros F. exfalso. destruct Hst as [A|(H1 & k1 & A)].
    - rewrite A in F. discriminate.
    - apply (hf_status _ HF) in A. destruct A as (_ & _ & A & _).
      rewrite F in A. unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in A. lia. }
  split.
  { intros _. destruct (hs_pos _ _ Hce) as (P1 & P2 & P3). rewrite P1, P2, P3. exact (Hdz HD). }
  right. split.
  { destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                         destruct Hr as (_ & _ & _ & _ & _ & ->); lia]. }
  destruct r as [c|].
  - destruct Hr as (-> & Hz0 & Hpn & Hlf' & [(Hb & Hk' & Had)|HI']).
    + right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
      split. { intros _. intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split. { rewrite Had, Hwr. apply hs_chk_nil. }
      exists H, []. split; [exact HG|]. rewrite <- app_assoc, HJ, Hk', app_nil_r.
      apply sublist_same; reflexivity.
    + left. unfold ph1. pose proof (hf_status _ HF _ _ _ _ HI') as (Hw2' & _).
      split; [lia|]. split; [reflexivity|].
      split. { intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split; [lia|]. split; [rewrite CEF; lia|].
      exists H, k'. split; [exact HI'|]. rewrite <- app_assoc. exact HJ.
  - destruct Hr as (Hk' & Hb & Hpn & Hpo & Had & Hlf').
    rewrite (pend_nil _ Hpn), app_nil_r in HJ.
    right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split. { intros Hw. rewrite HJ, Hk', sublist_same by reflexivity.
      eapply hdr_good_ne; eauto. }
    split. { rewrite Had, Hwr. apply hs_chk_nil. }
    exists H, []. split; [exact HG|]. rewrite (pend_nil _ Hpn), app_nil_r, HJ, Hk', app_nil_r.
    apply sublist_same; reflexivity.
Qed.

(** [LTApiHdrSt.hdr_stage_ok] for [MidW], by [hf_run_wide]. *)
Lemma hdrw_core : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W -> hdr_facts HI -> hf_run_wide HI ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_gzhead s2 = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s2 z2 /\ z_next_in z2 = z_next_in z /\
    match r with
    | Some c => c = Z_OK
    | None => d_pending s2 = 0 /\
              (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z CF HF HR M Hpend Hlf Hfl Hao Hfin.
  pose proof M as M0.
  destruct (midw_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ M) as [Hzao Hzto].
  destruct M as (ZR & Hn0 & Hsz1 & Ha & Hsz2 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & Htin & HF6 & _ & Hph).
  pose proof ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  pose proof (cf_prm _ CF _ HW) as Hprm.
  destruct Hph as [P0 | [Hlf2 [P1 | [P2 | P3]]]].
  - destruct P0 as (Hst & Hw & HD & HO & _ & Hbv & Hsym & _ & _ & Hss & Had).
    set (H := hdr_bytes s (z_adler z)).
    assert (HG : hdr_good dict wrap H).
    { destruct Hst as [[Hst Hwl]|[Hst Hw2']].
      - assert (wrap = 0 \/ wrap = 1) as [->| ->] by lia.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_good_raw.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_zlib_good; [exact Hprm|exact Hss|].
          intros _. apply Had. reflexivity.
      - subst wrap. rewrite (Hw2 eq_refl). unfold H, hdr_bytes. rewrite Hw. simpl.
        apply hs_gz_good; [exact Hgz|intros _; apply hs_xfl]. }
    assert (Hpre : hdr_pre_wide HI s z H 0).
    { unfold hdr_pre_wide. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hgz|].
      destruct Hst as [[Hst Hwl]|[Hst Hw2']]; [left|right; left]; repeat split; auto; lia. }
    destruct (HR _ _ _ _ Hpre) as (s' & z' & r & HS & HP).
    refine (hdrw_tail W HI dict wrap D O inb nin aout tin tout flush s z H 0 s' z' r CF HF M0 Hpend Hlf Hfl Hao
              Hw Hbv Hsym HG ltac:(lia) HD _ HS HP).
    rewrite HO. symmetry. apply sublist_nil.
  - destruct P1 as (Hw & HD & HOne & Hbv & Hsym & H & k & HIk & HOk).
    destruct (hf_status _ HF _ _ _ _ HIk) as (Hw' & [h Hh] & _ & [xfl HH] & Hk).
    assert (HG : hdr_good dict wrap H).
    { subst wrap. rewrite (Hw2 eq_refl), HH. apply hs_gz_good; [exact Hgz|congruence]. }
    rewrite (pend_nil _ Hpend), app_nil_r in HOk.
    assert (Hpre : hdr_pre_wide HI s z H k).
    { unfold hdr_pre_wide. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hgz|]. right; right; exact HIk. }
    destruct (HR _ _ _ _ Hpre) as (s' & z' & r & HS & HP).
    exact (hdrw_tail W HI dict wrap D O inb nin aout tin tout flush s z H k s' z' r CF HF M0 Hpend Hlf Hfl Hao
             ltac:(lia) Hbv Hsym HG ltac:(lia) HD HOk HS HP).
  - exists s, z, None. rewrite hdr_stages_busy by (left; apply P2).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|left; apply P2].
  - exists s, z, None. rewrite hdr_stages_busy by (right; apply P3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|right; split; [apply P3|apply Hfin, P3]].
Qed.

Lemma hdrw_stage_ok : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W -> hdr_facts HI -> hf_run_wide HI ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_gzhead s2 = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s2 z2 /\ z_next_in z2 = z_next_in z /\
    (0 <= z_adler z < 4294967296 -> 0 <= z_adler z2 < 4294967296) /\
    match r with
    | Some c => c = Z_OK
    | None => d_pending s2 = 0 /\
              (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z CF HF HR M Hpend Hlf Hfl Hao Hfin.
  destruct (hdrw_core W HI dict wrap D O inb nin aout tin tout flush s z CF HF HR M Hpend Hlf Hfl Hao Hfin)
    as (s2 & z2 & r & HS & Hg & M2 & Hn & Hr).
  exists s2, z2, r. split; [exact HS|]. split; [exact Hg|]. split; [exact M2|]. split; [exact Hn|].
  split; [|exact Hr].
  intros A. exact (proj2 (hdr_stages_adq _ _ _ _ _ HS (midw_pbq _ _ _ _ _ _ _ _ _ _ _ _ _ _ M) A)).
Qed.

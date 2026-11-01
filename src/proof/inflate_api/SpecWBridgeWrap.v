(* inflate() never changes state->wrap: no case of the model (Model.v, Model2.v), inflate_fast's model and the
   exit (inf_leave: window update, counters, check value) writes the field i_wrap.  The bridge of
   SpecWBridge.v needs it: a raw stream stays raw across a call, so the adler cell of the allocator-generic
   specifications chosen from the stream before the call describes the stream after it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

(* the wrap field of the machine in an outcome of a case *)
Definition iw (o: iout) : Z := match o with IBrk m => i_wrap (m_s m) | IRet _ m => i_wrap (m_s m) end.
Definition cw (o: clout) : Z := match o with CLnext m => i_wrap (m_s m) | CLleave m => i_wrap (m_s m) | CLbad m => i_wrap (m_s m) end.

(* reduction of the field access through the setters of the records and the small machine updates *)
Ltac wred := cbn [iw cw r_m m_s i_wrap set_i_mode set_i_last set_i_wrap set_i_havedict set_i_flags set_i_dmax set_i_check set_i_total set_i_head set_i_wbits set_i_wsize set_i_whave set_i_wnext set_i_win set_i_wdata set_i_hold set_i_bits set_i_length set_i_offset set_i_extra set_i_lencode set_i_distcode set_i_lenbits set_i_distbits set_i_ncode set_i_nlen set_i_ndist set_i_have set_i_next set_i_lens set_i_codes set_i_sane set_i_back set_i_was set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out set_m_ret set_m_leave set_m_adler set_m_msg set_m_tin set_m_tout set_m_snx set_m_sow
                  set_mode upd_s upd_h set_leave set_bad dropbits initbits bytebits restore pull fpull] in *.

Lemma needbits_f_w: forall k n m, i_wrap (m_s (needbits_f k n m)) = i_wrap (m_s m).
Proof.
  induction k; intros; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto.
  rewrite IHk. reflexivity.
Qed.

Lemma needbits_w: forall n m, i_wrap (m_s (needbits n m)) = i_wrap (m_s m).
Proof. intros; apply needbits_f_w. Qed.

Lemma crc_if_w: forall m d, i_wrap (m_s (crc_if m d)) = i_wrap (m_s m).
Proof. intros; unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_w: forall k fx dx t nb m h m' ok,
  lookup1_f k fx dx t nb m = (h, m', ok) -> i_wrap (m_s m') = i_wrap (m_s m).
Proof.
  induction k; intros; simpl in H.
  - inversion H; auto.
  - destruct (_ <=? _). inversion H; auto.
    destruct (m_have m =? 0). inversion H; auto.
    apply IHk in H. rewrite H. reflexivity.
Qed.

Lemma lookup1_w: forall fx dx t nb m h m' ok,
  lookup1 fx dx t nb m = (h, m', ok) -> i_wrap (m_s m') = i_wrap (m_s m).
Proof. intros; eapply lookup1_f_w; eauto. Qed.

Lemma lookup2_f_w: forall k fx dx t l m h m' ok,
  lookup2_f k fx dx t l m = (h, m', ok) -> i_wrap (m_s m') = i_wrap (m_s m).
Proof.
  induction k; intros; simpl in H.
  - inversion H; auto.
  - destruct (_ <=? _). inversion H; auto.
    destruct (m_have m =? 0). inversion H; auto.
    apply IHk in H. rewrite H. reflexivity.
Qed.

Lemma lookup2_w: forall fx dx t l m h m' ok,
  lookup2 fx dx t l m = (h, m', ok) -> i_wrap (m_s m') = i_wrap (m_s m).
Proof. intros; eapply lookup2_f_w; eauto. Qed.

Lemma fwalk_f_w: forall fx dx k il t h m h' m',
  fwalk_f fx dx k il t h m = (h', m') -> i_wrap (m_s m') = i_wrap (m_s m).
Proof.
  induction k; intros; simpl in H.
  - inversion H; auto.
  - destruct (il (e_op h)). apply IHk in H. rewrite H. reflexivity.
    inversion H; auto.
Qed.

(* Case analysis of a model function: the `if`s and the tuples are split; a tuple produced by a lookup or
   a table walk leaves an equation saying that the machine it returns has the same wrap field. *)
Ltac wsplit :=
  repeat (cbv beta iota zeta;
    match goal with
    | |- context [lookup1 ?fx ?dx ?t ?nb ?m] =>
        let E := fresh "E" in destruct (lookup1 fx dx t nb m) as [[? ?] ?] eqn:E; apply lookup1_w in E
    | |- context [lookup2 ?fx ?dx ?t ?l ?m] =>
        let E := fresh "E" in destruct (lookup2 fx dx t l m) as [[? ?] ?] eqn:E; apply lookup2_w in E
    | |- context [fwalk_f ?fx ?dx ?k ?il ?t ?h ?m] =>
        let E := fresh "E" in destruct (fwalk_f fx dx k il t h m) as [? ?] eqn:E; apply fwalk_f_w in E
    | |- context [if ?b then _ else _] => destruct b
    | |- context [match ?p with (_, _) => _ end] => destruct p
    end).

Ltac wfin :=
  repeat match goal with H: context [if ?b then _ else _] |- _ => destruct b end;
  repeat (wred; rewrite ?needbits_w, ?crc_if_w in * ); try congruence.

Lemma c_DONE_w: forall m, iw (c_DONE m) = i_wrap (m_s m).
Proof. intros; unfold c_DONE; wsplit; wfin. Qed.
Lemma c_BAD_w: forall m, iw (c_BAD m) = i_wrap (m_s m).
Proof. intros; unfold c_BAD; wsplit; wfin. Qed.
Lemma c_LENGTH_w: forall m, iw (c_LENGTH m) = i_wrap (m_s m).
Proof. intros; unfold c_LENGTH; wsplit; rewrite ?c_DONE_w; wfin. Qed.
Lemma c_CHECK_w: forall m, iw (c_CHECK m) = i_wrap (m_s m).
Proof. intros; unfold c_CHECK; wsplit; rewrite ?c_LENGTH_w; wfin. Qed.


(* inflate_fast *)
Lemma fast_iter_w: forall fx dx m b m', fast_iter fx dx m = (b, m') -> i_wrap (m_s m') = i_wrap (m_s m).
Proof. intros fx dx m b m' H; revert H; unfold fast_iter; wsplit; intro H; inversion H; subst; wfin. Qed.

Lemma fast_loop_w: forall fx dx k m, i_wrap (m_s (fast_loop fx dx k m)) = i_wrap (m_s m).
Proof.
  induction k; intros; simpl; auto.
  destruct (fast_iter fx dx m) as [b m'] eqn:E. apply fast_iter_w in E.
  destruct (_ && _ && _); [rewrite IHk|]; congruence.
Qed.

Lemma fast_w: forall fx dx m, i_wrap (m_s (fast fx dx m)) = i_wrap (m_s m).
Proof. intros; unfold fast; wred; apply fast_loop_w. Qed.

(* the loops of the dynamic-table cases *)
Lemma lens_fill_w: forall k len s, i_wrap (lens_fill k len s) = i_wrap s.
Proof. induction k; intros; simpl; auto. rewrite IHk; reflexivity. Qed.

Lemma lenlens_zero_w: forall k s, i_wrap (lenlens_zero k s) = i_wrap s.
Proof. induction k; intros; simpl; auto. destruct (_ <? 19); auto. rewrite IHk; reflexivity. Qed.

Lemma lenlens_loop_w: forall k m, i_wrap (m_s (lenlens_loop k m)) = i_wrap (m_s m).
Proof.
  induction k; intros; simpl; auto.
  destruct (_ <? _); auto. destruct (m_leave (needbits 3 m) =? 1). apply needbits_w.
  rewrite IHk. wfin.
Qed.

Lemma codelens_iter_w: forall fx dx m, cw (codelens_iter fx dx m) = i_wrap (m_s m).
Proof. intros; unfold codelens_iter; wsplit; wfin; rewrite ?lens_fill_w; wfin. Qed.

Lemma codelens_loop_w: forall fx dx k m, cw (codelens_loop fx dx k m) = i_wrap (m_s m).
Proof.
  induction k; intros; simpl; auto.
  destruct (_ <? _); auto.
  pose proof (codelens_iter_w fx dx m) as E. destruct (codelens_iter fx dx m); simpl in E; auto.
  rewrite IHk; auto.
Qed.

Lemma updatewindow_w: forall s d, i_wrap (updatewindow s d) = i_wrap s.
Proof. intros; unfold updatewindow; wsplit; wred; reflexivity. Qed.

(* the cases of the switch keep the wrap field, for any inflate_fast that keeps it *)
Section Cases.
Context (flush: Z) (fx dx: list entry) (fst: mst -> mst).
Context (Hf: forall m, i_wrap (m_s (fst m)) = i_wrap (m_s m)).

Lemma c_LIT_w: forall m, iw (c_LIT m) = i_wrap (m_s m).
Proof. intros; unfold c_LIT; wsplit; wfin. Qed.
Lemma c_MATCH_w: forall m, iw (c_MATCH m) = i_wrap (m_s m).
Proof. intros; unfold c_MATCH; wsplit; wfin. Qed.
Lemma c_DISTEXT_w: forall m, iw (c_DISTEXT m) = i_wrap (m_s m).
Proof. intros; unfold c_DISTEXT; wsplit; rewrite ?c_MATCH_w; wfin. Qed.
Lemma c_DIST_w: forall m, iw (c_DIST fx dx m) = i_wrap (m_s m).
Proof. intros; unfold c_DIST; wsplit; rewrite ?c_DISTEXT_w; wfin. Qed.
Lemma c_LENEXT_w: forall m, iw (c_LENEXT fx dx m) = i_wrap (m_s m).
Proof. intros; unfold c_LENEXT; wsplit; rewrite ?c_DIST_w; wfin. Qed.
Lemma c_LEN_w: forall m, iw (c_LEN fx dx fst m) = i_wrap (m_s m).
Proof. intros; unfold c_LEN; wsplit; rewrite ?c_LENEXT_w; wfin; rewrite Hf; wfin. Qed.
Lemma c_LEN__w: forall m, iw (c_LEN_ fx dx fst m) = i_wrap (m_s m).
Proof. intros; unfold c_LEN_; rewrite c_LEN_w; wfin. Qed.
Lemma c_CODELENS_w: forall m, iw (c_CODELENS flush fx dx fst m) = i_wrap (m_s m).
Proof.
  intros; unfold c_CODELENS.
  pose proof (codelens_loop_w fx dx 320 m) as E0; revert E0;
    generalize (codelens_loop fx dx 320 m) as o; intros o E0. destruct o; simpl in E0; wsplit; rewrite ?c_LEN__w; wfin.
Qed.
Lemma c_LENLENS_w: forall m, iw (c_LENLENS flush fx dx fst m) = i_wrap (m_s m).
Proof.
  (* the loops are generalized: the kernel must not unfold their fuel *)
  intros; unfold c_LENLENS; cbv beta zeta.
  pose proof (lenlens_loop_w 19 m) as E0; revert E0; generalize (lenlens_loop 19 m) as m1; intros m1 E0.
  pose proof (lenlens_zero_w 19 (m_s m1)) as E1; revert E1; generalize (lenlens_zero 19 (m_s m1)) as s1;
    intros s1 E1.
  wsplit; rewrite ?c_CODELENS_w; wfin.
Qed.
Lemma c_TABLE_w: forall m, iw (c_TABLE flush fx dx fst m) = i_wrap (m_s m).
Proof. intros; unfold c_TABLE; wsplit; rewrite ?c_LENLENS_w; wfin. Qed.
Lemma c_COPY_w: forall m, iw (c_COPY m) = i_wrap (m_s m).
Proof. intros; unfold c_COPY; wsplit; wfin. Qed.
Lemma c_COPY__w: forall m, iw (c_COPY_ m) = i_wrap (m_s m).
Proof. intros; unfold c_COPY_; rewrite c_COPY_w; wfin. Qed.
Lemma c_STORED_w: forall m, iw (c_STORED flush m) = i_wrap (m_s m).
Proof. intros; unfold c_STORED; wsplit; rewrite ?c_COPY__w; wfin. Qed.
Lemma c_TYPEDO_w: forall m, iw (c_TYPEDO flush m) = i_wrap (m_s m).
Proof. intros; unfold c_TYPEDO; wsplit; wfin. Qed.
Lemma c_TYPE_w: forall m, iw (c_TYPE flush m) = i_wrap (m_s m).
Proof. intros; unfold c_TYPE; wsplit; rewrite ?c_TYPEDO_w; wfin. Qed.
Lemma c_DICT_w: forall m, iw (c_DICT flush m) = i_wrap (m_s m).
Proof. intros; unfold c_DICT; wsplit; rewrite ?c_TYPE_w; wfin. Qed.
Lemma c_DICTID_w: forall m, iw (c_DICTID flush m) = i_wrap (m_s m).
Proof. intros; unfold c_DICTID; wsplit; rewrite ?c_DICT_w; wfin. Qed.
Lemma c_HCRC_w: forall m, iw (c_HCRC m) = i_wrap (m_s m).
Proof. intros; unfold c_HCRC; wsplit; wfin. Qed.
Lemma c_COMMENT2_w: forall m, iw (c_COMMENT2 m) = i_wrap (m_s m).
Proof. intros; unfold c_COMMENT2; wsplit; rewrite ?c_HCRC_w; wfin. Qed.
Lemma c_NAME2_w: forall m, iw (c_NAME2 m) = i_wrap (m_s m).
Proof. intros; unfold c_NAME2; wsplit; rewrite ?c_COMMENT2_w; wfin. Qed.
Lemma c_EXTRA2_w: forall m, iw (c_EXTRA2 m) = i_wrap (m_s m).
Proof. intros; unfold c_EXTRA2; wsplit; rewrite ?c_NAME2_w; wfin. Qed.
Lemma c_EXLEN2_w: forall m, iw (c_EXLEN2 m) = i_wrap (m_s m).
Proof. intros; unfold c_EXLEN2; wsplit; rewrite ?c_EXTRA2_w; wfin. Qed.
Lemma c_OS2_w: forall m, iw (c_OS2 m) = i_wrap (m_s m).
Proof. intros; unfold c_OS2; wsplit; rewrite ?c_EXLEN2_w; wfin. Qed.
Lemma c_TIME2_w: forall m, iw (c_TIME2 m) = i_wrap (m_s m).
Proof. intros; unfold c_TIME2; wsplit; rewrite ?c_OS2_w; wfin. Qed.
Lemma c_FLAGS2_w: forall m, iw (c_FLAGS2 m) = i_wrap (m_s m).
Proof. intros; unfold c_FLAGS2; wsplit; rewrite ?c_TIME2_w; wfin. Qed.
Lemma c_HEAD2_w: forall m, iw (c_HEAD2 m) = i_wrap (m_s m).
Proof. intros; unfold c_HEAD2; wsplit; wfin. Qed.

Lemma step2_w: forall m, iw (step2 flush fx dx fst m) = i_wrap (m_s m).
Proof.
  intros; unfold step2.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  rewrite ?c_HEAD2_w, ?c_FLAGS2_w, ?c_TIME2_w, ?c_OS2_w, ?c_EXLEN2_w, ?c_EXTRA2_w, ?c_NAME2_w,
    ?c_COMMENT2_w, ?c_HCRC_w, ?c_DICTID_w, ?c_DICT_w, ?c_TYPE_w, ?c_TYPEDO_w, ?c_STORED_w, ?c_COPY__w,
    ?c_COPY_w, ?c_TABLE_w, ?c_LENLENS_w, ?c_CODELENS_w, ?c_LEN__w, ?c_LEN_w, ?c_LENEXT_w, ?c_DIST_w,
    ?c_DISTEXT_w, ?c_MATCH_w, ?c_LIT_w, ?c_CHECK_w, ?c_LENGTH_w, ?c_DONE_w, ?c_BAD_w; reflexivity.
Qed.

End Cases.

Lemma loop2_w: forall flush fx dx m o, loop2 flush fx dx m o -> iw o = i_wrap (m_s m).
Proof.
  induction 1; pose proof (step2_w flush fx dx (fast fx dx) (fast_w fx dx) m) as E;
    unfold stepf2 in H; rewrite H in E; simpl in *; congruence.
Qed.

Lemma leave_fin_w: forall flush m, i_wrap (m_s (r_m (leave_fin flush m))) = i_wrap (m_s m).
Proof. intros; unfold leave_fin; wsplit; wfin; rewrite ?updatewindow_w; wfin. Qed.

Lemma run2_wrap: forall flush fx dx m0 res,
  run2 flush fx dx m0 res -> i_wrap (m_s (r_m res)) = i_wrap (m_s m0).
Proof.
  intros flush fx dx m0 res [o [Hl Ho]]. apply loop2_w in Hl.
  destruct o; simpl in Hl.
  - inversion Ho; subst.
    + wred. exact Hl.
    + rewrite leave_fin_w. exact Hl.
  - subst; simpl; exact Hl.
Qed.

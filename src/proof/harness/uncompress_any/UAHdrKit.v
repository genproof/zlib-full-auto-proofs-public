(* The header facts of one pass of the switch (Model2.v's stepf2): the input m_inp, i_head and the three
   maxima of the gz_header are kept, and h_xp / h_np / h_cp are only cleared.  Adapted from
   StepHd5.v with m_inp added; used by UALive (contract fix F7: case HEAD is Model2.c_HEAD2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

Definition hrel (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ i_head (m_s m') = i_head (m_s m) /\
  h_extra_max (m_h m') = h_extra_max (m_h m) /\ h_name_max (m_h m') = h_name_max (m_h m) /\
  h_comm_max (m_h m') = h_comm_max (m_h m) /\
  (h_xp (m_h m') = true -> h_xp (m_h m) = true) /\
  (h_np (m_h m') = true -> h_np (m_h m) = true) /\
  (h_cp (m_h m') = true -> h_cp (m_h m) = true).

Definition hgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => hrel m m' | IRet _ m' => hrel m m' end.

Lemma hrel_refl m : hrel m m.
Proof. unfold hrel; intuition. Qed.

Lemma hrel_trans m1 m2 m3 : hrel m1 m2 -> hrel m2 m3 -> hrel m1 m3.
Proof. unfold hrel; intuition congruence. Qed.

Lemma hgood_trans m m' o : hrel m m' -> hgood m' o -> hgood m o.
Proof. destruct o; cbn; apply hrel_trans. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers keep the header record and i_head                                                  *)

Lemma pull_h m : m_h (pull m) = m_h m.
Proof. reflexivity. Qed.
Lemma pull_hd m : i_head (m_s (pull m)) = i_head (m_s m).
Proof. reflexivity. Qed.
Lemma pull_inp m : m_inp (pull m) = m_inp m.
Proof. reflexivity. Qed.

Lemma needbits_f_h k n m : m_h (needbits_f k n m) = m_h m /\ i_head (m_s (needbits_f k n m)) = i_head (m_s m) /\
  m_inp (needbits_f k n m) = m_inp m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as [-> [-> ->]]; auto.
Qed.

Lemma needbits_h n m : m_h (needbits n m) = m_h m.
Proof. apply needbits_f_h. Qed.
Lemma needbits_hd n m : i_head (m_s (needbits n m)) = i_head (m_s m).
Proof. apply needbits_f_h. Qed.
Lemma needbits_inp n m : m_inp (needbits n m) = m_inp m.
Proof. apply needbits_f_h. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_h m d : m_h (crc_if m d) = m_h m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_hd m d : i_head (m_s (crc_if m d)) = i_head (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_inp m d : m_inp (crc_if m d) = m_inp m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_h k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m) /\ m_inp m' = m_inp m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> [-> ->]]; auto.
Qed.

Lemma lookup1_h fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m) /\ m_inp m' = m_inp m.
Proof. apply lookup1_f_h. Qed.

Lemma lookup2_f_h k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m) /\ m_inp m' = m_inp m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> [-> ->]]; auto.
Qed.

Lemma lookup2_h fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m) /\ m_inp m' = m_inp m.
Proof. apply lookup2_f_h. Qed.

Lemma lens_fill_hd k len s : i_head (lens_fill k len s) = i_head s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite IHk; reflexivity. Qed.

Lemma lenlens_zero_hd k s : i_head (lenlens_zero k s) = i_head s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [rewrite IHk|]; reflexivity.
Qed.

Lemma lenlens_loop_h k m : m_h (lenlens_loop k m) = m_h m /\ i_head (m_s (lenlens_loop k m)) = i_head (m_s m) /\
  m_inp (lenlens_loop k m) = m_inp m.
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (m_leave (needbits 3 m) =? 1); [rewrite needbits_h, needbits_hd, needbits_inp; auto|].
  match goal with |- context [lenlens_loop k ?x] => destruct (IHk x) as [-> [-> ->]] end.
  cbn. rewrite needbits_h, needbits_hd, needbits_inp; auto.
Qed.

Lemma lenlens_loop_h1 k m : m_h (lenlens_loop k m) = m_h m.
Proof. apply lenlens_loop_h. Qed.
Lemma lenlens_loop_hd k m : i_head (m_s (lenlens_loop k m)) = i_head (m_s m).
Proof. apply lenlens_loop_h. Qed.
Lemma lenlens_loop_inp k m : m_inp (lenlens_loop k m) = m_inp m.
Proof. apply lenlens_loop_h. Qed.

Lemma fwalk_f_h fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') -> m_h m' = m_h m /\ i_head (m_s m') = i_head (m_s m) /\ m_inp m' = m_inp m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as [-> [-> ->]]; cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite pull_h pull_hd pull_inp needbits_h needbits_hd needbits_inp crc_if_h crc_if_hd crc_if_inp
  lens_fill_hd lenlens_zero_hd lenlens_loop_h1 lenlens_loop_hd lenlens_loop_inp : hd.

(* destruct every closed if / match of the goal, innermost scrutinee first *)
Ltac hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => hdest c
  | context [match ?c with _ => _ end] => hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => hdest x
          end).

(* use the equations of the destructed helper calls *)
Ltac huse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_h in E; destruct E as [? [? ?]]
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_h in E; destruct E as [? [? ?]]
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_h in E; destruct E as [? [? ?]]
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_h ?a = _ |- context [m_h ?a] => rewrite H
  | H: i_head ?a = _ |- context [i_head ?a] => rewrite H
  | H: m_inp ?a = _ |- context [m_inp ?a] => rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast] in H.

Ltac hnorm := repeat progress (hcbn; autorewrite with hd; hrw).

Ltac hhyp :=
  repeat match goal with
  | H: i_head ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with hd in H))
  | H: m_inp ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with hd in H))
  end.

Ltac hclose := unfold hrel; hhyp; hnorm; repeat split; intros; try discriminate; auto.


Lemma codelens_iter_h fx dx m : m_h (clm (codelens_iter fx dx m)) = m_h m /\
                                 i_head (m_s (clm (codelens_iter fx dx m))) = i_head (m_s m) /\
                                 m_inp (clm (codelens_iter fx dx m)) = m_inp m.
Proof. unfold codelens_iter. hsplit; huse; hnorm; auto. Qed.

Lemma codelens_loop_h fx dx k m : m_h (clm (codelens_loop fx dx k m)) = m_h m /\
                                   i_head (m_s (clm (codelens_loop fx dx k m))) = i_head (m_s m) /\
                                   m_inp (clm (codelens_loop fx dx k m)) = m_inp m.
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (codelens_iter_h fx dx m) as [A [B C]].
  destruct (codelens_iter fx dx m) eqn:E; cbn in A, B, C |- *; auto.
  destruct (IHk m0) as [-> [-> ->]]; auto.
Qed.

Lemma fast_iter_h fx dx m : m_h (snd (fast_iter fx dx m)) = m_h m /\
                             i_head (m_s (snd (fast_iter fx dx m))) = i_head (m_s m) /\
                             m_inp (snd (fast_iter fx dx m)) = m_inp m.
Proof. unfold fast_iter. hsplit; huse; hnorm; auto. Qed.

Lemma fast_loop_h fx dx k m : m_h (fast_loop fx dx k m) = m_h m /\
                               i_head (m_s (fast_loop fx dx k m)) = i_head (m_s m) /\
                               m_inp (fast_loop fx dx k m) = m_inp m.
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [auto|].
  destruct (fast_iter_h fx dx m) as [A [B C]].
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A, B, C |- *.
  destruct (_ && _); [destruct (IHk m1) as [-> [-> ->]]|]; auto.
Qed.

Lemma fast_h fx dx m : m_h (fast fx dx m) = m_h m.
Proof. unfold fast. cbn. apply fast_loop_h. Qed.
Lemma fast_hd fx dx m : i_head (m_s (fast fx dx m)) = i_head (m_s m).
Proof. unfold fast. cbn. apply fast_loop_h. Qed.
Lemma fast_inp fx dx m : m_inp (fast fx dx m) = m_inp m.
Proof. unfold fast. cbn. apply fast_loop_h. Qed.

Hint Rewrite fast_h fast_hd fast_inp : hd.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb hdc.

Ltac hleaf :=
  match goal with
  | |- hgood _ (IBrk _) => unfold hgood; hclose
  | |- hgood _ (IRet _ _) => unfold hgood; hclose
  | |- hgood ?m (?f ?x) => apply (hgood_trans m x); [hclose | auto with hdc]
  end.

Ltac huse_cl :=
  repeat match goal with
  | E: codelens_loop ?a ?b ?k ?x = _ |- _ =>
      let H := fresh in pose proof (codelens_loop_h a b k x) as H; rewrite E in H; cbn [clm] in H;
      destruct H as [? [? ?]]; clear E
  end.

Ltac hcase := hsplit; huse; huse_cl; hleaf.

Section CasesHd.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_hd m : hgood m (c_DONE m).
Proof. unfold c_DONE; hcase. Qed.
Hint Resolve c_DONE_hd : hdc.
Lemma c_BAD_hd m : hgood m (c_BAD m).
Proof. unfold c_BAD; hcase. Qed.
Hint Resolve c_BAD_hd : hdc.
Lemma c_LENGTH_hd m : hgood m (c_LENGTH m).
Proof. unfold c_LENGTH; hcase. Qed.
Hint Resolve c_LENGTH_hd : hdc.
Lemma c_CHECK_hd m : hgood m (c_CHECK m).
Proof. unfold c_CHECK; hcase. Qed.
Hint Resolve c_CHECK_hd : hdc.
Lemma c_LIT_hd m : hgood m (c_LIT m).
Proof. unfold c_LIT; hcase. Qed.
Hint Resolve c_LIT_hd : hdc.
Lemma c_MATCH_hd m : hgood m (c_MATCH m).
Proof. unfold c_MATCH; hcase. Qed.
Hint Resolve c_MATCH_hd : hdc.
Lemma c_DISTEXT_hd m : hgood m (c_DISTEXT m).
Proof. unfold c_DISTEXT; hcase. Qed.
Hint Resolve c_DISTEXT_hd : hdc.
Lemma c_DIST_hd m : hgood m (c_DIST fx dx m).
Proof. unfold c_DIST; hcase. Qed.
Hint Resolve c_DIST_hd : hdc.
Lemma c_LENEXT_hd m : hgood m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; hcase. Qed.
Hint Resolve c_LENEXT_hd : hdc.
Lemma c_LEN_hd m : hgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold c_LEN.
  assert (Hf: m_h (fast fx dx (restore m)) = m_h m /\ i_head (m_s (fast fx dx (restore m))) = i_head (m_s m) /\
              m_inp (fast fx dx (restore m)) = m_inp m)
    by (rewrite fast_h, fast_hd, fast_inp; auto).
  revert Hf; generalize (fast fx dx (restore m)); intros mf [Hf1 [Hf2 Hf3]].
  hcase.
Qed.
Hint Resolve c_LEN_hd : hdc.
Lemma c_LEN__hd m : hgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold c_LEN_; hcase. Qed.
Hint Resolve c_LEN__hd : hdc.


Lemma c_CODELENS_hd m : hgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_CODELENS.
  pose proof (codelens_loop_h fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; destruct H as [Ha [Hb Hc]]; hcase.
Time Qed.
Hint Resolve c_CODELENS_hd : hdc.
Lemma c_LENLENS_hd m : hgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_h 19 m) as [A [B D]]; revert A B D.
  generalize (lenlens_loop 19 m); intros ml A B D.
  pose proof (lenlens_zero_hd 19 (m_s ml)) as C; revert C.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C.
  hcase.
Time Qed.
Hint Resolve c_LENLENS_hd : hdc.
Lemma c_TABLE_hd m : hgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold c_TABLE; hcase. Qed.
Hint Resolve c_TABLE_hd : hdc.
Lemma c_COPY_hd m : hgood m (c_COPY m).
Proof. unfold c_COPY; hcase. Qed.
Hint Resolve c_COPY_hd : hdc.
Lemma c_COPY__hd m : hgood m (c_COPY_ m).
Proof. unfold c_COPY_; hcase. Qed.
Hint Resolve c_COPY__hd : hdc.
Lemma c_STORED_hd m : hgood m (c_STORED fl m).
Proof. unfold c_STORED; hcase. Qed.
Hint Resolve c_STORED_hd : hdc.
Lemma c_TYPEDO_hd m : hgood m (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; hcase. Qed.
Hint Resolve c_TYPEDO_hd : hdc.
Lemma c_TYPE_hd m : hgood m (c_TYPE fl m).
Proof. unfold c_TYPE; hcase. Qed.
Hint Resolve c_TYPE_hd : hdc.
Lemma c_DICT_hd m : hgood m (c_DICT fl m).
Proof. unfold c_DICT; hcase. Qed.
Hint Resolve c_DICT_hd : hdc.
Lemma c_DICTID_hd m : hgood m (c_DICTID fl m).
Proof. unfold c_DICTID; hcase. Qed.
Hint Resolve c_DICTID_hd : hdc.
Lemma c_HCRC_hd m : hgood m (c_HCRC m).
Proof. unfold c_HCRC; hcase. Qed.
Hint Resolve c_HCRC_hd : hdc.
Lemma c_COMMENT2_hd m : hgood m (c_COMMENT2 m).
Proof. unfold c_COMMENT2; hcase. Qed.
Hint Resolve c_COMMENT2_hd : hdc.
Lemma c_NAME2_hd m : hgood m (c_NAME2 m).
Proof. unfold c_NAME2; hcase. Qed.
Hint Resolve c_NAME2_hd : hdc.
Lemma c_EXTRA2_hd m : hgood m (c_EXTRA2 m).
Proof. unfold c_EXTRA2; hcase. Qed.
Hint Resolve c_EXTRA2_hd : hdc.
Lemma c_EXLEN2_hd m : hgood m (c_EXLEN2 m).
Proof. unfold c_EXLEN2; hcase. Qed.
Hint Resolve c_EXLEN2_hd : hdc.
Lemma c_OS2_hd m : hgood m (c_OS2 m).
Proof. unfold c_OS2; hcase. Qed.
Hint Resolve c_OS2_hd : hdc.
Lemma c_TIME2_hd m : hgood m (c_TIME2 m).
Proof. unfold c_TIME2; hcase. Qed.
Hint Resolve c_TIME2_hd : hdc.
Lemma c_FLAGS2_hd m : hgood m (c_FLAGS2 m).
Proof. unfold c_FLAGS2; hcase. Qed.
Hint Resolve c_FLAGS2_hd : hdc.
Lemma c_HEAD2_hd m : hgood m (c_HEAD2 m).
Proof. unfold c_HEAD2; hcase. Qed.
Hint Resolve c_HEAD2_hd : hdc.

Lemma stepf2_hgood m : hgood m (stepf2 fl fx dx m).
Proof.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD); [apply c_HEAD2_hd|].
  destruct (m_mode m =? FLAGS); [apply c_FLAGS2_hd|].
  destruct (m_mode m =? TIME); [apply c_TIME2_hd|].
  destruct (m_mode m =? OS); [apply c_OS2_hd|].
  destruct (m_mode m =? EXLEN); [apply c_EXLEN2_hd|].
  destruct (m_mode m =? EXTRA); [apply c_EXTRA2_hd|].
  destruct (m_mode m =? NAME); [apply c_NAME2_hd|].
  destruct (m_mode m =? COMMENT); [apply c_COMMENT2_hd|].
  destruct (m_mode m =? HCRC); [apply c_HCRC_hd|].
  destruct (m_mode m =? DICTID); [apply c_DICTID_hd|].
  destruct (m_mode m =? DICT); [apply c_DICT_hd|].
  destruct (m_mode m =? TYPE); [apply c_TYPE_hd|].
  destruct (m_mode m =? TYPEDO); [apply c_TYPEDO_hd|].
  destruct (m_mode m =? STORED); [apply c_STORED_hd|].
  destruct (m_mode m =? COPY_); [apply c_COPY__hd|].
  destruct (m_mode m =? COPY); [apply c_COPY_hd|].
  destruct (m_mode m =? TABLE); [apply c_TABLE_hd|].
  destruct (m_mode m =? LENLENS); [apply c_LENLENS_hd|].
  destruct (m_mode m =? CODELENS); [apply c_CODELENS_hd|].
  destruct (m_mode m =? LEN_); [apply c_LEN__hd|].
  destruct (m_mode m =? LEN); [apply c_LEN_hd|].
  destruct (m_mode m =? LENEXT); [apply c_LENEXT_hd|].
  destruct (m_mode m =? DIST); [apply c_DIST_hd|].
  destruct (m_mode m =? DISTEXT); [apply c_DISTEXT_hd|].
  destruct (m_mode m =? MATCH); [apply c_MATCH_hd|].
  destruct (m_mode m =? LIT); [apply c_LIT_hd|].
  destruct (m_mode m =? CHECK); [apply c_CHECK_hd|].
  destruct (m_mode m =? LENGTH); [apply c_LENGTH_hd|].
  destruct (m_mode m =? DONE); [apply c_DONE_hd|].
  destruct (m_mode m =? BAD); [apply c_BAD_hd|].
  destruct (m_mode m =? MEM); exact (hrel_refl m).
Qed.

End CasesHd.

Lemma stepf2_hrel fl fx dx m :
  match stepf2 fl fx dx m with IBrk m' => hrel m m' | IRet _ m' => hrel m m' end.
Proof. exact (stepf2_hgood fl fx dx m). Qed.

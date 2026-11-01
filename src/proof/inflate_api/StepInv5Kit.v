(* One pass of the switch of Model2.v (stepf2) keeps the window flag, wbits (outside HEAD), avail_out
   on entry, and only grows the output; `out` is only set (by CHECK) to `left`; a pass that does not
   start in HEAD does not end in HEAD.  Used by Body5StepInv.stepf_inv5. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

(* the facts kept by the helpers (needbits, lookups, the CODELENS loop, inflate_fast) *)
Definition wkeep (m m': mst) : Prop :=
  m_aout m' = m_aout m /\ m_out m' = m_out m /\ i_win (m_s m') = i_win (m_s m) /\
  i_wbits (m_s m') = i_wbits (m_s m) /\ Zlength (m_ow m) <= Zlength (m_ow m') /\
  (i_mode (m_s m') = i_mode (m_s m) \/ i_mode (m_s m') = TYPE \/ i_mode (m_s m') = BAD).

(* the relation of a case's input and output *)
Definition wrel (m m': mst) : Prop :=
  i_win (m_s m') = i_win (m_s m) /\ i_wbits (m_s m') = i_wbits (m_s m) /\
  m_aout m' = m_aout m /\ Zlength (m_ow m) <= Zlength (m_ow m') /\
  (m_out m' = m_out m \/ (m_out m' <= m_aout m' /\ m_aout m' - Zlength (m_ow m') <= m_out m')) /\
  i_mode (m_s m') <> HEAD.

Definition wgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => wrel m m' | IRet _ m' => wrel m m' end.

Lemma wkeep_trans m1 m2 m3 : wkeep m1 m2 -> wkeep m2 m3 -> wkeep m1 m3.
Proof.
  unfold wkeep; intros (A1 & B1 & C1 & D1 & E1 & F1) (A2 & B2 & C2 & D2 & E2 & F2).
  repeat split; try congruence; try lia.
Qed.

Lemma wrel_trans m1 m2 m3 : wrel m1 m2 -> wrel m2 m3 -> wrel m1 m3.
Proof.
  unfold wrel; intros (A1 & B1 & C1 & D1 & E1 & F1) (A2 & B2 & C2 & D2 & E2 & F2).
  repeat split; try congruence; try lia; auto.
Qed.

Lemma wgood_trans m m' o : wrel m m' -> wgood m' o -> wgood m o.
Proof. destruct o; cbn; apply wrel_trans. Qed.

Ltac wmodes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma needbits_f_k k n m :
  m_s (needbits_f k n m) = m_s m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_ow (needbits_f k n m) = m_ow m /\ m_out (needbits_f k n m) = m_out m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as (-> & -> & -> & ->); auto.
Qed.

Lemma needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply needbits_f_k. Qed.
Lemma needbits_aout n m : m_aout (needbits n m) = m_aout m.
Proof. apply needbits_f_k. Qed.
Lemma needbits_ow n m : m_ow (needbits n m) = m_ow m.
Proof. apply needbits_f_k. Qed.
Lemma needbits_out n m : m_out (needbits n m) = m_out m.
Proof. apply needbits_f_k. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_win m d : i_win (m_s (crc_if m d)) = i_win (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_wbits m d : i_wbits (m_s (crc_if m d)) = i_wbits (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_mode m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_aout m d : m_aout (crc_if m d) = m_aout m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_ow m d : m_ow (crc_if m d) = m_ow m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_out m d : m_out (crc_if m d) = m_out m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lens_fill_k k len s :
  i_win (lens_fill k len s) = i_win s /\ i_wbits (lens_fill k len s) = i_wbits s /\
  i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|].
  match goal with |- context [lens_fill k len ?x] => destruct (IHk x) as (-> & -> & ->) end; auto. Qed.
Lemma lens_fill_win k len s : i_win (lens_fill k len s) = i_win s.
Proof. apply lens_fill_k. Qed.
Lemma lens_fill_wbits k len s : i_wbits (lens_fill k len s) = i_wbits s.
Proof. apply lens_fill_k. Qed.
Lemma lens_fill_mode k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. apply lens_fill_k. Qed.

Lemma lenlens_zero_k k s :
  i_win (lenlens_zero k s) = i_win s /\ i_wbits (lenlens_zero k s) = i_wbits s /\
  i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto].
  match goal with |- context [lenlens_zero k ?x] => destruct (IHk x) as (-> & -> & ->) end; auto.
Qed.

Lemma copy_f_len n w sr ow : Zlength ow <= Zlength (fst (copy_f n w sr ow)).
Proof.
  revert sr ow; induction n; intros sr ow; cbn [copy_f]; [cbn; lia|].
  destruct sr; (eapply Z.le_trans; [|apply IHn]); rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma copy_bytes_len w sr n ow ow' sr' : copy_bytes w sr n ow = (ow', sr') -> Zlength ow <= Zlength ow'.
Proof.
  unfold copy_bytes; intros E. pose proof (copy_f_len (Z.to_nat n) w sr ow) as H. rewrite E in H. exact H.
Qed.

Lemma lookup1_f_k k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma lookup1_k fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply lookup1_f_k. Qed.

Lemma lookup2_f_k k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma lookup2_k fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply lookup2_f_k. Qed.

Lemma fwalk_f_k fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as (-> & -> & -> & ->); cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite needbits_s needbits_aout needbits_ow needbits_out crc_if_win crc_if_wbits crc_if_mode
  crc_if_aout crc_if_ow crc_if_out lens_fill_win lens_fill_wbits lens_fill_mode : wi.

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

Ltac huse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_k in E; destruct E as (? & ? & ? & ?)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_k in E; destruct E as (? & ? & ? & ?)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_k in E; destruct E as (? & ? & ? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => apply copy_bytes_len in E
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: m_aout ?a = _ |- context [m_aout ?a] => rewrite H
  | H: m_ow ?a = _ |- context [m_ow ?a] => rewrite H
  | H: m_out ?a = _ |- context [m_out ?a] => rewrite H
  | H: i_win (m_s ?a) = _ |- context [i_win (m_s ?a)] => rewrite H
  | H: i_wbits (m_s ?a) = _ |- context [i_wbits (m_s ?a)] => rewrite H
  | H: i_win ?a = _ |- context [i_win ?a] => is_var a; rewrite H
  | H: i_wbits ?a = _ |- context [i_wbits ?a] => is_var a; rewrite H
  | H: i_mode ?a = _ |- context [i_mode ?a] => is_var a; rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength] in H.

(* normalize the helper facts, and rewrite them with each other *)
Ltac hyp_norm :=
  repeat match goal with
  | H: m_s _ = _ |- _ => progress (hcbn_in H; autorewrite with wi in H)
  | H: m_aout _ = _ |- _ => progress (hcbn_in H; autorewrite with wi in H)
  | H: m_ow _ = _ |- _ => progress (hcbn_in H; autorewrite with wi in H)
  | H: m_out _ = _ |- _ => progress (hcbn_in H; autorewrite with wi in H)
  | H: Zlength _ <= Zlength _ |- _ => progress (hcbn_in H; autorewrite with wi in H)
  end;
  repeat match goal with
  | H: m_s ?a = _, H2: context [m_s ?a] |- _ => is_var a; rewrite H in H2
  | H: m_aout ?a = _, H2: context [m_aout ?a] |- _ => is_var a; rewrite H in H2
  | H: m_ow ?a = _, H2: context [m_ow ?a] |- _ => is_var a; rewrite H in H2
  | H: m_out ?a = _, H2: context [m_out ?a] |- _ => is_var a; rewrite H in H2
  end.

Ltac wnorm := hyp_norm; repeat progress (hcbn; autorewrite with wi; hrw).

Ltac zlnn :=
  repeat match goal with
  | |- context [Zlength ?l] =>
      lazymatch goal with
      | _: 0 <= Zlength l |- _ => fail
      | _ => pose proof (Zlength_nonneg l)
      end
  | _: context [Zlength ?l] |- _ =>
      lazymatch goal with
      | _: 0 <= Zlength l |- _ => fail
      | _ => pose proof (Zlength_nonneg l)
      end
  end.

Ltac wfin := unfold m_left, m_mode in *; rewrite ?Zlength_app in *; zlnn; wmodes;
  repeat split; try reflexivity; try lia.

Ltac kclose := unfold wkeep; wnorm; wfin.
Ltac wclose := unfold wrel; wnorm; wfin.

Lemma codelens_iter_k fx dx m : wkeep m (clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. hsplit; huse; kclose. Qed.

Lemma wkeep_refl m : wkeep m m.
Proof. unfold wkeep; repeat split; auto; lia. Qed.

Lemma codelens_loop_k fx dx k m : wkeep m (clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply wkeep_refl|].
  destruct (_ <? _); [|apply wkeep_refl].
  pose proof (codelens_iter_k fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply wkeep_trans; [exact A | apply IHk].
Qed.

Lemma lenlens_loop_k k m :
  m_aout (lenlens_loop k m) = m_aout m /\ m_out (lenlens_loop k m) = m_out m /\
  m_ow (lenlens_loop k m) = m_ow m /\ i_win (m_s (lenlens_loop k m)) = i_win (m_s m) /\
  i_wbits (m_s (lenlens_loop k m)) = i_wbits (m_s m) /\ i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [repeat split|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|repeat split].
  destruct (m_leave (needbits 3 m) =? 1); [autorewrite with wi; repeat split|].
  match goal with |- context [lenlens_loop _ ?x] => destruct (IHk x) as (-> & -> & -> & -> & -> & ->) end.
  cbn. autorewrite with wi; repeat split.
Qed.

Lemma fast_iter_k fx dx m : wkeep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. hsplit; huse; kclose. Qed.

Lemma fast_loop_k fx dx k m : wkeep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply wkeep_refl|].
  pose proof (fast_iter_k fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [eapply wkeep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma fast_k fx dx m : wkeep m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (fast_loop_k fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply wkeep_trans; [exact A|]. kclose.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases other than HEAD                                                                      *)

Create HintDb wdc.
#[export] Hint Extern 1 (m_mode _ <> HEAD) => (unfold m_mode in *; hcbn; wmodes; lia) : wdc.

Ltac wleaf :=
  match goal with
  | |- wgood _ (IBrk _) => unfold wgood; wclose
  | |- wgood _ (IRet _ _) => unfold wgood; wclose
  | |- wgood ?m (?f ?x) => apply (wgood_trans m x); [wclose | auto with wdc]
  end.

Ltac wcase := hsplit; huse; wleaf.

Section CasesW.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_w m : m_mode m <> HEAD -> wgood m (c_DONE m).
Proof. intros H; unfold c_DONE; wcase. Qed.
Hint Resolve c_DONE_w : wdc.
Lemma c_BAD_w m : m_mode m <> HEAD -> wgood m (c_BAD m).
Proof. intros H; unfold c_BAD; wcase. Qed.
Hint Resolve c_BAD_w : wdc.
Lemma c_LENGTH_w m : m_mode m <> HEAD -> wgood m (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; wcase. Qed.
Hint Resolve c_LENGTH_w : wdc.
Lemma c_CHECK_w m : m_mode m <> HEAD -> wgood m (c_CHECK m).
Proof. intros H; unfold c_CHECK; wcase. Qed.
Hint Resolve c_CHECK_w : wdc.
Lemma c_LIT_w m : m_mode m <> HEAD -> wgood m (c_LIT m).
Proof. intros H; unfold c_LIT; wcase. Qed.
Hint Resolve c_LIT_w : wdc.
Lemma c_MATCH_w m : m_mode m <> HEAD -> wgood m (c_MATCH m).
Proof. intros H; unfold c_MATCH; wcase. Qed.
Hint Resolve c_MATCH_w : wdc.
Lemma c_DISTEXT_w m : m_mode m <> HEAD -> wgood m (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; wcase. Qed.
Hint Resolve c_DISTEXT_w : wdc.
Lemma c_DIST_w m : m_mode m <> HEAD -> wgood m (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; wcase. Qed.
Hint Resolve c_DIST_w : wdc.
Lemma c_LENEXT_w m : m_mode m <> HEAD -> wgood m (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; wcase. Qed.
Hint Resolve c_LENEXT_w : wdc.
Lemma c_LEN_w m : m_mode m <> HEAD -> wgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LEN.
  pose proof (fast_k fx dx (restore m)) as Hf; unfold wkeep in Hf; hcbn_in Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf (Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6).
  wcase.
Qed.
Hint Resolve c_LEN_w : wdc.
Lemma c_LEN__w m : m_mode m <> HEAD -> wgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H; unfold c_LEN_; wcase. Qed.
Hint Resolve c_LEN__w : wdc.

Lemma c_CODELENS_w m : m_mode m <> HEAD -> wgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_CODELENS.
  pose proof (codelens_loop_k fx dx 320 m) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [clm] in Hc; unfold wkeep in Hc; destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6);
    wcase.
Time Qed.
Hint Resolve c_CODELENS_w : wdc.
Lemma c_LENLENS_w m : m_mode m <> HEAD -> wgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_k 19 m) as (A1 & A2 & A3 & A4 & A5 & A6); revert A1 A2 A3 A4 A5 A6.
  generalize (lenlens_loop 19 m); intros ml A1 A2 A3 A4 A5 A6.
  pose proof (lenlens_zero_k 19 (m_s ml)) as (C1 & C2 & C3); revert C1 C2 C3.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C1 C2 C3.
  wcase.
Time Qed.
Hint Resolve c_LENLENS_w : wdc.
Lemma c_TABLE_w m : m_mode m <> HEAD -> wgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros H; unfold c_TABLE; wcase. Qed.
Hint Resolve c_TABLE_w : wdc.
Lemma c_COPY_w m : m_mode m <> HEAD -> wgood m (c_COPY m).
Proof. intros H; unfold c_COPY; wcase. Qed.
Hint Resolve c_COPY_w : wdc.
Lemma c_COPY__w m : m_mode m <> HEAD -> wgood m (c_COPY_ m).
Proof. intros H; unfold c_COPY_; wcase. Qed.
Hint Resolve c_COPY__w : wdc.
Lemma c_STORED_w m : m_mode m <> HEAD -> wgood m (c_STORED fl m).
Proof. intros H; unfold c_STORED; wcase. Qed.
Hint Resolve c_STORED_w : wdc.
Lemma c_TYPEDO_w m : m_mode m <> HEAD -> wgood m (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; wcase. Qed.
Hint Resolve c_TYPEDO_w : wdc.
Lemma c_TYPE_w m : m_mode m <> HEAD -> wgood m (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; wcase. Qed.
Hint Resolve c_TYPE_w : wdc.
Lemma c_DICT_w m : m_mode m <> HEAD -> wgood m (c_DICT fl m).
Proof. intros H; unfold c_DICT; wcase. Qed.
Hint Resolve c_DICT_w : wdc.
Lemma c_DICTID_w m : m_mode m <> HEAD -> wgood m (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; wcase. Qed.
Hint Resolve c_DICTID_w : wdc.
Lemma c_HCRC_w m : m_mode m <> HEAD -> wgood m (c_HCRC m).
Proof. intros H; unfold c_HCRC; wcase. Qed.
Hint Resolve c_HCRC_w : wdc.
Lemma c_COMMENT2_w m : m_mode m <> HEAD -> wgood m (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; wcase. Qed.
Hint Resolve c_COMMENT2_w : wdc.
Lemma c_NAME2_w m : m_mode m <> HEAD -> wgood m (c_NAME2 m).
Proof. intros H; unfold c_NAME2; wcase. Qed.
Hint Resolve c_NAME2_w : wdc.
Lemma c_EXTRA2_w m : m_mode m <> HEAD -> wgood m (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; wcase. Qed.
Hint Resolve c_EXTRA2_w : wdc.
Lemma c_EXLEN2_w m : m_mode m <> HEAD -> wgood m (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; wcase. Qed.
Hint Resolve c_EXLEN2_w : wdc.
Lemma c_OS2_w m : m_mode m <> HEAD -> wgood m (c_OS2 m).
Proof. intros H; unfold c_OS2; wcase. Qed.
Hint Resolve c_OS2_w : wdc.
Lemma c_TIME2_w m : m_mode m <> HEAD -> wgood m (c_TIME2 m).
Proof. intros H; unfold c_TIME2; wcase. Qed.
Hint Resolve c_TIME2_w : wdc.
Lemma c_FLAGS2_w m : m_mode m <> HEAD -> wgood m (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; wcase. Qed.
Hint Resolve c_FLAGS2_w : wdc.

Lemma wrel_refl m : m_mode m <> HEAD -> wrel m m.
Proof. intros H; unfold wrel, m_mode in *; repeat split; auto; lia. Qed.

Lemma stepf2_wgood m : m_mode m <> HEAD -> wgood m (stepf2 fl fx dx m).
Proof.
  intros H0.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  destruct (m_mode m =? FLAGS); [apply c_FLAGS2_w; exact H0|].
  destruct (m_mode m =? TIME); [apply c_TIME2_w; exact H0|].
  destruct (m_mode m =? OS); [apply c_OS2_w; exact H0|].
  destruct (m_mode m =? EXLEN); [apply c_EXLEN2_w; exact H0|].
  destruct (m_mode m =? EXTRA); [apply c_EXTRA2_w; exact H0|].
  destruct (m_mode m =? NAME); [apply c_NAME2_w; exact H0|].
  destruct (m_mode m =? COMMENT); [apply c_COMMENT2_w; exact H0|].
  destruct (m_mode m =? HCRC); [apply c_HCRC_w; exact H0|].
  destruct (m_mode m =? DICTID); [apply c_DICTID_w; exact H0|].
  destruct (m_mode m =? DICT); [apply c_DICT_w; exact H0|].
  destruct (m_mode m =? TYPE); [apply c_TYPE_w; exact H0|].
  destruct (m_mode m =? TYPEDO); [apply c_TYPEDO_w; exact H0|].
  destruct (m_mode m =? STORED); [apply c_STORED_w; exact H0|].
  destruct (m_mode m =? COPY_); [apply c_COPY__w; exact H0|].
  destruct (m_mode m =? COPY); [apply c_COPY_w; exact H0|].
  destruct (m_mode m =? TABLE); [apply c_TABLE_w; exact H0|].
  destruct (m_mode m =? LENLENS); [apply c_LENLENS_w; exact H0|].
  destruct (m_mode m =? CODELENS); [apply c_CODELENS_w; exact H0|].
  destruct (m_mode m =? LEN_); [apply c_LEN__w; exact H0|].
  destruct (m_mode m =? LEN); [apply c_LEN_w; exact H0|].
  destruct (m_mode m =? LENEXT); [apply c_LENEXT_w; exact H0|].
  destruct (m_mode m =? DIST); [apply c_DIST_w; exact H0|].
  destruct (m_mode m =? DISTEXT); [apply c_DISTEXT_w; exact H0|].
  destruct (m_mode m =? MATCH); [apply c_MATCH_w; exact H0|].
  destruct (m_mode m =? LIT); [apply c_LIT_w; exact H0|].
  destruct (m_mode m =? CHECK); [apply c_CHECK_w; exact H0|].
  destruct (m_mode m =? LENGTH); [apply c_LENGTH_w; exact H0|].
  destruct (m_mode m =? DONE); [apply c_DONE_w; exact H0|].
  destruct (m_mode m =? BAD); [apply c_BAD_w; exact H0|].
  destruct (m_mode m =? MEM); exact (wrel_refl m H0).
Qed.

End CasesW.

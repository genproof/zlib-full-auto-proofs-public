(* Law inflate_codes, theory part: no pass of the switch ends in DICT with a break (DICT only returns
   Z_NEED_DICT or goes on to TYPE). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition nodict_stmt : Prop :=
  forall flush m m', stepf2 flush lenfix_list distfix_list m = IBrk m' -> m_mode m' <> DICT.

(* ---------------------------------------------------------------------------------------------- *)
(* Frame facts of the helpers (a copy of inflate_api/StepInv5Kit.v, prefix nd_)                  *)

(* the facts kept by the helpers (needbits, lookups, the CODELENS loop, inflate_fast) *)
Definition nd_wkeep (m m': mst) : Prop :=
  i_mode (m_s m') = i_mode (m_s m) \/ i_mode (m_s m') = Zlib.proof.inflate.Model.TYPE \/ i_mode (m_s m') = BAD.

Lemma nd_wkeep_trans m1 m2 m3 : nd_wkeep m1 m2 -> nd_wkeep m2 m3 -> nd_wkeep m1 m3.
Proof. unfold nd_wkeep; intros F1 F2. destruct F2 as [F2|F2]; rewrite ?F2; auto. Qed.

Ltac nd_wmodes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma nd_needbits_f_k k n m :
  m_s (needbits_f k n m) = m_s m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_ow (needbits_f k n m) = m_ow m /\ m_out (needbits_f k n m) = m_out m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as (-> & -> & -> & ->); auto.
Qed.

Lemma nd_needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply nd_needbits_f_k. Qed.
Lemma nd_needbits_aout n m : m_aout (needbits n m) = m_aout m.
Proof. apply nd_needbits_f_k. Qed.
Lemma nd_needbits_ow n m : m_ow (needbits n m) = m_ow m.
Proof. apply nd_needbits_f_k. Qed.
Lemma nd_needbits_out n m : m_out (needbits n m) = m_out m.
Proof. apply nd_needbits_f_k. Qed.

Local Opaque needbits needbits_f.

Lemma nd_crc_if_win m d : i_win (m_s (crc_if m d)) = i_win (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma nd_crc_if_wbits m d : i_wbits (m_s (crc_if m d)) = i_wbits (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma nd_crc_if_mode m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma nd_crc_if_aout m d : m_aout (crc_if m d) = m_aout m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma nd_crc_if_ow m d : m_ow (crc_if m d) = m_ow m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma nd_crc_if_out m d : m_out (crc_if m d) = m_out m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.

Lemma nd_lens_fill_k k len s :
  i_win (lens_fill k len s) = i_win s /\ i_wbits (lens_fill k len s) = i_wbits s /\
  i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|].
  match goal with |- context [lens_fill k len ?x] => destruct (IHk x) as (-> & -> & ->) end; auto. Qed.
Lemma nd_lens_fill_win k len s : i_win (lens_fill k len s) = i_win s.
Proof. apply nd_lens_fill_k. Qed.
Lemma nd_lens_fill_wbits k len s : i_wbits (lens_fill k len s) = i_wbits s.
Proof. apply nd_lens_fill_k. Qed.
Lemma nd_lens_fill_mode k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. apply nd_lens_fill_k. Qed.

Lemma nd_lenlens_zero_k k s :
  i_win (lenlens_zero k s) = i_win s /\ i_wbits (lenlens_zero k s) = i_wbits s /\
  i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto].
  match goal with |- context [lenlens_zero k ?x] => destruct (IHk x) as (-> & -> & ->) end; auto.
Qed.

Lemma nd_copy_f_len n w sr ow : Zlength ow <= Zlength (fst (copy_f n w sr ow)).
Proof.
  revert sr ow; induction n; intros sr ow; cbn [copy_f]; [cbn; lia|].
  destruct sr; (eapply Z.le_trans; [|apply IHn]); rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma nd_copy_bytes_len w sr n ow ow' sr' : copy_bytes w sr n ow = (ow', sr') -> Zlength ow <= Zlength ow'.
Proof.
  unfold copy_bytes; intros E. pose proof (nd_copy_f_len (Z.to_nat n) w sr ow) as H. rewrite E in H. exact H.
Qed.

Lemma nd_lookup1_f_k k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma nd_lookup1_k fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply nd_lookup1_f_k. Qed.

Lemma nd_lookup2_f_k k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma nd_lookup2_k fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply nd_lookup2_f_k. Qed.

Lemma nd_fwalk_f_k fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as (-> & -> & -> & ->); cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Definition nd_clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite nd_needbits_s nd_needbits_aout nd_needbits_ow nd_needbits_out nd_crc_if_win nd_crc_if_wbits nd_crc_if_mode
  nd_crc_if_aout nd_crc_if_ow nd_crc_if_out nd_lens_fill_win nd_lens_fill_wbits nd_lens_fill_mode : nd_wi.

(* destruct every closed if / match of the goal, innermost scrutinee first *)
Ltac nd_hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => nd_hdest c
  | context [match ?c with _ => _ end] => nd_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac nd_hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => nd_hdest x
          end).

Ltac nd_huse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply nd_lookup1_k in E; destruct E as (? & ? & ? & ?)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply nd_lookup2_k in E; destruct E as (? & ? & ? & ?)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply nd_fwalk_f_k in E; destruct E as (? & ? & ? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => apply nd_copy_bytes_len in E
  end.

Ltac nd_hrw :=
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

Ltac nd_hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength].

Ltac nd_hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength] in H.

(* normalize the helper facts, and rewrite them with each other *)
Ltac nd_hyp_norm :=
  repeat match goal with
  | H: m_s _ = _ |- _ => progress (nd_hcbn_in H; autorewrite with nd_wi in H)
  | H: m_aout _ = _ |- _ => progress (nd_hcbn_in H; autorewrite with nd_wi in H)
  | H: m_ow _ = _ |- _ => progress (nd_hcbn_in H; autorewrite with nd_wi in H)
  | H: m_out _ = _ |- _ => progress (nd_hcbn_in H; autorewrite with nd_wi in H)
  | H: Zlength _ <= Zlength _ |- _ => progress (nd_hcbn_in H; autorewrite with nd_wi in H)
  end;
  repeat match goal with
  | H: m_s ?a = _, H2: context [m_s ?a] |- _ => is_var a; rewrite H in H2
  | H: m_aout ?a = _, H2: context [m_aout ?a] |- _ => is_var a; rewrite H in H2
  | H: m_ow ?a = _, H2: context [m_ow ?a] |- _ => is_var a; rewrite H in H2
  | H: m_out ?a = _, H2: context [m_out ?a] |- _ => is_var a; rewrite H in H2
  end.

Ltac nd_wnorm := nd_hyp_norm; repeat progress (nd_hcbn; autorewrite with nd_wi; nd_hrw).

Ltac nd_zlnn :=
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

Ltac nd_wfin := unfold m_left, m_mode in *; rewrite ?Zlength_app in *; nd_zlnn; nd_wmodes;
  repeat split; try reflexivity; try lia.

Ltac nd_kclose := unfold nd_wkeep; nd_wnorm; nd_wfin.

Lemma nd_codelens_iter_k fx dx m : nd_wkeep m (nd_clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. nd_hsplit; nd_huse; nd_kclose. Qed.

Lemma nd_wkeep_refl m : nd_wkeep m m.
Proof. unfold nd_wkeep; auto. Qed.

Lemma nd_codelens_loop_k fx dx k m : nd_wkeep m (nd_clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply nd_wkeep_refl|].
  destruct (_ <? _); [|apply nd_wkeep_refl].
  pose proof (nd_codelens_iter_k fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply nd_wkeep_trans; [exact A | apply IHk].
Qed.

Lemma nd_lenlens_loop_k k m :
  m_aout (lenlens_loop k m) = m_aout m /\ m_out (lenlens_loop k m) = m_out m /\
  m_ow (lenlens_loop k m) = m_ow m /\ i_win (m_s (lenlens_loop k m)) = i_win (m_s m) /\
  i_wbits (m_s (lenlens_loop k m)) = i_wbits (m_s m) /\ i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [repeat split|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|repeat split].
  destruct (m_leave (needbits 3 m) =? 1); [autorewrite with nd_wi; repeat split|].
  match goal with |- context [lenlens_loop _ ?x] => destruct (IHk x) as (-> & -> & -> & -> & -> & ->) end.
  cbn. autorewrite with nd_wi; repeat split.
Qed.

(* a light closer for inflate_fast's leaves: only the mode matters *)
Ltac nd_fclose :=
  nd_huse;
  repeat match goal with
  | H: (_ = true) |- _ => clear H | H: (_ = false) |- _ => clear H
  | H: copy_bytes _ _ _ _ = _ |- _ => clear H
  | H: m_aout _ = _ |- _ => clear H | H: m_ow _ = _ |- _ => clear H | H: m_out _ = _ |- _ => clear H
  end;
  unfold nd_wkeep in *; cbn in *;
  first [left; congruence | right; left; reflexivity | right; right; reflexivity].

Lemma nd_fast_iter_k fx dx m : nd_wkeep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. nd_hsplit; nd_fclose. Qed.

Lemma nd_fast_loop_k fx dx k m : nd_wkeep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply nd_wkeep_refl|].
  pose proof (nd_fast_iter_k fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (andb _ _); [eapply nd_wkeep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma nd_fast_k fx dx m : nd_wkeep m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (nd_fast_loop_k fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply nd_wkeep_trans; [exact A|]. nd_kclose.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Definition nd_good (o: iout) : Prop :=
  match o with IBrk m' => m_mode m' <> DICT | IRet _ _ => True end.

Ltac nd_mclose := unfold m_mode in *; nd_wnorm; nd_wfin.

Create HintDb nd_db.
#[export] Hint Extern 1 (m_mode _ <> DICT) => nd_mclose : nd_db.

Ltac nd_leaf :=
  match goal with
  | |- nd_good (IBrk _) => unfold nd_good; nd_mclose
  | |- nd_good (IRet _ _) => exact I
  | |- nd_good (?f ?x) => auto with nd_db
  end.

Ltac nd_case := nd_hsplit; nd_huse; nd_leaf.

Section CasesND.
Variables (fl: Z) (fx dx: list entry).

Lemma nd_c_DONE m : m_mode m <> DICT -> nd_good (c_DONE m).
Proof. intros H; unfold c_DONE; nd_case. Qed.
#[local] Hint Resolve nd_c_DONE : nd_db.
Lemma nd_c_BAD m : m_mode m <> DICT -> nd_good (c_BAD m).
Proof. intros H; unfold c_BAD; nd_case. Qed.
#[local] Hint Resolve nd_c_BAD : nd_db.
Lemma nd_c_LENGTH m : m_mode m <> DICT -> nd_good (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; nd_case. Qed.
#[local] Hint Resolve nd_c_LENGTH : nd_db.
Lemma nd_c_CHECK m : m_mode m <> DICT -> nd_good (c_CHECK m).
Proof. intros H; unfold c_CHECK; nd_case. Qed.
#[local] Hint Resolve nd_c_CHECK : nd_db.
Lemma nd_c_LIT m : m_mode m <> DICT -> nd_good (c_LIT m).
Proof. intros H; unfold c_LIT; nd_case. Qed.
#[local] Hint Resolve nd_c_LIT : nd_db.
Lemma nd_c_MATCH m : m_mode m <> DICT -> nd_good (c_MATCH m).
Proof. intros H; unfold c_MATCH; nd_case. Qed.
#[local] Hint Resolve nd_c_MATCH : nd_db.
Lemma nd_c_DISTEXT m : m_mode m <> DICT -> nd_good (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; nd_case. Qed.
#[local] Hint Resolve nd_c_DISTEXT : nd_db.
Lemma nd_c_DIST m : m_mode m <> DICT -> nd_good (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; nd_case. Qed.
#[local] Hint Resolve nd_c_DIST : nd_db.
Lemma nd_c_LENEXT m : m_mode m <> DICT -> nd_good (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; nd_case. Qed.
#[local] Hint Resolve nd_c_LENEXT : nd_db.
Lemma nd_c_LEN m : m_mode m <> DICT -> nd_good (c_LEN fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LEN.
  pose proof (nd_fast_k fx dx (restore m)) as Hf; unfold nd_wkeep in Hf; nd_hcbn_in Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf.
  nd_case.
Qed.
#[local] Hint Resolve nd_c_LEN : nd_db.
Lemma nd_c_LEN_ m : m_mode m <> DICT -> nd_good (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H; unfold c_LEN_; nd_case. Qed.
#[local] Hint Resolve nd_c_LEN_ : nd_db.
Lemma nd_c_CODELENS m : m_mode m <> DICT -> nd_good (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_CODELENS.
  pose proof (nd_codelens_loop_k fx dx 320 m) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [nd_clm] in Hc; unfold nd_wkeep in Hc;
    nd_case.
Qed.
#[local] Hint Resolve nd_c_CODELENS : nd_db.
Lemma nd_c_LENLENS m : m_mode m <> DICT -> nd_good (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (nd_lenlens_loop_k 19 m) as (A1 & A2 & A3 & A4 & A5 & A6); revert A1 A2 A3 A4 A5 A6.
  generalize (lenlens_loop 19 m); intros ml A1 A2 A3 A4 A5 A6.
  pose proof (nd_lenlens_zero_k 19 (m_s ml)) as (C1 & C2 & C3); revert C1 C2 C3.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C1 C2 C3.
  nd_case.
Qed.
#[local] Hint Resolve nd_c_LENLENS : nd_db.
Lemma nd_c_TABLE m : m_mode m <> DICT -> nd_good (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros H; unfold c_TABLE; nd_case. Qed.
#[local] Hint Resolve nd_c_TABLE : nd_db.
Lemma nd_c_COPY m : m_mode m <> DICT -> nd_good (c_COPY m).
Proof. intros H; unfold c_COPY; nd_case. Qed.
#[local] Hint Resolve nd_c_COPY : nd_db.
Lemma nd_c_COPY_ m : m_mode m <> DICT -> nd_good (c_COPY_ m).
Proof. intros H; unfold c_COPY_; nd_case. Qed.
#[local] Hint Resolve nd_c_COPY_ : nd_db.
Lemma nd_c_STORED m : m_mode m <> DICT -> nd_good (c_STORED fl m).
Proof. intros H; unfold c_STORED; nd_case. Qed.
#[local] Hint Resolve nd_c_STORED : nd_db.
Lemma nd_c_TYPEDO m : m_mode m <> DICT -> nd_good (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; nd_case. Qed.
#[local] Hint Resolve nd_c_TYPEDO : nd_db.
Lemma nd_c_TYPE m : m_mode m <> DICT -> nd_good (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; nd_case. Qed.
#[local] Hint Resolve nd_c_TYPE : nd_db.
Lemma nd_c_DICT m : nd_good (c_DICT fl m).
Proof. unfold c_DICT; nd_case. Qed.
#[local] Hint Resolve nd_c_DICT : nd_db.
Lemma nd_c_DICTID m : m_mode m <> DICT -> nd_good (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; nd_case. Qed.
#[local] Hint Resolve nd_c_DICTID : nd_db.
Lemma nd_c_HCRC m : m_mode m <> DICT -> nd_good (c_HCRC m).
Proof. intros H; unfold c_HCRC; nd_case. Qed.
#[local] Hint Resolve nd_c_HCRC : nd_db.
Lemma nd_c_COMMENT2 m : m_mode m <> DICT -> nd_good (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; nd_case. Qed.
#[local] Hint Resolve nd_c_COMMENT2 : nd_db.
Lemma nd_c_NAME2 m : m_mode m <> DICT -> nd_good (c_NAME2 m).
Proof. intros H; unfold c_NAME2; nd_case. Qed.
#[local] Hint Resolve nd_c_NAME2 : nd_db.
Lemma nd_c_EXTRA2 m : m_mode m <> DICT -> nd_good (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; nd_case. Qed.
#[local] Hint Resolve nd_c_EXTRA2 : nd_db.
Lemma nd_c_EXLEN2 m : m_mode m <> DICT -> nd_good (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; nd_case. Qed.
#[local] Hint Resolve nd_c_EXLEN2 : nd_db.
Lemma nd_c_OS2 m : m_mode m <> DICT -> nd_good (c_OS2 m).
Proof. intros H; unfold c_OS2; nd_case. Qed.
#[local] Hint Resolve nd_c_OS2 : nd_db.
Lemma nd_c_TIME2 m : m_mode m <> DICT -> nd_good (c_TIME2 m).
Proof. intros H; unfold c_TIME2; nd_case. Qed.
#[local] Hint Resolve nd_c_TIME2 : nd_db.
Lemma nd_c_FLAGS2 m : m_mode m <> DICT -> nd_good (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; nd_case. Qed.
#[local] Hint Resolve nd_c_FLAGS2 : nd_db.
Lemma nd_c_HEAD m : m_mode m <> DICT -> nd_good (c_HEAD m).
Proof. intros H; unfold c_HEAD; nd_case. Qed.
Lemma nd_c_HEAD2 m : m_mode m <> DICT -> nd_good (c_HEAD2 m).
Proof. intros H; unfold c_HEAD2; nd_case. Qed.

Lemma nd_step2 m : nd_good (step2 fl fx dx (fast fx dx) m).
Proof.
  unfold step2.
  destruct (Z.eq_dec (m_mode m) DICT) as [ED|ND].
  - rewrite ED. cbn -[c_DICT]. apply nd_c_DICT.
  - destruct (m_mode m =? HEAD); [apply nd_c_HEAD2; exact ND|].
    destruct (m_mode m =? FLAGS); [apply nd_c_FLAGS2; exact ND|].
    destruct (m_mode m =? TIME); [apply nd_c_TIME2; exact ND|].
    destruct (m_mode m =? OS); [apply nd_c_OS2; exact ND|].
    destruct (m_mode m =? EXLEN); [apply nd_c_EXLEN2; exact ND|].
    destruct (m_mode m =? EXTRA); [apply nd_c_EXTRA2; exact ND|].
    destruct (m_mode m =? NAME); [apply nd_c_NAME2; exact ND|].
    destruct (m_mode m =? COMMENT); [apply nd_c_COMMENT2; exact ND|].
    destruct (m_mode m =? HCRC); [apply nd_c_HCRC; exact ND|].
    destruct (m_mode m =? DICTID); [apply nd_c_DICTID; exact ND|].
    destruct (m_mode m =? DICT); [apply nd_c_DICT|].
    destruct (m_mode m =? Zlib.proof.inflate.Model.TYPE); [apply nd_c_TYPE; exact ND|].
    destruct (m_mode m =? TYPEDO); [apply nd_c_TYPEDO; exact ND|].
    destruct (m_mode m =? STORED); [apply nd_c_STORED; exact ND|].
    destruct (m_mode m =? COPY_); [apply nd_c_COPY_; exact ND|].
    destruct (m_mode m =? COPY); [apply nd_c_COPY; exact ND|].
    destruct (m_mode m =? TABLE); [apply nd_c_TABLE; exact ND|].
    destruct (m_mode m =? LENLENS); [apply nd_c_LENLENS; exact ND|].
    destruct (m_mode m =? CODELENS); [apply nd_c_CODELENS; exact ND|].
    destruct (m_mode m =? LEN_); [apply nd_c_LEN_; exact ND|].
    destruct (m_mode m =? LEN); [apply nd_c_LEN; exact ND|].
    destruct (m_mode m =? LENEXT); [apply nd_c_LENEXT; exact ND|].
    destruct (m_mode m =? DIST); [apply nd_c_DIST; exact ND|].
    destruct (m_mode m =? DISTEXT); [apply nd_c_DISTEXT; exact ND|].
    destruct (m_mode m =? MATCH); [apply nd_c_MATCH; exact ND|].
    destruct (m_mode m =? LIT); [apply nd_c_LIT; exact ND|].
    destruct (m_mode m =? CHECK); [apply nd_c_CHECK; exact ND|].
    destruct (m_mode m =? LENGTH); [apply nd_c_LENGTH; exact ND|].
    destruct (m_mode m =? DONE); [apply nd_c_DONE; exact ND|].
    destruct (m_mode m =? BAD); [apply nd_c_BAD; exact ND|].
    destruct (m_mode m =? MEM); exact I.
Qed.

End CasesND.

Lemma th_nodict : nodict_stmt.
Proof.
  intros flush m m' E.
  pose proof (nd_step2 flush lenfix_list distfix_list m) as G.
  unfold stepf2 in E; rewrite E in G; exact G.
Qed.

(* Law inflate_reset, theory: a one-stream fact of one pass of the switch (Model2.stepf2), used by IRRun.v next
   to the two-stream simulation (the sgroup parts): a pass from a valid mode other than SYNC never ends in
   SYNC, and returns (IRet) only Z_MEM_ERROR or c_DICT's Z_NEED_DICT (after RESTORE: mode DICT, next_out
   stored).  As inflate_codes' TheoryNoDict.v (nd_step2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition irp_good (o: iout) : Prop :=
  match o with
  | IBrk m' => m_mode m' <> SYNC
  | IRet r m' => r = Z_MEM_ERROR \/ (r = Z_NEED_DICT /\ m_mode m' = DICT /\ m_sow m' = Zlength (m_ow m'))
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* Frame facts of the helpers (a copy of inflate_api/StepInv5Kit.v, prefix irns_)                  *)

(* the facts kept by the helpers (needbits, lookups, the CODELENS loop, inflate_fast) *)
Definition irns_wkeep (m m': mst) : Prop :=
  i_mode (m_s m') = i_mode (m_s m) \/ i_mode (m_s m') = Zlib.proof.inflate.Model.TYPE \/ i_mode (m_s m') = BAD.

Lemma irns_wkeep_trans m1 m2 m3 : irns_wkeep m1 m2 -> irns_wkeep m2 m3 -> irns_wkeep m1 m3.
Proof. unfold irns_wkeep; intros F1 F2. destruct F2 as [F2|F2]; rewrite ?F2; auto. Qed.

Ltac irns_wmodes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma irns_needbits_f_k k n m :
  m_s (needbits_f k n m) = m_s m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_ow (needbits_f k n m) = m_ow m /\ m_out (needbits_f k n m) = m_out m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as (-> & -> & -> & ->); auto.
Qed.

Lemma irns_needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply irns_needbits_f_k. Qed.
Lemma irns_needbits_aout n m : m_aout (needbits n m) = m_aout m.
Proof. apply irns_needbits_f_k. Qed.
Lemma irns_needbits_ow n m : m_ow (needbits n m) = m_ow m.
Proof. apply irns_needbits_f_k. Qed.
Lemma irns_needbits_out n m : m_out (needbits n m) = m_out m.
Proof. apply irns_needbits_f_k. Qed.

Local Opaque needbits needbits_f.

Lemma irns_crc_if_win m d : i_win (m_s (crc_if m d)) = i_win (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma irns_crc_if_wbits m d : i_wbits (m_s (crc_if m d)) = i_wbits (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma irns_crc_if_mode m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma irns_crc_if_aout m d : m_aout (crc_if m d) = m_aout m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma irns_crc_if_ow m d : m_ow (crc_if m d) = m_ow m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.
Lemma irns_crc_if_out m d : m_out (crc_if m d) = m_out m.
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.

Lemma irns_lens_fill_k k len s :
  i_win (lens_fill k len s) = i_win s /\ i_wbits (lens_fill k len s) = i_wbits s /\
  i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|].
  match goal with |- context [lens_fill k len ?x] => destruct (IHk x) as (-> & -> & ->) end; auto. Qed.
Lemma irns_lens_fill_win k len s : i_win (lens_fill k len s) = i_win s.
Proof. apply irns_lens_fill_k. Qed.
Lemma irns_lens_fill_wbits k len s : i_wbits (lens_fill k len s) = i_wbits s.
Proof. apply irns_lens_fill_k. Qed.
Lemma irns_lens_fill_mode k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. apply irns_lens_fill_k. Qed.

Lemma irns_lenlens_zero_k k s :
  i_win (lenlens_zero k s) = i_win s /\ i_wbits (lenlens_zero k s) = i_wbits s /\
  i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto].
  match goal with |- context [lenlens_zero k ?x] => destruct (IHk x) as (-> & -> & ->) end; auto.
Qed.

Lemma irns_copy_f_len n w sr ow : Zlength ow <= Zlength (fst (copy_f n w sr ow)).
Proof.
  revert sr ow; induction n; intros sr ow; cbn [copy_f]; [cbn; lia|].
  destruct sr; (eapply Z.le_trans; [|apply IHn]); rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma irns_copy_bytes_len w sr n ow ow' sr' : copy_bytes w sr n ow = (ow', sr') -> Zlength ow <= Zlength ow'.
Proof.
  unfold copy_bytes; intros E. pose proof (irns_copy_f_len (Z.to_nat n) w sr ow) as H. rewrite E in H. exact H.
Qed.

Lemma irns_lookup1_f_k k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma irns_lookup1_k fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply irns_lookup1_f_k. Qed.

Lemma irns_lookup2_f_k k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as (-> & -> & -> & ->); auto.
Qed.

Lemma irns_lookup2_k fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof. apply irns_lookup2_f_k. Qed.

Lemma irns_fwalk_f_k fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') ->
  m_s m' = m_s m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\ m_out m' = m_out m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as (-> & -> & -> & ->); cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Definition irns_clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite irns_needbits_s irns_needbits_aout irns_needbits_ow irns_needbits_out irns_crc_if_win irns_crc_if_wbits irns_crc_if_mode
  irns_crc_if_aout irns_crc_if_ow irns_crc_if_out irns_lens_fill_win irns_lens_fill_wbits irns_lens_fill_mode : irns_wi.

(* destruct every closed if / match of the goal, innermost scrutinee first *)
Ltac irns_hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => irns_hdest c
  | context [match ?c with _ => _ end] => irns_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac irns_hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => irns_hdest x
          end).

Ltac irns_huse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply irns_lookup1_k in E; destruct E as (? & ? & ? & ?)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply irns_lookup2_k in E; destruct E as (? & ? & ? & ?)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply irns_fwalk_f_k in E; destruct E as (? & ? & ? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => apply irns_copy_bytes_len in E
  end.

Ltac irns_hrw :=
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

Ltac irns_hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength].

Ltac irns_hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength] in H.

(* normalize the helper facts, and rewrite them with each other *)
Ltac irns_hyp_norm :=
  repeat match goal with
  | H: m_s _ = _ |- _ => progress (irns_hcbn_in H; autorewrite with irns_wi in H)
  | H: m_aout _ = _ |- _ => progress (irns_hcbn_in H; autorewrite with irns_wi in H)
  | H: m_ow _ = _ |- _ => progress (irns_hcbn_in H; autorewrite with irns_wi in H)
  | H: m_out _ = _ |- _ => progress (irns_hcbn_in H; autorewrite with irns_wi in H)
  | H: Zlength _ <= Zlength _ |- _ => progress (irns_hcbn_in H; autorewrite with irns_wi in H)
  end;
  repeat match goal with
  | H: m_s ?a = _, H2: context [m_s ?a] |- _ => is_var a; rewrite H in H2
  | H: m_aout ?a = _, H2: context [m_aout ?a] |- _ => is_var a; rewrite H in H2
  | H: m_ow ?a = _, H2: context [m_ow ?a] |- _ => is_var a; rewrite H in H2
  | H: m_out ?a = _, H2: context [m_out ?a] |- _ => is_var a; rewrite H in H2
  end.

Ltac irns_wnorm := irns_hyp_norm; repeat progress (irns_hcbn; autorewrite with irns_wi; irns_hrw).

Ltac irns_zlnn :=
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

Ltac irns_wfin := unfold m_left, m_mode in *; rewrite ?Zlength_app in *; irns_zlnn; irns_wmodes;
  repeat split; try reflexivity; try lia.

Ltac irns_kclose := unfold irns_wkeep; irns_wnorm; irns_wfin.

Lemma irns_codelens_iter_k fx dx m : irns_wkeep m (irns_clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. irns_hsplit; irns_huse; irns_kclose. Qed.

Lemma irns_wkeep_refl m : irns_wkeep m m.
Proof. unfold irns_wkeep; auto. Qed.

Lemma irns_codelens_loop_k fx dx k m : irns_wkeep m (irns_clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply irns_wkeep_refl|].
  destruct (_ <? _); [|apply irns_wkeep_refl].
  pose proof (irns_codelens_iter_k fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply irns_wkeep_trans; [exact A | apply IHk].
Qed.

Lemma irns_lenlens_loop_k k m :
  m_aout (lenlens_loop k m) = m_aout m /\ m_out (lenlens_loop k m) = m_out m /\
  m_ow (lenlens_loop k m) = m_ow m /\ i_win (m_s (lenlens_loop k m)) = i_win (m_s m) /\
  i_wbits (m_s (lenlens_loop k m)) = i_wbits (m_s m) /\ i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [repeat split|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|repeat split].
  destruct (m_leave (needbits 3 m) =? 1); [autorewrite with irns_wi; repeat split|].
  match goal with |- context [lenlens_loop _ ?x] => destruct (IHk x) as (-> & -> & -> & -> & -> & ->) end.
  cbn. autorewrite with irns_wi; repeat split.
Qed.

(* a light closer for inflate_fast's leaves: only the mode matters *)
Ltac irns_fclose :=
  irns_huse;
  repeat match goal with
  | H: (_ = true) |- _ => clear H | H: (_ = false) |- _ => clear H
  | H: copy_bytes _ _ _ _ = _ |- _ => clear H
  | H: m_aout _ = _ |- _ => clear H | H: m_ow _ = _ |- _ => clear H | H: m_out _ = _ |- _ => clear H
  end;
  unfold irns_wkeep in *; cbn in *;
  first [left; congruence | right; left; reflexivity | right; right; reflexivity].

Lemma irns_fast_iter_k fx dx m : irns_wkeep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. irns_hsplit; irns_fclose. Qed.

Lemma irns_fast_loop_k fx dx k m : irns_wkeep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply irns_wkeep_refl|].
  pose proof (irns_fast_iter_k fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (andb _ _); [eapply irns_wkeep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma irns_fast_k fx dx m : irns_wkeep m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (irns_fast_loop_k fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply irns_wkeep_trans; [exact A|]. irns_kclose.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Ltac irns_mclose := unfold m_mode in *; irns_wnorm; irns_wfin.

Create HintDb irns_db.
#[export] Hint Extern 1 (m_mode _ <> SYNC) => irns_mclose : irns_db.
#[export] Hint Extern 1 (m_mode _ = DICT) => irns_mclose : irns_db.

Ltac irns_leaf :=
  match goal with
  | |- irp_good (IBrk _) => unfold irp_good; irns_mclose
  | |- irp_good (IRet _ _) => unfold irp_good; left; reflexivity
  | |- irp_good (?f ?x) => auto with irns_db
  end.

Ltac irns_case := irns_hsplit; irns_huse; irns_leaf.

Section CasesNS.
Variables (fl: Z) (fx dx: list entry).

Lemma irns_c_DONE m : m_mode m <> SYNC -> irp_good (c_DONE m).
Proof. intros H; unfold c_DONE; irns_case. Qed.
#[local] Hint Resolve irns_c_DONE : irns_db.
Lemma irns_c_BAD m : m_mode m <> SYNC -> irp_good (c_BAD m).
Proof. intros H; unfold c_BAD; irns_case. Qed.
#[local] Hint Resolve irns_c_BAD : irns_db.
Lemma irns_c_LENGTH m : m_mode m <> SYNC -> irp_good (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; irns_case. Qed.
#[local] Hint Resolve irns_c_LENGTH : irns_db.
Lemma irns_c_CHECK m : m_mode m <> SYNC -> irp_good (c_CHECK m).
Proof. intros H; unfold c_CHECK; irns_case. Qed.
#[local] Hint Resolve irns_c_CHECK : irns_db.
Lemma irns_c_LIT m : m_mode m <> SYNC -> irp_good (c_LIT m).
Proof. intros H; unfold c_LIT; irns_case. Qed.
#[local] Hint Resolve irns_c_LIT : irns_db.
Lemma irns_c_MATCH m : m_mode m <> SYNC -> irp_good (c_MATCH m).
Proof. intros H; unfold c_MATCH; irns_case. Qed.
#[local] Hint Resolve irns_c_MATCH : irns_db.
Lemma irns_c_DISTEXT m : m_mode m <> SYNC -> irp_good (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; irns_case. Qed.
#[local] Hint Resolve irns_c_DISTEXT : irns_db.
Lemma irns_c_DIST m : m_mode m <> SYNC -> irp_good (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; irns_case. Qed.
#[local] Hint Resolve irns_c_DIST : irns_db.
Lemma irns_c_LENEXT m : m_mode m <> SYNC -> irp_good (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; irns_case. Qed.
#[local] Hint Resolve irns_c_LENEXT : irns_db.
Lemma irns_c_LEN m : m_mode m <> SYNC -> irp_good (c_LEN fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LEN.
  pose proof (irns_fast_k fx dx (restore m)) as Hf; unfold irns_wkeep in Hf; irns_hcbn_in Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf.
  irns_case.
Qed.
#[local] Hint Resolve irns_c_LEN : irns_db.
Lemma irns_c_LEN_ m : m_mode m <> SYNC -> irp_good (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H; unfold c_LEN_; irns_case. Qed.
#[local] Hint Resolve irns_c_LEN_ : irns_db.
Lemma irns_c_CODELENS m : m_mode m <> SYNC -> irp_good (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_CODELENS.
  pose proof (irns_codelens_loop_k fx dx 320 m) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [irns_clm] in Hc; unfold irns_wkeep in Hc;
    irns_case.
Qed.
#[local] Hint Resolve irns_c_CODELENS : irns_db.
Lemma irns_c_LENLENS m : m_mode m <> SYNC -> irp_good (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (irns_lenlens_loop_k 19 m) as (A1 & A2 & A3 & A4 & A5 & A6); revert A1 A2 A3 A4 A5 A6.
  generalize (lenlens_loop 19 m); intros ml A1 A2 A3 A4 A5 A6.
  pose proof (irns_lenlens_zero_k 19 (m_s ml)) as (C1 & C2 & C3); revert C1 C2 C3.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C1 C2 C3.
  irns_case.
Qed.
#[local] Hint Resolve irns_c_LENLENS : irns_db.
Lemma irns_c_TABLE m : m_mode m <> SYNC -> irp_good (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros H; unfold c_TABLE; irns_case. Qed.
#[local] Hint Resolve irns_c_TABLE : irns_db.
Lemma irns_c_COPY m : m_mode m <> SYNC -> irp_good (c_COPY m).
Proof. intros H; unfold c_COPY; irns_case. Qed.
#[local] Hint Resolve irns_c_COPY : irns_db.
Lemma irns_c_COPY_ m : m_mode m <> SYNC -> irp_good (c_COPY_ m).
Proof. intros H; unfold c_COPY_; irns_case. Qed.
#[local] Hint Resolve irns_c_COPY_ : irns_db.
Lemma irns_c_STORED m : m_mode m <> SYNC -> irp_good (c_STORED fl m).
Proof. intros H; unfold c_STORED; irns_case. Qed.
#[local] Hint Resolve irns_c_STORED : irns_db.
Lemma irns_c_TYPEDO m : m_mode m <> SYNC -> irp_good (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; irns_case. Qed.
#[local] Hint Resolve irns_c_TYPEDO : irns_db.
Lemma irns_c_TYPE m : m_mode m <> SYNC -> irp_good (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; irns_case. Qed.
#[local] Hint Resolve irns_c_TYPE : irns_db.
Lemma irns_c_DICT m : m_mode m = DICT -> irp_good (c_DICT fl m).
Proof.
  intros H; unfold c_DICT; irns_hsplit.
  - unfold irp_good; right; split; [reflexivity|]. unfold m_mode in *; cbn in *. split; [exact H|reflexivity].
  - apply irns_c_TYPE. irns_mclose.
Qed.
#[local] Hint Resolve irns_c_DICT : irns_db.
Lemma irns_c_DICTID m : m_mode m <> SYNC -> irp_good (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; irns_case. Qed.
#[local] Hint Resolve irns_c_DICTID : irns_db.
Lemma irns_c_HCRC m : m_mode m <> SYNC -> irp_good (c_HCRC m).
Proof. intros H; unfold c_HCRC; irns_case. Qed.
#[local] Hint Resolve irns_c_HCRC : irns_db.
Lemma irns_c_COMMENT2 m : m_mode m <> SYNC -> irp_good (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; irns_case. Qed.
#[local] Hint Resolve irns_c_COMMENT2 : irns_db.
Lemma irns_c_NAME2 m : m_mode m <> SYNC -> irp_good (c_NAME2 m).
Proof. intros H; unfold c_NAME2; irns_case. Qed.
#[local] Hint Resolve irns_c_NAME2 : irns_db.
Lemma irns_c_EXTRA2 m : m_mode m <> SYNC -> irp_good (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; irns_case. Qed.
#[local] Hint Resolve irns_c_EXTRA2 : irns_db.
Lemma irns_c_EXLEN2 m : m_mode m <> SYNC -> irp_good (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; irns_case. Qed.
#[local] Hint Resolve irns_c_EXLEN2 : irns_db.
Lemma irns_c_OS2 m : m_mode m <> SYNC -> irp_good (c_OS2 m).
Proof. intros H; unfold c_OS2; irns_case. Qed.
#[local] Hint Resolve irns_c_OS2 : irns_db.
Lemma irns_c_TIME2 m : m_mode m <> SYNC -> irp_good (c_TIME2 m).
Proof. intros H; unfold c_TIME2; irns_case. Qed.
#[local] Hint Resolve irns_c_TIME2 : irns_db.
Lemma irns_c_FLAGS2 m : m_mode m <> SYNC -> irp_good (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; irns_case. Qed.
#[local] Hint Resolve irns_c_FLAGS2 : irns_db.
Lemma irns_c_HEAD m : m_mode m <> SYNC -> irp_good (c_HEAD2 m).
Proof. intros H; unfold c_HEAD2; irns_case. Qed.

Lemma irns_step2 m : HEAD <= m_mode m <= SYNC -> m_mode m <> SYNC -> irp_good (step2 fl fx dx (fast fx dx) m).
Proof.
  intros HR ND; unfold step2.
  destruct (Z.eq_dec (m_mode m) DICT) as [ED|NE].
  - rewrite ED. cbn -[c_DICT]. apply irns_c_DICT; exact ED.
  - destruct (m_mode m =? HEAD) eqn:?; [apply irns_c_HEAD; exact ND|].
    destruct (m_mode m =? FLAGS) eqn:?; [apply irns_c_FLAGS2; exact ND|].
    destruct (m_mode m =? TIME) eqn:?; [apply irns_c_TIME2; exact ND|].
    destruct (m_mode m =? OS) eqn:?; [apply irns_c_OS2; exact ND|].
    destruct (m_mode m =? EXLEN) eqn:?; [apply irns_c_EXLEN2; exact ND|].
    destruct (m_mode m =? EXTRA) eqn:?; [apply irns_c_EXTRA2; exact ND|].
    destruct (m_mode m =? NAME) eqn:?; [apply irns_c_NAME2; exact ND|].
    destruct (m_mode m =? COMMENT) eqn:?; [apply irns_c_COMMENT2; exact ND|].
    destruct (m_mode m =? HCRC) eqn:?; [apply irns_c_HCRC; exact ND|].
    destruct (m_mode m =? DICTID) eqn:?; [apply irns_c_DICTID; exact ND|].
    destruct (m_mode m =? DICT) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    destruct (m_mode m =? Zlib.proof.inflate.Model.TYPE) eqn:?; [apply irns_c_TYPE; exact ND|].
    destruct (m_mode m =? TYPEDO) eqn:?; [apply irns_c_TYPEDO; exact ND|].
    destruct (m_mode m =? STORED) eqn:?; [apply irns_c_STORED; exact ND|].
    destruct (m_mode m =? COPY_) eqn:?; [apply irns_c_COPY_; exact ND|].
    destruct (m_mode m =? COPY) eqn:?; [apply irns_c_COPY; exact ND|].
    destruct (m_mode m =? TABLE) eqn:?; [apply irns_c_TABLE; exact ND|].
    destruct (m_mode m =? LENLENS) eqn:?; [apply irns_c_LENLENS; exact ND|].
    destruct (m_mode m =? CODELENS) eqn:?; [apply irns_c_CODELENS; exact ND|].
    destruct (m_mode m =? LEN_) eqn:?; [apply irns_c_LEN_; exact ND|].
    destruct (m_mode m =? LEN) eqn:?; [apply irns_c_LEN; exact ND|].
    destruct (m_mode m =? LENEXT) eqn:?; [apply irns_c_LENEXT; exact ND|].
    destruct (m_mode m =? DIST) eqn:?; [apply irns_c_DIST; exact ND|].
    destruct (m_mode m =? DISTEXT) eqn:?; [apply irns_c_DISTEXT; exact ND|].
    destruct (m_mode m =? MATCH) eqn:?; [apply irns_c_MATCH; exact ND|].
    destruct (m_mode m =? LIT) eqn:?; [apply irns_c_LIT; exact ND|].
    destruct (m_mode m =? CHECK) eqn:?; [apply irns_c_CHECK; exact ND|].
    destruct (m_mode m =? LENGTH) eqn:?; [apply irns_c_LENGTH; exact ND|].
    destruct (m_mode m =? DONE) eqn:?; [apply irns_c_DONE; exact ND|].
    destruct (m_mode m =? BAD) eqn:?; [apply irns_c_BAD; exact ND|].
    destruct (m_mode m =? MEM) eqn:EM; [unfold irp_good; left; reflexivity|].
    exfalso. clear NE. revert HR ND.
    repeat match goal with H: (_ =? _) = false |- _ => apply Z.eqb_neq in H; revert H end.
    unfold m_mode; generalize (i_mode (m_s m)); intros z.
    irns_wmodes. lia.
Qed.

End CasesNS.

Lemma irps_nosync (flush: Z) (m: mst) :
  HEAD <= m_mode m <= SYNC -> m_mode m <> SYNC -> irp_good (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros HR ND. unfold stepf2. apply irns_step2; assumption.
Qed.

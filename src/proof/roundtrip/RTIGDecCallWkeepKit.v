(* RT-I: copy of rfc1951/DecCallWkeepKit.v over the generalized definitions RTIGDefs.v. *)
(* Part of dec_call: one pass of the switch of Model2.v (stepf2) keeps the window fields wsize,
   whave, wnext, wdata and win (every mode, HEAD too); the same scheme as src/proof/inflate/StepHd5.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Require Zlib.proof.inflate_api.StepInv5Kit.
Local Open Scope Z_scope.

Definition wf5 (s s': istate) : Prop :=
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\
  i_wdata s' = i_wdata s /\ i_win s' = i_win s.

Definition wkrel (m m': mst) : Prop := wf5 (m_s m) (m_s m').

Definition wkgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => wkrel m m' | IRet _ m' => wkrel m m' end.

Lemma wkrel_refl m : wkrel m m.
Proof. unfold wkrel, wf5; intuition. Qed.

Lemma wkrel_trans m1 m2 m3 : wkrel m1 m2 -> wkrel m2 m3 -> wkrel m1 m3.
Proof. unfold wkrel, wf5; intuition congruence. Qed.

Lemma wkgood_trans m m' o : wkrel m m' -> wkgood m' o -> wkgood m o.
Proof. destruct o; cbn; apply wkrel_trans. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply StepInv5Kit.needbits_s. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_s m d : wf5 (m_s m) (m_s (crc_if m d)).
Proof. unfold crc_if, wf5; destruct (_ && _); cbn; auto. Qed.

Lemma lens_fill_s k len s : wf5 s (lens_fill k len s).
Proof.
  revert s; induction k; intros s; cbn [lens_fill]; [unfold wf5; auto|].
  match goal with |- context [lens_fill k len ?x] => specialize (IHk x) end.
  unfold wf5 in *; cbn in *; intuition congruence.
Qed.

Lemma lenlens_zero_s k s : wf5 s (lenlens_zero k s).
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [unfold wf5; auto|].
  destruct (_ <? 19); [|unfold wf5; auto].
  match goal with |- context [lenlens_zero k ?x] => specialize (IHk x) end.
  unfold wf5 in *; cbn in *; intuition congruence.
Qed.

Lemma lenlens_loop_s k m : wf5 (m_s m) (m_s (lenlens_loop k m)).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [unfold wf5; auto|].
  destruct (_ <? _); [|unfold wf5; auto].
  destruct (m_leave (needbits 3 m) =? 1); [rewrite needbits_s; unfold wf5; auto|].
  match goal with |- context [lenlens_loop k ?x] => specialize (IHk x) end.
  unfold wf5 in *; cbn in *; rewrite needbits_s in *; cbn in *; intuition congruence.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Ltac wsplit H := unfold wf5 in H; destruct H as (? & ? & ? & ? & ?).

Lemma crc_if_ws m d : i_wsize (m_s (crc_if m d)) = i_wsize (m_s m).
Proof. apply crc_if_s. Qed.
Lemma crc_if_wh m d : i_whave (m_s (crc_if m d)) = i_whave (m_s m).
Proof. apply crc_if_s. Qed.
Lemma crc_if_wn m d : i_wnext (m_s (crc_if m d)) = i_wnext (m_s m).
Proof. apply crc_if_s. Qed.
Lemma crc_if_wd m d : i_wdata (m_s (crc_if m d)) = i_wdata (m_s m).
Proof. apply crc_if_s. Qed.
Lemma crc_if_wi m d : i_win (m_s (crc_if m d)) = i_win (m_s m).
Proof. apply crc_if_s. Qed.
Lemma lens_fill_ws k len s : i_wsize (lens_fill k len s) = i_wsize s.
Proof. apply lens_fill_s. Qed.
Lemma lens_fill_wh k len s : i_whave (lens_fill k len s) = i_whave s.
Proof. apply lens_fill_s. Qed.
Lemma lens_fill_wn k len s : i_wnext (lens_fill k len s) = i_wnext s.
Proof. apply lens_fill_s. Qed.
Lemma lens_fill_wd k len s : i_wdata (lens_fill k len s) = i_wdata s.
Proof. apply lens_fill_s. Qed.
Lemma lens_fill_wi k len s : i_win (lens_fill k len s) = i_win s.
Proof. apply lens_fill_s. Qed.
Lemma lenlens_zero_ws k s : i_wsize (lenlens_zero k s) = i_wsize s.
Proof. apply lenlens_zero_s. Qed.
Lemma lenlens_zero_wh k s : i_whave (lenlens_zero k s) = i_whave s.
Proof. apply lenlens_zero_s. Qed.
Lemma lenlens_zero_wn k s : i_wnext (lenlens_zero k s) = i_wnext s.
Proof. apply lenlens_zero_s. Qed.
Lemma lenlens_zero_wd k s : i_wdata (lenlens_zero k s) = i_wdata s.
Proof. apply lenlens_zero_s. Qed.
Lemma lenlens_zero_wi k s : i_win (lenlens_zero k s) = i_win s.
Proof. apply lenlens_zero_s. Qed.
Lemma lenlens_loop_ws k m : i_wsize (m_s (lenlens_loop k m)) = i_wsize (m_s m).
Proof. apply lenlens_loop_s. Qed.
Lemma lenlens_loop_wh k m : i_whave (m_s (lenlens_loop k m)) = i_whave (m_s m).
Proof. apply lenlens_loop_s. Qed.
Lemma lenlens_loop_wn k m : i_wnext (m_s (lenlens_loop k m)) = i_wnext (m_s m).
Proof. apply lenlens_loop_s. Qed.
Lemma lenlens_loop_wd k m : i_wdata (m_s (lenlens_loop k m)) = i_wdata (m_s m).
Proof. apply lenlens_loop_s. Qed.
Lemma lenlens_loop_wi k m : i_win (m_s (lenlens_loop k m)) = i_win (m_s m).
Proof. apply lenlens_loop_s. Qed.

Hint Rewrite needbits_s crc_if_ws crc_if_wh crc_if_wn crc_if_wd crc_if_wi
  lens_fill_ws lens_fill_wh lens_fill_wn lens_fill_wd lens_fill_wi
  lenlens_zero_ws lenlens_zero_wh lenlens_zero_wn lenlens_zero_wd lenlens_zero_wi
  lenlens_loop_ws lenlens_loop_wh lenlens_loop_wn lenlens_loop_wd lenlens_loop_wi : wk.

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
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply StepInv5Kit.lookup1_k in E; destruct E as (? & _ & _ & _)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply StepInv5Kit.lookup2_k in E; destruct E as (? & _ & _ & _)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply StepInv5Kit.fwalk_f_k in E; destruct E as (? & _ & _ & _)
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: i_wsize ?a = _ |- context [i_wsize ?a] => rewrite H
  | H: i_whave ?a = _ |- context [i_whave ?a] => rewrite H
  | H: i_wnext ?a = _ |- context [i_wnext ?a] => rewrite H
  | H: i_wdata ?a = _ |- context [i_wdata ?a] => rewrite H
  | H: i_win ?a = _ |- context [i_win ?a] => rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast] in H.

Ltac hnorm := repeat progress (hcbn; autorewrite with wk; hrw).

Ltac hhyp :=
  repeat match goal with
  | H: m_s ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  | H: i_wsize ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  | H: i_whave ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  | H: i_wnext ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  | H: i_wdata ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  | H: i_win ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with wk in H))
  end.

Ltac hclose := unfold wkrel, wf5; hhyp; hnorm; repeat split; auto.

Lemma codelens_iter_s fx dx m : wf5 (m_s m) (m_s (clm (codelens_iter fx dx m))).
Proof. unfold codelens_iter. hsplit; huse; hclose. Qed.

Lemma codelens_loop_s fx dx k m : wf5 (m_s m) (m_s (clm (codelens_loop fx dx k m))).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [unfold wf5; auto|].
  destruct (_ <? _); [|unfold wf5; auto].
  pose proof (codelens_iter_s fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  specialize (IHk m0). wsplit A; wsplit IHk. unfold wf5; repeat split; congruence.
Qed.

Lemma fast_iter_s fx dx m : wf5 (m_s m) (m_s (snd (fast_iter fx dx m))).
Proof. unfold fast_iter. hsplit; huse; hclose. Qed.

Lemma fast_loop_s fx dx k m : wf5 (m_s m) (m_s (fast_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [unfold wf5; auto|].
  pose proof (fast_iter_s fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [|exact A].
  specialize (IHk m1). wsplit A; wsplit IHk. unfold wf5; repeat split; congruence.
Qed.

Lemma fast_s fx dx m : wf5 (m_s m) (m_s (fast fx dx m)).
Proof. unfold fast. cbn. apply fast_loop_s. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb wkc.

Ltac hleaf :=
  match goal with
  | |- wkgood _ (IBrk _) => unfold wkgood; hclose
  | |- wkgood _ (IRet _ _) => unfold wkgood; hclose
  | |- wkgood ?m (?f ?x) => apply (wkgood_trans m x); [hclose | auto with wkc]
  end.

Ltac huse_cl :=
  repeat match goal with
  | E: codelens_loop ?a ?b ?k ?x = _ |- _ =>
      let H := fresh in pose proof (codelens_loop_s a b k x) as H; rewrite E in H; cbn [clm] in H;
      wsplit H; clear E
  end.

Ltac hcase := hsplit; huse; huse_cl; hleaf.

Section CasesWk.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_wk m : wkgood m (c_DONE m).
Proof. unfold c_DONE; hcase. Qed.
Hint Resolve c_DONE_wk : wkc.
Lemma c_BAD_wk m : wkgood m (c_BAD m).
Proof. unfold c_BAD; hcase. Qed.
Hint Resolve c_BAD_wk : wkc.
Lemma c_LENGTH_wk m : wkgood m (c_LENGTH m).
Proof. unfold c_LENGTH; hcase. Qed.
Hint Resolve c_LENGTH_wk : wkc.
Lemma c_CHECK_wk m : wkgood m (c_CHECK m).
Proof. unfold c_CHECK; hcase. Qed.
Hint Resolve c_CHECK_wk : wkc.
Lemma c_LIT_wk m : wkgood m (c_LIT m).
Proof. unfold c_LIT; hcase. Qed.
Hint Resolve c_LIT_wk : wkc.
Lemma c_MATCH_wk m : wkgood m (c_MATCH m).
Proof. unfold c_MATCH; hcase. Qed.
Hint Resolve c_MATCH_wk : wkc.
Lemma c_DISTEXT_wk m : wkgood m (c_DISTEXT m).
Proof. unfold c_DISTEXT; hcase. Qed.
Hint Resolve c_DISTEXT_wk : wkc.
Lemma c_DIST_wk m : wkgood m (c_DIST fx dx m).
Proof. unfold c_DIST; hcase. Qed.
Hint Resolve c_DIST_wk : wkc.
Lemma c_LENEXT_wk m : wkgood m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; hcase. Qed.
Hint Resolve c_LENEXT_wk : wkc.
Lemma c_LEN_wk m : wkgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold c_LEN.
  pose proof (fast_s fx dx (restore m)) as Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf; wsplit Hf; hhyp.
  hcase.
Qed.
Hint Resolve c_LEN_wk : wkc.
Lemma c_LEN__wk m : wkgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold c_LEN_; hcase. Qed.
Hint Resolve c_LEN__wk : wkc.


Lemma c_CODELENS_wk m : wkgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_CODELENS.
  pose proof (codelens_loop_s fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; wsplit H; hcase.
Time Qed.
Hint Resolve c_CODELENS_wk : wkc.
Lemma c_LENLENS_wk m : wkgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_s 19 m) as A; revert A.
  generalize (lenlens_loop 19 m); intros ml A.
  pose proof (lenlens_zero_s 19 (m_s ml)) as C; revert C.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C; wsplit A; wsplit C.
  hcase.
Time Qed.
Hint Resolve c_LENLENS_wk : wkc.
Lemma c_TABLE_wk m : wkgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold c_TABLE; hcase. Qed.
Hint Resolve c_TABLE_wk : wkc.
Lemma c_COPY_wk m : wkgood m (c_COPY m).
Proof. unfold c_COPY; hcase. Qed.
Hint Resolve c_COPY_wk : wkc.
Lemma c_COPY__wk m : wkgood m (c_COPY_ m).
Proof. unfold c_COPY_; hcase. Qed.
Hint Resolve c_COPY__wk : wkc.
Lemma c_STORED_wk m : wkgood m (c_STORED fl m).
Proof. unfold c_STORED; hcase. Qed.
Hint Resolve c_STORED_wk : wkc.
Lemma c_TYPEDO_wk m : wkgood m (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; hcase. Qed.
Hint Resolve c_TYPEDO_wk : wkc.
Lemma c_TYPE_wk m : wkgood m (c_TYPE fl m).
Proof. unfold c_TYPE; hcase. Qed.
Hint Resolve c_TYPE_wk : wkc.
Lemma c_DICT_wk m : wkgood m (c_DICT fl m).
Proof. unfold c_DICT; hcase. Qed.
Hint Resolve c_DICT_wk : wkc.
Lemma c_DICTID_wk m : wkgood m (c_DICTID fl m).
Proof. unfold c_DICTID; hcase. Qed.
Hint Resolve c_DICTID_wk : wkc.
Lemma c_HCRC_wk m : wkgood m (c_HCRC m).
Proof. unfold c_HCRC; hcase. Qed.
Hint Resolve c_HCRC_wk : wkc.
Lemma c_COMMENT2_wk m : wkgood m (c_COMMENT2 m).
Proof. unfold c_COMMENT2; hcase. Qed.
Hint Resolve c_COMMENT2_wk : wkc.
Lemma c_NAME2_wk m : wkgood m (c_NAME2 m).
Proof. unfold c_NAME2; hcase. Qed.
Hint Resolve c_NAME2_wk : wkc.
Lemma c_EXTRA2_wk m : wkgood m (c_EXTRA2 m).
Proof. unfold c_EXTRA2; hcase. Qed.
Hint Resolve c_EXTRA2_wk : wkc.
Lemma c_EXLEN2_wk m : wkgood m (c_EXLEN2 m).
Proof. unfold c_EXLEN2; hcase. Qed.
Hint Resolve c_EXLEN2_wk : wkc.
Lemma c_OS2_wk m : wkgood m (c_OS2 m).
Proof. unfold c_OS2; hcase. Qed.
Hint Resolve c_OS2_wk : wkc.
Lemma c_TIME2_wk m : wkgood m (c_TIME2 m).
Proof. unfold c_TIME2; hcase. Qed.
Hint Resolve c_TIME2_wk : wkc.
Lemma c_FLAGS2_wk m : wkgood m (c_FLAGS2 m).
Proof. unfold c_FLAGS2; hcase. Qed.
Hint Resolve c_FLAGS2_wk : wkc.
Lemma c_HEAD_wk m : wkgood m (c_HEAD2 m).
Proof. unfold c_HEAD2; hcase. Qed.
Hint Resolve c_HEAD_wk : wkc.

Lemma stepf2_wkgood m : wkgood m (stepf2 fl fx dx m).
Proof.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD); [apply c_HEAD_wk|].
  destruct (m_mode m =? FLAGS); [apply c_FLAGS2_wk|].
  destruct (m_mode m =? TIME); [apply c_TIME2_wk|].
  destruct (m_mode m =? OS); [apply c_OS2_wk|].
  destruct (m_mode m =? EXLEN); [apply c_EXLEN2_wk|].
  destruct (m_mode m =? EXTRA); [apply c_EXTRA2_wk|].
  destruct (m_mode m =? NAME); [apply c_NAME2_wk|].
  destruct (m_mode m =? COMMENT); [apply c_COMMENT2_wk|].
  destruct (m_mode m =? HCRC); [apply c_HCRC_wk|].
  destruct (m_mode m =? DICTID); [apply c_DICTID_wk|].
  destruct (m_mode m =? DICT); [apply c_DICT_wk|].
  destruct (m_mode m =? TYPE); [apply c_TYPE_wk|].
  destruct (m_mode m =? TYPEDO); [apply c_TYPEDO_wk|].
  destruct (m_mode m =? STORED); [apply c_STORED_wk|].
  destruct (m_mode m =? COPY_); [apply c_COPY__wk|].
  destruct (m_mode m =? COPY); [apply c_COPY_wk|].
  destruct (m_mode m =? TABLE); [apply c_TABLE_wk|].
  destruct (m_mode m =? LENLENS); [apply c_LENLENS_wk|].
  destruct (m_mode m =? CODELENS); [apply c_CODELENS_wk|].
  destruct (m_mode m =? LEN_); [apply c_LEN__wk|].
  destruct (m_mode m =? LEN); [apply c_LEN_wk|].
  destruct (m_mode m =? LENEXT); [apply c_LENEXT_wk|].
  destruct (m_mode m =? DIST); [apply c_DIST_wk|].
  destruct (m_mode m =? DISTEXT); [apply c_DISTEXT_wk|].
  destruct (m_mode m =? MATCH); [apply c_MATCH_wk|].
  destruct (m_mode m =? LIT); [apply c_LIT_wk|].
  destruct (m_mode m =? CHECK); [apply c_CHECK_wk|].
  destruct (m_mode m =? LENGTH); [apply c_LENGTH_wk|].
  destruct (m_mode m =? DONE); [apply c_DONE_wk|].
  destruct (m_mode m =? BAD); [apply c_BAD_wk|].
  destruct (m_mode m =? MEM); exact (wkrel_refl m).
Qed.

End CasesWk.

Lemma stepf2_wkrel fl fx dx m :
  match stepf2 fl fx dx m with IBrk m' => wkrel m m' | IRet _ m' => wkrel m m' end.
Proof. exact (stepf2_wkgood fl fx dx m). Qed.

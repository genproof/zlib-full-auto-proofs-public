(* One pass of the switch of Model2.v (stepf2) only ever sets `leave` to 1 (set_leave): from a loop head with
   leave = 0, the next loop head has leave 0 or 1.  Used by the call lemma (SICall.v) to apply the simulation
   lemmas (which start from leave = 0) at every loop head of a call. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

(* r m m': the pass from m to m' kept `leave` or set it to 1 *)
Definition lrel (m m': mst) : Prop := m_leave m' = m_leave m \/ m_leave m' = 1.

Definition lgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => lrel m m' | IRet _ m' => lrel m m' end.

Lemma lrel_refl m : lrel m m.
Proof. left; reflexivity. Qed.

Lemma lrel_trans m1 m2 m3 : lrel m1 m2 -> lrel m2 m3 -> lrel m1 m3.
Proof. unfold lrel; intuition congruence. Qed.

Lemma lgood_trans m m' o : lrel m m' -> lgood m' o -> lgood m o.
Proof. destruct o; cbn; apply lrel_trans. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers: NEEDBITS and the lookups set leave (input exhausted), the others keep it          *)

Lemma needbits_l n m : lrel m (needbits n m).
Proof.
  unfold needbits; generalize 4%nat as k; intros k.
  revert m; induction k; intros m; cbn [needbits_f]; [apply lrel_refl|].
  destruct (m_bits m <? n); [|apply lrel_refl].
  destruct (m_have m =? 0); [right; reflexivity|].
  exact (IHk (pull m)).
Qed.

Lemma crc_if_l m d : m_leave (crc_if m d) = m_leave m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Local Opaque needbits needbits_f.

Lemma lenlens_loop_l k m : lrel m (lenlens_loop k m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [apply lrel_refl|].
  destruct (_ <? _); [|apply lrel_refl].
  destruct (m_leave (needbits 3 m) =? 1); [apply needbits_l|].
  eapply lrel_trans; [apply (needbits_l 3 m)|].
  eapply lrel_trans; [|apply IHk].
  unfold lrel; left; cbn [dropbits upd_s set_m_s set_m_bits set_m_hold m_leave]; reflexivity.
Qed.

Lemma lookup1_l fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) -> lrel m m'.
Proof.
  unfold lookup1; generalize 3%nat as k; intros k.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; subst; apply lrel_refl.
  - destruct (_ <=? _); [inversion E; subst; apply lrel_refl|].
    destruct (m_have m =? 0); [inversion E; subst; right; reflexivity|].
    apply IHk in E. exact E.
Qed.

Lemma lookup2_l fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) -> lrel m m'.
Proof.
  unfold lookup2; generalize 3%nat as k; intros k.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; subst; apply lrel_refl.
  - destruct (_ <=? _); [inversion E; subst; apply lrel_refl|].
    destruct (m_have m =? 0); [inversion E; subst; right; reflexivity|].
    apply IHk in E. exact E.
Qed.

Lemma fwalk_f_l fx dx k il t here m h' m' : fwalk_f fx dx k il t here m = (h', m') -> m_leave m' = m_leave m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; reflexivity.
  - destruct (il _); [apply IHk in E; rewrite E; reflexivity|inversion E; subst; reflexivity].
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

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

Ltac lcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast].
Ltac lcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast] in H.

(* turn the equations of the destructed helper calls into facts on leave *)
Ltac luse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_l in E
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_l in E
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_l in E
  end.

(* abstract the NEEDBITS / lenlens_loop calls of the goal, with their fact on leave *)
Ltac labs :=
  repeat match goal with
  | |- context [needbits ?n ?x] =>
      let H := fresh "L" in pose proof (needbits_l n x) as H; revert H;
      generalize (needbits n x); intros ? H
  | |- context [lenlens_loop ?k ?x] =>
      let H := fresh "L" in pose proof (lenlens_loop_l k x) as H; revert H;
      generalize (lenlens_loop k x); intros ? H
  end.

(* goal lrel a b: reduce every leave to the leave of an atom, then case on the facts *)
Ltac lclose :=
  labs; unfold lrel in *;
  repeat match goal with
  | H: context [m_leave ?a] |- _ =>
      tryif is_var a then fail else (progress (lcbn_in H; repeat (rewrite crc_if_l in H; lcbn_in H)))
  end;
  lcbn; repeat (rewrite crc_if_l; lcbn);
  repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] end;
  first [left; congruence | right; congruence].

Lemma codelens_iter_l fx dx m : lrel m (clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. hsplit; luse; lclose. Qed.

Lemma codelens_loop_l fx dx k m : lrel m (clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply lrel_refl|].
  destruct (_ <? _); [|apply lrel_refl].
  pose proof (codelens_iter_l fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply lrel_trans; [exact A|apply IHk].
Qed.

Lemma fast_iter_l fx dx m : m_leave (snd (fast_iter fx dx m)) = m_leave m.
Proof.
  unfold fast_iter. hsplit; luse; lcbn;
  repeat match goal with H: m_leave _ = _ |- _ => lcbn_in H; revert H end; intros; congruence.
Qed.

Lemma fast_loop_l fx dx k m : m_leave (fast_loop fx dx k m) = m_leave m.
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [reflexivity|].
  pose proof (fast_iter_l fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [rewrite IHk|]; exact A.
Qed.

Lemma fast_l fx dx m : m_leave (fast fx dx m) = m_leave m.
Proof. unfold fast. cbn. apply fast_loop_l. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb lvc.

Ltac lleaf :=
  match goal with
  | |- lgood _ (IBrk _) => unfold lgood; lclose
  | |- lgood _ (IRet _ _) => unfold lgood; lclose
  | |- lgood ?m (?f ?x) => apply (lgood_trans m x); [lclose | auto with lvc]
  end.

Ltac luse_cl :=
  repeat match goal with
  | E: codelens_loop ?a ?b ?k ?x = _ |- _ =>
      let H := fresh in pose proof (codelens_loop_l a b k x) as H; rewrite E in H; cbn [clm] in H; clear E
  end.

Ltac lcase := hsplit; luse; luse_cl; lleaf.

Section CasesL.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_l m : lgood m (c_DONE m).
Proof. unfold c_DONE; lcase. Qed.
Hint Resolve c_DONE_l : lvc.
Lemma c_BAD_l m : lgood m (c_BAD m).
Proof. unfold c_BAD; lcase. Qed.
Hint Resolve c_BAD_l : lvc.
Lemma c_LENGTH_l m : lgood m (c_LENGTH m).
Proof. unfold c_LENGTH; lcase. Qed.
Hint Resolve c_LENGTH_l : lvc.
Lemma c_CHECK_l m : lgood m (c_CHECK m).
Proof. unfold c_CHECK; lcase. Qed.
Hint Resolve c_CHECK_l : lvc.
Lemma c_LIT_l m : lgood m (c_LIT m).
Proof. unfold c_LIT; lcase. Qed.
Hint Resolve c_LIT_l : lvc.
Lemma c_MATCH_l m : lgood m (c_MATCH m).
Proof. unfold c_MATCH; lcase. Qed.
Hint Resolve c_MATCH_l : lvc.
Lemma c_DISTEXT_l m : lgood m (c_DISTEXT m).
Proof. unfold c_DISTEXT; lcase. Qed.
Hint Resolve c_DISTEXT_l : lvc.
Lemma c_DIST_l m : lgood m (c_DIST fx dx m).
Proof. unfold c_DIST; lcase. Qed.
Hint Resolve c_DIST_l : lvc.
Lemma c_LENEXT_l m : lgood m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; lcase. Qed.
Hint Resolve c_LENEXT_l : lvc.
Lemma c_LEN_l m : lgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold c_LEN.
  pose proof (fast_l fx dx (restore m)) as Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf; lcbn_in Hf.
  lcase.
Qed.
Hint Resolve c_LEN_l : lvc.
Lemma c_LEN__l m : lgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold c_LEN_; lcase. Qed.
Hint Resolve c_LEN__l : lvc.
Lemma c_CODELENS_l m : lgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_CODELENS.
  pose proof (codelens_loop_l fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; lcase.
Qed.
Hint Resolve c_CODELENS_l : lvc.
Lemma c_LENLENS_l m : lgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_l 19 m) as A; revert A.
  generalize (lenlens_loop 19 m); intros ml A.
  lcase.
Qed.
Hint Resolve c_LENLENS_l : lvc.
Lemma c_TABLE_l m : lgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold c_TABLE; lcase. Qed.
Hint Resolve c_TABLE_l : lvc.
Lemma c_COPY_l m : lgood m (c_COPY m).
Proof. unfold c_COPY; lcase. Qed.
Hint Resolve c_COPY_l : lvc.
Lemma c_COPY__l m : lgood m (c_COPY_ m).
Proof. unfold c_COPY_; lcase. Qed.
Hint Resolve c_COPY__l : lvc.
Lemma c_STORED_l m : lgood m (c_STORED fl m).
Proof. unfold c_STORED; lcase. Qed.
Hint Resolve c_STORED_l : lvc.
Lemma c_TYPEDO_l m : lgood m (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; lcase. Qed.
Hint Resolve c_TYPEDO_l : lvc.
Lemma c_TYPE_l m : lgood m (c_TYPE fl m).
Proof. unfold c_TYPE; lcase. Qed.
Hint Resolve c_TYPE_l : lvc.
Lemma c_DICT_l m : lgood m (c_DICT fl m).
Proof. unfold c_DICT; lcase. Qed.
Hint Resolve c_DICT_l : lvc.
Lemma c_DICTID_l m : lgood m (c_DICTID fl m).
Proof. unfold c_DICTID; lcase. Qed.
Hint Resolve c_DICTID_l : lvc.
Lemma c_HCRC_l m : lgood m (c_HCRC m).
Proof. unfold c_HCRC; lcase. Qed.
Hint Resolve c_HCRC_l : lvc.
Lemma c_COMMENT2_l m : lgood m (c_COMMENT2 m).
Proof. unfold c_COMMENT2; lcase. Qed.
Hint Resolve c_COMMENT2_l : lvc.
Lemma c_NAME2_l m : lgood m (c_NAME2 m).
Proof. unfold c_NAME2; lcase. Qed.
Hint Resolve c_NAME2_l : lvc.
Lemma c_EXTRA2_l m : lgood m (c_EXTRA2 m).
Proof. unfold c_EXTRA2; lcase. Qed.
Hint Resolve c_EXTRA2_l : lvc.
Lemma c_EXLEN2_l m : lgood m (c_EXLEN2 m).
Proof. unfold c_EXLEN2; lcase. Qed.
Hint Resolve c_EXLEN2_l : lvc.
Lemma c_OS2_l m : lgood m (c_OS2 m).
Proof. unfold c_OS2; lcase. Qed.
Hint Resolve c_OS2_l : lvc.
Lemma c_TIME2_l m : lgood m (c_TIME2 m).
Proof. unfold c_TIME2; lcase. Qed.
Hint Resolve c_TIME2_l : lvc.
Lemma c_FLAGS2_l m : lgood m (c_FLAGS2 m).
Proof. unfold c_FLAGS2; lcase. Qed.
Hint Resolve c_FLAGS2_l : lvc.
Lemma c_HEAD2_l m : lgood m (c_HEAD2 m).
Proof. unfold c_HEAD2; lcase. Qed.
Hint Resolve c_HEAD2_l : lvc.

Lemma stepf2_lgood m : lgood m (stepf2 fl fx dx m).
Proof.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD); [apply c_HEAD2_l|].
  destruct (m_mode m =? FLAGS); [apply c_FLAGS2_l|].
  destruct (m_mode m =? TIME); [apply c_TIME2_l|].
  destruct (m_mode m =? OS); [apply c_OS2_l|].
  destruct (m_mode m =? EXLEN); [apply c_EXLEN2_l|].
  destruct (m_mode m =? EXTRA); [apply c_EXTRA2_l|].
  destruct (m_mode m =? NAME); [apply c_NAME2_l|].
  destruct (m_mode m =? COMMENT); [apply c_COMMENT2_l|].
  destruct (m_mode m =? HCRC); [apply c_HCRC_l|].
  destruct (m_mode m =? DICTID); [apply c_DICTID_l|].
  destruct (m_mode m =? DICT); [apply c_DICT_l|].
  destruct (m_mode m =? TYPE); [apply c_TYPE_l|].
  destruct (m_mode m =? TYPEDO); [apply c_TYPEDO_l|].
  destruct (m_mode m =? STORED); [apply c_STORED_l|].
  destruct (m_mode m =? COPY_); [apply c_COPY__l|].
  destruct (m_mode m =? COPY); [apply c_COPY_l|].
  destruct (m_mode m =? TABLE); [apply c_TABLE_l|].
  destruct (m_mode m =? LENLENS); [apply c_LENLENS_l|].
  destruct (m_mode m =? CODELENS); [apply c_CODELENS_l|].
  destruct (m_mode m =? LEN_); [apply c_LEN__l|].
  destruct (m_mode m =? LEN); [apply c_LEN_l|].
  destruct (m_mode m =? LENEXT); [apply c_LENEXT_l|].
  destruct (m_mode m =? DIST); [apply c_DIST_l|].
  destruct (m_mode m =? DISTEXT); [apply c_DISTEXT_l|].
  destruct (m_mode m =? MATCH); [apply c_MATCH_l|].
  destruct (m_mode m =? LIT); [apply c_LIT_l|].
  destruct (m_mode m =? CHECK); [apply c_CHECK_l|].
  destruct (m_mode m =? LENGTH); [apply c_LENGTH_l|].
  destruct (m_mode m =? DONE); [apply c_DONE_l|].
  destruct (m_mode m =? BAD); [apply c_BAD_l|].
  destruct (m_mode m =? MEM); exact (lrel_refl m).
Qed.

End CasesL.

Lemma si_call_leave : forall fl fx dx m,
  match stepf2 fl fx dx m with
  | IBrk m' => m_leave m' = m_leave m \/ m_leave m' = 1
  | IRet _ m' => m_leave m' = m_leave m \/ m_leave m' = 1
  end.
Proof. intros fl fx dx m. exact (stepf2_lgood fl fx dx m). Qed.

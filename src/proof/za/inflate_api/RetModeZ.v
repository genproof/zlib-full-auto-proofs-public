(* A pass of the switch (Model2.v stepf2) that returns from inside inflate() -- Z_NEED_DICT in DICT,
   Z_MEM_ERROR in MEM, Z_STREAM_ERROR on a mode outside the switch -- leaves the saved state in neither
   EXLEN nor EXTRA.  So the gzip-extra facts of InvW.swfW (which constrain only those two modes) hold for
   the state such a return hands back to the application: inflate()'s postcondition (Spec5.inflate_spec_za)
   asks for them.  Likewise a return in mode MEM is MEM's own return (stepf2_ret_mem): the allocator's
   events of the call (ZEvents.win_ev) record no failed allocation for it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

(* [retd o]: if [o] is a return from inflate(), the state it saves is in mode DICT (the only return
   reached through a case of the switch is DICT's Z_NEED_DICT). *)
Definition retd (o: iout) : Prop :=
  match o with IBrk _ => True | IRet _ m' => i_mode (m_s m') = DICT end.

Lemma retd_brk m : retd (IBrk m).
Proof. exact I. Qed.

Lemma retd_if (b: bool) x y : retd x -> retd y -> retd (if b then x else y).
Proof. destruct b; auto. Qed.

(* walk down a case's body: split every test and every tuple-valued let, close the breaks, and use
   the lemmas of the cases it falls through to *)
Ltac retd_go :=
  repeat match goal with
  | |- retd (IBrk _) => apply retd_brk
  | |- retd (if _ then _ else _) => apply retd_if
  | |- retd (match ?p with (_, _) => _ end) => destruct p
  | |- retd (match ?p with CLnext _ => _ | CLleave _ => _ | CLbad _ => _ end) => destruct p
  | |- retd (let _ := _ in _) => cbv zeta
  | |- retd _ => solve [auto with retd]
  end.

Create HintDb retd.

(* every case of the switch, from the ones others fall through into up to HEAD: a return it makes
   saves a state in mode DICT *)
Section Cases.
Variables (fl: Z) (fx dx: list entry) (fs: mst -> mst).

Lemma c_DONE_r m : retd (c_DONE m).        Proof. exact I. Qed.
#[local] Hint Resolve c_DONE_r : retd.
Lemma c_BAD_r m : retd (c_BAD m).          Proof. exact I. Qed.
#[local] Hint Resolve c_BAD_r : retd.
Lemma c_LENGTH_r m : retd (c_LENGTH m).
Proof. unfold c_LENGTH; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_LENGTH_r : retd.
Lemma c_CHECK_r m : retd (c_CHECK m).
Proof. unfold c_CHECK; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_CHECK_r : retd.
Lemma c_LIT_r m : retd (c_LIT m).
Proof. unfold c_LIT; retd_go. Qed.
#[local] Hint Resolve c_LIT_r : retd.
Lemma c_MATCH_r m : retd (c_MATCH m).
Proof. unfold c_MATCH; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_MATCH_r : retd.
Lemma c_DISTEXT_r m : retd (c_DISTEXT m).
Proof. unfold c_DISTEXT; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_DISTEXT_r : retd.
Lemma c_DIST_r m : retd (c_DIST fx dx m).
Proof. unfold c_DIST; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_DIST_r : retd.
Lemma c_LENEXT_r m : retd (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_LENEXT_r : retd.
Lemma c_LEN_r m : retd (c_LEN fx dx fs m).
Proof. unfold c_LEN; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_LEN_r : retd.
Lemma c_LEN__r m : retd (c_LEN_ fx dx fs m).
Proof. apply c_LEN_r. Qed.
#[local] Hint Resolve c_LEN__r : retd.
Lemma c_CODELENS_r m : retd (c_CODELENS fl fx dx fs m).
Proof. unfold c_CODELENS; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_CODELENS_r : retd.
Lemma c_LENLENS_r m : retd (c_LENLENS fl fx dx fs m).
Proof. unfold c_LENLENS; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_LENLENS_r : retd.
Lemma c_TABLE_r m : retd (c_TABLE fl fx dx fs m).
Proof. unfold c_TABLE; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_TABLE_r : retd.
Lemma c_COPY_r m : retd (c_COPY m).
Proof. unfold c_COPY; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_COPY_r : retd.
Lemma c_COPY__r m : retd (c_COPY_ m).
Proof. apply c_COPY_r. Qed.
#[local] Hint Resolve c_COPY__r : retd.
Lemma c_STORED_r m : retd (c_STORED fl m).
Proof. unfold c_STORED; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_STORED_r : retd.
Lemma c_TYPEDO_r m : retd (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_TYPEDO_r : retd.
Lemma c_TYPE_r m : retd (c_TYPE fl m).
Proof. unfold c_TYPE; retd_go. Qed.
#[local] Hint Resolve c_TYPE_r : retd.

(* DICT returns Z_NEED_DICT with the state it was entered in, up to the stream positions *)
Lemma c_DICT_r m : i_mode (m_s m) = DICT -> retd (c_DICT fl m).
Proof.
  intros H; unfold c_DICT; cbv zeta; apply retd_if; [|apply c_TYPE_r].
  (* restore and the stream-position setter keep the mode *)
  exact H.
Qed.

Lemma c_DICTID_r m : retd (c_DICTID fl m).
Proof.
  unfold c_DICTID; cbv zeta; apply retd_if; [apply retd_brk|].
  apply c_DICT_r. reflexivity.
Qed.
#[local] Hint Resolve c_DICTID_r : retd.

Lemma c_HCRC_r m : retd (c_HCRC m).
Proof. unfold c_HCRC; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_HCRC_r : retd.
Lemma c_COMMENT2_r m : retd (c_COMMENT2 m).
Proof. unfold c_COMMENT2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_COMMENT2_r : retd.
Lemma c_NAME2_r m : retd (c_NAME2 m).
Proof. unfold c_NAME2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_NAME2_r : retd.
Lemma c_EXTRA2_r m : retd (c_EXTRA2 m).
Proof. unfold c_EXTRA2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_EXTRA2_r : retd.
Lemma c_EXLEN2_r m : retd (c_EXLEN2 m).
Proof. unfold c_EXLEN2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_EXLEN2_r : retd.
Lemma c_OS2_r m : retd (c_OS2 m).
Proof. unfold c_OS2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_OS2_r : retd.
Lemma c_TIME2_r m : retd (c_TIME2 m).
Proof. unfold c_TIME2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_TIME2_r : retd.
Lemma c_FLAGS2_r m : retd (c_FLAGS2 m).
Proof. unfold c_FLAGS2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_FLAGS2_r : retd.
Lemma c_HEAD2_r m : retd (c_HEAD2 m).
Proof. unfold c_HEAD2; cbv zeta; retd_go. Qed.
#[local] Hint Resolve c_HEAD2_r : retd.

End Cases.

#[local] Hint Resolve c_DONE_r c_BAD_r c_LENGTH_r c_CHECK_r c_LIT_r c_MATCH_r c_DISTEXT_r c_DIST_r
  c_LENEXT_r c_LEN_r c_LEN__r c_CODELENS_r c_LENLENS_r c_TABLE_r c_COPY_r c_COPY__r c_STORED_r
  c_TYPEDO_r c_TYPE_r c_DICTID_r c_HCRC_r c_COMMENT2_r c_NAME2_r c_EXTRA2_r c_EXLEN2_r c_OS2_r
  c_TIME2_r c_FLAGS2_r c_HEAD2_r : retd.

Lemma retd_mode o r m' : retd o -> o = IRet r m' -> i_mode (m_s m') <> EXLEN /\ i_mode (m_s m') <> EXTRA.
Proof. intros R ->; cbn in R; rewrite R; split; cbv; discriminate. Qed.

Lemma stepf2_ret_mode: forall fl fx dx m r m',
  stepf2 fl fx dx m = IRet r m' -> i_mode (m_s m') <> EXLEN /\ i_mode (m_s m') <> EXTRA.
Proof.
  intros fl fx dx m r m' H; unfold stepf2, step2 in H.
  repeat match type of H with (if ?b then _ else _) = _ => let E := fresh "E" in destruct b eqn:E end.
  all: try (eapply retd_mode; [|exact H]; auto with retd; fail).
  - (* DICT *)
    eapply retd_mode; [|exact H]. apply c_DICT_r. apply Z.eqb_eq; assumption.
  - (* MEM *)
    inversion H; subst. unfold m_mode in *. split; intro X; rewrite X in *; discriminate.
  - (* a mode outside the switch: returned unchanged *)
    inversion H; subst. unfold m_mode in *. split; intro X; rewrite X in *; cbv in *; discriminate.
Qed.

Lemma retd_mem o r m' : retd o -> o = IRet r m' -> i_mode (m_s m') <> MEM.
Proof. intros R ->; cbn in R; rewrite R; cbv; discriminate. Qed.

(* a return in mode MEM returns the state MEM was entered in *)
Lemma stepf2_ret_mem: forall fl fx dx m r m',
  stepf2 fl fx dx m = IRet r m' -> i_mode (m_s m') = MEM -> i_mode (m_s m) = MEM.
Proof.
  intros fl fx dx m r m' H HM; unfold stepf2, step2 in H.
  repeat match type of H with (if ?b then _ else _) = _ => let E := fresh "E" in destruct b eqn:E end.
  all: try (exfalso; eapply retd_mem; [|exact H|exact HM]; auto with retd; fail).
  - (* DICT *)
    exfalso. eapply retd_mem; [|exact H|exact HM]. apply c_DICT_r. apply Z.eqb_eq; assumption.
  - (* MEM *)
    inversion H; subst. exact HM.
  - (* a mode outside the switch: returned unchanged *)
    inversion H; subst. exact HM.
Qed.

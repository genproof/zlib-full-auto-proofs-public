(* Part of RT-I: one pass of the switch of Model2.v (stepf2) from a mode after the header modes
   keeps the application's gz_header m_h.  The same scheme as rfc1951/DecCallWkeepKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

Definition hkrel (m m': mst) : Prop := m_h m' = m_h m.

Definition hkgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => hkrel m m' | IRet _ m' => hkrel m m' end.

Lemma hkrel_refl m : hkrel m m.
Proof. reflexivity. Qed.

Lemma hkgood_trans m m' o : hkrel m m' -> hkgood m' o -> hkgood m o.
Proof. unfold hkrel; destruct o; cbn; congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma needbits_f_h k n m : m_h (needbits_f k n m) = m_h m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  rewrite IHk; reflexivity.
Qed.

Lemma needbits_h n m : m_h (needbits n m) = m_h m.
Proof. apply needbits_f_h. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_h m d : m_h (crc_if m d) = m_h m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_h k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) -> m_h m' = m_h m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; rewrite E; reflexivity.
Qed.

Lemma lookup1_h fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) -> m_h m' = m_h m.
Proof. apply lookup1_f_h. Qed.

Lemma lookup2_f_h k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) -> m_h m' = m_h m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; rewrite E; reflexivity.
Qed.

Lemma lookup2_h fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) -> m_h m' = m_h m.
Proof. apply lookup2_f_h. Qed.

Lemma fwalk_f_h fx dx k il t here m h' m' : fwalk_f fx dx k il t here m = (h', m') -> m_h m' = m_h m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; rewrite E; cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Lemma lenlens_loop_h k m : m_h (lenlens_loop k m) = m_h m.
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (m_leave (needbits 3 m) =? 1); [cbn; rewrite ?needbits_h; auto|].
  rewrite IHk; cbn; rewrite ?needbits_h; auto.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite needbits_h crc_if_h lenlens_loop_h : hk.

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
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_h in E
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_h in E
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_h in E
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_h ?a = _ |- context [m_h ?a] => rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast] in H.

Ltac hnorm := repeat progress (hcbn; autorewrite with hk; hrw).

Ltac hhyp :=
  repeat match goal with
  | H: m_h ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with hk in H))
  end.

Ltac hclose := unfold hkrel; hhyp; hnorm; auto.

Lemma codelens_iter_h fx dx m : m_h (clm (codelens_iter fx dx m)) = m_h m.
Proof. unfold codelens_iter. hsplit; huse; hclose. Qed.

Lemma codelens_loop_h fx dx k m : m_h (clm (codelens_loop fx dx k m)) = m_h m.
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  pose proof (codelens_iter_h fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  rewrite IHk; exact A.
Qed.

Lemma fast_iter_h fx dx m : m_h (snd (fast_iter fx dx m)) = m_h m.
Proof. unfold fast_iter. hsplit; huse; hclose. Qed.

Lemma fast_loop_h fx dx k m : m_h (fast_loop fx dx k m) = m_h m.
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [auto|].
  pose proof (fast_iter_h fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [|exact A].
  rewrite IHk; exact A.
Qed.

Lemma fast_h fx dx m : m_h (fast fx dx m) = m_h m.
Proof. unfold fast. cbn. apply fast_loop_h. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb hkc.

Ltac hleaf :=
  match goal with
  | |- hkgood _ (IBrk _) => unfold hkgood; hclose
  | |- hkgood _ (IRet _ _) => unfold hkgood; hclose
  | |- hkgood ?m (?f ?x) => apply (hkgood_trans m x); [hclose | auto with hkc]
  end.

Ltac huse_cl :=
  repeat match goal with
  | E: codelens_loop ?a ?b ?k ?x = _ |- _ =>
      let H := fresh in pose proof (codelens_loop_h a b k x) as H; rewrite E in H; cbn [clm] in H; clear E
  end.

Ltac hcase := hsplit; huse; huse_cl; hleaf.

Section CasesHk.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_hk m : hkgood m (c_DONE m).
Proof. unfold c_DONE; hcase. Qed.
Hint Resolve c_DONE_hk : hkc.
Lemma c_BAD_hk m : hkgood m (c_BAD m).
Proof. unfold c_BAD; hcase. Qed.
Hint Resolve c_BAD_hk : hkc.
Lemma c_LENGTH_hk m : hkgood m (c_LENGTH m).
Proof. unfold c_LENGTH; hcase. Qed.
Hint Resolve c_LENGTH_hk : hkc.
Lemma c_CHECK_hk m : hkgood m (c_CHECK m).
Proof. unfold c_CHECK; hcase. Qed.
Hint Resolve c_CHECK_hk : hkc.
Lemma c_LIT_hk m : hkgood m (c_LIT m).
Proof. unfold c_LIT; hcase. Qed.
Hint Resolve c_LIT_hk : hkc.
Lemma c_MATCH_hk m : hkgood m (c_MATCH m).
Proof. unfold c_MATCH; hcase. Qed.
Hint Resolve c_MATCH_hk : hkc.
Lemma c_DISTEXT_hk m : hkgood m (c_DISTEXT m).
Proof. unfold c_DISTEXT; hcase. Qed.
Hint Resolve c_DISTEXT_hk : hkc.
Lemma c_DIST_hk m : hkgood m (c_DIST fx dx m).
Proof. unfold c_DIST; hcase. Qed.
Hint Resolve c_DIST_hk : hkc.
Lemma c_LENEXT_hk m : hkgood m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; hcase. Qed.
Hint Resolve c_LENEXT_hk : hkc.
Lemma c_LEN_hk m : hkgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold c_LEN.
  pose proof (fast_h fx dx (restore m)) as Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf; hhyp.
  hcase.
Qed.
Hint Resolve c_LEN_hk : hkc.
Lemma c_LEN__hk m : hkgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold c_LEN_; hcase. Qed.
Hint Resolve c_LEN__hk : hkc.

Lemma c_CODELENS_hk m : hkgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_CODELENS.
  pose proof (codelens_loop_h fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; hcase.
Qed.
Hint Resolve c_CODELENS_hk : hkc.
Lemma c_LENLENS_hk m : hkgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_h 19 m) as A; revert A.
  generalize (lenlens_loop 19 m); intros ml A.
  hcase.
Qed.
Hint Resolve c_LENLENS_hk : hkc.
Lemma c_TABLE_hk m : hkgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold c_TABLE; hcase. Qed.
Hint Resolve c_TABLE_hk : hkc.
Lemma c_COPY_hk m : hkgood m (c_COPY m).
Proof. unfold c_COPY; hcase. Qed.
Hint Resolve c_COPY_hk : hkc.
Lemma c_COPY__hk m : hkgood m (c_COPY_ m).
Proof. unfold c_COPY_; hcase. Qed.
Hint Resolve c_COPY__hk : hkc.
Lemma c_STORED_hk m : hkgood m (c_STORED fl m).
Proof. unfold c_STORED; hcase. Qed.
Hint Resolve c_STORED_hk : hkc.
Lemma c_TYPEDO_hk m : hkgood m (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; hcase. Qed.
Hint Resolve c_TYPEDO_hk : hkc.
Lemma c_TYPE_hk m : hkgood m (c_TYPE fl m).
Proof. unfold c_TYPE; hcase. Qed.
Hint Resolve c_TYPE_hk : hkc.

End CasesHk.

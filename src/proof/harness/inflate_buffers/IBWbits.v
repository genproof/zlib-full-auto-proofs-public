(* Law inflate_buffers, theory: inflate() keeps windowBits <= 15 (IBFacts.ib_wbits_stmt).  On Model2 only
   c_HEAD2 writes i_wbits (contract fix F7: the zlib header's window size is checked before it is stored; the gzip
   branch stores 15 when wbits is 0); every other case and inf_leave (RESTORE, updatewindow, the counters) keep it.
   The case analysis is StepHd5.v's (i_head) with i_wbits. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.inflate_buffers.IBFacts.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

Module IBW.

Definition hrel (m m': mst) : Prop := i_wbits (m_s m) <= 15 -> i_wbits (m_s m') <= 15.

Definition hgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => hrel m m' | IRet _ m' => hrel m m' end.

Lemma hrel_refl m : hrel m m.
Proof. unfold hrel; auto. Qed.

Lemma hrel_trans m1 m2 m3 : hrel m1 m2 -> hrel m2 m3 -> hrel m1 m3.
Proof. unfold hrel; auto. Qed.

Lemma hgood_trans m m' o : hrel m m' -> hgood m' o -> hgood m o.
Proof. destruct o; cbn; apply hrel_trans. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers keep the header record and i_wbits                                                  *)

Lemma pull_h m : m_h (pull m) = m_h m.
Proof. reflexivity. Qed.
Lemma pull_hd m : i_wbits (m_s (pull m)) = i_wbits (m_s m).
Proof. reflexivity. Qed.

Lemma needbits_f_h k n m : m_h (needbits_f k n m) = m_h m /\ i_wbits (m_s (needbits_f k n m)) = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as [-> ->]; auto.
Qed.

Lemma needbits_h n m : m_h (needbits n m) = m_h m.
Proof. apply needbits_f_h. Qed.
Lemma needbits_hd n m : i_wbits (m_s (needbits n m)) = i_wbits (m_s m).
Proof. apply needbits_f_h. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_h m d : m_h (crc_if m d) = m_h m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_hd m d : i_wbits (m_s (crc_if m d)) = i_wbits (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lookup1_f_h k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) -> m_h m' = m_h m /\ i_wbits (m_s m') = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> ->]; auto.
Qed.

Lemma lookup1_h fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) -> m_h m' = m_h m /\ i_wbits (m_s m') = i_wbits (m_s m).
Proof. apply lookup1_f_h. Qed.

Lemma lookup2_f_h k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) -> m_h m' = m_h m /\ i_wbits (m_s m') = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> ->]; auto.
Qed.

Lemma lookup2_h fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) -> m_h m' = m_h m /\ i_wbits (m_s m') = i_wbits (m_s m).
Proof. apply lookup2_f_h. Qed.

Lemma lens_fill_hd k len s : i_wbits (lens_fill k len s) = i_wbits s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite IHk; reflexivity. Qed.

Lemma lenlens_zero_hd k s : i_wbits (lenlens_zero k s) = i_wbits s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [rewrite IHk|]; reflexivity.
Qed.

Lemma lenlens_loop_h k m : m_h (lenlens_loop k m) = m_h m /\ i_wbits (m_s (lenlens_loop k m)) = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (m_leave (needbits 3 m) =? 1); [rewrite needbits_h, needbits_hd; auto|].
  match goal with |- context [lenlens_loop k ?x] => destruct (IHk x) as [-> ->] end.
  cbn. rewrite needbits_h, needbits_hd; auto.
Qed.

Lemma lenlens_loop_h1 k m : m_h (lenlens_loop k m) = m_h m.
Proof. apply lenlens_loop_h. Qed.
Lemma lenlens_loop_hd k m : i_wbits (m_s (lenlens_loop k m)) = i_wbits (m_s m).
Proof. apply lenlens_loop_h. Qed.

Lemma fwalk_f_h fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') -> m_h m' = m_h m /\ i_wbits (m_s m') = i_wbits (m_s m).
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as [-> ->]; cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Hint Rewrite pull_h pull_hd needbits_h needbits_hd crc_if_h crc_if_hd lens_fill_hd lenlens_zero_hd
  lenlens_loop_h1 lenlens_loop_hd : ibwb.

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
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_h in E; destruct E as [? ?]
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_h in E; destruct E as [? ?]
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_h in E; destruct E as [? ?]
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_h ?a = _ |- context [m_h ?a] => rewrite H
  | H: i_wbits ?a = _ |- context [i_wbits ?a] => rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast] in H.

Ltac hnorm := repeat progress (hcbn; autorewrite with ibwb; hrw).

Ltac hhyp :=
  repeat match goal with
  | H: i_wbits ?a = _ |- _ => tryif is_var a then fail else (progress (hcbn_in H; autorewrite with ibwb in H))
  end.

Ltac hclose := unfold hrel; hhyp; hnorm; intros; try lia.


Lemma codelens_iter_h fx dx m : m_h (clm (codelens_iter fx dx m)) = m_h m /\
                                 i_wbits (m_s (clm (codelens_iter fx dx m))) = i_wbits (m_s m).
Proof. unfold codelens_iter. hsplit; huse; hnorm; auto. Qed.

Lemma codelens_loop_h fx dx k m : m_h (clm (codelens_loop fx dx k m)) = m_h m /\
                                   i_wbits (m_s (clm (codelens_loop fx dx k m))) = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (codelens_iter_h fx dx m) as [A B].
  destruct (codelens_iter fx dx m) eqn:E; cbn in A, B |- *; auto.
  destruct (IHk m0) as [-> ->]; auto.
Qed.

Lemma fast_iter_h fx dx m : m_h (snd (fast_iter fx dx m)) = m_h m /\
                             i_wbits (m_s (snd (fast_iter fx dx m))) = i_wbits (m_s m).
Proof. unfold fast_iter. hsplit; huse; hnorm; auto. Qed.

Lemma fast_loop_h fx dx k m : m_h (fast_loop fx dx k m) = m_h m /\
                               i_wbits (m_s (fast_loop fx dx k m)) = i_wbits (m_s m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [auto|].
  destruct (fast_iter_h fx dx m) as [A B].
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A, B |- *.
  destruct (_ && _); [destruct (IHk m1) as [-> ->]|]; auto.
Qed.

Lemma fast_h fx dx m : m_h (fast fx dx m) = m_h m.
Proof. unfold fast. cbn. apply fast_loop_h. Qed.
Lemma fast_hd fx dx m : i_wbits (m_s (fast fx dx m)) = i_wbits (m_s m).
Proof. unfold fast. cbn. apply fast_loop_h. Qed.

Hint Rewrite fast_h fast_hd : ibwb.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb ibwbc.

Ltac hleaf :=
  match goal with
  | |- hgood _ (IBrk _) => unfold hgood; hclose
  | |- hgood _ (IRet _ _) => unfold hgood; hclose
  | |- hgood ?m (?f ?x) => apply (hgood_trans m x); [hclose | auto with ibwbc]
  end.

Ltac huse_cl :=
  repeat match goal with
  | E: codelens_loop ?a ?b ?k ?x = _ |- _ =>
      let H := fresh in pose proof (codelens_loop_h a b k x) as H; rewrite E in H; cbn [clm] in H;
      destruct H as [? ?]; clear E
  end.

Ltac hcase := hsplit; huse; huse_cl; hleaf.

Section CasesHd.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_hd m : hgood m (c_DONE m).
Proof. unfold c_DONE; hcase. Qed.
Hint Resolve c_DONE_hd : ibwbc.
Lemma c_BAD_hd m : hgood m (c_BAD m).
Proof. unfold c_BAD; hcase. Qed.
Hint Resolve c_BAD_hd : ibwbc.
Lemma c_LENGTH_hd m : hgood m (c_LENGTH m).
Proof. unfold c_LENGTH; hcase. Qed.
Hint Resolve c_LENGTH_hd : ibwbc.
Lemma c_CHECK_hd m : hgood m (c_CHECK m).
Proof. unfold c_CHECK; hcase. Qed.
Hint Resolve c_CHECK_hd : ibwbc.
Lemma c_LIT_hd m : hgood m (c_LIT m).
Proof. unfold c_LIT; hcase. Qed.
Hint Resolve c_LIT_hd : ibwbc.
Lemma c_MATCH_hd m : hgood m (c_MATCH m).
Proof. unfold c_MATCH; hcase. Qed.
Hint Resolve c_MATCH_hd : ibwbc.
Lemma c_DISTEXT_hd m : hgood m (c_DISTEXT m).
Proof. unfold c_DISTEXT; hcase. Qed.
Hint Resolve c_DISTEXT_hd : ibwbc.
Lemma c_DIST_hd m : hgood m (c_DIST fx dx m).
Proof. unfold c_DIST; hcase. Qed.
Hint Resolve c_DIST_hd : ibwbc.
Lemma c_LENEXT_hd m : hgood m (c_LENEXT fx dx m).
Proof. unfold c_LENEXT; hcase. Qed.
Hint Resolve c_LENEXT_hd : ibwbc.
Lemma c_LEN_hd m : hgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold c_LEN.
  assert (Hf: m_h (fast fx dx (restore m)) = m_h m /\ i_wbits (m_s (fast fx dx (restore m))) = i_wbits (m_s m))
    by (rewrite fast_h, fast_hd; auto).
  revert Hf; generalize (fast fx dx (restore m)); intros mf [Hf1 Hf2].
  hcase.
Qed.
Hint Resolve c_LEN_hd : ibwbc.
Lemma c_LEN__hd m : hgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold c_LEN_; hcase. Qed.
Hint Resolve c_LEN__hd : ibwbc.


Lemma c_CODELENS_hd m : hgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_CODELENS.
  pose proof (codelens_loop_h fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; destruct H as [Ha Hb]; hcase.
Time Qed.
Hint Resolve c_CODELENS_hd : ibwbc.
Lemma c_LENLENS_hd m : hgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_h 19 m) as [A B]; revert A B.
  generalize (lenlens_loop 19 m); intros ml A B.
  pose proof (lenlens_zero_hd 19 (m_s ml)) as C; revert C.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C.
  hcase.
Time Qed.
Hint Resolve c_LENLENS_hd : ibwbc.
Lemma c_TABLE_hd m : hgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold c_TABLE; hcase. Qed.
Hint Resolve c_TABLE_hd : ibwbc.
Lemma c_COPY_hd m : hgood m (c_COPY m).
Proof. unfold c_COPY; hcase. Qed.
Hint Resolve c_COPY_hd : ibwbc.
Lemma c_COPY__hd m : hgood m (c_COPY_ m).
Proof. unfold c_COPY_; hcase. Qed.
Hint Resolve c_COPY__hd : ibwbc.
Lemma c_STORED_hd m : hgood m (c_STORED fl m).
Proof. unfold c_STORED; hcase. Qed.
Hint Resolve c_STORED_hd : ibwbc.
Lemma c_TYPEDO_hd m : hgood m (c_TYPEDO fl m).
Proof. unfold c_TYPEDO; hcase. Qed.
Hint Resolve c_TYPEDO_hd : ibwbc.
Lemma c_TYPE_hd m : hgood m (c_TYPE fl m).
Proof. unfold c_TYPE; hcase. Qed.
Hint Resolve c_TYPE_hd : ibwbc.
Lemma c_DICT_hd m : hgood m (c_DICT fl m).
Proof. unfold c_DICT; hcase. Qed.
Hint Resolve c_DICT_hd : ibwbc.
Lemma c_DICTID_hd m : hgood m (c_DICTID fl m).
Proof. unfold c_DICTID; hcase. Qed.
Hint Resolve c_DICTID_hd : ibwbc.
Lemma c_HCRC_hd m : hgood m (c_HCRC m).
Proof. unfold c_HCRC; hcase. Qed.
Hint Resolve c_HCRC_hd : ibwbc.
Lemma c_COMMENT2_hd m : hgood m (c_COMMENT2 m).
Proof. unfold c_COMMENT2; hcase. Qed.
Hint Resolve c_COMMENT2_hd : ibwbc.
Lemma c_NAME2_hd m : hgood m (c_NAME2 m).
Proof. unfold c_NAME2; hcase. Qed.
Hint Resolve c_NAME2_hd : ibwbc.
Lemma c_EXTRA2_hd m : hgood m (c_EXTRA2 m).
Proof. unfold c_EXTRA2; hcase. Qed.
Hint Resolve c_EXTRA2_hd : ibwbc.
Lemma c_EXLEN2_hd m : hgood m (c_EXLEN2 m).
Proof. unfold c_EXLEN2; hcase. Qed.
Hint Resolve c_EXLEN2_hd : ibwbc.
Lemma c_OS2_hd m : hgood m (c_OS2 m).
Proof. unfold c_OS2; hcase. Qed.
Hint Resolve c_OS2_hd : ibwbc.
Lemma c_TIME2_hd m : hgood m (c_TIME2 m).
Proof. unfold c_TIME2; hcase. Qed.
Hint Resolve c_TIME2_hd : ibwbc.
Lemma c_FLAGS2_hd m : hgood m (c_FLAGS2 m).
Proof. unfold c_FLAGS2; hcase. Qed.
Hint Resolve c_FLAGS2_hd : ibwbc.
Lemma c_HEAD2_hd m : hgood m (c_HEAD2 m).
Proof.
  unfold c_HEAD2; hcase.
  all: repeat match goal with H: (_ || _) = false |- _ => apply orb_false_iff in H; destruct H end.
  all: repeat match goal with H: (_ =? _) = _ |- _ => first [apply Z.eqb_eq in H | apply Z.eqb_neq in H] end.
  all: repeat match goal with H: (_ <? _) = false |- _ => apply Z.ltb_ge in H end.
  all: try lia.
  all: destruct (i_wbits (m_s m) =? 0); [|lia].
  all: try lia.
  all: match goal with Hx: _ mod 16 + 8 <= 15 |- _ => cbn -[needbits needbits_f] in Hx end.
  all: lia.
Qed.
Hint Resolve c_HEAD2_hd : ibwbc.

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

End IBW.

Lemma ib_uw_wbits s d : i_wbits (updatewindow s d) = i_wbits s.
Proof. unfold updatewindow. cbv zeta. repeat (destruct (_ =? _) || destruct (_ <=? _) || destruct (_ <? _)); reflexivity. Qed.

Lemma ib_leave_wbits fl m : i_wbits (m_s (r_m (leave_fin fl m))) = i_wbits (m_s m).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok fl m); cbn -[updatewindow u32 u64];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn -[updatewindow u32 u64]; rewrite ?ib_uw_wbits; reflexivity.
Qed.

Lemma ib_loop_wbits fl m o : loop2 fl lenfix_list distfix_list m o -> i_wbits (m_s m) <= 15 ->
  match o with IBrk m' => i_wbits (m_s m') <= 15 | IRet _ m' => i_wbits (m_s m') <= 15 end.
Proof.
  intros HL. induction HL as [m r m' E | m m' E Hlv | m m' o E Hlv HL IH]; intros W.
  - pose proof (IBW.stepf2_hgood fl lenfix_list distfix_list m) as G. rewrite E in G. exact (G W).
  - pose proof (IBW.stepf2_hgood fl lenfix_list distfix_list m) as G. rewrite E in G. exact (G W).
  - pose proof (IBW.stepf2_hgood fl lenfix_list distfix_list m) as G. rewrite E in G. exact (IH (G W)).
Qed.

Lemma ib_wbits : ib_wbits_stmt.
Proof.
  intros flush z L inp res _ _ W (o & Hlo & Hres).
  assert (W0: i_wbits (m_s (m_init z L inp)) <= 15).
  { unfold m_init. cbn [m_s]. destruct (_ =? _); exact W. }
  pose proof (ib_loop_wbits flush _ _ Hlo W0) as H.
  destruct o as [m'|r m'].
  - inversion Hres; subst; cbn [r_m].
    + exact H.
    + rewrite ib_leave_wbits. exact H.
  - subst res. exact H.
Qed.

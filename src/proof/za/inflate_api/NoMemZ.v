(* A pass of the switch (Model2.v stepf2) never goes on in mode MEM: inflate.c sets the mode MEM only after a
   failed window allocation at the exit (updatewindow), not in a case of the switch.  So within a call of
   inflate() that does not start in MEM, every state the loop reaches is outside MEM; the allocator-generic
   specification of inflate() (ZEvents.win_ev) records a failed allocation exactly when the call enters MEM. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

(* [nm m]: the machine is not in mode MEM *)
Definition nm (m: mst) : Prop := i_mode (m_s m) <> MEM.

(* [nomem o]: a break of the switch leaves a machine outside MEM (returns are not constrained) *)
Definition nomem (o: iout) : Prop :=
  match o with IBrk m => nm m | IRet _ _ => True end.

(* the same for the outcomes of the inner loops: a pass of inflate_fast's loop, a pass of CODELENS *)
Definition pnm {A: Type} (p: A * mst) : Prop := nm (snd p).
Definition clnm (c: clout) : Prop :=
  match c with CLnext m | CLleave m | CLbad m => nm m end.

(* ---------------------------------------------------------------------------------------------- *)
(* The state updates of the cases                                                                 *)

Lemma nm_conv m m' : i_mode (m_s m') = i_mode (m_s m) -> nm m -> nm m'.
Proof. unfold nm; intros ->; auto. Qed.

Lemma snm_conv s s' : i_mode s' = i_mode s -> i_mode s <> MEM -> i_mode s' <> MEM.
Proof. intros ->; auto. Qed.

Lemma lit_not_mem v : (v =? MEM) = false -> v <> MEM.
Proof. apply Z.eqb_neq. Qed.

Lemma nm_set_mode m v : v <> MEM -> nm (set_mode m v).
Proof. exact (fun H => H). Qed.

Lemma nm_set_bad m e : nm (set_bad m e).
Proof. apply nm_set_mode, lit_not_mem; reflexivity. Qed.

Lemma nm_if (b: bool) x y : nm x -> nm y -> nm (if b then x else y).
Proof. destruct b; auto. Qed.

Lemma nm_set_m_s m s : i_mode s <> MEM -> nm (set_m_s m s).
Proof. exact (fun H => H). Qed.

Lemma nm_crc_if m d : nm m -> nm (crc_if m d).
Proof. unfold crc_if; destruct (_ && _); auto. Qed.

Lemma lenlens_zero_mode k s : i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k as [|k IH]; intros s; cbn [lenlens_zero]; [reflexivity|].
  destruct (_ <? _); [rewrite IH|]; reflexivity.
Qed.

Lemma lens_fill_mode k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k as [|k IH]; intros s; cbn [lens_fill]; [|rewrite IH]; reflexivity. Qed.

Lemma nm_lens_fill k len m : nm m -> nm (upd_s m (lens_fill k len)).
Proof. intros H; unfold nm in *; change (i_mode (lens_fill k len (m_s m)) <> MEM); rewrite lens_fill_mode; auto. Qed.

Lemma nm_needbits n m : nm m -> nm (needbits n m).
Proof.
  unfold needbits; generalize 4%nat as k; intros k; revert m.
  induction k as [|k IH]; intros m H; cbn [needbits_f]; [exact H|].
  destruct (_ <? _); [|exact H]. destruct (_ =? _); [exact H|].
  apply IH; exact H.
Qed.

Lemma lookup1_nm fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) -> nm m -> nm m'.
Proof.
  unfold lookup1; generalize 3%nat as k; intros k; revert m.
  induction k as [|k IH]; intros m E H; cbn [lookup1_f] in E.
  - inversion E; subst; exact H.
  - destruct (_ <=? _); [inversion E; subst; exact H|].
    destruct (_ =? _); [inversion E; subst; exact H|].
    eapply IH; [exact E|exact H].
Qed.

Lemma lookup2_nm fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) -> nm m -> nm m'.
Proof.
  unfold lookup2; generalize 3%nat as k; intros k; revert m.
  induction k as [|k IH]; intros m E H; cbn [lookup2_f] in E.
  - inversion E; subst; exact H.
  - destruct (_ <=? _); [inversion E; subst; exact H|].
    destruct (_ =? _); [inversion E; subst; exact H|].
    eapply IH; [exact E|exact H].
Qed.

Lemma fwalk_nm fx dx k il t here m h m' : fwalk_f fx dx k il t here m = (h, m') -> nm m -> nm m'.
Proof.
  revert here m; induction k as [|k IH]; intros here m E H; cbn [fwalk_f] in E.
  - inversion E; subst; exact H.
  - destruct (il _); [|inversion E; subst; exact H].
    eapply IH; [exact E|exact H].
Qed.

Lemma nm_lenlens_loop k m : nm m -> nm (lenlens_loop k m).
Proof.
  revert m; induction k as [|k IH]; intros m H; cbn [lenlens_loop]; [exact H|].
  destruct (_ <? _); [|exact H].
  destruct (_ =? _); [apply nm_needbits; exact H|].
  apply IH. apply (nm_needbits 3) in H. exact H.
Qed.

(* close [nm x] (or [i_mode s <> MEM]) through the updates that keep the mode or set a literal one *)
Ltac mode_lit :=
  lazymatch goal with
  | |- (if ?b then _ else _) <> MEM => destruct b; mode_lit
  | |- _ <> MEM => apply lit_not_mem; reflexivity
  end.

(* the facts about inflate_fast's model and the CODELENS loop, proved below, extend [nms] *)
Ltac nms_ext := fail.

(* An update [f] that keeps the mode is shown to do so on a variable [y] first, then instantiated: a
   conversion on the concrete (large) machine sends the kernel into unfolding what computed it. *)

Ltac nms :=
  lazymatch goal with
  | |- i_mode (set_i_mode _ ?v) <> MEM => mode_lit
  | |- i_mode (lenlens_zero _ _) <> MEM => rewrite lenlens_zero_mode; nms
  | |- i_mode (m_s ?m) <> MEM => change (nm m); nms
  | |- i_mode ?s <> MEM =>
      first [ assumption
            | lazymatch s with
              | ?f ?s' ?a => let L := fresh "L" in
                  assert (L: forall y: istate, i_mode (f y a) = i_mode y) by (intros; reflexivity);
                  apply (snm_conv s' _ (L s')); clear L; nms
              end ]
  | |- nm (set_mode _ _) => apply nm_set_mode; mode_lit
  | |- nm (set_bad _ _) => apply nm_set_bad
  | |- nm (if _ then _ else _) => apply nm_if; nms
  | |- nm (needbits _ _) => apply nm_needbits; nms
  | |- nm (lenlens_loop _ _) => apply nm_lenlens_loop; nms
  | |- nm (crc_if _ _) => apply nm_crc_if; nms
  | |- nm (upd_s _ (lens_fill _ _)) => apply nm_lens_fill; nms
  | |- nm (set_m_s _ _) => apply nm_set_m_s; nms
  | |- nm ?x =>
      first
        [ assumption
        | nms_ext
        | (* a premise that the function (inflate_fast's model) keeps the machine outside MEM *)
          lazymatch x with
          | ?f _ => match goal with Hf: forall m, nm m -> nm (f m) |- _ => apply Hf; nms end
          end
        | match goal with
          | E: lookup1 _ _ _ _ _ = (_, x, _) |- _ => eapply lookup1_nm; [exact E|]; nms
          | E: lookup2 _ _ _ _ _ = (_, x, _) |- _ => eapply lookup2_nm; [exact E|]; nms
          | E: fwalk_f _ _ _ _ _ _ _ = (_, x) |- _ => eapply fwalk_nm; [exact E|]; nms
          end
        | lazymatch x with
          | ?f ?m => let L := fresh "L" in
              assert (L: forall y: mst, i_mode (m_s (f y)) = i_mode (m_s y)) by (intros; reflexivity);
              apply (nm_conv m _ (L m)); clear L; nms
          end
        | lazymatch x with
          | ?f ?m ?a => let L := fresh "L" in
              assert (L: forall y: mst, i_mode (m_s (f y a)) = i_mode (m_s y)) by (intros; reflexivity);
              apply (nm_conv m _ (L m)); clear L; nms
          end
        | lazymatch x with
          | ?f ?a ?m => let L := fresh "L" in
              assert (L: forall y: mst, i_mode (m_s (f a y)) = i_mode (m_s y)) by (intros; reflexivity);
              apply (nm_conv m _ (L m)); clear L; nms
          end ]
  end.

(* walk down a body: split every test, every tuple-valued or clout-valued let (remembering the call
   it destructs), and close the breaks with [nms] and the calls of other cases with their lemmas *)
Ltac split_scrut p :=
  lazymatch p with
  | if ?b then _ else _ => destruct b
  | let _ := _ in _ => cbv zeta
  | match ?q with (_, _) => _ end => split_scrut q
  | match ?q with CLnext _ => _ | CLleave _ => _ | CLbad _ => _ end => split_scrut q
  | (_, _) => cbv beta iota
  | CLnext _ => cbv beta iota
  | CLleave _ => cbv beta iota
  | CLbad _ => cbv beta iota
  | _ => first [ is_var p; destruct p | let E := fresh "E" in destruct p eqn:E ]
  end.

Create HintDb nomem.
#[local] Hint Extern 1 (nm _) => nms : nomem.

Ltac walk :=
  repeat match goal with
  | |- nomem (IBrk ?m) => change (nm m); nms
  | |- nomem (IRet _ _) => exact I
  | |- clnm (CLnext ?m) => change (nm m); nms
  | |- clnm (CLleave ?m) => change (nm m); nms
  | |- clnm (CLbad ?m) => change (nm m); nms
  | |- pnm (_, ?m) => change (nm m); nms
  | |- ?P (let _ := _ in _) => cbv zeta
  | |- ?P (if ?b then _ else _) => destruct b
  | |- ?P (match ?p with (_, _) => _ end) => split_scrut p
  | |- ?P (match ?p with CLnext _ => _ | CLleave _ => _ | CLbad _ => _ end) => split_scrut p
  | |- nomem _ => solve [eauto with nomem]
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast keeps the mode or sets TYPE / BAD                                                 *)

Lemma fast_iter_nm fx dx m b m' : fast_iter fx dx m = (b, m') -> nm m -> nm m'.
Proof.
  intros E H. assert (P: pnm (fast_iter fx dx m)) by (unfold fast_iter; walk).
  rewrite E in P; exact P.
Qed.

Lemma nm_fast_loop fx dx k m : nm m -> nm (fast_loop fx dx k m).
Proof.
  revert m; induction k as [|k IH]; intros m H; cbn [fast_loop]; [exact H|].
  destruct (fast_iter fx dx m) as [b m1] eqn:E.
  pose proof (fast_iter_nm _ _ _ _ _ E H) as H1.
  destruct (_ && _); auto.
Qed.

Ltac nms_ext ::=
  lazymatch goal with
  | |- nm (fast_loop _ _ _ _) => apply nm_fast_loop; nms
  | |- nm ?x => match goal with
                | E: fast_iter _ _ _ = (_, x) |- _ => eapply fast_iter_nm; [exact E|]; nms
                end
  end.

Lemma nm_fast fx dx m : nm m -> nm (fast fx dx m).
Proof. intros H; unfold fast; cbv zeta; nms. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the CODELENS loop keeps the mode or sets BAD                                                   *)

Lemma codelens_iter_nm fx dx m c : codelens_iter fx dx m = c -> nm m -> clnm c.
Proof. intros <- H; unfold codelens_iter; walk. Qed.

Lemma codelens_loop_nm fx dx k m c : codelens_loop fx dx k m = c -> nm m -> clnm c.
Proof.
  revert m; induction k as [|k IH]; intros m E H; cbn [codelens_loop] in E; [subst; exact H|].
  destruct (_ <? _); [|subst; exact H].
  destruct (codelens_iter fx dx m) eqn:E2; pose proof (codelens_iter_nm _ _ _ _ E2 H) as H2;
    cbn [clnm] in H2; [eapply IH; [exact E|exact H2]| subst; exact H2 | subst; exact H2].
Qed.

Ltac nms_ext ::=
  lazymatch goal with
  | |- nm (fast_loop _ _ _ _) => apply nm_fast_loop; nms
  | |- nm (fast _ _ _) => apply nm_fast; nms
  | |- nm ?x => match goal with
                | E: fast_iter _ _ _ = (_, x) |- _ => eapply fast_iter_nm; [exact E|]; nms
                | E: codelens_iter _ _ _ = _ |- _ => refine (codelens_iter_nm _ _ _ _ E _); nms
                | E: codelens_loop _ _ _ _ = _ |- _ => refine (codelens_loop_nm _ _ _ _ _ E _); nms
                end
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* every case of the switch, from the ones others fall through into up to HEAD: entered outside   *)
(* MEM, a break it makes leaves the machine outside MEM                                           *)

Section Cases.
Variables (fl: Z) (fx dx: list entry).
(* inflate_fast's model, abstracted (it is [fast fx dx] in stepf2): only its keeping the machine outside
   MEM (the premise [fs_nm]) is used, so the kernel never unfolds its loop when it checks these proofs *)
Variable fs : mst -> mst.

Lemma c_DONE_n m : nm m -> nomem (c_DONE m).
Proof. intros H; unfold c_DONE; walk. Qed.
#[local] Hint Resolve c_DONE_n : nomem.
Lemma c_BAD_n m : nm m -> nomem (c_BAD m).
Proof. intros H; unfold c_BAD; walk. Qed.
#[local] Hint Resolve c_BAD_n : nomem.
Lemma c_LENGTH_n m : nm m -> nomem (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; walk. Qed.
#[local] Hint Resolve c_LENGTH_n : nomem.
Lemma c_CHECK_n m : nm m -> nomem (c_CHECK m).
Proof. intros H; unfold c_CHECK; walk. Qed.
#[local] Hint Resolve c_CHECK_n : nomem.
Lemma c_LIT_n m : nm m -> nomem (c_LIT m).
Proof. intros H; unfold c_LIT; walk. Qed.
#[local] Hint Resolve c_LIT_n : nomem.
Lemma c_MATCH_n m : nm m -> nomem (c_MATCH m).
Proof. intros H; unfold c_MATCH; walk. Qed.
#[local] Hint Resolve c_MATCH_n : nomem.
Lemma c_DISTEXT_n m : nm m -> nomem (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; walk. Qed.
#[local] Hint Resolve c_DISTEXT_n : nomem.
Lemma c_DIST_n m : nm m -> nomem (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; walk. Qed.
#[local] Hint Resolve c_DIST_n : nomem.
Lemma c_LENEXT_n m : nm m -> nomem (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; walk. Qed.
#[local] Hint Resolve c_LENEXT_n : nomem.
Lemma c_LEN_n (fs_nm: forall m, nm m -> nm (fs m)) m : nm m -> nomem (c_LEN fx dx fs m).
Proof. intros H; unfold c_LEN; walk. Qed.
#[local] Hint Resolve c_LEN_n : nomem.
Lemma c_LEN__n (fs_nm: forall m, nm m -> nm (fs m)) m : nm m -> nomem (c_LEN_ fx dx fs m).
Proof. intros H; unfold c_LEN_; walk. Qed.
#[local] Hint Resolve c_LEN__n : nomem.
Lemma c_CODELENS_n (fs_nm: forall m, nm m -> nm (fs m)) m : nm m -> nomem (c_CODELENS fl fx dx fs m).
Proof.
  intros H; unfold c_CODELENS.
  (* the loop's outcome, abstracted: it keeps the machine outside MEM *)
  generalize (codelens_loop_nm fx dx 320 m _ eq_refl H).
  destruct (codelens_loop fx dx 320 m) as [m1|m1|m1]; cbn [clnm]; intros H1; [|walk..].
  (* inflate_table's model, abstracted: nothing about it is needed, and the kernel must not compute it *)
  pattern call_table; generalize call_table; intros ct; walk.
Qed.
#[local] Hint Resolve c_CODELENS_n : nomem.
Lemma c_LENLENS_n (fs_nm: forall m, nm m -> nm (fs m)) m : nm m -> nomem (c_LENLENS fl fx dx fs m).
Proof.
  intros H; unfold c_LENLENS.
  pattern call_table; generalize call_table; intros ct; walk.
Qed.
#[local] Hint Resolve c_LENLENS_n : nomem.
Lemma c_TABLE_n (fs_nm: forall m, nm m -> nm (fs m)) m : nm m -> nomem (c_TABLE fl fx dx fs m).
Proof. intros H; unfold c_TABLE; walk. Qed.
#[local] Hint Resolve c_TABLE_n : nomem.
Lemma c_COPY_n m : nm m -> nomem (c_COPY m).
Proof. intros H; unfold c_COPY; walk. Qed.
#[local] Hint Resolve c_COPY_n : nomem.
Lemma c_COPY__n m : nm m -> nomem (c_COPY_ m).
Proof. intros H; unfold c_COPY_; walk. Qed.
#[local] Hint Resolve c_COPY__n : nomem.
Lemma c_STORED_n m : nm m -> nomem (c_STORED fl m).
Proof. intros H; unfold c_STORED; walk. Qed.
#[local] Hint Resolve c_STORED_n : nomem.
Lemma c_TYPEDO_n m : nm m -> nomem (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; walk. Qed.
#[local] Hint Resolve c_TYPEDO_n : nomem.
Lemma c_TYPE_n m : nm m -> nomem (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; walk. Qed.
#[local] Hint Resolve c_TYPE_n : nomem.
Lemma c_DICT_n m : nm m -> nomem (c_DICT fl m).
Proof. intros H; unfold c_DICT; walk. Qed.
#[local] Hint Resolve c_DICT_n : nomem.
Lemma c_DICTID_n m : nm m -> nomem (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; walk. Qed.
#[local] Hint Resolve c_DICTID_n : nomem.
Lemma c_HCRC_n m : nm m -> nomem (c_HCRC m).
Proof. intros H; unfold c_HCRC; walk. Qed.
#[local] Hint Resolve c_HCRC_n : nomem.
Lemma c_COMMENT2_n m : nm m -> nomem (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; walk. Qed.
#[local] Hint Resolve c_COMMENT2_n : nomem.
Lemma c_NAME2_n m : nm m -> nomem (c_NAME2 m).
Proof. intros H; unfold c_NAME2; walk. Qed.
#[local] Hint Resolve c_NAME2_n : nomem.
Lemma c_EXTRA2_n m : nm m -> nomem (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; walk. Qed.
#[local] Hint Resolve c_EXTRA2_n : nomem.
Lemma c_EXLEN2_n m : nm m -> nomem (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; walk. Qed.
#[local] Hint Resolve c_EXLEN2_n : nomem.
Lemma c_OS2_n m : nm m -> nomem (c_OS2 m).
Proof. intros H; unfold c_OS2; walk. Qed.
#[local] Hint Resolve c_OS2_n : nomem.
Lemma c_TIME2_n m : nm m -> nomem (c_TIME2 m).
Proof. intros H; unfold c_TIME2; walk. Qed.
#[local] Hint Resolve c_TIME2_n : nomem.
Lemma c_FLAGS2_n m : nm m -> nomem (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; walk. Qed.
#[local] Hint Resolve c_FLAGS2_n : nomem.
Lemma c_HEAD2_n m : nm m -> nomem (c_HEAD2 m).
Proof. intros H; unfold c_HEAD2; walk. Qed.
#[local] Hint Resolve c_HEAD2_n : nomem.

End Cases.

#[local] Hint Resolve nm_fast : nomem.
#[local] Hint Resolve c_DONE_n c_BAD_n c_LENGTH_n c_CHECK_n c_LIT_n c_MATCH_n c_DISTEXT_n c_DIST_n c_LENEXT_n c_LEN_n c_LEN__n c_CODELENS_n c_LENLENS_n c_TABLE_n c_COPY_n c_COPY__n c_STORED_n c_TYPEDO_n c_TYPE_n c_DICT_n c_DICTID_n c_HCRC_n c_COMMENT2_n c_NAME2_n c_EXTRA2_n c_EXLEN2_n c_OS2_n c_TIME2_n c_FLAGS2_n c_HEAD2_n : nomem.

Lemma stepf2_brk_not_mem: forall fl fx dx m m',
  stepf2 fl fx dx m = IBrk m' -> i_mode (m_s m') <> MEM.
Proof.
  intros fl fx dx m m' H. change (nomem (IBrk m')). rewrite <- H. unfold stepf2, step2.
  repeat match goal with |- nomem (if ?b then _ else _) => let E := fresh "E" in destruct b eqn:E end.
  all: try exact I.
  (* the dispatched mode is a mode of the switch, not MEM *)
  all: match goal with E: (m_mode ?m0 =? _) = true |- _ =>
         apply Z.eqb_eq in E; assert (nm m0) by (change (m_mode m0 <> MEM); rewrite E; mode_lit) end.
  all: eauto with nomem.
Qed.

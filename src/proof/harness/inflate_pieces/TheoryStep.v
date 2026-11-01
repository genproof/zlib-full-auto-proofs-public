(* The laws rj_any_input, api_counters and api_untouched_output, the theory: one pass of the switch of
   Model2.v (stepf2) keeps the wrapper (state->wrap) and the discipline of the return code `ret`:
   - ret is Z_OK while the mode is neither BAD nor DONE (inflate_table's result is stored in ret, and BAD
     follows when it is not 0);
   - when the loop is left (leave = 1) in DONE, ret = Z_STREAM_END; in BAD, ret = Z_DATA_ERROR (only the
     cases DONE and BAD set leave in these modes);
   - the only return of a pass from a mode in HEAD..BAD (DICT's Z_NEED_DICT) is in mode DICT.
   These facts are about the model only (no bound on the buffers); the case analysis reuses the tactics
   of inflate_buffers/IBStepKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Require Import Zlib.proof.harness.inflate_buffers.IBStepKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the discipline of ret at a loop head or at the exit of the loop *)
Definition rk (m: mst) : Prop :=
  (m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK) /\
  (m_leave m = 1 -> m_mode m = DONE -> m_ret m = Z_STREAM_END) /\
  (m_leave m = 1 -> m_mode m = BAD -> m_ret m = Z_DATA_ERROR).

(* what a pass (or the rest of a pass, from a fallthrough) gives *)
Definition pgood (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => i_wrap (m_s m') = i_wrap (m_s m) /\ rk m'
  | IRet _ m' => i_wrap (m_s m') = i_wrap (m_s m) /\ m_mode m' = DICT
  end.

(* the entry of a case other than DONE and BAD at a loop head *)
Definition ppre (m: mst) : Prop :=
  m_leave m = 0 /\ m_ret m = Z_OK /\ m_mode m <> BAD /\ m_mode m <> DONE.

Lemma pgood_trans m x o : i_wrap (m_s x) = i_wrap (m_s m) -> pgood x o -> pgood m o.
Proof. destruct o; cbn; intros A [B C]; split; auto; congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma needbits_f_rl k n m :
  m_ret (needbits_f k n m) = m_ret m /\
  (m_leave (needbits_f k n m) = m_leave m \/ m_leave (needbits_f k n m) = 1).
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as [A B]. cbn in A, B. auto.
Qed.

Lemma needbits_ret n m : m_ret (needbits n m) = m_ret m.
Proof. apply needbits_f_rl. Qed.
Lemma needbits_leave n m : m_leave (needbits n m) = m_leave m \/ m_leave (needbits n m) = 1.
Proof. apply needbits_f_rl. Qed.

Lemma crc_if_wrap m d : i_wrap (m_s (crc_if m d)) = i_wrap (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_ret m d : m_ret (crc_if m d) = m_ret m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_leave m d : m_leave (crc_if m d) = m_leave m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lens_fill_wrap k len s : i_wrap (lens_fill k len s) = i_wrap s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite IHk. reflexivity. Qed.

Lemma lenlens_zero_wrap k s : i_wrap (lenlens_zero k s) = i_wrap s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto]. rewrite IHk. reflexivity.
Qed.

Lemma lookup1_f_rl k fx dx t nb m h m' ok : lookup1_f k fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ (ok = true -> m_leave m' = m_leave m).
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; split; [auto|split; [auto|discriminate]]|].
    apply IHk in E. cbn in E. exact E.
Qed.

Lemma lookup1_rl fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) ->
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ (ok = true -> m_leave m' = m_leave m).
Proof. apply lookup1_f_rl. Qed.

Lemma lookup2_f_rl k fx dx t last m h m' ok : lookup2_f k fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ (ok = true -> m_leave m' = m_leave m).
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; subst; auto.
  - destruct (_ <=? _); [inversion E; subst; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; split; [auto|split; [auto|discriminate]]|].
    apply IHk in E. cbn in E. exact E.
Qed.

Lemma lookup2_rl fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) ->
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ (ok = true -> m_leave m' = m_leave m).
Proof. apply lookup2_f_rl. Qed.

Lemma fwalk_f_rl fx dx k il t here m h' m' : fwalk_f fx dx k il t here m = (h', m') ->
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ m_leave m' = m_leave m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; auto.
  - destruct (il (e_op here)).
    + apply IHk in E. cbn in E. exact E.
    + inversion E; subst; auto.
Qed.

Create HintDb pkw.
Hint Rewrite needbits_s needbits_ret crc_if_mode crc_if_wrap crc_if_ret crc_if_leave lens_fill_mode
  lenlens_zero_mode lens_fill_wrap lenlens_zero_wrap : pkw.

(* the facts of the helpers met in a case *)
Ltac puse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_rl in E; destruct E as (? & ? & ?)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_rl in E; destruct E as (? & ? & ?)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_rl in E; destruct E as (? & ? & ?)
  end.

(* the tests of the case as arithmetic facts *)
Ltac pbool :=
  repeat match goal with
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: negb _ = false |- _ => apply negb_false_iff in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H: ?b = true |- _ => is_var b; subst b
  | H: ?b = false |- _ => is_var b; subst b
  | H: true = true -> _ |- _ => specialize (H eq_refl)
  | H: false = true -> _ |- _ => clear H
  end.

(* NEEDBITS sets leave or keeps it *)
Ltac pleave :=
  repeat match goal with
  | _: context [m_leave (needbits ?n ?x)] |- _ =>
      lazymatch goal with
      | _: m_leave (needbits n x) = m_leave x \/ _ |- _ => fail
      | _ => pose proof (needbits_leave n x)
      end
  | |- context [m_leave (needbits ?n ?x)] =>
      lazymatch goal with
      | _: m_leave (needbits n x) = m_leave x \/ _ |- _ => fail
      | _ => pose proof (needbits_leave n x)
      end
  end.

Ltac prw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: m_ret ?a = _ |- context [m_ret ?a] => rewrite H
  | H: m_leave ?a = m_leave _ |- context [m_leave ?a] => rewrite H
  | H: m_s ?a = _, H2: context [m_s ?a] |- _ => is_var a; rewrite H in H2
  | H: m_ret ?a = _, H2: context [m_ret ?a] |- _ => is_var a; rewrite H in H2
  | H: m_leave ?a = m_leave _, H2: context [m_leave ?a] |- _ => is_var a; rewrite H in H2
  end.

Ltac pnorm :=
  repeat match goal with H: _ |- _ => progress (hcbn_in H) end;
  autorewrite with pkw in *;
  repeat progress (hcbn; autorewrite with pkw; prw).

Ltac pfin := unfold rk, m_mode, Z_OK, Z_STREAM_END, Z_DATA_ERROR in *; pleave; wmodes; repeat split; intros; try reflexivity; try lia.
Ltac pclose := unfold rk, m_mode in *; pnorm; pleave; pnorm; pfin.

Lemma lenlens_loop_rl k m :
  i_wrap (m_s (lenlens_loop k m)) = i_wrap (m_s m) /\ i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m) /\
  m_ret (lenlens_loop k m) = m_ret m /\
  (m_leave (lenlens_loop k m) = m_leave m \/ m_leave (lenlens_loop k m) = 1).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [auto|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|auto].
  destruct (m_leave (needbits 3 m) =? 1) eqn:E.
  - apply Z.eqb_eq in E. rewrite needbits_s, needbits_ret, E. auto.
  - apply Z.eqb_neq in E. destruct (needbits_leave 3 m) as [E'|E']; [|contradiction].
    match goal with |- context [lenlens_loop _ ?x] =>
      destruct (IHk x) as (A & B & C & D);
      assert (X: i_wrap (m_s x) = i_wrap (m_s m) /\ i_mode (m_s x) = i_mode (m_s m) /\ m_ret x = m_ret m /\
                 m_leave x = m_leave m) by (cbn -[needbits]; rewrite needbits_s, needbits_ret; auto) end.
    intuition congruence.
Qed.

(* one pass of CODELENS' while loop *)
Definition cl_rl (m: mst) (o: clout) : Prop :=
  match o with
  | CLnext m' => i_wrap (m_s m') = i_wrap (m_s m) /\ m_ret m' = m_ret m /\ m_mode m' = m_mode m /\ m_leave m' = 0
  | CLleave m' => i_wrap (m_s m') = i_wrap (m_s m) /\ m_ret m' = m_ret m /\ m_mode m' = m_mode m
  | CLbad m' => i_wrap (m_s m') = i_wrap (m_s m) /\ m_ret m' = m_ret m /\ m_mode m' = BAD /\ m_leave m' = 0
  end.

Lemma codelens_iter_rl fx dx m : m_leave m = 0 -> cl_rl m (codelens_iter fx dx m).
Proof.
  intros L0. unfold codelens_iter. hsplit; puse; pbool; unfold cl_rl; pclose.
Qed.

Lemma codelens_loop_rl fx dx k m : m_leave m = 0 -> cl_rl m (codelens_loop fx dx k m).
Proof.
  revert m; induction k; intros m L0; cbn [codelens_loop]; [unfold cl_rl; auto|].
  destruct (_ <? _); [|unfold cl_rl; auto].
  pose proof (codelens_iter_rl fx dx m L0) as A.
  destruct (codelens_iter fx dx m) as [m1|m1|m1]; [|exact A|exact A].
  destruct A as (A1 & A2 & A3 & A4). specialize (IHk m1 A4).
  destruct (codelens_loop fx dx k m1); cbn in IHk |- *; unfold m_mode in *; intuition congruence.
Qed.

(* inflate_fast changes the mode only to TYPE or BAD *)
Definition fk (m m': mst) : Prop :=
  i_wrap (m_s m') = i_wrap (m_s m) /\ m_ret m' = m_ret m /\ m_leave m' = m_leave m /\
  (m_mode m' = m_mode m \/ m_mode m' = TYPE \/ m_mode m' = BAD).

Lemma fk_refl m : fk m m.
Proof. unfold fk; auto. Qed.

Lemma fk_trans m1 m2 m3 : fk m1 m2 -> fk m2 m3 -> fk m1 m3.
Proof. unfold fk; intros (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2). intuition congruence. Qed.

Lemma fast_iter_fk fx dx m : fk m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. hsplit; puse; unfold fk, m_mode; repeat progress (hcbn; prw); repeat split; auto. Qed.

Lemma fast_loop_fk fx dx k m : fk m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply fk_refl|].
  pose proof (fast_iter_fk fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [eapply fk_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma fast_fk fx dx m : fk m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (fast_loop_fk fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply fk_trans; [exact A|]. unfold fk, m_mode; cbn. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Create HintDb pdc.
#[export] Hint Extern 1 (ppre _) => (unfold ppre; pclose) : pdc.
#[export] Hint Extern 1 (m_mode _ = _) => pclose : pdc.

Ltac pleaf :=
  match goal with
  | |- pgood _ (IBrk _) => unfold pgood; pclose
  | |- pgood _ (IRet _ _) => unfold pgood; pclose
  | |- pgood ?m (?f ?x) => apply (pgood_trans m x); [pclose | auto with pdc]
  end.

Ltac pcase := unfold ppre in *; hsplit; puse; pbool; pleaf.

Section CasesP.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_p m : m_mode m = DONE -> pgood m (c_DONE m).
Proof. intros H; unfold c_DONE; pcase. Qed.
Hint Resolve c_DONE_p : pdc.
Lemma c_BAD_p m : m_mode m = BAD -> pgood m (c_BAD m).
Proof. intros H; unfold c_BAD; pcase. Qed.
Hint Resolve c_BAD_p : pdc.
Lemma c_LENGTH_p m : ppre m -> pgood m (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; pcase. Qed.
Hint Resolve c_LENGTH_p : pdc.
Lemma c_CHECK_p m : ppre m -> pgood m (c_CHECK m).
Proof. intros H; unfold c_CHECK; pcase. Qed.
Hint Resolve c_CHECK_p : pdc.
Lemma c_LIT_p m : ppre m -> pgood m (c_LIT m).
Proof. intros H; unfold c_LIT; pcase. Qed.
Hint Resolve c_LIT_p : pdc.
Lemma c_MATCH_p m : ppre m -> pgood m (c_MATCH m).
Proof. intros H; unfold c_MATCH; pcase. Qed.
Hint Resolve c_MATCH_p : pdc.
Lemma c_DISTEXT_p m : ppre m -> pgood m (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; pcase. Qed.
Hint Resolve c_DISTEXT_p : pdc.
Lemma c_DIST_p m : ppre m -> pgood m (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; pcase. Qed.
Hint Resolve c_DIST_p : pdc.
Lemma c_LENEXT_p m : ppre m -> pgood m (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; pcase. Qed.
Hint Resolve c_LENEXT_p : pdc.
Lemma c_LEN_p m : ppre m -> pgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LEN.
  pose proof (fast_fk fx dx (restore m)) as Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf; unfold fk, m_mode in Hf; hcbn_in Hf.
  destruct Hf as (Hf1 & Hf2 & Hf3 & Hf4).
  pcase.
Qed.
Hint Resolve c_LEN_p : pdc.
Lemma c_LEN__p m : ppre m -> pgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H; unfold c_LEN_; pcase. Qed.
Hint Resolve c_LEN__p : pdc.
Lemma c_CODELENS_p m : ppre m -> pgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_CODELENS.
  pose proof (codelens_loop_rl fx dx 320 m (proj1 H)) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [cl_rl] in Hc; unfold m_mode in Hc.
  - destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4); pcase.
  - destruct Hc as (Hc1 & Hc2 & Hc3); pcase.
  - destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4); pcase.
Qed.
Hint Resolve c_CODELENS_p : pdc.
Lemma c_LENLENS_p m : ppre m -> pgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_rl 19 m) as (A1 & A2 & A3 & A4); revert A1 A2 A3 A4.
  generalize (lenlens_loop 19 m); intros ml A1 A2 A3 A4.
  pose proof (lenlens_zero_mode 19 (m_s ml)) as C1; pose proof (lenlens_zero_wrap 19 (m_s ml)) as C2;
    revert C1 C2.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C1 C2.
  pcase.
Qed.
Hint Resolve c_LENLENS_p : pdc.
Lemma c_TABLE_p m : ppre m -> pgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros H; unfold c_TABLE; pcase. Qed.
Hint Resolve c_TABLE_p : pdc.
Lemma c_COPY_p m : ppre m -> pgood m (c_COPY m).
Proof. intros H; unfold c_COPY; pcase. Qed.
Hint Resolve c_COPY_p : pdc.
Lemma c_COPY__p m : ppre m -> pgood m (c_COPY_ m).
Proof. intros H; unfold c_COPY_; pcase. Qed.
Hint Resolve c_COPY__p : pdc.
Lemma c_STORED_p m : ppre m -> pgood m (c_STORED fl m).
Proof. intros H; unfold c_STORED; pcase. Qed.
Hint Resolve c_STORED_p : pdc.
Lemma c_TYPEDO_p m : ppre m -> pgood m (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; pcase. Qed.
Hint Resolve c_TYPEDO_p : pdc.
Lemma c_TYPE_p m : ppre m -> pgood m (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; pcase. Qed.
Hint Resolve c_TYPE_p : pdc.
Lemma c_DICT_p m : ppre m -> m_mode m = DICT -> pgood m (c_DICT fl m).
Proof. intros H H'; unfold c_DICT; pcase. Qed.
Hint Resolve c_DICT_p : pdc.
Lemma c_DICTID_p m : ppre m -> pgood m (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; pcase. Qed.
Hint Resolve c_DICTID_p : pdc.
Lemma c_HCRC_p m : ppre m -> pgood m (c_HCRC m).
Proof. intros H; unfold c_HCRC; pcase. Qed.
Hint Resolve c_HCRC_p : pdc.
Lemma c_COMMENT2_p m : ppre m -> pgood m (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; pcase. Qed.
Hint Resolve c_COMMENT2_p : pdc.
Lemma c_NAME2_p m : ppre m -> pgood m (c_NAME2 m).
Proof. intros H; unfold c_NAME2; pcase. Qed.
Hint Resolve c_NAME2_p : pdc.
Lemma c_EXTRA2_p m : ppre m -> pgood m (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; pcase. Qed.
Hint Resolve c_EXTRA2_p : pdc.
Lemma c_EXLEN2_p m : ppre m -> pgood m (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; pcase. Qed.
Hint Resolve c_EXLEN2_p : pdc.
Lemma c_OS2_p m : ppre m -> pgood m (c_OS2 m).
Proof. intros H; unfold c_OS2; pcase. Qed.
Hint Resolve c_OS2_p : pdc.
Lemma c_TIME2_p m : ppre m -> pgood m (c_TIME2 m).
Proof. intros H; unfold c_TIME2; pcase. Qed.
Hint Resolve c_TIME2_p : pdc.
Lemma c_FLAGS2_p m : ppre m -> pgood m (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; pcase. Qed.
Hint Resolve c_FLAGS2_p : pdc.
Lemma c_HEAD2_p m : ppre m -> pgood m (c_HEAD2 m).
Proof. intros H; unfold c_HEAD2; pcase. Qed.

Ltac md_pre E H := unfold ppre; apply Z.eqb_eq in E; unfold md_rng, m_mode in *; rewrite E in *;
  repeat split; try assumption; try apply H; wmodes; lia.

(* one pass from a loop head in HEAD..BAD with the discipline of ret *)
Lemma stepf2_pgood m : md_rng m -> m_leave m = 0 -> (m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK) ->
  pgood m (stepf2 fl fx dx m).
Proof.
  intros H0 L0 H1.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD) eqn:E1; [apply c_HEAD2_p; md_pre E1 H1|].
  destruct (m_mode m =? FLAGS) eqn:E2; [apply c_FLAGS2_p; md_pre E2 H1|].
  destruct (m_mode m =? TIME) eqn:E3; [apply c_TIME2_p; md_pre E3 H1|].
  destruct (m_mode m =? OS) eqn:E4; [apply c_OS2_p; md_pre E4 H1|].
  destruct (m_mode m =? EXLEN) eqn:E5; [apply c_EXLEN2_p; md_pre E5 H1|].
  destruct (m_mode m =? EXTRA) eqn:E6; [apply c_EXTRA2_p; md_pre E6 H1|].
  destruct (m_mode m =? NAME) eqn:E7; [apply c_NAME2_p; md_pre E7 H1|].
  destruct (m_mode m =? COMMENT) eqn:E8; [apply c_COMMENT2_p; md_pre E8 H1|].
  destruct (m_mode m =? HCRC) eqn:E9; [apply c_HCRC_p; md_pre E9 H1|].
  destruct (m_mode m =? DICTID) eqn:E10; [apply c_DICTID_p; md_pre E10 H1|].
  destruct (m_mode m =? DICT) eqn:E11;
    [apply c_DICT_p; [md_pre E11 H1 | apply Z.eqb_eq in E11; exact E11]|].
  destruct (m_mode m =? TYPE) eqn:E12; [apply c_TYPE_p; md_pre E12 H1|].
  destruct (m_mode m =? TYPEDO) eqn:E13; [apply c_TYPEDO_p; md_pre E13 H1|].
  destruct (m_mode m =? STORED) eqn:E14; [apply c_STORED_p; md_pre E14 H1|].
  destruct (m_mode m =? COPY_) eqn:E15; [apply c_COPY__p; md_pre E15 H1|].
  destruct (m_mode m =? COPY) eqn:E16; [apply c_COPY_p; md_pre E16 H1|].
  destruct (m_mode m =? TABLE) eqn:E17; [apply c_TABLE_p; md_pre E17 H1|].
  destruct (m_mode m =? LENLENS) eqn:E18; [apply c_LENLENS_p; md_pre E18 H1|].
  destruct (m_mode m =? CODELENS) eqn:E19; [apply c_CODELENS_p; md_pre E19 H1|].
  destruct (m_mode m =? LEN_) eqn:E20; [apply c_LEN__p; md_pre E20 H1|].
  destruct (m_mode m =? LEN) eqn:E21; [apply c_LEN_p; md_pre E21 H1|].
  destruct (m_mode m =? LENEXT) eqn:E22; [apply c_LENEXT_p; md_pre E22 H1|].
  destruct (m_mode m =? DIST) eqn:E23; [apply c_DIST_p; md_pre E23 H1|].
  destruct (m_mode m =? DISTEXT) eqn:E24; [apply c_DISTEXT_p; md_pre E24 H1|].
  destruct (m_mode m =? MATCH) eqn:E25; [apply c_MATCH_p; md_pre E25 H1|].
  destruct (m_mode m =? LIT) eqn:E26; [apply c_LIT_p; md_pre E26 H1|].
  destruct (m_mode m =? CHECK) eqn:E27; [apply c_CHECK_p; md_pre E27 H1|].
  destruct (m_mode m =? LENGTH) eqn:E28; [apply c_LENGTH_p; md_pre E28 H1|].
  destruct (m_mode m =? DONE) eqn:E29; [apply c_DONE_p; apply Z.eqb_eq in E29; exact E29|].
  destruct (m_mode m =? BAD) eqn:E30; [apply c_BAD_p; apply Z.eqb_eq in E30; exact E30|].
  exfalso. pose proof (md_rng_hit (m_mode m) H0) as Hh.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, E19, E20, E21,
    E22, E23, E24, E25, E26, E27, E28, E29, E30 in Hh.
  discriminate.
Qed.

End CasesP.

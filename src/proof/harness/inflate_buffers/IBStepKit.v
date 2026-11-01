(* Law inflate_buffers: one pass of the switch of Model2.v (stepf2) keeps the input, avail_out on entry, `in`
   and total_in; only grows the output; keeps total_out + out (mod 2^64: only CHECK moves `out` to `left`
   and adds the difference to total_out); keeps left <= out; header modes (HEAD..DICT) are only reached from
   header modes without output; every break leaves a mode in HEAD..BAD; the only return (from a mode in
   HEAD..BAD) is DICT's Z_NEED_DICT, after RESTORE and the total_in update.
   (Modelled on inflate_api/StepInv5Kit.v.) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

Definition hdr_md (md: Z) : Prop := HEAD <= md <= DICT.

(* the facts kept by the helpers that do not touch the machine's outer fields *)
Definition fr (m m': mst) : Prop :=
  m_s m' = m_s m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\
  m_in m' = m_in m /\ m_out m' = m_out m /\ m_tin m' = m_tin m /\ m_tout m' = m_tout m.

(* the facts kept by the helpers (the CODELENS loop, inflate_fast) *)
Definition hk (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_in m' = m_in m /\ m_tin m' = m_tin m /\
  m_tout m' = m_tout m /\ m_out m' = m_out m /\ Zlength (m_ow m) <= Zlength (m_ow m') /\
  (i_mode (m_s m') = i_mode (m_s m) \/ i_mode (m_s m') = TYPE \/ i_mode (m_s m') = BAD).

(* the relation of a case's input and output (break) *)
Definition trel (m m': mst) : Prop :=
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_in m' = m_in m /\ m_tin m' = m_tin m /\
  Zlength (m_ow m) <= Zlength (m_ow m') /\
  (m_tout m' + m_out m') mod 2 ^ 64 = (m_tout m + m_out m) mod 2 ^ 64 /\
  (m_left m <= m_out m -> m_left m' <= m_out m') /\
  (hdr_md (m_mode m') -> hdr_md (m_mode m) /\ Zlength (m_ow m') = Zlength (m_ow m) /\
     m_out m' = m_out m /\ m_tout m' = m_tout m) /\
  HEAD <= m_mode m' <= BAD.

(* ... and of a return (DICT's Z_NEED_DICT) *)
Definition tret (m m': mst) : Prop :=
  hdr_md (m_mode m) /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_in m' = m_in m /\
  m_snx m' = m_nx m' /\ m_sow m' = Zlength (m_ow m') /\ Zlength (m_ow m') = Zlength (m_ow m) /\
  m_out m' = m_out m /\ m_tout m' = m_tout m /\
  m_tin m' = u64 (m_tin m + u32 (m_in m - (Zlength (m_inp m) - m_nx m'))).

Definition tgood (m: mst) (o: iout) : Prop :=
  match o with IBrk m' => trel m m' | IRet r m' => r = Z_NEED_DICT /\ tret m m' end.

Lemma trel_trans m1 m2 m3 : trel m1 m2 -> trel m2 m3 -> trel m1 m3.
Proof.
  unfold trel; intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1 & I1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2 & I2).
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [lia|]. split; [congruence|]. split; [auto|].
  split; [|exact I2].
  intros Hh. destruct (H2 Hh) as (J1 & J2 & J3 & J4). destruct (H1 J1) as (K1 & K2 & K3 & K4).
  split; [exact K1|]. split; [congruence|]. split; congruence.
Qed.

Lemma tgood_trans m m' o : trel m m' -> tgood m' o -> tgood m o.
Proof.
  destruct o as [m''|r m'']; cbn; [apply trel_trans|].
  unfold trel, tret; intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1 & I1) (R & J1 & A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2 & I2).
  destruct (H1 J1) as (K1 & K2 & K3 & K4).
  split; [exact R|]. split; [exact K1|].
  repeat split; try congruence.
  all: rewrite I2, D1, C1, A1; reflexivity.
Qed.

Ltac wmodes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
  LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma fr_refl m : fr m m.
Proof. unfold fr; repeat split. Qed.

Lemma fr_trans m1 m2 m3 : fr m1 m2 -> fr m2 m3 -> fr m1 m3.
Proof.
  unfold fr; intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  repeat split; congruence.
Qed.

Lemma fr_pull m : fr m (pull m).
Proof. unfold fr; repeat split. Qed.

Lemma fr_leave m : fr m (set_leave m).
Proof. unfold fr; repeat split. Qed.

Lemma needbits_f_fr k n m : fr m (needbits_f k n m).
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [apply fr_refl|].
  destruct (m_bits m <? n); [|apply fr_refl].
  destruct (m_have m =? 0); [apply fr_leave|].
  eapply fr_trans; [apply fr_pull | apply IHk].
Qed.

Lemma needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_inp n m : m_inp (needbits n m) = m_inp m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_aout n m : m_aout (needbits n m) = m_aout m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_ow n m : m_ow (needbits n m) = m_ow m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_in n m : m_in (needbits n m) = m_in m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_out n m : m_out (needbits n m) = m_out m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_tin n m : m_tin (needbits n m) = m_tin m.
Proof. apply needbits_f_fr. Qed.
Lemma needbits_tout n m : m_tout (needbits n m) = m_tout m.
Proof. apply needbits_f_fr. Qed.

Local Opaque needbits needbits_f.

Lemma crc_if_mode m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_inp m d : m_inp (crc_if m d) = m_inp m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_aout m d : m_aout (crc_if m d) = m_aout m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_ow m d : m_ow (crc_if m d) = m_ow m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_in m d : m_in (crc_if m d) = m_in m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_out m d : m_out (crc_if m d) = m_out m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_tin m d : m_tin (crc_if m d) = m_tin m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_tout m d : m_tout (crc_if m d) = m_tout m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma crc_if_nx m d : m_nx (crc_if m d) = m_nx m.
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.

Lemma lens_fill_mode k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite IHk. reflexivity. Qed.

Lemma lenlens_zero_mode k s : i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto]. rewrite IHk. reflexivity.
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

Lemma lookup1_f_fr k fx dx t nb m h m' ok : lookup1_f k fx dx t nb m = (h, m', ok) -> fr m m'.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; subst; apply fr_refl.
  - destruct (_ <=? _); [inversion E; subst; apply fr_refl|].
    destruct (m_have m =? 0); [inversion E; subst; apply fr_leave|].
    apply IHk in E. eapply fr_trans; [apply fr_pull | exact E].
Qed.

Lemma lookup1_fr fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) -> fr m m'.
Proof. apply lookup1_f_fr. Qed.

Lemma lookup2_f_fr k fx dx t last m h m' ok : lookup2_f k fx dx t last m = (h, m', ok) -> fr m m'.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; subst; apply fr_refl.
  - destruct (_ <=? _); [inversion E; subst; apply fr_refl|].
    destruct (m_have m =? 0); [inversion E; subst; apply fr_leave|].
    apply IHk in E. eapply fr_trans; [apply fr_pull | exact E].
Qed.

Lemma lookup2_fr fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) -> fr m m'.
Proof. apply lookup2_f_fr. Qed.

(* fwalk_f changes only hold and bits *)
Lemma fwalk_f_fr fx dx k il t here m h' m' : fwalk_f fx dx k il t here m = (h', m') -> fr m m'.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; unfold fr; repeat split.
  - destruct (il (e_op here)).
    + apply IHk in E. eapply fr_trans; [|exact E]. unfold fr; repeat split.
    + inversion E; subst; unfold fr; repeat split.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Create HintDb ibw.
Hint Rewrite needbits_s needbits_inp needbits_aout needbits_ow needbits_in needbits_out needbits_tin
  needbits_tout crc_if_mode crc_if_inp crc_if_aout crc_if_ow crc_if_in crc_if_out crc_if_tin crc_if_tout
  crc_if_nx lens_fill_mode lenlens_zero_mode : ibw.

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
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_fr in E; destruct E as (? & ? & ? & ? & ? & ? & ? & ?)
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_fr in E; destruct E as (? & ? & ? & ? & ? & ? & ? & ?)
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_fr in E; destruct E as (? & ? & ? & ? & ? & ? & ? & ?)
  | E: copy_bytes _ _ _ _ = (_, _) |- _ => apply copy_bytes_len in E
  end.

Ltac hrw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: m_inp ?a = _ |- context [m_inp ?a] => rewrite H
  | H: m_aout ?a = _ |- context [m_aout ?a] => rewrite H
  | H: m_ow ?a = _ |- context [m_ow ?a] => rewrite H
  | H: m_in ?a = _ |- context [m_in ?a] => rewrite H
  | H: m_out ?a = _ |- context [m_out ?a] => rewrite H
  | H: m_tin ?a = _ |- context [m_tin ?a] => rewrite H
  | H: m_tout ?a = _ |- context [m_tout ?a] => rewrite H
  | H: i_mode ?a = _ |- context [i_mode ?a] => is_var a; rewrite H
  end.

Ltac hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength u32 u64
                    updatewindow update_check].

Ltac hcbn_in H := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC
                    DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN
                    LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC Zlength u32 u64
                    updatewindow update_check] in H.

(* normalize the helper facts, and rewrite them with each other *)
Ltac hyp_norm :=
  repeat match goal with
  | H: m_s _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_inp _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_aout _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_ow _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_in _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_out _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_tin _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: m_tout _ = _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  | H: Zlength _ <= Zlength _ |- _ => progress (hcbn_in H; autorewrite with ibw in H)
  end;
  repeat match goal with
  | H: m_s ?a = _, H2: context [m_s ?a] |- _ => is_var a; rewrite H in H2
  | H: m_inp ?a = _, H2: context [m_inp ?a] |- _ => is_var a; rewrite H in H2
  | H: m_aout ?a = _, H2: context [m_aout ?a] |- _ => is_var a; rewrite H in H2
  | H: m_ow ?a = _, H2: context [m_ow ?a] |- _ => is_var a; rewrite H in H2
  | H: m_in ?a = _, H2: context [m_in ?a] |- _ => is_var a; rewrite H in H2
  | H: m_out ?a = _, H2: context [m_out ?a] |- _ => is_var a; rewrite H in H2
  | H: m_tin ?a = _, H2: context [m_tin ?a] |- _ => is_var a; rewrite H in H2
  | H: m_tout ?a = _, H2: context [m_tout ?a] |- _ => is_var a; rewrite H in H2
  end.

Ltac wnorm := hyp_norm; repeat progress (hcbn; autorewrite with ibw; hrw).

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

Ltac wfin := unfold m_left, m_mode, m_have, hdr_md in *; rewrite ?Zlength_app in *; zlnn; wmodes;
  repeat split; try reflexivity; try lia.

Ltac kclose := unfold hk; wnorm; wfin.
Ltac wclose := unfold trel; wnorm; wfin.
Ltac rclose := unfold tret; wnorm; wfin.

Lemma hk_refl m : hk m m.
Proof. unfold hk; repeat split; auto; lia. Qed.

Lemma hk_trans m1 m2 m3 : hk m1 m2 -> hk m2 m3 -> hk m1 m3.
Proof.
  unfold hk; intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  repeat split; try congruence; try lia.
  all: destruct H1 as [H1|[H1|H1]]; destruct H2 as [H2|[H2|H2]]; rewrite H2; auto; rewrite H1; auto.
Qed.

Lemma codelens_iter_k fx dx m : hk m (clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. hsplit; huse; kclose. Qed.

Lemma codelens_loop_k fx dx k m : hk m (clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply hk_refl|].
  destruct (_ <? _); [|apply hk_refl].
  pose proof (codelens_iter_k fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply hk_trans; [exact A | apply IHk].
Qed.

Lemma lenlens_loop_k k m :
  m_inp (lenlens_loop k m) = m_inp m /\ m_aout (lenlens_loop k m) = m_aout m /\
  m_in (lenlens_loop k m) = m_in m /\ m_tin (lenlens_loop k m) = m_tin m /\
  m_tout (lenlens_loop k m) = m_tout m /\ m_out (lenlens_loop k m) = m_out m /\
  m_ow (lenlens_loop k m) = m_ow m /\ i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [repeat split|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|repeat split].
  destruct (m_leave (needbits 3 m) =? 1); [autorewrite with ibw; repeat split|].
  match goal with |- context [lenlens_loop _ ?x] => destruct (IHk x) as (-> & -> & -> & -> & -> & -> & -> & ->) end.
  cbn. autorewrite with ibw; repeat split.
Qed.

Lemma fast_iter_k fx dx m : hk m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. hsplit; huse; kclose. Qed.

Lemma fast_loop_k fx dx k m : hk m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply hk_refl|].
  pose proof (fast_iter_k fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (_ && _); [eapply hk_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma fast_k fx dx m : hk m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (fast_loop_k fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply hk_trans; [exact A|]. kclose.
Qed.

(* CHECK: total_out += out - left, out = left *)
Lemma ck_mod T O L : 0 <= L <= O -> O - L < 2 ^ 32 ->
  (u64 (T + u32 (O - L)) + L) mod 2 ^ 64 = (T + O) mod 2 ^ 64.
Proof.
  intros A B. unfold u64, u32. rewrite (Z.mod_small (O - L)) by lia. rewrite Zplus_mod_idemp_l.
  f_equal; lia.
Qed.

Ltac wfin ::= unfold m_left, m_mode, m_have, hdr_md in *; rewrite ?Zlength_app in *; zlnn; wmodes;
  repeat split; try reflexivity; try (rewrite ck_mod by lia; reflexivity); try lia.
Ltac wclose ::= unfold trel, m_left, m_mode, m_have, hdr_md in *; wnorm; wfin.
Ltac rclose ::= unfold tret, m_left, m_mode, m_have, hdr_md in *; wnorm; wfin.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases                                                                                      *)

Definition md_rng (m: mst) : Prop := HEAD <= m_mode m <= BAD.
Definition md_rng2 (m: mst) : Prop := DICT < m_mode m <= BAD.
Definition md_hdr (m: mst) : Prop := HEAD <= m_mode m <= DICT.

Create HintDb tdc.
#[export] Hint Extern 1 (md_rng _) => (unfold md_rng, m_mode in *; hcbn; wmodes; lia) : tdc.
#[export] Hint Extern 1 (md_rng2 _) => (unfold md_rng2, m_mode in *; hcbn; wmodes; lia) : tdc.
#[export] Hint Extern 1 (md_hdr _) => (unfold md_hdr, m_mode in *; hcbn; wmodes; lia) : tdc.
#[export] Hint Extern 1 (m_mode _ = _) => (unfold m_mode in *; hcbn; wmodes; lia) : tdc.

Ltac wleaf :=
  match goal with
  | |- tgood _ (IBrk _) => unfold tgood; wclose
  | |- tgood _ (IRet _ _) => unfold tgood; split; [reflexivity | rclose]
  | |- tgood ?m (?f ?x) => apply (tgood_trans m x); [wclose | auto with tdc]
  end.

Ltac wcase := unfold md_rng, md_rng2, md_hdr in *; hsplit; huse; wleaf.

Section CasesT.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_t m : md_rng2 m -> tgood m (c_DONE m).
Proof. intros H; unfold c_DONE; wcase. Qed.
Hint Resolve c_DONE_t : tdc.
Lemma c_BAD_t m : md_rng2 m -> tgood m (c_BAD m).
Proof. intros H; unfold c_BAD; wcase. Qed.
Hint Resolve c_BAD_t : tdc.
Lemma c_LENGTH_t m : md_rng2 m -> tgood m (c_LENGTH m).
Proof. intros H; unfold c_LENGTH; wcase. Qed.
Hint Resolve c_LENGTH_t : tdc.
Lemma c_LIT_t m : md_rng2 m -> tgood m (c_LIT m).
Proof. intros H; unfold c_LIT; wcase. Qed.
Hint Resolve c_LIT_t : tdc.
Lemma c_MATCH_t m : md_rng2 m -> tgood m (c_MATCH m).
Proof. intros H; unfold c_MATCH; wcase. Qed.
Hint Resolve c_MATCH_t : tdc.
Lemma c_DISTEXT_t m : md_rng2 m -> tgood m (c_DISTEXT m).
Proof. intros H; unfold c_DISTEXT; wcase. Qed.
Hint Resolve c_DISTEXT_t : tdc.
Lemma c_DIST_t m : md_rng2 m -> tgood m (c_DIST fx dx m).
Proof. intros H; unfold c_DIST; wcase. Qed.
Hint Resolve c_DIST_t : tdc.
Lemma c_LENEXT_t m : md_rng2 m -> tgood m (c_LENEXT fx dx m).
Proof. intros H; unfold c_LENEXT; wcase. Qed.
Hint Resolve c_LENEXT_t : tdc.
Lemma c_LEN_t m : md_rng2 m -> tgood m (c_LEN fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LEN.
  pose proof (fast_k fx dx (restore m)) as Hf; unfold hk in Hf; hcbn_in Hf; revert Hf.
  generalize (fast fx dx (restore m)); intros mf (Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8).
  wcase.
Qed.
Hint Resolve c_LEN_t : tdc.
Lemma c_LEN__t m : md_rng2 m -> tgood m (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H; unfold c_LEN_; wcase. Qed.
Hint Resolve c_LEN__t : tdc.

Lemma c_CODELENS_t m : md_rng2 m -> tgood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_CODELENS.
  pose proof (codelens_loop_k fx dx 320 m) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [clm] in Hc; unfold hk in Hc;
    destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8); wcase.
Qed.
Hint Resolve c_CODELENS_t : tdc.
Lemma c_LENLENS_t m : md_rng2 m -> tgood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  intros H; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_k 19 m) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8);
    revert A1 A2 A3 A4 A5 A6 A7 A8.
  generalize (lenlens_loop 19 m); intros ml A1 A2 A3 A4 A5 A6 A7 A8.
  pose proof (lenlens_zero_mode 19 (m_s ml)) as C1; revert C1.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C1.
  wcase.
Qed.
Hint Resolve c_LENLENS_t : tdc.
Lemma c_TABLE_t m : md_rng2 m -> tgood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros H; unfold c_TABLE; wcase. Qed.
Hint Resolve c_TABLE_t : tdc.
Lemma c_COPY_t m : md_rng2 m -> tgood m (c_COPY m).
Proof. intros H; unfold c_COPY; wcase. Qed.
Hint Resolve c_COPY_t : tdc.
Lemma c_COPY__t m : md_rng2 m -> tgood m (c_COPY_ m).
Proof. intros H; unfold c_COPY_; wcase. Qed.
Hint Resolve c_COPY__t : tdc.
Lemma c_STORED_t m : md_rng2 m -> tgood m (c_STORED fl m).
Proof. intros H; unfold c_STORED; wcase. Qed.
Hint Resolve c_STORED_t : tdc.
Lemma c_TYPEDO_t m : md_rng2 m -> tgood m (c_TYPEDO fl m).
Proof. intros H; unfold c_TYPEDO; wcase. Qed.
Hint Resolve c_TYPEDO_t : tdc.
Lemma c_TYPE_t m : md_rng2 m -> tgood m (c_TYPE fl m).
Proof. intros H; unfold c_TYPE; wcase. Qed.
Hint Resolve c_TYPE_t : tdc.
Lemma c_DICT_t m : md_hdr m -> m_mode m = DICT -> tgood m (c_DICT fl m).
Proof. intros H H'; unfold c_DICT; wcase. Qed.
Hint Resolve c_DICT_t : tdc.
Lemma c_DICTID_t m : md_hdr m -> tgood m (c_DICTID fl m).
Proof. intros H; unfold c_DICTID; wcase. Qed.
Hint Resolve c_DICTID_t : tdc.
Lemma c_HCRC_t m : md_hdr m -> tgood m (c_HCRC m).
Proof. intros H; unfold c_HCRC; wcase. Qed.
Hint Resolve c_HCRC_t : tdc.
Lemma c_COMMENT2_t m : md_hdr m -> tgood m (c_COMMENT2 m).
Proof. intros H; unfold c_COMMENT2; wcase. Qed.
Hint Resolve c_COMMENT2_t : tdc.
Lemma c_NAME2_t m : md_hdr m -> tgood m (c_NAME2 m).
Proof. intros H; unfold c_NAME2; wcase. Qed.
Hint Resolve c_NAME2_t : tdc.
Lemma c_EXTRA2_t m : md_hdr m -> tgood m (c_EXTRA2 m).
Proof. intros H; unfold c_EXTRA2; wcase. Qed.
Hint Resolve c_EXTRA2_t : tdc.
Lemma c_EXLEN2_t m : md_hdr m -> tgood m (c_EXLEN2 m).
Proof. intros H; unfold c_EXLEN2; wcase. Qed.
Hint Resolve c_EXLEN2_t : tdc.
Lemma c_OS2_t m : md_hdr m -> tgood m (c_OS2 m).
Proof. intros H; unfold c_OS2; wcase. Qed.
Hint Resolve c_OS2_t : tdc.
Lemma c_TIME2_t m : md_hdr m -> tgood m (c_TIME2 m).
Proof. intros H; unfold c_TIME2; wcase. Qed.
Hint Resolve c_TIME2_t : tdc.
Lemma c_FLAGS2_t m : md_hdr m -> tgood m (c_FLAGS2 m).
Proof. intros H; unfold c_FLAGS2; wcase. Qed.
Hint Resolve c_FLAGS2_t : tdc.
Lemma c_HEAD2_t m : md_hdr m -> tgood m (c_HEAD2 m).
Proof. intros H; unfold c_HEAD2; wcase. Qed.
Hint Resolve c_HEAD2_t : tdc.
Lemma c_CHECK_t m : md_rng2 m -> 0 <= m_left m <= m_out m -> m_out m < 2 ^ 32 -> tgood m (c_CHECK m).
Proof. intros H H1 H2; unfold c_CHECK; wcase. Qed.

Lemma md_rng_hit x : HEAD <= x <= BAD ->
  (x =? HEAD) || (x =? FLAGS) || (x =? TIME) || (x =? OS) || (x =? EXLEN) || (x =? EXTRA) || (x =? NAME) ||
  (x =? COMMENT) || (x =? HCRC) || (x =? DICTID) || (x =? DICT) || (x =? TYPE) || (x =? TYPEDO) ||
  (x =? STORED) || (x =? COPY_) || (x =? COPY) || (x =? TABLE) || (x =? LENLENS) || (x =? CODELENS) ||
  (x =? LEN_) || (x =? LEN) || (x =? LENEXT) || (x =? DIST) || (x =? DISTEXT) || (x =? MATCH) ||
  (x =? LIT) || (x =? CHECK) || (x =? LENGTH) || (x =? DONE) || (x =? BAD) = true.
Proof.
  intros H. wmodes.
  assert (exists n, (n < 30)%nat /\ x = 16180 + Z.of_nat n) as (n & Hn & ->)
    by (exists (Z.to_nat (x - 16180)); lia).
  do 30 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Ltac md_tac E := unfold md_rng, md_rng2, md_hdr in *; apply Z.eqb_eq in E; unfold m_mode in *; rewrite E in *; wmodes; lia.

Lemma stepf2_tgood m : md_rng m -> 0 <= m_left m <= m_out m -> m_out m < 2 ^ 32 ->
  tgood m (stepf2 fl fx dx m).
Proof.
  intros H0 H1 H2.
  unfold stepf2, step2.
  destruct (m_mode m =? HEAD) eqn:E1; [apply c_HEAD2_t; try assumption; md_tac E1|].
  destruct (m_mode m =? FLAGS) eqn:E2; [apply c_FLAGS2_t; try assumption; md_tac E2|].
  destruct (m_mode m =? TIME) eqn:E3; [apply c_TIME2_t; try assumption; md_tac E3|].
  destruct (m_mode m =? OS) eqn:E4; [apply c_OS2_t; try assumption; md_tac E4|].
  destruct (m_mode m =? EXLEN) eqn:E5; [apply c_EXLEN2_t; try assumption; md_tac E5|].
  destruct (m_mode m =? EXTRA) eqn:E6; [apply c_EXTRA2_t; try assumption; md_tac E6|].
  destruct (m_mode m =? NAME) eqn:E7; [apply c_NAME2_t; try assumption; md_tac E7|].
  destruct (m_mode m =? COMMENT) eqn:E8; [apply c_COMMENT2_t; try assumption; md_tac E8|].
  destruct (m_mode m =? HCRC) eqn:E9; [apply c_HCRC_t; try assumption; md_tac E9|].
  destruct (m_mode m =? DICTID) eqn:E10; [apply c_DICTID_t; try assumption; md_tac E10|].
  destruct (m_mode m =? DICT) eqn:E11; [apply c_DICT_t; try assumption; md_tac E11|].
  destruct (m_mode m =? TYPE) eqn:E12; [apply c_TYPE_t; try assumption; md_tac E12|].
  destruct (m_mode m =? TYPEDO) eqn:E13; [apply c_TYPEDO_t; try assumption; md_tac E13|].
  destruct (m_mode m =? STORED) eqn:E14; [apply c_STORED_t; try assumption; md_tac E14|].
  destruct (m_mode m =? COPY_) eqn:E15; [apply c_COPY__t; try assumption; md_tac E15|].
  destruct (m_mode m =? COPY) eqn:E16; [apply c_COPY_t; try assumption; md_tac E16|].
  destruct (m_mode m =? TABLE) eqn:E17; [apply c_TABLE_t; try assumption; md_tac E17|].
  destruct (m_mode m =? LENLENS) eqn:E18; [apply c_LENLENS_t; try assumption; md_tac E18|].
  destruct (m_mode m =? CODELENS) eqn:E19; [apply c_CODELENS_t; try assumption; md_tac E19|].
  destruct (m_mode m =? LEN_) eqn:E20; [apply c_LEN__t; try assumption; md_tac E20|].
  destruct (m_mode m =? LEN) eqn:E21; [apply c_LEN_t; try assumption; md_tac E21|].
  destruct (m_mode m =? LENEXT) eqn:E22; [apply c_LENEXT_t; try assumption; md_tac E22|].
  destruct (m_mode m =? DIST) eqn:E23; [apply c_DIST_t; try assumption; md_tac E23|].
  destruct (m_mode m =? DISTEXT) eqn:E24; [apply c_DISTEXT_t; try assumption; md_tac E24|].
  destruct (m_mode m =? MATCH) eqn:E25; [apply c_MATCH_t; try assumption; md_tac E25|].
  destruct (m_mode m =? LIT) eqn:E26; [apply c_LIT_t; try assumption; md_tac E26|].
  destruct (m_mode m =? CHECK) eqn:E27; [apply c_CHECK_t; try assumption; md_tac E27|].
  destruct (m_mode m =? LENGTH) eqn:E28; [apply c_LENGTH_t; try assumption; md_tac E28|].
  destruct (m_mode m =? DONE) eqn:E29; [apply c_DONE_t; try assumption; md_tac E29|].
  destruct (m_mode m =? BAD) eqn:E30; [apply c_BAD_t; try assumption; md_tac E30|].
  exfalso. pose proof (md_rng_hit (m_mode m) H0) as Hh.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, E19, E20, E21,
    E22, E23, E24, E25, E26, E27, E28, E29, E30 in Hh.
  discriminate.
Qed.

End CasesT.

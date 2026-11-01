(* The modes after the header keep the header model and the flags (RTH8Defs.stepf2_nh_stmt, leave_nh_stmt).
   Only the header cases HEAD .. HCRC write the gz_header model (upd_h) or state->flags; the cases DICTID .. SYNC
   only go to modes after the header (DICTID .. SYNC), and the exit inf_leave only to MEM.  The proof follows the
   case analysis of Body5HdrKit: every if of a case is destructed, and the helpers (NEEDBITS, the table lookups,
   the CODELENS loop, inflate_fast, the window update) are shown to keep the header, the flags and the mode (or to
   go to TYPE / BAD only). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8Defs.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module NH.
Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

(* what a pass keeps: the header model and the flags *)
Definition kept (m m': mst) : Prop := m_h m' = m_h m /\ i_flags (m_s m') = i_flags (m_s m).

(* the outcome of a case from m: the header and the flags kept, the mode after the header *)
Definition ngood (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => kept m m' /\ hdr_mode (m_mode m') = false
  | IRet _ m' => kept m m' /\ hdr_mode (m_mode m') = false
  end.

Lemma ngood_trans m x o : kept m x -> ngood x o -> ngood m o.
Proof. unfold ngood, kept; destruct o; intuition congruence. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The helpers                                                                                    *)

Lemma needbits_f_s k n m : m_s (needbits_f k n m) = m_s m /\ m_h (needbits_f k n m) = m_h m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  destruct (IHk (pull m)) as [-> ->]; auto.
Qed.
Lemma needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply needbits_f_s. Qed.
Lemma needbits_h n m : m_h (needbits n m) = m_h m.
Proof. apply needbits_f_s. Qed.

Lemma lookup1_f_s k fx dx t nb m h m' ok :
  lookup1_f k fx dx t nb m = (h, m', ok) -> m_s m' = m_s m /\ m_h m' = m_h m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> ->]; auto.
Qed.
Lemma lookup1_s fx dx t nb m h m' ok :
  lookup1 fx dx t nb m = (h, m', ok) -> m_s m' = m_s m /\ m_h m' = m_h m.
Proof. apply lookup1_f_s. Qed.

Lemma lookup2_f_s k fx dx t last m h m' ok :
  lookup2_f k fx dx t last m = (h, m', ok) -> m_s m' = m_s m /\ m_h m' = m_h m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; destruct E as [-> ->]; auto.
Qed.
Lemma lookup2_s fx dx t last m h m' ok :
  lookup2 fx dx t last m = (h, m', ok) -> m_s m' = m_s m /\ m_h m' = m_h m.
Proof. apply lookup2_f_s. Qed.

Lemma fwalk_f_s fx dx k il t here m h' m' :
  fwalk_f fx dx k il t here m = (h', m') -> m_s m' = m_s m /\ m_h m' = m_h m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; destruct E as [-> ->]; cbn; auto.
    + inversion E; subst; cbn; auto.
Qed.

Lemma lens_fill_fm k len s : i_flags (lens_fill k len s) = i_flags s /\ i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite (proj1 (IHk _)), (proj2 (IHk _)); auto. Qed.
Lemma lens_fill_f k len s : i_flags (lens_fill k len s) = i_flags s.
Proof. apply lens_fill_fm. Qed.
Lemma lens_fill_m k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. apply lens_fill_fm. Qed.

Lemma lenlens_zero_fm k s : i_flags (lenlens_zero k s) = i_flags s /\ i_mode (lenlens_zero k s) = i_mode s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [rewrite (proj1 (IHk _)), (proj2 (IHk _))|]; auto.
Qed.
Lemma lenlens_zero_f k s : i_flags (lenlens_zero k s) = i_flags s.
Proof. apply lenlens_zero_fm. Qed.
Lemma lenlens_zero_m k s : i_mode (lenlens_zero k s) = i_mode s.
Proof. apply lenlens_zero_fm. Qed.

Local Opaque needbits needbits_f.

Lemma lenlens_loop_fm k m : m_h (lenlens_loop k m) = m_h m /\ i_flags (m_s (lenlens_loop k m)) = i_flags (m_s m) /\
  i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [auto|].
  destruct (_ <? _); [|auto].
  destruct (m_leave (needbits 3 m) =? 1); [rewrite needbits_h, needbits_s; auto|].
  match goal with |- context [lenlens_loop k ?x] => destruct (IHk x) as [-> [-> ->]] end.
  cbn. rewrite needbits_h, needbits_s; auto.
Qed.

Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

(* a helper's machine: header and flags kept, the mode kept or BAD / TYPE *)
Definition hk (m m': mst) : Prop :=
  m_h m' = m_h m /\ i_flags (m_s m') = i_flags (m_s m) /\
  (i_mode (m_s m') = i_mode (m_s m) \/ i_mode (m_s m') = IM.BAD \/ i_mode (m_s m') = IM.TYPE).

Lemma hk_refl m : hk m m.
Proof. unfold hk; auto. Qed.
Lemma hk_trans m1 m2 m3 : hk m1 m2 -> hk m2 m3 -> hk m1 m3.
Proof. unfold hk; intuition congruence. Qed.

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
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply lookup1_s in E; destruct E as [? ?]
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply lookup2_s in E; destruct E as [? ?]
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply fwalk_f_s in E; destruct E as [? ?]
  end.

Hint Rewrite needbits_s needbits_h lens_fill_f lens_fill_m lenlens_zero_f lenlens_zero_m : nh.

Ltac nrw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: m_h ?a = _ |- context [m_h ?a] => rewrite H
  | H: i_flags ?a = _ |- context [i_flags ?a] => rewrite H
  | H: i_mode ?a = _ |- context [i_mode ?a] => rewrite H
  end.
Ltac ncbn := cbn -[needbits_f needbits lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero lenlens_loop
                   codelens_iter codelens_loop call_table copy_bytes fwalk_f fast_iter fast_loop fast updatewindow
                   hdr_mode].
Ltac nnorm := repeat progress (ncbn; autorewrite with nh; nrw).
Ltac nclose :=
  nnorm; repeat split;
  try (left; reflexivity); try (right; left; reflexivity); try (right; right; reflexivity); auto.

Lemma codelens_iter_hk fx dx m : hk m (clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. hsplit; huse; cbn [clm]; unfold hk; nclose. Qed.

Lemma codelens_loop_hk fx dx k m : hk m (clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply hk_refl|].
  destruct (_ <? _); [|apply hk_refl].
  pose proof (codelens_iter_hk fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn [clm] in A |- *; auto.
  exact (hk_trans _ _ _ A (IHk m0)).
Qed.

Lemma fast_iter_hk fx dx m : hk m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. hsplit; huse; cbn [snd]; unfold hk; nclose. Qed.

Lemma fast_loop_hk fx dx k m : hk m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply hk_refl|].
  pose proof (fast_iter_hk fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn [snd] in A.
  match goal with |- hk _ (if ?c then _ else _) => destruct c end; [exact (hk_trans _ _ _ A (IHk m1))|exact A].
Qed.

Lemma fast_hk fx dx m : hk m (fast fx dx m).
Proof.
  unfold fast. pose proof (fast_loop_hk fx dx (Z.to_nat (m_aout m) + 1) m) as A.
  revert A; generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  unfold hk in *; cbn; exact A.
Qed.

Lemma updatewindow_fm s d : i_flags (updatewindow s d) = i_flags s /\ i_mode (updatewindow s d) = i_mode s.
Proof. unfold updatewindow. hsplit; cbn; auto. Qed.

Lemma lenlens_loop_h k m : m_h (lenlens_loop k m) = m_h m.
Proof. apply lenlens_loop_fm. Qed.
Lemma lenlens_loop_f k m : i_flags (m_s (lenlens_loop k m)) = i_flags (m_s m).
Proof. apply lenlens_loop_fm. Qed.
Lemma lenlens_loop_m k m : i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof. apply lenlens_loop_fm. Qed.
Hint Rewrite lenlens_loop_h lenlens_loop_f lenlens_loop_m : nh.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases after the header                                                                     *)

Create HintDb nhc.

Ltac nfall :=
  match goal with
  | |- ngood ?x (?f ?x) =>
      let H := fresh "Hx" in
      assert (H: hdr_mode (m_mode x) = false) by (unfold m_mode; nnorm; first [assumption | reflexivity]);
      auto with nhc
  end.

Ltac nleaf :=
  match goal with
  | |- ngood _ (IBrk _) => unfold ngood, kept, m_mode; nclose; try reflexivity
  | |- ngood _ (IRet _ _) => unfold ngood, kept, m_mode; nclose; try reflexivity
  | |- ngood ?m (?f ?x) => apply (ngood_trans m x); [unfold kept; nclose | nfall]
  end.

Section CasesNH.
Variables (fl: Z) (fx dx: list entry).

Lemma c_DONE_nh m : hdr_mode (m_mode m) = false -> ngood m (c_DONE m).
Proof. unfold m_mode; intros Hn; unfold c_DONE; hsplit; huse; nleaf. Qed.
Hint Resolve c_DONE_nh : nhc.

Lemma c_BAD_nh m : hdr_mode (m_mode m) = false -> ngood m (c_BAD m).
Proof. unfold m_mode; intros Hn; unfold c_BAD; hsplit; huse; nleaf. Qed.
Hint Resolve c_BAD_nh : nhc.
Lemma c_LENGTH_nh m : hdr_mode (m_mode m) = false -> ngood m (c_LENGTH m).
Proof. unfold m_mode; intros Hn; unfold c_LENGTH; hsplit; huse; nleaf. Qed.
Hint Resolve c_LENGTH_nh : nhc.
Lemma c_CHECK_nh m : hdr_mode (m_mode m) = false -> ngood m (c_CHECK m).
Proof. unfold m_mode; intros Hn; unfold c_CHECK; hsplit; huse; nleaf. Qed.
Hint Resolve c_CHECK_nh : nhc.
Lemma c_LIT_nh m : hdr_mode (m_mode m) = false -> ngood m (c_LIT m).
Proof. unfold m_mode; intros Hn; unfold c_LIT; hsplit; huse; nleaf. Qed.
Hint Resolve c_LIT_nh : nhc.
Lemma c_MATCH_nh m : hdr_mode (m_mode m) = false -> ngood m (c_MATCH m).
Proof. unfold m_mode; intros Hn; unfold c_MATCH; hsplit; huse; nleaf. Qed.
Hint Resolve c_MATCH_nh : nhc.
Lemma c_DISTEXT_nh m : hdr_mode (m_mode m) = false -> ngood m (c_DISTEXT m).
Proof. unfold m_mode; intros Hn; unfold c_DISTEXT; hsplit; huse; nleaf. Qed.
Hint Resolve c_DISTEXT_nh : nhc.
Lemma c_DIST_nh m : hdr_mode (m_mode m) = false -> ngood m (c_DIST fx dx m).
Proof. unfold m_mode; intros Hn; unfold c_DIST; hsplit; huse; nleaf. Qed.
Hint Resolve c_DIST_nh : nhc.
Lemma c_LENEXT_nh m : hdr_mode (m_mode m) = false -> ngood m (c_LENEXT fx dx m).
Proof. unfold m_mode; intros Hn; unfold c_LENEXT; hsplit; huse; nleaf. Qed.
Hint Resolve c_LENEXT_nh : nhc.
Lemma c_LEN_nh m : hdr_mode (m_mode m) = false -> ngood m (c_LEN fx dx (fast fx dx) m).
Proof.
  unfold m_mode; intros Hn; unfold c_LEN.
  pose proof (fast_hk fx dx (restore m)) as (A & B & C); revert A B C.
  generalize (fast fx dx (restore m)); intros mf A B C.
  destruct C as [C|[C|C]]; hsplit; huse; nleaf.
Qed.
Hint Resolve c_LEN_nh : nhc.
Lemma c_LEN__nh m : hdr_mode (m_mode m) = false -> ngood m (c_LEN_ fx dx (fast fx dx) m).
Proof. unfold m_mode; intros Hn; unfold c_LEN_; hsplit; huse; nleaf. Qed.
Hint Resolve c_LEN__nh : nhc.
Lemma c_CODELENS_nh m : hdr_mode (m_mode m) = false -> ngood m (c_CODELENS fl fx dx (fast fx dx) m).
Proof.
  unfold m_mode; intros Hn; unfold c_CODELENS.
  pose proof (codelens_loop_hk fx dx 320 m) as H; revert H.
  generalize (codelens_loop fx dx 320 m); intros o H.
  destruct o as [m0|m0|m0]; cbn [clm] in H; destruct H as (A & B & [C|[C|C]]); hsplit; huse; nleaf.
Qed.
Hint Resolve c_CODELENS_nh : nhc.
Lemma c_LENLENS_nh m : hdr_mode (m_mode m) = false -> ngood m (c_LENLENS fl fx dx (fast fx dx) m).
Proof.
  unfold m_mode; intros Hn; unfold c_LENLENS. cbv beta iota zeta.
  pose proof (lenlens_loop_fm 19 m) as (A & B & D); revert A B D.
  generalize (lenlens_loop 19 m); intros ml A B D.
  pose proof (lenlens_zero_fm 19 (m_s ml)) as (C & C'); revert C C'.
  generalize (lenlens_zero 19 (m_s ml)); intros sz C C'.
  hsplit; huse; nleaf.
Qed.
Hint Resolve c_LENLENS_nh : nhc.
Lemma c_TABLE_nh m : hdr_mode (m_mode m) = false -> ngood m (c_TABLE fl fx dx (fast fx dx) m).
Proof. unfold m_mode; intros Hn; unfold c_TABLE; hsplit; huse; nleaf. Qed.
Hint Resolve c_TABLE_nh : nhc.
Lemma c_COPY_nh m : hdr_mode (m_mode m) = false -> ngood m (c_COPY m).
Proof. unfold m_mode; intros Hn; unfold c_COPY; hsplit; huse; nleaf. Qed.
Hint Resolve c_COPY_nh : nhc.
Lemma c_COPY__nh m : hdr_mode (m_mode m) = false -> ngood m (c_COPY_ m).
Proof. unfold m_mode; intros Hn; unfold c_COPY_; hsplit; huse; nleaf. Qed.
Hint Resolve c_COPY__nh : nhc.
Lemma c_STORED_nh m : hdr_mode (m_mode m) = false -> ngood m (c_STORED fl m).
Proof. unfold m_mode; intros Hn; unfold c_STORED; hsplit; huse; nleaf. Qed.
Hint Resolve c_STORED_nh : nhc.
Lemma c_TYPEDO_nh m : hdr_mode (m_mode m) = false -> ngood m (c_TYPEDO fl m).
Proof. unfold m_mode; intros Hn; unfold c_TYPEDO; hsplit; huse; nleaf. Qed.
Hint Resolve c_TYPEDO_nh : nhc.
Lemma c_TYPE_nh m : hdr_mode (m_mode m) = false -> ngood m (c_TYPE fl m).
Proof. unfold m_mode; intros Hn; unfold c_TYPE; hsplit; huse; nleaf. Qed.
Hint Resolve c_TYPE_nh : nhc.
Lemma c_DICT_nh m : hdr_mode (m_mode m) = false -> ngood m (c_DICT fl m).
Proof. unfold m_mode; intros Hn; unfold c_DICT; hsplit; huse; nleaf. Qed.
Hint Resolve c_DICT_nh : nhc.
Lemma c_DICTID_nh m : hdr_mode (m_mode m) = false -> ngood m (c_DICTID fl m).
Proof. unfold m_mode; intros Hn; unfold c_DICTID; hsplit; huse; nleaf. Qed.
Hint Resolve c_DICTID_nh : nhc.

End CasesNH.

Hint Resolve c_DONE_nh c_BAD_nh c_LENGTH_nh c_CHECK_nh c_LIT_nh c_MATCH_nh c_DISTEXT_nh c_DIST_nh c_LENEXT_nh
  c_LEN_nh c_LEN__nh c_CODELENS_nh c_LENLENS_nh c_TABLE_nh c_COPY_nh c_COPY__nh c_STORED_nh c_TYPEDO_nh c_TYPE_nh
  c_DICT_nh c_DICTID_nh : nhc.

(* one pass of the switch from a mode after the header *)
Lemma stepf2_ngood fl fx dx m : hdr_mode (m_mode m) = false -> ngood m (stepf2 fl fx dx m).
Proof.
  intros Hn. unfold stepf2, step2.
  destruct (m_mode m =? IM.HEAD) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.FLAGS) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.TIME) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.OS) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.EXLEN) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.EXTRA) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.NAME) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.COMMENT) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.HCRC) eqn:E; [exfalso; apply Z.eqb_eq in E; rewrite E in Hn; vm_compute in Hn; discriminate|clear E].
  destruct (m_mode m =? IM.DICTID); [auto with nhc|].
  destruct (m_mode m =? IM.DICT); [auto with nhc|].
  destruct (m_mode m =? IM.TYPE); [auto with nhc|].
  destruct (m_mode m =? IM.TYPEDO); [auto with nhc|].
  destruct (m_mode m =? IM.STORED); [auto with nhc|].
  destruct (m_mode m =? IM.COPY_); [auto with nhc|].
  destruct (m_mode m =? IM.COPY); [auto with nhc|].
  destruct (m_mode m =? IM.TABLE); [auto with nhc|].
  destruct (m_mode m =? IM.LENLENS); [auto with nhc|].
  destruct (m_mode m =? IM.CODELENS); [auto with nhc|].
  destruct (m_mode m =? IM.LEN_); [auto with nhc|].
  destruct (m_mode m =? IM.LEN); [auto with nhc|].
  destruct (m_mode m =? IM.LENEXT); [auto with nhc|].
  destruct (m_mode m =? IM.DIST); [auto with nhc|].
  destruct (m_mode m =? IM.DISTEXT); [auto with nhc|].
  destruct (m_mode m =? IM.MATCH); [auto with nhc|].
  destruct (m_mode m =? IM.LIT); [auto with nhc|].
  destruct (m_mode m =? IM.CHECK); [auto with nhc|].
  destruct (m_mode m =? IM.LENGTH); [auto with nhc|].
  destruct (m_mode m =? IM.DONE); [auto with nhc|].
  destruct (m_mode m =? IM.BAD); [auto with nhc|].
  destruct (m_mode m =? IM.MEM); unfold ngood, kept; auto.
Qed.

Lemma updatewindow_f s d : i_flags (updatewindow s d) = i_flags s.
Proof. apply updatewindow_fm. Qed.
Lemma updatewindow_m s d : i_mode (updatewindow s d) = i_mode s.
Proof. apply updatewindow_fm. Qed.
Hint Rewrite updatewindow_f updatewindow_m : nh.

(* the exit: MEM, or the mode and the flags kept *)
Lemma leave_ngood flush m res : inf_leave flush m res -> hdr_mode (m_mode m) = false ->
  hdr_mode (m_mode (r_m res)) = false /\ i_flags (m_s (r_m res)) = i_flags (m_s m).
Proof.
  intros L Hn; destruct L as [_ _|]; unfold m_mode in *.
  - split; reflexivity.
  - unfold leave_fin; hsplit; cbn [r_m]; nnorm; auto.
Qed.

End NH.

Lemma rth8_pure : stepf2_nh_stmt /\ leave_nh_stmt.
Proof.
  split.
  - intros flush m _ _ Hn.
    pose proof (NH.stepf2_ngood flush lenfix_list distfix_list m Hn) as G.
    destruct (stepf2 flush lenfix_list distfix_list m); cbn in G; unfold NH.kept in G; tauto.
  - intros flush m res _ _ _ L Hn. exact (NH.leave_ngood flush m res L Hn).
Qed.

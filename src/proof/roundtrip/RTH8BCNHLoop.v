(* inflate()'s main loop from a machine past the header (RTH8BCKit.nhloop8_stmt): the headless loop
   (RTH8Defs.loop_part8_stmt) on the machine with the small header RTH8W.mcanon, the header head_rep8a of the
   real machine in the frame, the run transferred back to the real machine by RTH8W.sim_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8BCKit.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5StepInv.
Require Import Zlib.proof.inflate_api.Body5StepHdr.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.inflate_api.LibProof5.
Require Import Zlib.proof.inflate.InvQ5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the header frame head_rep8a reads only the flags and the header model *)
Lemma hd8a_same: forall F m c, i_flags (m_s c) = i_flags (m_s m) -> m_h c = m_h m -> hd8a F c = hd8a F m.
Proof. intros F m c E1 E2. unfold hd8a, head_rep8a, fextra. rewrite E1, E2. reflexivity. Qed.

(* a machine with the small header of h is the small machine of its copy with the header h *)
Lemma mcanon_set_back: forall c h, m_h c = hcanon h -> mcanon (set_m_h c h) = c.
Proof. intros [] h E; simpl in E; subst; reflexivity. Qed.

(* the loop's pure invariants do not read the header model *)
Lemma pinv8_set_h: forall m0 c h, pinv8 m0 (set_m_h c h) <-> pinv8 m0 c.
Proof. intros m0 [] h. reflexivity. Qed.

Lemma qinv8_set_h: forall m0 c h, qinv8 m0 (set_m_h c h) <-> qinv8 m0 c.
Proof. intros m0 [] h. reflexivity. Qed.

(* the facts of a machine of the headless run on the small machine: past the header, the small header of the
   real header h, the real machine's flags, a header attached *)
Definition nh_inv (h: hstate) (fl: Z) (c: mst) : Prop :=
  hdr_mode (m_mode c) = false /\ m_h c = hcanon h /\ i_flags (m_s c) = fl /\ i_head (m_s c) = true.

(* a machine c of the headless run, back on the real machine m's header: everything nhloop8_stmt's
   postconditions need of it *)
Lemma back_facts: forall F m c, mwf3_8 m -> hd_ok F m -> i_head (m_s m) = true ->
  mwf3 c -> nh_inv (m_h m) (i_flags (m_s m)) c ->
  mwf3_8 (set_m_h c (m_h m)) /\ hd_ok F (set_m_h c (m_h m)) /\
  hdr_mode (m_mode (set_m_h c (m_h m))) = false /\ i_head (m_s (set_m_h c (m_h m))) = true /\
  hd8a F (set_m_h c (m_h m)) = hd8a F m /\ mcanon (set_m_h c (m_h m)) = c.
Proof.
  intros F m c [_ W8] D I W (M & H & Fl & Ic).
  assert (B: mcanon (set_m_h c (m_h m)) = c) by (apply mcanon_set_back; exact H).
  split; [ | split; [ | split; [ | split; [ | split]]]].
  - split; [rewrite B; exact W | exact W8].
  - apply (hd_ok_set_h F m); [exact D | destruct c; simpl in *; congruence | destruct c; reflexivity].
  - destruct c; exact M.
  - destruct c; exact Ic.
  - apply hd8a_same; destruct c; simpl in *; [exact Fl | reflexivity].
  - exact B.
Qed.

Lemma nhloop8 : cases_nh -> loop_part8_stmt -> stepf2_nh_stmt -> sim_stmt -> nhloop8_stmt.
Proof.
  intros HC HLP HNH HSIM Espec F X m0 m R HF HRet Reach W8 L D HM HI Pm.
  pose proof W8 as [Wc W8h].
  set (mc := mcanon m).
  set (P := fun c => nh_inv (m_h m) (i_flags (m_s m)) c /\ pinv8 m0 c).
  set (Q := fun c => nh_inv (m_h m) (i_flags (m_s m)) c /\ qinv8 m0 c).
  assert (HPmc: P mc).
  { split; [ | apply (proj2 (pinv8_set_h m0 m _)); exact Pm].
    unfold mc; destruct m; repeat split; assumption. }
  assert (Hind: forall c, P c -> hind c) by (intros c (A & _); right; apply A).
  assert (Back: forall o, loop2 (f_flush F) lenfix_list distfix_list mc o ->
     loop2 (f_flush F) lenfix_list distfix_list m0 (out_h o (m_h m))).
  { intros o Ho. apply Reach.
    destruct (proj1 (proj2 HSIM) (f_flush F) mc (m_h m) o (Hind mc HPmc) Ho) as [Ho' _].
    unfold mc in Ho'. rewrite mcanon_back in Ho'. exact Ho'. }
  assert (HPk: p_kept F P Q).
  { intros c W Lc Dc (N & PI).
    destruct N as (M & H & Fl & Ic). destruct PI as (OI & Wi & WI & Inp).
    pose proof (HNH (f_flush F) c W Lc M) as S1.
    pose proof (stepf2_hdr (f_flush F) c W Lc) as S2.
    pose proof (stepf_inv5 (f_flush F) c W Lc OI WI) as S3.
    destruct (stepf2 (f_flush F) lenfix_list distfix_list c) as [c' | r c'].
    - destruct S1 as (M' & H' & Fl'). destruct S2 as ((Ih & _) & Inp').
      destruct S3 as (OI' & Wi' & WI').
      unfold P, nh_inv, pinv8.
      refine (conj (conj M' (conj _ (conj _ _))) (conj OI' (conj _ (conj WI' _)))); congruence.
    - destruct S1 as (M' & H' & Fl'). destruct S2 as ((Ih & _) & Inp').
      destruct S3 as (Wi' & WI').
      unfold Q, nh_inv, qinv8.
      refine (conj (conj M' (conj _ (conj _ _))) (conj _ (conj WI' _))); congruence. }
  assert (RO: ret_ok5_hl F (X * hd8a F m) mc Q R).
  { intros r c Hl W Dc (N & QI).
    destruct (back_facts F m c W8 D HI W N) as (W' & D' & M' & I' & E8 & B).
    pose proof (HRet r (set_m_h c (m_h m)) (Back _ Hl) W' D' M' I' (proj2 (qinv8_set_h _ _ _) QI)) as E.
    rewrite E8, mem_rep_hl_set_h in E.
    rewrite <- hdr_tok_mcanon, B in E. exact E. }
  assert (Wmc: mwf3 mc) by exact Wc.
  assert (Lmc: m_leave mc = 0) by exact L.
  pose proof (HLP Espec F (X * hd8a F m) mc P Q R HC stepf2_mwf3_proof stepf2_hd_proof stepf2_hdr HF
                (fun c Pc => proj1 (proj1 Pc)) HPk Wmc Lmc (hd_ok_mcanon F m) HPmc RO) as LP.
  replace (lstateH F (X * hd8a F m) m) with (lstate_hl F (X * hd8a F m) mc)
    by (unfold mc; rewrite lstate_hl_H, lstateH_mcanon; reflexivity).
  destruct R as [Rn Rb Rc Rr]. eapply semax_post; [ | | | | exact LP]; simpl.
  - intros rho. apply andp_left2. unfold loop_exit_hl, loop_exit8. simpl. apply exp_left. intros c.
    apply (exp_right (set_m_h c (m_h m))). simpl. apply derives_extract_prop. intros (Hl & W & Dc & Lc & N & PI).
    destruct (back_facts F m c W8 D HI W N) as (W' & D' & M' & I' & E8 & B).
    rewrite E8.
    replace (lstateH F (X * hd8a F m) (set_m_h c (m_h m))) with (lstate_hl F (X * hd8a F m) c)
      by (rewrite <- (lstateH_mcanon F (X * hd8a F m) (set_m_h c (m_h m))), B; reflexivity).
    apply andp_right; [apply prop_right | apply derives_refl].
    refine (conj (Back _ Hl) (conj W' (conj D' (conj _ (conj M' (conj I' _)))))).
    + destruct c; exact Lc.
    + apply (proj2 (pinv8_set_h _ _ _)); exact PI.
  - intros rho. apply andp_left2. apply derives_refl.
  - intros rho. apply andp_left2. apply derives_refl.
  - intros vl rho. apply andp_left2. apply derives_refl.
Qed.

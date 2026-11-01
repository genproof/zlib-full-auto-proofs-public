(* Law inflate_reset, theory: one inflate() call on two related streams.  The pass lemma from the parts (every
   mode is in one group), the loop (Model2.loop2) on both machines in lockstep, the exit (leave_fin) on
   related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Require Import Zlib.proof.harness.inflate_reset.IRPassNs.
Require Import Zlib.proof.harness.inflate_reset.IRPassOut.
Import ListNotations.
Local Open Scope Z_scope.

Ltac irl_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH] in *; lia.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Definition irl_hdr_b (md: Z) : bool :=
  (md =? FLAGS) || (md =? TIME) || (md =? OS) || (md =? EXLEN) || (md =? EXTRA) || (md =? NAME) ||
  (md =? COMMENT) || (md =? HCRC).
Definition irl_dict_b (md: Z) : bool :=
  (md =? DICTID) || (md =? DICT) || (md =? Zlib.proof.inflate.Model.TYPE) || (md =? TYPEDO).
Definition irl_block_b (md: Z) : bool :=
  (md =? STORED) || (md =? COPY_) || (md =? COPY) || (md =? CHECK) || (md =? LENGTH) || (md =? DONE) ||
  (md =? BAD) || (md =? MEM) || (md =? SYNC).
Definition irl_dec_b (md: Z) : bool :=
  (md =? LEN_) || (md =? LEN) || (md =? LENEXT) || (md =? DIST) || (md =? DISTEXT) || (md =? MATCH) ||
  (md =? LIT).
Definition irl_tab_b (md: Z) : bool := (md =? TABLE) || (md =? LENLENS) || (md =? CODELENS).
Definition irl_all_b (md: Z) : bool :=
  (md =? HEAD) || irl_hdr_b md || irl_dict_b md || irl_block_b md || irl_dec_b md || irl_tab_b md.

Lemma irl_all_true (n: nat) : (n < 32)%nat -> irl_all_b (16180 + Z.of_nat n) = true.
Proof.
  intros H. do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Ltac irl_b H := unfold irl_hdr_b, irl_dict_b, irl_block_b, irl_dec_b, irl_tab_b in H;
  repeat rewrite orb_true_iff in H; rewrite ?Z.eqb_eq in H.

Lemma irl_mode_groups (md: Z) : HEAD <= md <= SYNC ->
  md_head md \/ md_hdr md \/ md_dict md \/ md_block md \/ decode_mode md \/ md_tab md.
Proof.
  intros H.
  assert (E: exists n, (n < 32)%nat /\ md = 16180 + Z.of_nat n).
  { exists (Z.to_nat (md - 16180)). unfold HEAD, SYNC in H. lia. }
  destruct E as [n [Hn E]].
  pose proof (irl_all_true n Hn) as A. rewrite <- E in A. clear E Hn H.
  unfold irl_all_b in A. rewrite !orb_true_iff in A.
  unfold md_head, md_hdr, md_dict, md_block, decode_mode, md_tab.
  destruct A as [[[[[A|A]|A]|A]|A]|A].
  - left. apply Z.eqb_eq; exact A.
  - right; left. irl_b A. tauto.
  - right; right; left. irl_b A. tauto.
  - right; right; right; left. irl_b A. tauto.
  - right; right; right; right; left. irl_b A. tauto.
  - right; right; right; right; right. irl_b A. tauto.
Qed.

Lemma irl_step : stepf2_mwf3_stmt -> Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt ->
  head_sim_stmt -> hdr_sim_stmt -> dict_sim_stmt -> block_sim_stmt -> fast_sim_stmt -> dec_sim_stmt ->
  tab_sim_stmt -> sgroup_ok (fun _ => True).
Proof.
  intros SM CV TD HE HD DI BL FA DE TA.
  assert (DE': sgroup_ok decode_mode) by exact (DE FA).
  assert (TA': sgroup_ok md_tab) by exact (TA SM CV TD DE').
  intros W0 wrap src pos inp aout flush ma mb C K Wa Wb L _.
  pose proof (sw_mode _ (mw_s _ (mwf3_mwf _ Wb))) as R.
  destruct (irl_mode_groups (m_mode mb) R) as [G|[G|[G|[G|[G|G]]]]].
  - apply HE; auto.
  - apply HD; auto.
  - apply DI; auto.
  - apply BL; auto.
  - apply DE'; auto.
  - apply TA'; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop on both machines                                                                     *)

Definition irl_post (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (oa ob: iout) : Prop :=
  match oa, ob with
  | IBrk ma', IBrk mb' =>
      Kr W0 wrap src pos inp aout ma' mb' /\ mwf3 ma' /\ mwf3 mb' /\ m_leave mb' = 1 /\ irp_out mb' /\
      m_mode mb' <> SYNC
  | IRet ra ma', IRet rb mb' =>
      ra = rb /\ Kr W0 wrap src pos inp aout ma' mb' /\ mwf3 ma' /\ mwf3 mb' /\
      (ra = Z_MEM_ERROR \/
       (ra = Z_NEED_DICT /\ m_mode mb' = DICT /\ m_sow ma' = Zlength (m_ow ma') /\
        m_sow mb' = Zlength (m_ow mb')))
  | _, _ => False
  end.

Lemma irl_mode_eq (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (ma mb: mst) :
  Kr W0 wrap src pos inp aout ma mb -> m_mode ma = m_mode mb.
Proof. intros K. exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))). Qed.

Lemma irl_leave_eq (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (ma mb: mst) :
  Kr W0 wrap src pos inp aout ma mb -> m_leave ma = m_leave mb.
Proof. intros K. exact (mr_leave _ _ (kr_rel _ _ _ _ _ _ _ _ K)). Qed.

Lemma irl_loop : stepf2_mwf3_stmt -> sgroup_ok (fun _ => True) ->
  forall W0 wrap src pos inp aout flush ma oa,
  ir_ctx src pos inp -> loop2 flush lenfix_list distfix_list ma oa ->
  forall mb ob, loop2 flush lenfix_list distfix_list mb ob ->
  Kr W0 wrap src pos inp aout ma mb -> mwf3 ma -> mwf3 mb -> m_leave mb = 0 -> irp_out mb ->
  m_mode mb <> SYNC ->
  irl_post W0 wrap src pos inp aout oa ob.
Proof.
  intros SM ST W0 wrap src pos inp aout flush ma oa C LA.
  induction LA as [ma r ma' E | ma ma' E L1 | ma ma' oa E L1 LA IH];
    intros mb ob LB K Wa Wb L0 Ob NS;
    pose proof (irl_leave_eq _ _ _ _ _ _ _ _ K) as LE;
    pose proof (ST W0 wrap src pos inp aout flush ma mb C K Wa Wb L0 I) as P;
    pose proof (SM flush ma Wa ltac:(congruence)) as Wa';
    pose proof (SM flush mb Wb L0) as Wb';
    pose proof (irps_out flush mb Wb L0 Ob) as Ob';
    pose proof (irps_nosync flush mb (sw_mode _ (mw_s _ (mwf3_mwf _ Wb))) NS) as Gb;
    pose proof (irps_nosync flush ma (sw_mode _ (mw_s _ (mwf3_mwf _ Wa)))
                  ltac:(rewrite (irl_mode_eq _ _ _ _ _ _ _ _ K); exact NS)) as Ga;
    rewrite E in P, Wa', Ga;
    destruct (stepf2 flush lenfix_list distfix_list mb) as [mb'|rb mb'] eqn:Eb; cbn in P; try contradiction.
  - (* return *)
    destruct P as [-> K'].
    inversion LB; subst; try congruence.
    match goal with H: stepf2 _ _ _ mb = IRet _ _ |- _ => rewrite Eb in H; inversion H; subst end.
    cbn. split; [reflexivity|]. split; [exact K'|]. split; [exact Wa'|]. split; [exact Wb'|].
    cbn in Ga, Gb. destruct Gb as [Gb|(Gb1 & Gb2 & Gb3)]; [left; exact Gb|].
    destruct Ga as [Ga|(Ga1 & Ga2 & Ga3)]; [left; exact Ga|].
    right. auto.
  - (* leave *)
    assert (L1': m_leave mb' = 1) by (rewrite <- (irl_leave_eq _ _ _ _ _ _ _ _ P); exact L1).
    inversion LB; subst; try congruence;
      match goal with H: stepf2 _ _ _ mb = _ |- _ => rewrite Eb in H; inversion H; subst end.
    cbn in Gb |- *. auto 10.
  - (* next *)
    assert (L1': m_leave mb' <> 1) by (rewrite <- (irl_leave_eq _ _ _ _ _ _ _ _ P); exact L1).
    assert (L0': m_leave mb' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ Wb')); lia).
    inversion LB; subst; try congruence;
      match goal with H: stepf2 _ _ _ mb = _ |- _ => rewrite Eb in H; inversion H; subst end.
    eapply IH; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* leave_fin in explicit form                                                                     *)

Definition irl_out (m: mst) : Z := u32 (m_out m - m_left m).
Definition irl_inn (m: mst) : Z := u32 (m_in m - m_have m).
Definition irl_data (m: mst) : list Z := sublist (Zlength (m_ow m) - irl_out m) (Zlength (m_ow m)) (m_ow m).
Definition irl_s1 (m: mst) : istate := set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m).
Definition irl_s2 (upd: bool) (m: mst) : istate :=
  if upd then set_i_win (updatewindow (irl_s1 m) (irl_data m)) true else irl_s1 m.
Definition irl_s3 (upd: bool) (m: mst) : istate :=
  set_i_total (irl_s2 upd m) (u64 (i_total (irl_s2 upd m) + irl_out m)).
Definition irl_ck (m: mst) : bool := andb (negb (Z.land (i_wrap (m_s m)) 4 =? 0)) (negb (irl_out m =? 0)).
Definition irl_c (m: mst) : Z := update_check (i_flags (m_s m)) (i_check (m_s m)) (irl_data m).
Definition irl_s4 (upd: bool) (m: mst) : istate :=
  if irl_ck m then set_i_check (irl_s3 upd m) (irl_c m) else irl_s3 upd m.
Definition irl_ret (flush: Z) (m: mst) : Z :=
  if andb (orb (andb (irl_inn m =? 0) (irl_out m =? 0)) (flush =? Z_FINISH)) (m_ret m =? Z_OK)
  then Z_BUF_ERROR else m_ret m.
Definition irl_m (upd: bool) (m: mst) : mst :=
  MS (irl_s4 upd m) (m_h m) (m_inp m) (m_aout m) (m_nx m) (m_ow m) (m_hold m) (m_bits m) (m_in m) (m_out m)
     (m_ret m) (m_leave m) (if irl_ck m then irl_c m else m_adler m) (m_msg m) (u64 (m_tin m + irl_inn m))
     (u64 (m_tout m + irl_out m)) (m_nx m) (Zlength (m_ow m)).
Definition irl_dt (m: mst) : Z :=
  m_bits m + (if i_last (m_s m) =? 0 then 0 else 64) +
  (if i_mode (m_s m) =? Zlib.proof.inflate.Model.TYPE then 128 else 0) +
  (if orb (i_mode (m_s m) =? LEN_) (i_mode (m_s m) =? COPY_) then 256 else 0).

Lemma irl_uw_keep (s: istate) (d: list Z) :
  i_wrap (updatewindow s d) = i_wrap s /\ i_flags (updatewindow s d) = i_flags s /\
  i_check (updatewindow s d) = i_check s /\ i_last (updatewindow s d) = i_last s /\
  i_mode (updatewindow s d) = i_mode s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
Qed.

Lemma irl_s2_keep (upd: bool) (m: mst) :
  i_wrap (irl_s2 upd m) = i_wrap (m_s m) /\ i_flags (irl_s2 upd m) = i_flags (m_s m) /\
  i_check (irl_s2 upd m) = i_check (m_s m) /\ i_last (irl_s2 upd m) = i_last (m_s m) /\
  i_mode (irl_s2 upd m) = i_mode (m_s m).
Proof.
  unfold irl_s2. destruct upd; cbn [set_i_win i_wrap i_flags i_check i_last i_mode].
  - destruct (irl_uw_keep (irl_s1 m) (irl_data m)) as (A & B & C & D & E). rewrite A, B, C, D, E. cbn. auto.
  - cbn. auto.
Qed.

Lemma irl_lf (flush: Z) (m: mst) :
  let res := leave_fin flush m in
  r_ret res = irl_ret flush m /\ r_dtype res = Some (irl_dt m) /\
  m_inp (r_m res) = m_inp m /\ m_aout (r_m res) = m_aout m /\ m_ow (r_m res) = m_ow m /\
  m_msg (r_m res) = m_msg m /\ m_snx (r_m res) = m_nx m /\ m_sow (r_m res) = Zlength (m_ow m) /\
  m_tin (r_m res) = u64 (m_tin m + irl_inn m) /\ m_tout (r_m res) = u64 (m_tout m + irl_out m) /\
  m_adler (r_m res) = (if irl_ck m then irl_c m else m_adler m) /\
  m_s (r_m res) = irl_s4 (leave_ok flush m) m.
Proof.
  cbv zeta. unfold leave_fin.
  set (upd := leave_ok flush m).
  set (m1 := restore m).
  set (m2 := if upd then _ else m1).
  assert (E2: m_s m2 = irl_s2 upd m /\ m_snx m2 = m_nx m /\ m_sow m2 = Zlength (m_ow m) /\
              m_inp m2 = m_inp m /\ m_aout m2 = m_aout m /\ m_msg m2 = m_msg m /\ m_ow m2 = m_ow m /\
              m_in m2 = m_in m /\ m_nx m2 = m_nx m /\ m_out m2 = m_out m /\ m_ret m2 = m_ret m /\
              m_tin m2 = m_tin m /\ m_tout m2 = m_tout m /\ m_adler m2 = m_adler m /\ m_bits m2 = m_bits m).
  { unfold m2, m1, irl_s2. destruct upd; cbn; repeat split. }
  clearbody m2.
  destruct E2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15).
  assert (IN: u32 (m_in m2 - m_have m2) = irl_inn m) by (unfold irl_inn, m_have; rewrite A8, A4, A9; reflexivity).
  assert (OUT: u32 (m_out m2 - m_left m2) = irl_out m) by (unfold irl_out, m_left; rewrite A10, A5, A7; reflexivity).
  destruct (irl_s2_keep upd m) as (K1 & K2 & K3 & K4 & K5).
  cbv zeta. cbn [upd_s set_m_s set_m_tin set_m_tout set_m_adler m_s m_inp m_aout m_ow m_msg m_snx m_sow m_tin m_tout
                 m_adler m_in m_nx m_out m_ret m_bits m_h m_hold m_leave set_i_total set_i_check
                 i_wrap i_flags i_check i_last i_mode m_left m_have r_ret r_m r_dtype].
  rewrite ?IN, ?OUT, ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?A13, ?A14, ?A15.
  rewrite ?K1, ?K2, ?K3.
  unfold irl_ck, irl_c, irl_s4, irl_s3, irl_data, irl_ret, irl_dt.
  rewrite ?K1, ?K2, ?K3.
  destruct (andb (negb (Z.land (i_wrap (m_s m)) 4 =? 0)) (negb (irl_out m =? 0))) eqn:CK; cbn;
    rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?A13, ?A14, ?A15;
    rewrite ?K1, ?K2, ?K3, ?K4, ?K5; unfold irl_ck, irl_c; rewrite ?CK; repeat split.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* srel through the exit                                                                          *)

Lemma irl_treach (kind: Z) (sa sb sa' sb': istate) (t: tref) (rb: Z) :
  i_codes sa' = i_codes sa -> i_codes sb' = i_codes sb -> treach_eq kind sa sb t rb -> treach_eq kind sa' sb' t rb.
Proof.
  intros A B T. unfold treach_eq, tab_entry in *. rewrite A, B. exact T.
Qed.

Ltac irl_srel_tr H :=
  destruct H; constructor;
  unfold lenlive in *;
  cbn [set_i_bits set_i_hold set_i_total set_i_check set_i_win set_i_wsize set_i_whave set_i_wnext set_i_wdata
       set_i_mode set_i_wbits set_i_wrap set_i_last set_i_havedict set_i_flags set_i_dmax set_i_head set_i_lencode
       set_i_distcode set_i_next set_i_sane set_i_back] in *;
  try reflexivity; try (left; reflexivity); try assumption; try congruence;
  try (match goal with
       | T: _ -> treach_eq _ _ _ _ _ /\ treach_eq _ _ _ _ _ |- _ =>
           intros X; destruct (T X); split; (eapply irl_treach; [| |eassumption]; reflexivity)
       | T: _ -> treach_eq _ _ _ _ _ |- _ =>
           intros X; (eapply irl_treach; [| |apply T; exact X]; reflexivity)
       end).

Lemma irl_srel_weak (P Q: Prop) (sa sb: istate) : (P -> Q) -> srel P sa sb -> srel Q sa sb.
Proof. intros PQ H. irl_srel_tr H. tauto. Qed.

Lemma irl_srel_refl (P: Prop) (s: istate) : srel P s s.
Proof.
  constructor; unfold treach_eq; auto; intros; repeat split; auto.
Qed.

Lemma irl_srel_hb (P: Prop) (sa sb: istate) (h b: Z) :
  srel P sa sb -> srel P (set_i_bits (set_i_hold sa h) b) (set_i_bits (set_i_hold sb h) b).
Proof. intros H. irl_srel_tr H. Qed.

Lemma irl_srel_total (P: Prop) (sa sb: istate) (t: Z) :
  srel P sa sb -> srel P (set_i_total sa t) (set_i_total sb t).
Proof. intros H. irl_srel_tr H. Qed.

Lemma irl_srel_check (P: Prop) (sa sb: istate) (c: Z) :
  srel P sa sb -> srel P (set_i_check sa c) (set_i_check sb c).
Proof. intros H. irl_srel_tr H. Qed.

Lemma irl_srel_win (P: Prop) (sa sb: istate) (ws wn wh: Z) (wd: list Z) :
  srel P sa sb ->
  srel P (set_i_win (set_i_wdata (set_i_whave (set_i_wnext (set_i_wsize sa ws) wn) wh) wd) true)
         (set_i_win (set_i_wdata (set_i_whave (set_i_wnext (set_i_wsize sb ws) wn) wh) wd) true).
Proof. intros H. irl_srel_tr H. Qed.

Lemma irl_uw_shape (s: istate) (d: list Z) :
  updatewindow s d =
  set_i_wdata (set_i_whave (set_i_wnext (set_i_wsize s (i_wsize (updatewindow s d))) (i_wnext (updatewindow s d)))
                           (i_whave (updatewindow s d))) (i_wdata (updatewindow s d)).
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0);
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; destruct s; reflexivity.
Qed.

Lemma irl_uw_cong (sa sb: istate) (d: list Z) :
  i_wsize sa = i_wsize sb -> (i_wsize sb = 0 -> i_wbits sa = i_wbits sb) ->
  i_whave sa = i_whave sb -> i_wnext sa = i_wnext sb -> i_wdata sa = i_wdata sb ->
  i_wsize (updatewindow sa d) = i_wsize (updatewindow sb d) /\
  i_wnext (updatewindow sa d) = i_wnext (updatewindow sb d) /\
  i_whave (updatewindow sa d) = i_whave (updatewindow sb d) /\
  i_wdata (updatewindow sa d) = i_wdata (updatewindow sb d).
Proof.
  intros A B C D E. unfold updatewindow. cbv zeta. rewrite A.
  destruct (i_wsize sb =? 0) eqn:EZ.
  - apply Z.eqb_eq in EZ. rewrite (B EZ). cbn [set_i_whave set_i_wnext set_i_wsize i_wsize i_wnext i_whave i_wdata].
    rewrite E. repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
  - rewrite A, C, D, E. repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split;
      exact A.
Qed.

Lemma irl_out0 (m: mst) : irp_out m -> m_ow m = [] -> irl_out m = 0.
Proof.
  intros (O1 & O2 & _) E. unfold irl_out, m_left in *. rewrite E, Zlength_nil in *.
  replace (m_out m - (m_aout m - 0)) with 0 by lia. reflexivity.
Qed.

Lemma irl_s2_rel (P: Prop) (upd: bool) (ma mb: mst) :
  srel P (m_s ma) (m_s mb) -> m_hold ma = m_hold mb -> m_bits ma = m_bits mb -> irl_data ma = irl_data mb ->
  (upd = true -> i_wsize (m_s mb) = 0 -> i_wbits (m_s ma) = i_wbits (m_s mb)) ->
  srel P (irl_s2 upd ma) (irl_s2 upd mb).
Proof.
  intros S H B D W. unfold irl_s2.
  assert (S1: srel P (irl_s1 ma) (irl_s1 mb)) by (unfold irl_s1; rewrite H, B; apply irl_srel_hb; exact S).
  destruct upd; [|exact S1].
  rewrite D, (irl_uw_shape (irl_s1 ma)), (irl_uw_shape (irl_s1 mb)).
  destruct (irl_uw_cong (irl_s1 ma) (irl_s1 mb) (irl_data mb)) as (U1 & U2 & U3 & U4).
  - exact (sr_wsize _ _ _ S1).
  - intros Z. apply W; [reflexivity | exact Z].
  - exact (sr_whave _ _ _ S1).
  - exact (sr_wnext _ _ _ S1).
  - exact (sr_wdata _ _ _ S1).
  - rewrite U1, U2, U3, U4. apply irl_srel_win. exact S1.
Qed.

Lemma irl_exit (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout flush: Z) (ma mb: mst) :
  Kr W0 wrap src pos inp aout ma mb -> irp_out mb ->
  let ra := leave_fin flush ma in let rb := leave_fin flush mb in
  r_ret ra = r_ret rb /\ r_dtype ra = r_dtype rb /\
  m_inp (r_m ra) = m_inp (r_m rb) /\ m_aout (r_m ra) = m_aout (r_m rb) /\ m_ow (r_m ra) = m_ow (r_m rb) /\
  m_msg (r_m ra) = m_msg (r_m rb) /\ m_snx (r_m ra) = m_snx (r_m rb) /\ m_sow (r_m ra) = m_sow (r_m rb) /\
  m_tin (r_m ra) = m_tin (r_m rb) /\ m_tout (r_m ra) = m_tout (r_m rb) /\
  m_adler (r_m ra) = m_adler (r_m rb) /\
  srel True (m_s (r_m ra)) (m_s (r_m rb)).
Proof.
  intros K O. cbv zeta.
  destruct (kr_rel _ _ _ _ _ _ _ _ K) as [S Hinp Haout Hnx How Hhold Hbits Hin Hout Hret Hleave Hadler Hmsg
                                         Htin Htout Hsnx Hsow].
  destruct (irl_lf flush ma) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  destruct (irl_lf flush mb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  assert (EO: irl_out ma = irl_out mb) by (unfold irl_out, m_left; rewrite Hout, Haout, How; reflexivity).
  assert (EI: irl_inn ma = irl_inn mb) by (unfold irl_inn, m_have; rewrite Hin, Hinp, Hnx; reflexivity).
  assert (ED: irl_data ma = irl_data mb) by (unfold irl_data; rewrite EO, How; reflexivity).
  assert (EU: leave_ok flush ma = leave_ok flush mb).
  { unfold leave_ok, m_left, m_mode. rewrite (sr_wsize _ _ _ S), (sr_mode _ _ _ S), Hout, Haout, How. reflexivity. }
  assert (ECK: irl_ck ma = irl_ck mb) by (unfold irl_ck; rewrite (sr_wrap _ _ _ S), EO; reflexivity).
  assert (EC: irl_ck mb = true -> irl_c ma = irl_c mb).
  { unfold irl_ck, irl_c. intros CK. rewrite (sr_flags _ _ _ S), ED. f_equal.
    destruct (sr_check _ _ _ S) as [C|[C|(_ & C)]]; [exact C| |].
    - rewrite C in CK. discriminate.
    - rewrite (irl_out0 mb O C) in CK. rewrite andb_false_r in CK. discriminate. }
  rewrite A1, B1, A2, B2, A3, B3, A4, B4, A5, B5, A6, B6, A7, B7, A8, B8, A9, B9, A10, B10, A11, B11, A12, B12.
  split; [unfold irl_ret; rewrite EI, EO, Hret; reflexivity|].
  split; [unfold irl_dt; rewrite Hbits, (sr_last _ _ _ S), (sr_mode _ _ _ S); reflexivity|].
  do 2 (split; [assumption|]). split; [congruence|].
  split; [assumption|]. split; [assumption|]. split; [congruence|].
  split; [rewrite Htin, EI; reflexivity|]. split; [rewrite Htout, EO; reflexivity|].
  split; [rewrite ECK; destruct (irl_ck mb) eqn:CK; [apply EC; reflexivity | exact Hadler]|].
  (* the state *)
  rewrite EU. set (upd := leave_ok flush mb).
  assert (S2: srel (m_ow mb = []) (irl_s2 upd ma) (irl_s2 upd mb)).
  { apply irl_s2_rel; auto. intros U Z.
    destruct (sr_wbits _ _ _ S) as [Wb|[Hd|Bd]]; [exact Wb| |].
    - destruct O as (O1 & O2 & O3). specialize (O3 Hd).
      unfold upd, leave_ok in U. rewrite Z in U. cbn in U.
      unfold m_left in *. rewrite O3, Zlength_nil in *.
      replace (m_out mb) with (m_aout mb - 0) in U by lia. rewrite Z.eqb_refl in U. discriminate.
    - unfold upd, leave_ok, m_mode in U. rewrite Z, Bd in U. cbn in U.
      rewrite andb_false_r in U. discriminate. }
  assert (S3: srel (m_ow mb = []) (irl_s3 upd ma) (irl_s3 upd mb)).
  { unfold irl_s3. rewrite (sr_total _ _ _ S2), EO. apply irl_srel_total. exact S2. }
  apply (irl_srel_weak (m_ow mb = [])); [auto|].
  unfold irl_s4. rewrite ECK. destruct (irl_ck mb) eqn:CK; [|exact S3].
  rewrite (EC eq_refl). apply irl_srel_check. exact S3.
Qed.

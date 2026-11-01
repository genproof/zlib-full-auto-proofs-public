(** * deflate_api theory: deflateInit2, deflateTune, deflateSetDictionary, deflateSetHeader

    The fields af_init, af_tune, af_dict, af_head of [api_facts (Iapi W HI) Iend] (RTDLawFacts.v), for any [W],
    [HI] with [core_facts W] / [hdr_facts HI].  af_init and af_tune also say that last_flush is -2 after them,
    and af_dict is proved for fresh streams (last_flush = -2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTApiOut Zlib.proof.roundtrip.RTDLTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma init_wbw : forall wbits : Z,
  (if wbits <? 0 then if wbits <? -15 then None else Some (- wbits, 0)
   else if wbits >? 15 then Some (wbits - 16, 2) else Some (wbits, 1)) =
  (if wbits <? -15 then None else Some (wb_of wbits, wrap_of wbits)).
Proof.
  intros wbits; unfold wb_of, wrap_of.
  destruct (wbits <? 0) eqn:E0, (wbits <? -15) eqn:E1, (wbits >? 15) eqn:E2; auto; lia.
Qed.

Lemma init_check_eq : forall level method wbits mem strategy,
  (wbits <? -15) = false ->
  ((mem <? 1) || (mem >? MAX_MEM_LEVEL) || negb (method =? Z_DEFLATED) ||
   (wb_of wbits <? 8) || (wb_of wbits >? 15) ||
   ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) <? 0) ||
   ((if level =? Z_DEFAULT_COMPRESSION then 6 else level) >? 9) ||
   (strategy <? 0) || (strategy >? Z_FIXED) || ((wb_of wbits =? 8) && negb (wrap_of wbits =? 1)))
  = negb (params_ok level method wbits mem strategy).
Proof.
  intros level method wbits mem strategy H. unfold params_ok.
  rewrite H. unfold MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED, Z_DEFAULT_COMPRESSION.
  rewrite !Z.gtb_ltb, !Z.ltb_antisym.
  repeat match goal with
         | |- context [?a <=? ?b] => destruct (a <=? b); cbn [negb orb andb]
         | |- context [?a =? ?b] => destruct (a =? b); cbn [negb orb andb]
         end; reflexivity.
Qed.

Lemma init_shape : forall level method wbits mem strategy a1 a2 a3 a4 a5 z,
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z =
  if params_ok level method wbits mem strategy then
    if a1 then
      if a2 && a3 && a4 && a5 then
        c_deflateInit2_ true true false level method wbits mem strategy true true true true true z
      else Some (None, set_z_msg (set_z_msg z None) (Some Z_MEM_ERROR), Z_MEM_ERROR)
    else Some (None, set_z_msg z None, Z_MEM_ERROR)
  else Some (None, set_z_msg z None, Z_STREAM_ERROR).
Proof.
  intros level method wbits mem strategy a1 a2 a3 a4 a5 z.
  destruct (wbits <? -15) eqn:Ew.
  - assert (P : params_ok level method wbits mem strategy = false) by (unfold params_ok; rewrite Ew; reflexivity).
    rewrite P. unfold c_deflateInit2_. cbv zeta. cbn [negb orb]. rewrite init_wbw, Ew. reflexivity.
  - pose proof (init_check_eq level method wbits mem strategy Ew) as C.
    destruct (params_ok level method wbits mem strategy) eqn:P.
    + destruct a1, a2, a3, a4, a5; try reflexivity;
      unfold c_deflateInit2_; cbv zeta; cbn [negb orb]; rewrite init_wbw, Ew, C; cbn [negb andb];
      reflexivity.
    + unfold c_deflateInit2_; cbv zeta; cbn [negb orb]; rewrite init_wbw, Ew, C. reflexivity.
Qed.

Section Init.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.

(** The status of a stream satisfying [Iapi] passes deflateStateCheck. *)
Lemma Iapi_bad_state : forall dict wrap D O fin s tin tout adler,
    hdr_facts HI -> Iapi W HI dict wrap D O fin s tin tout adler -> bad_state s = false.
Proof.
  intros dict wrap D O fin s tin tout adler HF HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  assert (Hst : d_status s = INIT_STATE \/ d_status s = GZIP_STATE \/ d_status s = EXTRA_STATE \/
                d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/ d_status s = HCRC_STATE \/
                d_status s = BUSY_STATE \/ d_status s = FINISH_STATE).
  { destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
    - destruct P0 as [[[-> _] | [-> _]] _]; tauto.
    - destruct P1 as (_ & _ & _ & _ & _ & H & k & Hh & _).
      destruct (hf_status HI HF s adler H k Hh) as (_ & _ & Hs & _). tauto.
    - destruct P2 as [-> _]. tauto.
    - destruct P3 as [-> _]. tauto. }
  unfold bad_state, c_deflateStateCheck, status_ok.
  destruct Hst as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
Qed.

(** [Iapi] only sees W, the API part, the output part and the positions. *)
Lemma Iapi_frame : forall dict wrap D O fin s s' tin tout adler,
    hdr_facts HI -> Iapi W HI dict wrap D O fin s tin tout adler -> W s' -> api_eq s s' -> out_eq s s' ->
    d_pending_buf_size s' = d_pending_buf_size s -> d_sym_next s' = d_sym_next s ->
    d_lookahead s' = d_lookahead s -> d_strstart s' = d_strstart s -> d_block_start s' = d_block_start s ->
    Iapi W HI dict wrap D O fin s' tin tout adler.
Proof.
  intros dict wrap D O fin s s' tin tout adler HF HI' HW (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3)
    E1 E2 E3 E4 E5.
  assert (Hpend : pend s' = pend s) by (unfold pend, d_pending; rewrite B1, B3; reflexivity).
  assert (Hpen : d_pending s' = d_pending s) by (unfold d_pending; rewrite B1; reflexivity).
  assert (Hbv : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid; rewrite B1; reflexivity).
  assert (Hout : outok s' <-> outok s).
  { unfold outok, d_pb, d_pending. rewrite B1, B2, B3, E1. tauto. }
  destruct HI' as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & Hph).
  unfold Iapi. rewrite A1, A3, A5. split; [exact HW|]. split; [apply Hout; exact H2|].
  do 11 (split; [assumption|]).
  split; [rewrite E3, E4, E5; exact H14|].
  destruct Hph as [P0 | (Hlf & Ph)]; [left | right; split; [exact Hlf|]].
  - unfold ph0 in *. rewrite A1, A2, Hpen, Hbv, E2, E3, E4, E5. exact P0.
  - destruct Ph as [P1 | [P2 | P3]]; [left | right; left | right; right].
    + unfold ph1 in *. rewrite Hbv, E2, Hpend.
      destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5 & H & k & Hh & Q6).
      do 5 (split; [assumption|]). exists H, k. split; [|exact Q6].
      apply (hf_frame HI HF s s' adler H k Hh); auto.
    + unfold ph2 in *. rewrite A1, A2, Hbv, Hpend. exact P2.
    + unfold ph3 in *. rewrite A1, A2, Hbv, Hpend, E2, E3. exact P3.
Qed.

Lemma api_init : forall level method wbits mem strategy a1 a2 a3 a4 a5 z,
    core_facts W -> hdr_facts HI ->
    s32 level -> s32 method -> s32 wbits -> s32 mem -> s32 strategy ->
    (exists r, c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      (code = Z_OK \/ code = Z_STREAM_ERROR \/ code = Z_MEM_ERROR) /\
      (code = Z_STREAM_ERROR <-> params_ok level method wbits mem strategy = false) /\
      (code = Z_OK -> exists s, os = Some s /\ d_gzhead s = None /\ d_last_flush s = -2 /\
                       Iapi W HI [] (wrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z')).
Proof.
  intros level method wbits mem strategy a1 a2 a3 a4 a5 z CF HF _ _ _ _ _.
  rewrite init_shape.
  destruct (params_ok level method wbits mem strategy) eqn:P.
  2:{ split; [eauto|]. intros os z' code E. inversion E; subst.
      split; [auto|]. split; [tauto|]. unfold Z_STREAM_ERROR, Z_OK; intros; lia. }
  destruct (cf_init W CF level method wbits mem strategy z P)
    as (s & z' & E & HW & HO & Hst & Hwr & Hgz & Hgi & Hlf & Hpo & Hpe & Hbv & Hss & Hla & Hbs & Hsn & _ & _ & _ & _ & Hz').
  destruct a1; [|split; [eauto|]; intros os z1 code E1; inversion E1; subst;
                 split; [auto|]; split; [unfold Z_MEM_ERROR, Z_STREAM_ERROR; split; intros; [lia|discriminate]|];
                 unfold Z_MEM_ERROR, Z_OK; intros; lia].
  destruct (a2 && a3 && a4 && a5);
    [|split; [eauto|]; intros os z1 code E1; inversion E1; subst;
      split; [auto|]; split; [unfold Z_MEM_ERROR, Z_STREAM_ERROR; split; intros; [lia|discriminate]|];
      unfold Z_MEM_ERROR, Z_OK; intros; lia].
  rewrite E. split; [eauto|]. intros os z1 code E1. inversion E1; subst; clear E1.
  split; [auto|]. split; [unfold Z_OK, Z_STREAM_ERROR; split; intros; [lia|discriminate]|].
  intros _. exists s. split; [reflexivity|]. split; [exact Hgz|]. split; [exact Hlf|].
  cbn [z_total_in z_total_out z_adler].
  assert (Hw : 0 <= wrap_of wbits <= 2) by (unfold wrap_of; destruct (wbits <? 0), (wbits >? 15); lia).
  unfold Iapi. split; [exact HW|]. split; [exact HO|]. split; [exact Hw|].
  split; [auto|]. split; [constructor|]. split; [cbn; lia|]. split; [rewrite Hlf; lia|].
  split; [rewrite Hgz; discriminate|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|].
  split; [cbn; lia|].
  split; [rewrite Hst; destruct (wrap_of wbits =? 2); unfold INIT_STATE, GZIP_STATE, FINISH_STATE; discriminate|].
  split; [intros _; split; [exact Hla|lia]|].
  left. unfold ph0. split.
  { rewrite Hst. destruct (wrap_of wbits =? 2) eqn:E2; [right|left]; split; auto; lia. }
  split; [exact Hwr|]. do 2 (split; [reflexivity|]).
  do 4 (split; [assumption|]). split; [lia|]. split; [tauto|].
  intros H1. rewrite H1. reflexivity.
Qed.

Lemma api_tune : forall wrap s tin tout adler good lazy nice chain z,
    core_facts W -> hdr_facts HI ->
    Iapi W HI [] wrap [] [] None s tin tout adler -> s32 good -> s32 lazy -> s32 nice -> s32 chain ->
    exists s', c_deflateTune s z good lazy nice chain = Some (s', z, Z_OK) /\ d_gzhead s' = d_gzhead s /\
               d_last_flush s' = d_last_flush s /\
               Iapi W HI [] wrap [] [] None s' tin tout adler.
Proof.
  intros wrap s tin tout adler good lazy nice chain z CF HF HI' _ _ Hn _.
  exists (tune_set s good lazy nice chain).
  unfold c_deflateTune. rewrite (Iapi_bad_state _ _ _ _ _ _ _ _ _ HF HI').
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  eapply Iapi_frame; eauto.
  - apply (cf_tune W CF); auto. destruct HI' as [HW _]. exact HW.
  - repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.

Lemma api_dict : forall wrap s tin tout adler d ain aout msg,
    core_facts W -> hdr_facts HI ->
    Iapi W HI [] wrap [] [] None s tin tout adler ->
    bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z' code,
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_STREAM_ERROR) /\ (code = Z_STREAM_ERROR <-> wrap = 2) /\
      d_last_flush s' = d_last_flush s /\
      Iapi W HI (if wrap =? 2 then [] else d) wrap [] [] None s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros wrap s tin tout adler d ain aout msg HC HH HI0 Hd Hdl Hain Haout.
  pose proof HI0 as (HW & Hok & Hwr & Hw2 & Hbd & Hdl0 & Hlfr & Hgz & Hto & HbO & HbD & Htin & Hfin & Hdz & Hph).
  rewrite Zlength_nil in Htin.
  destruct (Hdz eq_refl) as (Hla & Hsb & Hs00). pose proof (Hs00 eq_refl) as Hss0.
  assert (Hbs0 : d_block_start s = 0) by lia.
  assert (Htin0 : tin = 0) by lia. subst tin.
  assert (Hb : bad_state s = false) by exact (Iapi_bad_state _ _ _ _ _ _ _ _ _ HH HI0).
  (* the cases: a fresh gzip stream (error), a fresh raw / zlib stream (ph0), a raw stream after deflate() calls
     without data (ph2) *)
  assert (Hcase : (d_status s = GZIP_STATE /\ wrap = 2 /\ d_wrap s = 2) \/
                  (d_status s = INIT_STATE /\ wrap <= 1 /\ d_wrap s = wrap /\ ph0 [] wrap [] [] s 0 adler) \/
                  (d_status s = BUSY_STATE /\ wrap = 0 /\ d_wrap s = 0 /\ d_last_flush s <> -2)).
  { destruct Hph as [P0 | (Hne & [P1 | [P2 | P3]])].
    - pose proof P0 as P0'. destruct P0' as ([[Hst Hw1] | [Hst Hw2']] & Hdw & _).
      + right; left. auto.
      + left. subst wrap. auto.
    - destruct P1 as (_ & _ & Hne1 & _). congruence.
    - destruct P2 as (Hst & Hdw & _ & HOne & _).
      assert (wrap = 0) by (destruct (Z.eq_dec wrap 0); [auto|exfalso; apply (HOne n); reflexivity]).
      right; right. subst wrap. auto.
    - destruct P3 as [Hst _]. specialize (Hfin Hst). discriminate. }
  destruct Hcase as [(Hst & -> & Hdw) | [(Hst & Hw1 & Hdw & P0) | (Hst & -> & Hdw & Hne)]].
  { exists s, (zcall [] 0 ain 0 aout tout adler msg), Z_STREAM_ERROR.
    unfold c_deflateSetDictionary. rewrite Hb, Hdw. simpl.
    split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    split; [tauto|]. split; [reflexivity|]. simpl. exact HI0. }
  - destruct P0 as (_ & _ & _ & _ & Hpe & Hbi & Hsn & _ & _ & Hs0 & Had).
    assert (Hss : d_strstart s = 0) by (apply Hs0; reflexivity).
    destruct (cf_dict W HC s (zcall [] 0 ain 0 aout tout adler msg) d HW ltac:(lia) Hb
                (fun _ => Hst) Hss Hla Hbs0 Hd Hdl ltac:(simpl; lia))
      as (s' & z' & k & Hc & HW' & Hae & Hoe & Hsp & Hla' & Hsb' & Hs0' & Hsn' & Hk & Hz').
    { unfold adler_pre. split; [|intros; lia]. intros Hw. rewrite Hdw in Hw. simpl. rewrite (Had Hw).
      unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence. }
    exists s', z', Z_OK.
    destruct Hae as (Hast & Haw & Hagz & Hagi & Half & Ham).
    destruct Hoe as (Hotr & Hopbm & Hopo).
    assert (Hw2f : (wrap =? 2) = false) by (apply Z.eqb_neq; lia).
    rewrite Hw2f.
    split; [exact Hc|]. split; [exact Hagz|]. split; [left; reflexivity|].
    split; [split; [discriminate | lia]|]. split; [exact Half|].
    subst z'. simpl.
    assert (Hok' : outok s').
    { unfold outok, d_pb, d_pending in *. rewrite Hotr, Hopbm, Hopo.
      destruct Hsp as (_ & _ & _ & _ & -> & _). exact Hok. }
    unfold Iapi.
    split; [exact HW'|]. split; [exact Hok'|]. split; [lia|]. split; [intros; lia|].
    split; [exact Hd|]. split; [exact Hdl|]. split; [rewrite Half; lia|].
    split; [rewrite Hagz; exact Hgz|]. split; [exact Hto|]. split; [exact HbO|]. split; [exact HbD|].
    split; [rewrite !Zlength_nil; lia|].
    split; [rewrite Hast, Hst; intros Hf; discriminate|].
    split; [intros _; split; [exact Hla'|split; [exact Hsb'|intros Hdn; apply Hs0'; exact Hdn]]|].
    left. unfold ph0. rewrite Hast, Haw, Hdw.
    assert (Hpe' : d_pending s' = 0) by (unfold d_pending in *; rewrite Hotr; exact Hpe).
    assert (Hbi' : d_bi_valid s' = 0) by (unfold d_bi_valid in *; rewrite Hotr; exact Hbi).
    split; [left; split; [exact Hst|lia]|].
    do 5 (split; [first [reflexivity | assumption]|]).
    split; [rewrite Hsn'; exact Hsn|].
    do 2 (split; [first [reflexivity | assumption]|]).
    split; [exact Hs0'|].
    intros Hw. rewrite (Had Hw), Hw. reflexivity.
  - destruct (cf_dict W HC s (zcall [] 0 ain 0 aout tout adler msg) d HW ltac:(lia) Hb
                ltac:(intros; lia) Hss0 Hla Hbs0 Hd Hdl ltac:(simpl; lia))
      as (s' & z' & k & Hc & HW' & Hae & Hoe & Hsp & Hla' & Hsb' & Hs0' & Hsn' & Hk & Hz').
    { rewrite Hdw. unfold adler_pre. split; intros; lia. }
    exists s', z', Z_OK.
    destruct Hae as (Hast & Haw & Hagz & Hagi & Half & Ham).
    destruct Hoe as (Hotr & Hopbm & Hopo).
    split; [exact Hc|]. split; [exact Hagz|]. split; [left; reflexivity|].
    split; [split; [discriminate | lia]|]. split; [exact Half|].
    subst z'. simpl. rewrite Hdw. simpl.
    assert (Hok' : outok s').
    { unfold outok, d_pb, d_pending in *. rewrite Hotr, Hopbm, Hopo.
      destruct Hsp as (_ & _ & _ & _ & -> & _). exact Hok. }
    assert (Hpend' : pend s' = pend s) by (unfold pend, d_pending; rewrite Hotr, Hopo; reflexivity).
    assert (Hbi' : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid; rewrite Hotr; reflexivity).
    unfold Iapi.
    split; [exact HW'|]. split; [exact Hok'|]. split; [lia|]. split; [intros; lia|].
    split; [exact Hd|]. split; [exact Hdl|]. split; [rewrite Half; lia|].
    split; [rewrite Hagz; exact Hgz|]. split; [exact Hto|]. split; [exact HbO|]. split; [exact HbD|].
    split; [rewrite !Zlength_nil; lia|].
    split; [rewrite Hast, Hst; intros Hf; discriminate|].
    split; [intros _; split; [exact Hla'|split; [exact Hsb'|intros Hdn; apply Hs0'; exact Hdn]]|].
    right. split; [rewrite Half; exact Hne|]. right; left. unfold ph2.
    split; [rewrite Hast; exact Hst|]. split; [rewrite Haw; exact Hdw|].
    split; [rewrite Hbi'; destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])];
            [destruct P0 as (_ & _ & _ & _ & _ & Hbi0 & _); lia
            |destruct P1 as (_ & _ & _ & Hbi0 & _); lia
            |destruct P2 as (_ & _ & Hbi0 & _); lia
            |destruct P3 as (_ & _ & _ & Hbi0 & _); lia]|].
    split; [intros Hn; contradiction|].
    split; [unfold chk_ok; split; intros; lia|].
    exists [], (pend s'). split; [|reflexivity].
    unfold hdr_good. split; [constructor|]. split; [reflexivity|]. split; intros; lia.
Qed.

Lemma api_head : forall dict wrap s tin tout adler h z,
    core_facts W -> hdr_facts HI ->
    Iapi W HI dict wrap [] [] None s tin tout adler -> hdr_ok h ->
    (wrap = 2 -> c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
                 Iapi W HI dict wrap [] [] None (set_d_gzhead s (Some h)) tin tout adler) /\
    (wrap <> 2 -> c_deflateSetHeader s z (Some h) = Some (s, z, Z_STREAM_ERROR)).
Proof.
  intros dict wrap s tin tout adler h z CF HF HI' Hh.
  assert (Hw : d_wrap s = wrap /\ (ph0 dict wrap [] [] s tin adler \/ ph2 dict wrap [] [] s tin adler)).
  { destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin & _ & Hph).
    destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
    - split; [apply P0|]. left; exact P0.
    - destruct P1 as (_ & _ & Hne & _). congruence.
    - split; [apply P2|]. right; exact P2.
    - destruct P3 as [Hst _]. specialize (Hfin Hst). discriminate. }
  destruct Hw as [Hw Hph].
  assert (Hb := Iapi_bad_state _ _ _ _ _ _ _ _ _ HF HI').
  unfold c_deflateSetHeader. rewrite Hb, Hw. split.
  - intros ->. cbn. split; [reflexivity|].
    pose proof HI' as HI0.
    destruct HI0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & _).
    assert (Hce : core_eq s (set_d_gzhead s (Some h))) by (unfold core_eq; repeat split; reflexivity).
    unfold Iapi. split; [exact (cf_frame W CF s _ H1 Hce)|].
    split; [exact H2|]. do 5 (split; [assumption|]).
    split; [intros h' E; cbn in E; injection E as <-; exact Hh|].
    do 5 (split; [assumption|]). split; [exact H14|].
    destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph0).
    destruct Hph0 as [P0 | (Hlf & [P1 | [P2 | P3]])].
    + left; exact P0.
    + destruct P1 as (_ & _ & Hne & _). congruence.
    + right. split; [exact Hlf|]. right; left; exact P2.
    + right. split; [exact Hlf|]. right; right; exact P3.
  - intros Hn. destruct (wrap =? 2) eqn:E; [apply Z.eqb_eq in E; contradiction|]. reflexivity.
Qed.

End Init.

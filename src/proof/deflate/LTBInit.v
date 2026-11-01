(** * deflate_bound theory: deflateInit2, deflateSetDictionary, deflateSetHeader *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTBDefs.
Import ListNotations.
Local Open Scope Z_scope.

Record init_facts : Prop := {
  in_bpre_init : forall W, core_facts W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z');
  in_bpre_dict : forall W, core_facts W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z');
  in_bpre_head : forall W, core_facts W -> forall level wbits mem strategy ds s tin tout adler h z,
    Bpre W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    Bpre W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler
}.


(** Helpers (from LTApiInit.v): the shape of the model's deflateInit2_. *)
Lemma bi_wbw : forall wbits : Z,
  (if wbits <? 0 then if wbits <? -15 then None else Some (- wbits, 0)
   else if wbits >? 15 then Some (wbits - 16, 2) else Some (wbits, 1)) =
  (if wbits <? -15 then None else Some (wb_of wbits, wrap_of wbits)).
Proof.
  intros wbits; unfold wb_of, wrap_of.
  destruct (wbits <? 0) eqn:E0, (wbits <? -15) eqn:E1, (wbits >? 15) eqn:E2; auto; lia.
Qed.

Lemma bi_check_eq : forall level method wbits mem strategy,
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

Lemma bi_shape : forall level method wbits mem strategy a1 a2 a3 a4 a5 z,
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
    rewrite P. unfold c_deflateInit2_. cbv zeta. cbn [negb orb]. rewrite bi_wbw, Ew. reflexivity.
  - pose proof (bi_check_eq level method wbits mem strategy Ew) as C.
    destruct (params_ok level method wbits mem strategy) eqn:P.
    + destruct a1, a2, a3, a4, a5; try reflexivity;
      unfold c_deflateInit2_; cbv zeta; cbn [negb orb]; rewrite bi_wbw, Ew, C; cbn [negb andb];
      reflexivity.
    + unfold c_deflateInit2_; cbv zeta; cbn [negb orb]; rewrite bi_wbw, Ew, C. reflexivity.
Qed.

Lemma bi_adler1 : Zlib.proof.adler32.Model.adler_valid 1.
Proof. unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence. Qed.

Lemma bi_wrap_range : forall wbits, 0 <= wrap_of wbits <= 2.
Proof. intros wbits; unfold wrap_of; destruct (wbits <? 0), (wbits >? 15); lia. Qed.

Lemma bi_init : forall W, core_facts W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros W CF level wbits mem strategy a1 a2 a3 a4 a5 z P.
  rewrite bi_shape, P.
  destruct (cf_init W CF level 8 wbits mem strategy z P)
    as (s & z' & E & HW & HO & Hst & Hwr & Hgz & Hgi & Hlf & Hpo & Hpe & Hbv & Hss & Hla & Hbs & Hsn &
        Hlv & Hstr & Hwb & Hhb & Hz').
  destruct a1;
    [| split; [eauto|]; intros os z1 code E1 Hc; inversion E1; subst; unfold Z_MEM_ERROR, Z_OK in *; lia].
  destruct (a2 && a3 && a4 && a5);
    [| split; [eauto|]; intros os z1 code E1 Hc; inversion E1; subst; unfold Z_MEM_ERROR, Z_OK in *; lia].
  rewrite E. split; [eauto|]. intros os z1 code E1 _. inversion E1; subst; clear E1.
  exists s. split; [reflexivity|]. split; [exact Hgz|].
  cbn [z_total_in z_total_out z_adler].
  unfold Bpre.
  split; [exact HW|]. split; [exact HO|]. split; [exact P|]. split; [exact Hst|]. split; [exact Hwr|].
  do 5 (split; [assumption|]). split; [lia|]. split; [intros _; split; [assumption|reflexivity]|].
  do 4 (split; [first [assumption|reflexivity]|]).
  split; [intros h' Eh; rewrite Hgz in Eh; discriminate|].
  split; [lia|]. split; [reflexivity|]. split; [lia|].
  unfold adler_ok. rewrite Hwr. split.
  - intros H1. rewrite H1. exact bi_adler1.
  - intros H2. rewrite H2. cbn. lia.
Qed.

Lemma bi_dict : forall W, core_facts W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros W CF level wbits mem strategy s tin tout adler d ain aout msg HB Hwb Hd Hdl Hain Haout.
  destruct HB as (HW & HO & P & Hst & Hwr & Hpe & Hpo & Hbv & Hsn & Hla & Hsb & Hds & Hlv & Hstr & Hwbits &
                  Hhb & Hgz & Hlf & Hto & Htin & Had).
  destruct (Hds eq_refl) as [Hss Htin0]. subst tin.
  assert (Hw2 : (wrap_of wbits =? 2) = false)
    by (unfold wrap_of; destruct (wbits <? 0) eqn:?, (wbits >? 15) eqn:?; auto; lia).
  rewrite Hw2 in Hst.
  assert (Hwr01 : 0 <= d_wrap s <= 1)
    by (rewrite Hwr; unfold wrap_of; destruct (wbits <? 0) eqn:?, (wbits >? 15) eqn:?; auto; lia).
  assert (Hbad : bad_state s = false) by (unfold bad_state, c_deflateStateCheck; rewrite Hst; reflexivity).
  destruct (cf_dict W CF s (zcall [] 0 ain 0 aout tout adler msg) d HW Hwr01 Hbad (fun _ => Hst) Hss Hla
              ltac:(lia) Hd Hdl ltac:(simpl; lia) Had) as (s' & z' & k & Hc & HW' & Hae & Hoe & Hsp & Hla' &
                                                     Hsb' & Hs0' & Hsn' & Hk & Hz').
  exists s', z'.
  destruct Hae as (Hast & Haw & Hagz & Hagi & Half & Ham).
  destruct Hoe as (Hotr & Hopbm & Hopo).
  destruct Hsp as (Hswb & Hsws & Hshb & HsL & Hspbs & Hslv & Hsstr).
  split; [exact Hc|]. split; [exact Hagz|].
  subst z'. cbn [z_total_in z_total_out z_adler zcall].
  unfold Bpre.
  split; [exact HW'|].
  split.
  { unfold outok, d_pb, d_pending in *. rewrite Hotr, Hopbm, Hopo, Hspbs. exact HO. }
  split; [exact P|]. split; [rewrite Hast, Hw2; exact Hst|]. split; [rewrite Haw; exact Hwr|].
  split; [unfold d_pending in *; rewrite Hotr; exact Hpe|]. split; [rewrite Hopo; exact Hpo|].
  split; [unfold d_bi_valid in *; rewrite Hotr; exact Hbv|].
  split; [rewrite Hsn'; exact Hsn|]. split; [exact Hla'|]. split; [exact Hsb'|]. split; [discriminate|].
  split; [rewrite Hslv; exact Hlv|]. split; [rewrite Hsstr; exact Hstr|].
  split; [rewrite Hswb; exact Hwbits|]. split; [rewrite Hshb; exact Hhb|].
  split; [unfold gzh_ok in *; rewrite Hagz; exact Hgz|]. split; [rewrite Half; exact Hlf|].
  split; [exact Hto|]. split; [lia|].
  unfold adler_ok. rewrite Haw. split.
  - intros H1. rewrite H1. cbn. apply Zlib.proof.adler32.Model.ref_adler32_valid. apply (proj1 Had). exact H1.
  - intros H2. lia.
Qed.

Lemma bi_head : forall W, core_facts W -> forall level wbits mem strategy ds s tin tout adler h z,
    Bpre W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    Bpre W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler.
Proof.
  intros W CF level wbits mem strategy ds s tin tout adler h z HB Hwb Hh.
  pose proof HB as (HW & HB').
  assert (Hw2 : wrap_of wbits = 2)
    by (unfold wrap_of; destruct (wbits <? 0) eqn:?, (wbits >? 15) eqn:?; auto; lia).
  assert (Hst : d_status s = GZIP_STATE) by (destruct HB' as (_ & _ & Hst & _); rewrite Hst, Hw2; reflexivity).
  assert (Hwr : d_wrap s = 2) by (destruct HB' as (_ & _ & _ & Hwr & _); rewrite Hwr, Hw2; reflexivity).
  assert (Hb : bad_state s = false) by (unfold bad_state, c_deflateStateCheck; rewrite Hst; reflexivity).
  unfold c_deflateSetHeader. rewrite Hb, Hwr. split; [reflexivity|].
  assert (Hce : core_eq s (set_d_gzhead s (Some h))) by (unfold core_eq; repeat split; reflexivity).
  split; [exact (cf_frame W CF s _ HW Hce)|].
  destruct HB' as (HO & P & Hst' & Hwr' & Hpe & Hpo & Hbv & Hsn & Hla & Hsb & Hds & Hlv & Hstr & Hwbits &
                   Hhb & Hgz & Hlf & Hto & Htin & Had).
  split; [exact HO|]. split; [exact P|].
  do 13 (split; [match goal with H : _ |- _ => exact H end|]).
  split; [intros h' E; cbn in E; injection E as <-; exact Hh|].
  split; [exact Hlf|]. split; [exact Hto|]. split; [exact Htin|]. exact Had.
Qed.

Theorem init_proof : init_facts.
Proof.
  constructor; [exact bi_init | exact bi_dict | exact bi_head].
Qed.

Lemma bpre_init : forall W, core_facts W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                Bpre W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z').
Proof. exact (in_bpre_init init_proof). Qed.

Lemma bpre_dict : forall W, core_facts W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 32768 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z').
Proof. exact (in_bpre_dict init_proof). Qed.

Lemma bpre_head : forall W, core_facts W -> forall level wbits mem strategy ds s tin tout adler h z,
    Bpre W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    Bpre W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler.
Proof. exact (in_bpre_head init_proof). Qed.




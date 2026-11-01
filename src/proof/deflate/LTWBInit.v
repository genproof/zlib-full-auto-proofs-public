(** * The deflateBound accounting for the short laws: deflateInit2, deflateSetDictionary, deflateSetHeader

    [BpreW] (LTWBDefs.v) after deflateInit2 with accepted parameters, after deflateSetDictionary with a dictionary
    of up to 2^32-1 bytes (raw and zlib streams, right after deflateInit2) and after deflateSetHeader with a header
    [hdr_ok_w].  Port of LTBInit.v to LTWIface's [core_facts_w]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWBDefs.
Require Import Zlib.proof.deflate.LTBInit.
Import ListNotations.
Local Open Scope Z_scope.

Record init_w_facts : Prop := {
  iw_bpre_init : forall W, core_facts_w W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                BpreW W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z');
  iw_bpre_dict : forall W, core_facts_w W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
    BpreW W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 4294967295 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      BpreW W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z');
  iw_bpre_head : forall W, core_facts_w W -> forall level wbits mem strategy ds s tin tout adler h z,
    BpreW W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok_w h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    BpreW W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler
}.

(** deflateInit2 with accepted parameters: [BpreW] holds of the new state, nothing read (total_in 0), nothing
    written (total_out 0), the initial check value. *)
Lemma biw_init : forall W, core_facts_w W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
    params_ok level 8 wbits mem strategy = true ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ d_gzhead s = None /\
                BpreW W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros W CF level wbits mem strategy a1 a2 a3 a4 a5 z P.
  rewrite bi_shape, P.
  destruct (cw_init W CF level 8 wbits mem strategy z P)
    as (s & z' & E & HW & HO & Hst & Hwr & Hgz & Hgi & Hlf & Hpo & Hpe & Hbv & Hss & Hla & Hbs & Hsn &
        Hlv & Hstr & Hwb & Hhb & Hz').
  destruct a1;
    [| split; [eauto|]; intros os z1 code E1 Hc; inversion E1; subst; unfold Z_MEM_ERROR, Z_OK in *; lia].
  destruct (a2 && a3 && a4 && a5);
    [| split; [eauto|]; intros os z1 code E1 Hc; inversion E1; subst; unfold Z_MEM_ERROR, Z_OK in *; lia].
  rewrite E. split; [eauto|]. intros os z1 code E1 _. inversion E1; subst; clear E1.
  exists s. split; [reflexivity|]. split; [exact Hgz|].
  cbn [z_total_in z_total_out z_adler].
  unfold BpreW.
  split; [exact HW|]. split; [exact HO|]. split; [exact P|]. split; [exact Hst|]. split; [exact Hwr|].
  do 5 (split; [assumption|]). split; [lia|]. split; [intros _; split; [assumption|reflexivity]|].
  do 4 (split; [first [assumption|reflexivity]|]).
  split; [intros h' Eh; rewrite Hgz in Eh; discriminate|].
  split; [lia|]. split; [reflexivity|]. split; [lia|].
  unfold adler_ok. rewrite Hwr. split.
  - intros H1. rewrite H1. exact bi_adler1.
  - intros H2. rewrite H2. cbn. lia.
Qed.

(** deflateSetDictionary right after deflateInit2 (raw or zlib stream): total_in moves from 0 to the [k <= 2^32-1]
    dictionary bytes used, so the addition modulo 2^64 does not wrap. *)
Lemma biw_dict : forall W, core_facts_w W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
    BpreW W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    bytes d -> Zlength d <= 4294967295 -> u32r ain -> u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      BpreW W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z').
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
  destruct (cw_dict W CF s (zcall [] 0 ain 0 aout tout adler msg) d HW Hwr01 Hbad (fun _ => Hst) Hss Hla
              ltac:(lia) Hd ltac:(lia) ltac:(simpl; lia) Had) as (s' & z' & k & Hc & HW' & Hae & Hoe & Hsp & Hla' &
                                                     Hsb' & Hs0' & Hsn' & Hk & Hz').
  exists s', z'.
  destruct Hae as (Hast & Haw & Hagz & Hagi & Half & Ham).
  destruct Hoe as (Hotr & Hopbm & Hopo).
  destruct Hsp as (Hswb & Hsws & Hshb & HsL & Hspbs & Hslv & Hsstr).
  split; [exact Hc|]. split; [exact Hagz|].
  subst z'. cbn [z_total_in z_total_out z_adler zcall].
  assert (Hu : u64 (0 + k) = k) by (unfold u64; apply Z.mod_small; lia).
  rewrite Hu.
  unfold BpreW.
  split; [exact HW'|].
  split.
  { unfold outok, d_pb, d_pending in *. rewrite Hotr, Hopbm, Hopo, Hspbs. exact HO. }
  split; [exact P|]. split; [rewrite Hast, Hw2; exact Hst|]. split; [rewrite Haw; exact Hwr|].
  split; [unfold d_pending in *; rewrite Hotr; exact Hpe|]. split; [rewrite Hopo; exact Hpo|].
  split; [unfold d_bi_valid in *; rewrite Hotr; exact Hbv|].
  split; [rewrite Hsn'; exact Hsn|]. split; [exact Hla'|]. split; [exact Hsb'|]. split; [discriminate|].
  split; [rewrite Hslv; exact Hlv|]. split; [rewrite Hsstr; exact Hstr|].
  split; [rewrite Hswb; exact Hwbits|]. split; [rewrite Hshb; exact Hhb|].
  split; [unfold gzh_ok_w in *; rewrite Hagz; exact Hgz|]. split; [rewrite Half; exact Hlf|].
  split; [exact Hto|]. split; [lia|].
  unfold adler_ok. rewrite Haw. split.
  - intros H1. rewrite H1. cbn. apply Zlib.proof.adler32.Model.ref_adler32_valid. apply (proj1 Had). exact H1.
  - intros H2. lia.
Qed.

(** deflateSetHeader on a gzip stream with a header [hdr_ok_w]: the core of the state does not change. *)
Lemma biw_head : forall W, core_facts_w W -> forall level wbits mem strategy ds s tin tout adler h z,
    BpreW W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok_w h ->
    c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
    BpreW W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler.
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
  split; [exact (cw_frame W CF s _ HW Hce)|].
  destruct HB' as (HO & P & Hst' & Hwr' & Hpe & Hpo & Hbv & Hsn & Hla & Hsb & Hds & Hlv & Hstr & Hwbits &
                   Hhb & Hgz & Hlf & Hto & Htin & Had).
  split; [exact HO|]. split; [exact P|].
  do 13 (split; [match goal with H : _ |- _ => exact H end|]).
  split; [intros h' E; cbn in E; injection E as <-; exact Hh|].
  split; [exact Hlf|]. split; [exact Hto|]. split; [exact Htin|]. exact Had.
Qed.

Theorem init_w_proof : init_w_facts.
Proof.
  constructor; [exact biw_init | exact biw_dict | exact biw_head].
Qed.

Lemma bpre_init_w : forall W, core_facts_w W -> forall level wbits mem strategy a1 a2 a3 a4 a5 z,
  params_ok level 8 wbits mem strategy = true ->
  (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some r) /\
  forall os z' code,
    c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', code) ->
    code = Z_OK ->
    exists s, os = Some s /\ d_gzhead s = None /\
              BpreW W level wbits mem strategy false s (z_total_in z') (z_total_out z') (z_adler z').
Proof. exact (iw_bpre_init init_w_proof). Qed.

Lemma bpre_dict_w : forall W, core_facts_w W -> forall level wbits mem strategy s tin tout adler d ain aout msg,
  BpreW W level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
  bytes d -> Zlength d <= 4294967295 -> u32r ain -> u32r aout ->
  exists s' z',
    c_deflateSetDictionary s (zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
    d_gzhead s' = d_gzhead s /\
    BpreW W level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z').
Proof. exact (iw_bpre_dict init_w_proof). Qed.

Lemma bpre_head_w : forall W, core_facts_w W -> forall level wbits mem strategy ds s tin tout adler h z,
  BpreW W level wbits mem strategy ds s tin tout adler -> 15 < wbits -> hdr_ok_w h ->
  c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK) /\
  BpreW W level wbits mem strategy ds (set_d_gzhead s (Some h)) tin tout adler.
Proof. exact (iw_bpre_head init_w_proof). Qed.

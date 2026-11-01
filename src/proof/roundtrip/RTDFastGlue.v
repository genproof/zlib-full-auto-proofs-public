(** * RT-D part FAST: the glue.  From the functional part statements of RTDFastKit.v (and the Qed
    safety parts of the deflate laws) to [comp_fspec 1 c_deflate_fast]: the relation [FR] between the start of
    the call and a point of the main loop, its composition, the step, the loop (same measure as the safety
    proof), the tail. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.
Local Strategy opaque [loop loop2].

(** From the start (s0, z0) of the call (history dict ++ D0, blocks BS0, bit position p0) to (s, z): the bytes
    consumed extend the history, the blocks BS follow BS0, the bits added are their encoding. *)
Definition FR (s0 : dstate) (z0 : strm) (dict D0 : list Z) (BS0 : list F.block) (p0 : Z)
    (s : dstate) (z : strm) (BS : list F.block) (syms : list (Z * Z)) : Prop :=
  exists k x,
    zstep (d_wrap s0) z0 z k x /\
    kcore dict (D0 ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS0 ++ BS) syms s /\
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_from p0 BS false.

Lemma FR_refl s0 z0 dict D0 BS0 p0 syms :
  zall z0 -> adler_ok (d_wrap s0) (z_adler z0) -> quiet s0 -> kcore dict D0 BS0 syms s0 ->
  FR s0 z0 dict D0 BS0 p0 s0 z0 [] syms.
Proof.
  intros Hz Ha Hq Hk. exists 0, []. split; [apply zstep_refl; auto|].
  rewrite Z.add_0_r, sublist_nil, !app_nil_r. split; [exact Hk|].
  rewrite (quiet_pend s0 Hq). reflexivity.
Qed.

(** one more piece from (s, z) to (s', z') *)
Lemma FR_trans s0 z0 dict D0 BS0 p0 s z BS k x s' z' k' x' BS' syms' :
  zin_in z0 -> adler_ok (d_wrap s0) (z_adler z0) ->
  zstep (d_wrap s0) z0 z k x ->
  F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_from p0 BS false ->
  zstep (d_wrap s0) z z' k' x' ->
  kcore dict ((D0 ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) ++
              sublist (z_next_in z) (z_next_in z + k') (z_in z)) ((BS0 ++ BS) ++ BS') syms' s' ->
  F.bytes_bits (x' ++ pend s') ++ bibits s' =
    F.bytes_bits (pend s) ++ bibits s ++ enc_from (p0 + Zlength (enc_from p0 BS false)) BS' false ->
  FR s0 z0 dict D0 BS0 p0 s' z' (BS ++ BS') syms'.
Proof.
  intros Hzi Ha Z1 B1 Z2 K2 B2.
  pose proof Z1 as (A1 & A2 & A3 & A4 & _). pose proof Z2 as (C1 & C2 & _).
  pose proof Hzi as (_ & Hn & Hai & Hl & _).
  exists (k + k'), (x ++ x'). split; [eapply zstep_trans; eauto|].
  split.
  - rewrite A1, A3 in K2. rewrite hist_app in K2 by lia. rewrite <- app_assoc in K2. exact K2.
  - rewrite <- app_assoc, bytes_bits_app, <- app_assoc, B2, enc_from_app_false.
    rewrite !app_assoc, <- bytes_bits_app, B1. reflexivity.
Qed.

(** the last piece (the tail): enc_out *)
Lemma FR_end s0 z0 dict D0 BS0 p0 s z BS k x s' z' k' x' BS' syms' fin :
  zin_in z0 -> adler_ok (d_wrap s0) (z_adler z0) -> (fin = true -> BS' <> []) ->
  zstep (d_wrap s0) z0 z k x ->
  F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_from p0 BS false ->
  zstep (d_wrap s0) z z' k' x' ->
  kcore dict ((D0 ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) ++
              sublist (z_next_in z) (z_next_in z + k') (z_in z)) ((BS0 ++ BS) ++ BS') syms' s' ->
  F.bytes_bits (x' ++ pend s') ++ bibits s' =
    F.bytes_bits (pend s) ++ bibits s ++ enc_out (p0 + Zlength (enc_from p0 BS false)) BS' fin ->
  exists k2 x2,
    zstep (d_wrap s0) z0 z' k2 x2 /\
    kcore dict (D0 ++ sublist (z_next_in z0) (z_next_in z0 + k2) (z_in z0)) (BS0 ++ (BS ++ BS')) syms' s' /\
    F.bytes_bits (x2 ++ pend s') ++ bibits s' = bibits s0 ++ enc_out p0 (BS ++ BS') fin.
Proof.
  intros Hzi Ha Hf Z1 B1 Z2 K2 B2.
  pose proof Z1 as (A1 & A2 & A3 & A4 & _). pose proof Z2 as (C1 & C2 & _).
  pose proof Hzi as (_ & Hn & Hai & Hl & _).
  exists (k + k'), (x ++ x'). split; [eapply zstep_trans; eauto|].
  split.
  - rewrite A1, A3 in K2. rewrite hist_app in K2 by lia. rewrite <- app_assoc in K2. exact K2.
  - rewrite <- app_assoc, bytes_bits_app, <- app_assoc, B2, (enc_out_app p0 BS BS' fin Hf).
    rewrite !app_assoc, <- bytes_bits_app, B1. reflexivity.
Qed.

(** the bit position at a point of the loop *)
Lemma FR_aligned s0 (s : dstate) (x : list Z) BS p0 :
  outok s0 -> outok s -> (p0 - d_bi_valid s0) mod 8 = 0 ->
  F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_from p0 BS false ->
  (p0 + Zlength (enc_from p0 BS false) - d_bi_valid s) mod 8 = 0.
Proof.
  intros (_ & (O0 & _) & _) (_ & (O1 & _) & _) Hp E. eapply bitpos_aligned; eauto; unfold d_bi_valid; lia.
Qed.

Lemma bytes_hist (D : list Z) (z : strm) n k :
  bytes D -> zin_in z -> bytes (D ++ sublist n (n + k) (z_in z)).
Proof.
  intros HD (Hb & _). apply Forall_app. split; [exact HD|]. apply bytes_sublist. exact Hb.
Qed.

(** ** One iteration after the refill *)
Lemma fstep_ok (Hov : Zlib.proof.huffman.Overlay.overlay_statement) :
  ins_fspec2 -> lm_fspec -> fbo_fspec -> fsearch_stmt -> flit_stmt -> fmatch_stmt -> fbflush_stmt ->
  forall s0 z0 dict D0 BS0 p0 s z BS syms r k x,
    zin_in z0 -> adler_ok (d_wrap s0) (z_adler z0) -> outok s0 -> 0 <= p0 -> (p0 - d_bi_valid s0) mod 8 = 0 ->
    Forall F.byte_ok dict -> bytes D0 ->
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 ->
    d_wrap s = d_wrap s0 -> ready s -> 1 <= d_lookahead s ->
    zstep (d_wrap s0) z0 z k x ->
    kcore dict (D0 ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS0 ++ BS) syms s ->
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_from p0 BS false ->
    df_step s z = Some r ->
    exists BS' syms', FR s0 z0 dict D0 BS0 p0 (fst (rst r)) (snd (rst r)) BS' syms'.
Proof.
  intros Hins2 Hlm2 Hfbo2 Hse Hli Hma Hbf s0 z0 dict D0 BS0 p0 s z BS syms r k x
    Hzi0 Ha0 Ho0 Hpp Hp0 Hdict HD0 HW Ho Hq Hz Ha Hfn Hwr Hrd Hla Z1 K1 B1 Er.
  destruct (trees_ok2 Hov) as (Htal & _ & _).
  destruct lm_ok as [Hins Hlm].
  set (D := D0 ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) in *.
  assert (HD : bytes D) by (apply bytes_hist; auto).
  rewrite df_step_eq in Er.
  destruct (fsearch s) as [s2|] eqn:E2; [|discriminate]. cbn [bind] in Er.
  destruct (fbranch s2) as [[s3 bf]|] eqn:E3; [|discriminate]. cbn [bind] in Er.
  destruct (search_ok Hins Hlm s HW Hfn Hrd Hla) as (s2' & E2' & HSR).
  rewrite E2 in E2'. injection E2' as <-.
  assert (Hkh : khash s) by (destruct K1 as (_ & Kh); exact Kh).
  destruct (Hse s s2 Hins2 Hlm2 HW Hfn Hrd Hla Hkh E2) as (Hch & Hpr & Hmt).
  assert (Hb : exists syms3, TS s3 syms3 bf /\ kt dict D (BS0 ++ BS) syms3 s3 /\ bibits s3 = bibits s /\
                 fr s s3).
  { unfold fbranch in E3. destruct (d_match_length s2 >=? MIN_MATCH) eqn:Em.
    - apply Z.geb_le in Em.
      destruct (match_ok2 Htal (insloop_ok Hins) s s2 HW Ho Hq Hfn Hrd Hla HSR Em)
        as (s3' & bf' & syms3' & E3' & _ & Hfr & _).
      rewrite E3 in E3'. injection E3' as <- <-.
      destruct (Hma s s2 s3 bf dict D (BS0 ++ BS) syms Htal Hins2 HW Ho Hq Hfn Hrd Hla HSR Em Hdict HD K1
                  Hch Hpr (Hmt Em) E3) as (syms3 & T & K & B).
      exists syms3. auto.
    - rewrite Z.geb_leb in Em. apply Z.leb_gt in Em.
      destruct (lit_ok2 Htal s s2 HW Ho Hq Hfn Hrd Hla HSR Em) as (s3' & bf' & syms3' & E3' & _ & Hfr & _).
      rewrite E3 in E3'. injection E3' as <- <-.
      destruct (Hli s s2 s3 bf dict D (BS0 ++ BS) syms Htal HW Ho Hq Hfn Hrd Hla HSR Em Hdict HD K1
                  Hch Hpr E3) as (syms3 & T & K & B).
      exists syms3. auto. }
  destruct Hb as (syms3 & HTS & Hkt & Hbi & Hfr).
  assert (Hwr3 : d_wrap s3 = d_wrap s) by (destruct Hfr as (_ & (_ & E & _) & _); exact E).
  assert (Ho3 : outok s3) by (destruct HTS as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & O & _) & _); exact O).
  assert (Hq3 : quiet s3) by (destruct HTS as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q & _) & _); exact Q).
  assert (Hal : (p0 + Zlength (enc_from p0 BS false) - d_bi_valid s3) mod 8 = 0).
  { assert (E : d_bi_valid s3 = d_bi_valid s).
    { destruct Hfr as (_ & _ & _ & G). specialize (G 0). unfold Gb in G.
      destruct Hq3 as (Q1 & _). destruct Hq as (Q2 & _). lia. }
    rewrite E. exact (FR_aligned s0 s x BS p0 Ho0 Ho Hp0 B1). }
  assert (Hp1 : 0 <= p0 + Zlength (enc_from p0 BS false)).
  { pose proof (Zlength_nonneg (enc_from p0 BS false)). lia. }
  rewrite <- Hwr3 in Ha.
  destruct (Hbf s3 z 0 syms3 bf r dict D (BS0 ++ BS) (p0 + Zlength (enc_from p0 BS false)) Hfbo2 HTS Hz Ha
              ltac:(lia) Hdict HD Hkt Hp1 Hal Er) as (x' & BS' & syms' & Z2 & K2 & B2).
  exists (BS ++ BS'), syms'.
  rewrite Hwr3, Hwr in Z2.
  eapply (FR_trans s0 z0 dict D0 BS0 p0 s z BS k x _ _ 0 x' BS' syms'); eauto.
  - rewrite Z.add_0_r, sublist_nil, app_nil_r. exact K2.
  - rewrite (quiet_pend s Hq), <- Hbi. exact B2.
Qed.

(** ** The main loop *)
Definition bs_nm (r : dexit) : Prop :=
  match r with (_, _, Some bs) => bs = need_more | _ => True end.

Lemma floop_ok (Hov : Zlib.proof.huffman.Overlay.overlay_statement) :
  fill_fspec -> ins_fspec2 -> lm_fspec -> fbo_fspec ->
  frefill_stmt -> fsearch_stmt -> flit_stmt -> fmatch_stmt -> fbflush_stmt ->
  forall s0 z0 flush dict D0 BS0 p0 syms0,
    W s0 -> outok s0 -> quiet s0 -> zall z0 -> adler_ok (d_wrap s0) (z_adler z0) -> fn_of s0 = 1 ->
    0 <= flush <= 5 -> 0 <= p0 -> (p0 - d_bi_valid s0) mod 8 = 0 ->
    Forall F.byte_ok dict -> bytes D0 -> kcore dict D0 BS0 syms0 s0 ->
    exists r, loop FUEL (df_body flush) (s0, z0) = Some r /\ loop_res s0 z0 flush r /\ bs_nm r /\
      exists BS syms, FR s0 z0 dict D0 BS0 p0 (fst (fst r)) (snd (fst r)) BS syms.
Proof.
  intros Hfill2 Hins2 Hlm2 Hfbo2 Hre Hse Hli Hma Hbf s0 z0 flush dict D0 BS0 p0 syms0
    HW0 Ho0 Hq0 Hz0 Ha0 Hfn0 Hfl Hpp Hp0 Hdict HD0 Hk0.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfb.
  destruct lm_ok as [Hins Hlm].
  pose proof Hz0 as [Hzi0 _].
  apply (fg_loop_measure (df_body flush)
           (fun a => exists evs BS syms, FI s0 z0 flush (fst a) (snd a) evs /\
                       FR s0 z0 dict D0 BS0 p0 (fst a) (snd a) BS syms)
           (fun r => loop_res s0 z0 flush r /\ bs_nm r /\
                       exists BS syms, FR s0 z0 dict D0 BS0 p0 (fst (fst r)) (snd (fst r)) BS syms)
           (fun a => z_avail_in (snd a) + d_lookahead (fst a))).
  - intros [s z] (evs & BS & syms & HFI & (k & x & Z1 & K1 & B1)). cbn [fst snd] in *.
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn0) as (HW & Ho & Hq & Hz & Ha & Hfn).
    assert (Hwr : d_wrap s = d_wrap s0) by (destruct (FI_sp _ _ _ _ _ _ HFI) as (_ & (_ & E & _)); exact E).
    split.
    { destruct HW as (_ & _ & (Hl & _) & _). destruct Hz as ((_ & _ & Hai & _) & _). lia. }
    destruct (refill_ok fill_ok s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r1 & E1 & H1).
    destruct (Hre s z flush r1 dict _ _ syms Hfill2 HW Ho Hq Hz Ha Hfn Hfl K1 E1) as (k1 & Zr & Kr & Pr & Br).
    rewrite Hwr in Zr.
    assert (FR1 : FR s0 z0 dict D0 BS0 p0 (fst (rst r1)) (snd (rst r1)) BS syms).
    { rewrite <- (app_nil_r BS).
      apply (FR_trans s0 z0 dict D0 BS0 p0 s z BS k x _ _ k1 [] [] syms Hzi0 Ha0 Z1 B1 Zr).
      - rewrite app_nil_r. exact Kr.
      - rewrite Pr, Br. cbn [app enc_from]. rewrite app_nil_r. reflexivity. }
    unfold df_body. rewrite E1. cbn [bind].
    destruct r1 as [[s1 z1]|[[s1 z1] [bs|]]]; cbn [rst fst snd] in FR1.
    + destruct H1 as (HFI1 & Hr1 & Hla1 & Hm1).
      destruct (FI_parts _ _ _ _ _ _ HFI1 Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
      assert (HFI01 : FI s0 z0 flush s1 z1 (evs ++ [])) by (eapply FI_trans; eauto).
      assert (Hwr1 : d_wrap s1 = d_wrap s0)
        by (destruct (FI_sp _ _ _ _ _ _ HFI01) as (_ & (_ & E & _)); exact E).
      destruct (Zlib.proof.roundtrip.RTDLTCFastGlue.step_ok (search_ok Hins Hlm) (lit_ok2 Htal) (match_ok2 Htal (insloop_ok Hins))
                  (bflush_ok (fbw_ok Hfb)) s1 z1 flush HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hr1 Hla1)
        as (r2 & E2 & H2).
      destruct FR1 as (k2 & x2 & Z2 & K2 & B2).
      destruct (fstep_ok Hov Hins2 Hlm2 Hfbo2 Hse Hli Hma Hbf s0 z0 dict D0 BS0 p0 s1 z1 BS syms r2 k2 x2
                  Hzi0 Ha0 Ho0 Hpp Hp0 Hdict HD0 HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hwr1 Hr1 Hla1 Z2 K2 B2 E2)
        as (BS3 & syms3 & FR3).
      rewrite E2. unfold step_res in H2.
      destruct r2 as [[s2 z2]|[[s2 z2] o]]; cbn [rst fst snd] in FR3.
      * destruct H2 as ((evs2 & HFI2) & Hm2). right. exists (s2, z2). split; [reflexivity|].
        cbn [fst snd]. split; [|lia].
        exists (evs ++ ([] ++ evs2)), BS3, syms3. split; [|exact FR3].
        eapply FI_trans; [exact Hz0|exact Ha0|exact HFI|].
        eapply FI_trans; [exact Hz|exact Ha|exact HFI1|exact HFI2].
      * destruct H2 as (-> & evs2 & Hc2 & Hb2). left. exists (s2, z2, Some need_more). split; [reflexivity|].
        split; [|split; [reflexivity|exists BS3, syms3; exact FR3]].
        cbv beta iota delta [loop_res]. exists (evs ++ ([] ++ evs2)). split.
        -- eapply crel_trans; [exact Hz0|exact Ha0|apply FI_crel; exact HFI|].
           eapply crel_trans; [exact Hz|exact Ha|apply FI_crel; exact HFI1|exact Hc2].
        -- destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1). destruct (FI_sp _ _ _ _ _ _ HFI1) as (P2 & A2).
           eapply (bpost_start s0 s z0 z); [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|].
           eapply bpost_start; [exact P2|exact A2|constructor|exact Hb2].
    + destruct H1 as (-> & Hc1 & Hb1). left. exists (s1, z1, Some need_more). split; [reflexivity|].
      split; [|split; [reflexivity|exists BS, syms; exact FR1]].
      cbv beta iota delta [loop_res]. exists (evs ++ []). split.
      * eapply crel_trans; [exact Hz0|exact Ha0|apply FI_crel; exact HFI|exact Hc1].
      * destruct (FI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
        eapply bpost_start; [exact P1|exact A1|apply (FI_last _ _ _ _ _ _ HFI)|exact Hb1].
    + destruct H1 as (HFI1 & H1). left. exists (s1, z1, None). split; [reflexivity|].
      split; [|split; [exact I|exists BS, syms; exact FR1]].
      cbv beta iota delta [loop_res]. exists (evs ++ []). split; [|exact H1].
      eapply FI_trans; [exact Hz0|exact Ha0|exact HFI|exact HFI1].
  - exists [], [], syms0. cbn [fst snd]. split; [apply FI_refl; auto|].
    apply FR_refl; auto.
  - cbn [fst snd]. destruct HW0 as (Hp & (_ & _ & Hws & _) & (_ & Hss & Hsl & _) & _).
    pose proof (prm_w_bound s0 Hp) as Hw.
    destruct Hz0 as ((_ & _ & Hai & _) & _). change (Z.of_nat FUEL) with 40. lia.
Qed.

(** ** deflate_fast from the functional parts *)
Theorem fast_from_fparts (Hov : Zlib.proof.huffman.Overlay.overlay_statement) :
  fill_fspec -> ins_fspec2 -> lm_fspec -> fbo_fspec ->
  frefill_stmt -> fsearch_stmt -> flit_stmt -> fmatch_stmt -> fbflush_stmt -> ftail_stmt ->
  comp_fspec 1 c_deflate_fast.
Proof.
  intros Hfill2 Hins2 Hlm2 Hfbo2 Hre Hse Hli Hma Hbf Hta
    s z flush s' z' bs dict D BS syms p HW3 Ho Hq Hfl Hzi Hwr Ha Hfn Hdict HD Hk Hpp Hp0 Ec.
  destruct HW3 as ((HW & _) & _).
  pose proof (zin_ok_zall z Hzi) as Hz. pose proof (adler_pre_ok _ _ Ha) as Ha'.
  pose proof Hz as [Hzi0 _].
  destruct (floop_ok Hov Hfill2 Hins2 Hlm2 Hfbo2 Hre Hse Hli Hma Hbf s z flush dict D BS p syms
              HW Ho Hq Hz Ha' Hfn Hfl Hpp Hp0 Hdict HD Hk) as (r & Er & Hr & Hnm & BS1 & syms1 & HFR).
  unfold c_deflate_fast in Ec. rewrite Er in Ec. cbn [bind] in Ec.
  destruct r as [[s1 z1] [bs1|]]; cbn [fst snd bs_nm] in *.
  - injection Ec as <- <- <-. subst bs1.
    destruct HFR as (k & x & Z1 & K1 & B1). exists k, x, BS1, syms1. cbn [fin_bs enc_out]. split; [exact Z1|]. split; [exact K1|]. split; [exact B1|discriminate].
  - cbv beta iota delta [loop_res] in Hr.
    destruct Hr as (evs & HFI & Hla & Hai & Hnf & Hss).
    destruct (FI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
    assert (Hwr1 : d_wrap s1 = d_wrap s) by (destruct (FI_sp _ _ _ _ _ _ HFI) as (_ & (_ & E & _)); exact E).
    destruct HFR as (k & x & Z1 & K1 & B1).
    assert (Hal := FR_aligned s s1 x BS1 p Ho Ho1 Hp0 B1).
    assert (Hp1 : 0 <= p + Zlength (enc_from p BS1 false)) by (pose proof (Zlength_nonneg (enc_from p BS1 false)); lia).
    assert (HDk : bytes (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z))) by (apply bytes_hist; auto).
    destruct (Hta s1 z1 flush s' z' bs dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BS ++ BS1)
                syms1 (p + Zlength (enc_from p BS1 false)) Hfbo2 HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl Hnf Hla Hai Hss
                Hdict HDk K1 Hp1 Hal Ec) as (x' & BS2 & syms2 & Z2 & K2 & B2 & F2).
    rewrite Hwr1 in Z2.
    destruct (FR_end s z dict D BS p s1 z1 BS1 k x s' z' 0 x' BS2 syms2 (fin_bs bs) Hzi0 Ha' F2 Z1 B1 Z2)
      as (k3 & x3 & Z3 & K3 & B3).
    { rewrite Z.add_0_r, sublist_nil, app_nil_r. exact K2. }
    { rewrite (quiet_pend s1 Hq1). exact B2. }
    exists k3, x3, (BS1 ++ BS2), syms2. split; [exact Z3|]. split; [exact K3|]. split; [exact B3|].
    intros Hf N. apply app_eq_nil in N. destruct N as [_ N]. exact (F2 Hf N).
Qed.

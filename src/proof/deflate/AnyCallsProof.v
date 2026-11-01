(** * Proof of [any_calls_stmt] (AnyCalls.v): deflate() calls of any kind after deflateInit2_

    From deflate() on the round trips' wide invariant (RTK7Api.api7_deflate_stmt, proved from
    RTK7Nocut.comp_nocut7): the calls api7_deflate_stmt covers (flush Z_NO_FLUSH .. Z_BLOCK, Z_FINISH repeated
    with the rest of the data once given), and the calls it does not: an invalid flush, a call after Z_FINISH
    with another flush or other data, the calls after Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Zlib.proof.roundtrip.RTK7Nocut.
Require Import Zlib.proof.deflate.DetTheory2Inv Zlib.proof.deflate.DetTheory2Params.
Require Zlib.proof.deflate.DetTheory2 Zlib.proof.deflate.DetTheory Zlib.proof.deflate.DetShift.
Require Zlib.proof.deflate.DetGz Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LTApiInit.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.roundtrip.RTK7AStages Zlib.proof.roundtrip.RTK7AComp.
Require Import Zlib.proof.roundtrip.RTDDfXTrail.
Require Zlib.proof.roundtrip.RTK7ACore Zlib.proof.roundtrip.RTK7Hdr Zlib.proof.huffman.Lemmas.
Open Scope cmodel_scope.

(** ** The trailer stage keeps [Mid7], also when it returns Z_STREAM_END

    RTK7DTrail.trailer_ok7 says so for Z_OK only; the same construction holds for Z_STREAM_END (the stream is
    then in FINISH_STATE with the trailer handed out, RTDLTApiDefs.ph3), which the calls after the end need. *)
Lemma trailer_mid7 : forall W HI dict wrap D O inb aout tin tout flush s z s4 z4 c,
  core_facts7 W -> hdr_facts7 HI ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (flush = Z_FINISH -> d_status s = FINISH_STATE) ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_trailer s z flush = Some (s4, z4, c) ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s4 z4.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s4 z4 c HW HH HM Hpd Hfl Hfs Hst E.
  unfold c_deflate_trailer in E.
  destruct (Z.eqb_spec flush Z_FINISH) as [EF|NF].
  2: { cbn [negb] in E. injection E as <- <- <-. exact HM. }
  subst flush. cbn [negb] in E. specialize (Hfs eq_refl).
  destruct (Z.leb_spec (d_wrap s) 0) as [Hw0|Hw0].
  { injection E as <- <- <-. exact HM. }
  assert (Hai0 : z_avail_in z = 0).
  { destruct Hst as [Hst|[_ Hst]]; [|exact Hst]. rewrite Hfs in Hst. unfold FINISH_STATE, BUSY_STATE in Hst. lia. }
  clear Hst.
  destruct HM as (Hz & Hsz1 & Hsz2 & Hsz3 & Hsz4 & HIa).
  pose proof Hz as Hz0.
  destruct Hz as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HWs & Hos & Hwr & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & HlD & Htin & Hfin & Hdz
                   & Hph).
  destruct Hph as [H0 | [Hlf2 [H1 | [H2 | H3]]]].
  { exfalso. destruct H0 as [[[Hs _]|[Hs _]] _]; rewrite Hfs in Hs; unfold FINISH_STATE, INIT_STATE, GZIP_STATE in Hs; lia. }
  { exfalso. destruct H1 as (_ & _ & _ & _ & _ & H & k & HIk & _).
    destruct (hf7_status HI HH _ _ _ _ HIk) as (_ & _ & Hs & _). rewrite Hfs in Hs.
    unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in Hs; lia. }
  { exfalso. destruct H2 as (Hs & _). rewrite Hfs in Hs. unfold FINISH_STATE, BUSY_STATE in Hs. lia. }
  destruct H3 as (_ & Hla & Hsy & Hbv & HOne & Hchk & H & body & Hhg & Hcase).
  pose proof (tk_pend_nil s Hpd) as Hpn.
  destruct Hcase as [[Hdw HO]|[? [? _]]]; [|lia].
  rewrite Hpn, app_nil_r in HO.
  pose proof (cf7_prm W HW s HWs) as Hprm.
  edestruct (tk_put_trailer s (z_adler z) (z_total_in z)) as (s1 & E1 & Hp1 & Ho1 & Hc1 & Ha1 & Hb1);
    eauto; [lia|].
  rewrite E1 in E. cbn [bind] in E.
  assert (Hzo0 := Zlength_nonneg (z_out z)). assert (HO0 := Zlength_nonneg O).
  rewrite Zlength_app in Htout.
  edestruct (flush_pending_ok7 s1 z) as (s' & x & Ef & Hpx & Hlx & Hbx & Ho' & Hc' & Ha' & Hb' & Hpd' & Hpo');
    auto; try lia.
  rewrite Ef in E. cbn [bind] in E.
  assert (Hdw' : d_wrap s' = wrap).
  { destruct Ha1 as (_ & W1 & _), Ha' as (_ & W2 & _). lia. }
  rewrite Hdw' in E. replace (wrap >? 0) with true in E by (symmetry; apply Z.gtb_lt; lia).
  injection E as <- <- <-.
  destruct Ha1 as (As1 & Aw1 & Ag1 & Ai1 & Al1 & Am1), Ha' as (As2 & Aw2 & Ag2 & Ai2 & Al2 & Am2).
  assert (Hc4 : core_eq s (set_d_wrap s' (- wrap))).
  { eapply core_eq_trans; [exact Hc1|]. eapply core_eq_trans; [exact Hc'|]. apply tk_core_eq_wrap. }
  pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & _ & _ & Hla4 & _ & Hsy4 & _).
  cbn [d_lookahead d_sym_next set_d_wrap] in Hla4, Hsy4.
  assert (Hx : x ++ pend s' = trailer wrap (z_adler z) (z_total_in z)) by congruence.
  assert (Hxa : Zlength x <= z_avail_out z) by lia.
  pose proof (tk_zrun7_step inb aout tin tout z x Hz0 Hxa Hbx) as Hz4.
  unfold Mid7. split; [exact Hz4|]. split; [exact Hsz1|]. split; [exact Hsz2|].
  split; [exact Hsz3|]. split; [exact Hsz4|].
  cbn [z_next_in z_out z_total_in z_total_out z_adler].
  unfold Iapi7.
  split; [exact (cf7_frame W HW s _ HWs Hc4)|].
  split; [exact Ho'|].
  split; [exact Hwr|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
  cbn [d_last_flush d_gzhead d_status set_d_wrap].
  split; [rewrite Al2, Al1; exact Hlf|].
  split; [intros h Eh; apply Hgz; congruence|].
  split; [rewrite app_assoc, !Zlength_app; lia|].
  split; [rewrite app_assoc; apply tk_bytes_app; auto|].
  split; [exact HbD|]. split; [exact HlD|]. split; [exact Htin|].
  split; [intros _; exact (Hfin Hfs)|].
  split; [intros Hn; pose proof (core_eq_fields _ _ Hc4) as (_ & _ & _ & _ & B4 & S4 & L4 & _);
          rewrite B4, S4, L4; exact (Hdz Hn)|].
  right. split; [congruence|]. right. right.
  unfold ph3. cbn [d_status d_wrap d_bi_valid d_lookahead d_sym_next set_d_wrap].
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [change (d_bi_valid (set_d_wrap s' (- wrap))) with (d_bi_valid s'); lia|].
  split.
  { intros Hw Hn. apply HOne; auto. rewrite app_assoc in Hn. apply app_eq_nil in Hn. tauto. }
  split; [exact Hchk|].
  exists H, body. split; [exact Hhg|]. right. split; [lia|]. split; [reflexivity|].
  change (pend (set_d_wrap s' (- wrap))) with (pend s').
  rewrite <- !app_assoc, Hx, app_assoc, HO, <- app_assoc. reflexivity.
Qed.

(** ** A call offered the whole object from next_in 0 ends in [Mid7], whatever it returns

    RTK7Api.api7_deflate0 with the trailer stage of [trailer_mid7]: after Z_STREAM_END too the stream satisfies
    [Iapi7] of the data consumed and the output produced. *)
Lemma api7_mid : comp_nocut7_stmt ->
  forall dict wrap D O fin s tin tout adler inb aout flush msg,
    Iapi7 W3 hinv7 dict wrap D O fin s tin tout adler ->
    0 <= flush <= 5 -> rbytes inb -> Zlength inb <= 4294967295 ->
    Zlength D + Zlength inb <= 18446744073709551615 ->
    0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
    (forall R, fin = Some R -> flush = Z_FINISH /\ inb = R) ->
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code) /\
      d_gzhead s' = d_gzhead s /\
      (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
      Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s' z'.
Proof.
  intros CN dict wrap D O fin s tin tout adler inb aout flush msg HIa Hfl Hb Hl Hd Ha Ho Hfin.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (Zlib.proof.roundtrip.RTK7ACore.rtk7_core_nocut Hov CN) as CF.
  pose proof Zlib.proof.roundtrip.RTK7Hdr.rtk7_hdr_ok as HF.
  change (rzcall inb 0 (Zlength inb) tin aout tout adler msg) with (zcall inb 0 (Zlength inb) tin aout tout adler msg).
  change (rbytes inb) with (bytes inb) in Hb.
  pose proof (mid7_start W3 hinv7 dict wrap D O fin s tin tout adler inb aout flush msg HIa Hb Hl Hd Ha Ho Hfin)
    as M0.
  set (z0 := zcall inb 0 (Zlength inb) tin aout tout adler msg) in *.
  assert (Ad0 : z_adler z0 = adler) by reflexivity.
  rewrite c_deflate_stages.
  rewrite (Iapi7_bad_state W3 hinv7 dict wrap D O fin s tin tout adler HF HIa).
  replace (flush >? Z_BLOCK) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
  replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  (* entry *)
  destruct (entry_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s z0 CF HF M0 eq_refl eq_refl eq_refl Hfl)
    as (s1 & z1 & o1 & E1 & G1 & M1 & P1).
  destruct (entry_keep _ _ _ _ _ _ E1) as [Wb1 A1].
  rewrite E1. destruct o1 as [c|].
  { cbn [then_stage bind]. exists s1, z1, c. split; [reflexivity|]. split; [exact G1|].
    split; [rewrite A1, Ad0; auto|exact M1]. }
  cbn [then_stage bind]. destruct P1 as (Q1 & Q2 & Q3 & Q4 & Q5).
  (* the headers *)
  destruct (hdr_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s1 z1 CF HF M1 Q1 Q2 Hfl Q3 Q5)
    as (s2 & z2 & r2 & E2 & Wb2 & A2).
  destruct (hdr_stage_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s1 z1 s2 z2 r2 CF HF M1 Q1 Q2 Hfl Q3 Q5
              E2) as (G2 & M2 & N2 & P2).
  rewrite E2. destruct r2 as [c|].
  { cbn [then_stage bind]. exists s2, z2, c. split; [reflexivity|]. split; [congruence|].
    split; [intros Hr; apply A2; rewrite A1, Ad0; exact Hr|exact M2]. }
  cbn [then_stage bind]. destruct P2 as (R1 & R2).
  (* the compression *)
  destruct (comp_stage_ex7n W3 hinv7 dict wrap D O inb aout tin tout flush s2 z2 CF HF Hb CN M2 R1 Hfl R2)
    as (s3 & z3 & o3 & E3 & G3 & Wb3 & M3 & A3 & P3).
  rewrite E3. destruct o3 as [c|].
  { cbn [bind]. exists s3, z3, c. split; [reflexivity|]. split; [congruence|].
    split; [intros Hr; apply A3, A2; rewrite A1, Ad0; exact Hr|exact M3]. }
  cbn [bind]. destruct P3 as (T1 & T2 & T3).
  (* the trailer *)
  destruct (trailer_ex7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 CF HF M3 T1 Hfl T2 T3)
    as (s4 & z4 & c & E4 & Wb4 & A4 & End4).
  destruct (trailer_ok7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 s4 z4 c CF HF M3 T1 Hfl T2 T3 E4)
    as (G4 & _).
  exists s4, z4, c. split; [exact E4|]. split; [congruence|].
  split; [intros Hr; rewrite A4; apply A3, A2; rewrite A1, Ad0; exact Hr|].
  exact (trailer_mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s3 z3 s4 z4 c CF HF M3 T1 Hfl T2 T3 E4).
Qed.

(** ** deflate(strm, Z_FINISH) in FINISH_STATE with input offered

    The entry stage returns (Z_OK when flushing the pending bytes fills the output, Z_BUF_ERROR otherwise), in
    the state the same call without input reaches at the end of its entry stage: flush_pending does not look at
    the input. *)

(* the stream [z] offered the input object [i] with [a] bytes available *)
Definition zin (z : strm) (i : list Z) (a : Z) : strm := set_z_avail_in (set_z_in z i) a.

Lemma flush_pending_zin : forall s z i a,
  c_flush_pending s (zin z i a) = option_map (fun p => (fst p, zin (snd p) i a)) (c_flush_pending s z).
Proof.
  intros s [zi zn za zt zo zao zto zad zm] i a. unfold c_flush_pending, bind.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|reflexivity].
  unfold zin, out_put; cbn [z_avail_out set_z_avail_in set_z_in z_out].
  destruct (_ =? 0); [reflexivity|].
  destruct (mb_read _ _ _); [|reflexivity].
  destruct (_ <=? _); reflexivity.
Qed.

Lemma entry_zin : forall s z i a s1 z1 o1,
  d_status s = FINISH_STATE -> z_avail_in z = 0 -> 0 < a ->
  c_deflate_entry s z Z_FINISH = Some (s1, z1, o1) ->
  exists m c, c_deflate_entry s (zin z i a) Z_FINISH = Some (s1, set_z_msg (zin z1 i a) m, Some c).
Proof.
  intros s z i a s1 z1 o1 Hs Hz Ha E. unfold c_deflate_entry in *.
  rewrite Hs in *. cbn [Z.eqb Pos.eqb FINISH_STATE Z_FINISH negb andb] in *.
  change (z_avail_out (zin z i a)) with (z_avail_out z).
  change (z_avail_in (zin z i a)) with a.
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (z_avail_out z =? 0).
  { injection E as <- <- <-. exists (Some Z_BUF_ERROR), Z_BUF_ERROR. destruct z; reflexivity. }
  unfold then_stage, bind in *.
  destruct (negb (d_pending (set_d_last_flush s Z_FINISH) =? 0)).
  - rewrite flush_pending_zin.
    destruct (c_flush_pending (set_d_last_flush s Z_FINISH) z) as [[s2 z2]|] eqn:Ef; [|discriminate].
    cbn [option_map fst snd].
    destruct (Zlib.proof.roundtrip.RTK7DStuck.sk_flush_pending _ _ _ _ Ef) as (_ & Hs2 & _).
    cbn in Hs2. rewrite Hs in Hs2.
    change (z_avail_out (zin z2 i a)) with (z_avail_out z2).
    destruct (z_avail_out z2 =? 0).
    + injection E as <- <- <-. exists (z_msg z2), Z_OK. destruct z2; reflexivity.
    + rewrite Hs2 in *. cbn [Z.eqb Pos.eqb FINISH_STATE andb negb] in *.
      change (z_avail_in (zin z2 i a)) with a.
      replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      exists (Some Z_BUF_ERROR), Z_BUF_ERROR.
      destruct (z_avail_in z2 =? 0); cbn [negb] in E; injection E as <- <- <-; destruct z2; reflexivity.
  - rewrite Hz in E. cbn [Z.eqb] in E.
    destruct (guard (in_int (d_last_flush s * 2))); [|discriminate].
    rewrite andb_false_r in E. cbn in E. rewrite Hs, Hz in E. cbn in E. injection E as <- <- <-.
    exists (Some Z_BUF_ERROR), Z_BUF_ERROR. cbn. rewrite Hs.
    replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    destruct z; reflexivity.
Qed.

(** ** The facts of a call that ends in [Mid7] *)
Lemma mid7_ok : forall dict wrap D O inb aout tin tout flush s z,
  Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s z ->
  call_ok7 inb 0 aout tin tout z /\
  Iapi7 W3 hinv7 dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) (fin_of flush inb z) s
    (z_total_in z) (z_total_out z) (z_adler z).
Proof.
  intros dict wrap D O inb aout tin tout flush s z ((Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8) & _ & _ & _ & _ & HI).
  split; [|exact HI].
  pose proof (Zlength_nonneg (z_out z)).
  split; [exact Z1|]. split; [lia|]. split; [exact Z3|]. split; [rewrite Z.sub_0_r; exact Z4|].
  split; [lia|]. split; [exact Z6|]. split; [rewrite Z7, Z6; reflexivity|exact Z8].
Qed.

Lemma sublist_00 : forall (l : list Z), sublist 0 0 l = [].
Proof. reflexivity. Qed.

(** deflate(strm, Z_FINISH) in FINISH_STATE with input offered: the entry stage returns, nothing is consumed,
    the pending bytes flushed are output, and [Iapi7] holds as after the same call without input. *)
Lemma finish_input : comp_nocut7_stmt -> forall wrap D O fin s tin tout adler inb aout msg,
  Iapi7 W3 hinv7 [] wrap D O fin s tin tout adler -> d_status s = FINISH_STATE -> 0 < Zlength inb ->
  0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
  exists s' z' code,
    c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) Z_FINISH = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\ z_adler z' = adler /\ call_ok7 inb 0 aout tin tout z' /\
    exists fin', Iapi7 W3 hinv7 [] wrap (D ++ sublist 0 (z_next_in z') inb) (O ++ z_out z') fin' s'
                   (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros CN wrap D O fin s tin tout adler inb aout msg HIa Hs Hl Ha Ho.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (Zlib.proof.roundtrip.RTK7ACore.rtk7_core_nocut Hov CN) as CF.
  pose proof Zlib.proof.roundtrip.RTK7Hdr.rtk7_hdr_ok as HF.
  assert (Hfin : fin = Some []).
  { destruct HIa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). exact (Hf Hs). }
  assert (HDl : Zlength D <= 18446744073709551615).
  { destruct HIa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
  pose proof (mid7_start W3 hinv7 [] wrap D O fin s tin tout adler [] aout Z_FINISH msg HIa ltac:(constructor)
                ltac:(rewrite Zlength_nil; lia) ltac:(rewrite Zlength_nil; lia) Ha Ho
                ltac:(intros R HR; rewrite Hfin in HR; injection HR as <-; split; reflexivity)) as M0.
  destruct (entry_ex7 W3 hinv7 [] wrap D O [] aout tin tout Z_FINISH s _ CF HF M0 eq_refl eq_refl eq_refl
              ltac:(unfold Z_FINISH; lia)) as (s1 & z1 & o1 & E1 & G1 & M1 & _).
  destruct (entry_zin s (zcall [] 0 (Zlength []) tin aout tout adler msg) inb (Zlength inb) s1 z1 o1 Hs eq_refl Hl E1) as (m & c & E).
  destruct (entry_keep _ _ _ _ _ _ E1) as [_ A1].
  destruct (mid7_ok _ _ _ _ _ _ _ _ _ _ _ M1) as [C1 HI1].
  destruct C1 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8).
  rewrite Zlength_nil in Z2. assert (Hn0 : z_next_in z1 = 0) by lia.
  exists s1, (set_z_msg (zin z1 inb (Zlength inb)) m), c.
  split.
  { change (rzcall inb 0 (Zlength inb) tin aout tout adler msg)
      with (zin (zcall [] 0 (Zlength (@nil Z)) tin aout tout adler msg) inb (Zlength inb)).
    rewrite c_deflate_stages, (Iapi7_bad_state W3 hinv7 [] wrap D O fin s tin tout adler HF HIa).
    change (false || (Z_FINISH >? Z_BLOCK) || (Z_FINISH <? 0)) with false. cbv iota.
    rewrite E. reflexivity. }
  split; [exact G1|].
  split; [cbn; rewrite A1; reflexivity|].
  split.
  { unfold call_ok7, zin; cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out set_z_msg
      set_z_in set_z_avail_in].
    rewrite Hn0 in *. pose proof (Zlength_nonneg inb).
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Z4|].
    split; [lia|]. split; [exact Z6|]. split; [exact Z7|exact Z8]. }
  exists (fin_of Z_FINISH [] z1).
  unfold zin; cbn [z_next_in z_out z_total_in z_total_out z_adler set_z_msg set_z_in set_z_avail_in].
  rewrite Hn0 in HI1 |- *. rewrite sublist_00. rewrite sublist_00 in HI1. exact HI1.
Qed.

(** ** Every call with a valid flush from [Iapi7] (total_out the length of the output kept)

    - not in FINISH_STATE: the call of RTK7Api (Z_FINISH may be given anew);
    - in FINISH_STATE (after Z_FINISH, also after Z_STREAM_END): Z_FINISH without input is the call of RTK7Api,
      Z_FINISH with input is [finish_input], another flush is Z_STREAM_ERROR at entry, nothing changed. *)
Lemma call_any7 : comp_nocut7_stmt -> forall fin wrap D O s tin adler inb aout flush msg,
  Iapi7 W3 hinv7 [] wrap D O fin s tin (Zlength O) adler -> 0 <= flush <= 5 -> bytes inb ->
  Zlength inb <= 4294967295 -> Zlength D + Zlength inb <= 18446744073709551615 ->
  0 <= aout <= 4294967295 -> Zlength O + aout <= 18446744073709551615 ->
  exists s' z' code,
    c_deflate s (rzcall inb 0 (Zlength inb) tin aout (Zlength O) adler msg) flush = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\ call_ok7 inb 0 aout tin (Zlength O) z' /\
    (0 <= adler < 4294967296 -> 0 <= z_adler z' < 4294967296) /\
    exists fin', Iapi7 W3 hinv7 [] wrap (D ++ sublist 0 (z_next_in z') inb) (O ++ z_out z') fin' s'
                   (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros CN fin wrap D O s tin adler inb aout flush msg HIa Hfl Hb Hl Hd Ha Ho.
  pose proof (Zlib.proof.deflate.DetTheory2.Iapi7_tin wrap D O fin s tin (Zlength O) adler HIa) as Htin.
  pose proof (Zlength_nonneg D) as HD0.
  pose proof Zlib.proof.roundtrip.RTK7Hdr.rtk7_hdr_ok as HF.
  match goal with |- ?G =>
    assert (Gen : forall fin0, Iapi7 W3 hinv7 [] wrap D O fin0 s tin (Zlength O) adler ->
                    (forall R, fin0 = Some R -> flush = Z_FINISH /\ inb = R) -> G) end.
  { intros fin0 HI0 Hf0.
    destruct (api7_mid CN [] wrap D O fin0 s tin (Zlength O) adler inb aout flush msg HI0 Hfl Hb Hl Hd Ha Ho Hf0)
      as (s' & z' & code & E & G & A & M).
    destruct (mid7_ok _ _ _ _ _ _ _ _ _ _ _ M) as [C HI'].
    exists s', z', code. split; [exact E|]. split; [exact G|]. split; [exact C|]. split; [exact A|].
    eexists; exact HI'. }
  destruct (Z.eq_dec (d_status s) FINISH_STATE) as [Hs|Hs].
  2: { apply (Gen None); [|discriminate].
       apply (Iapi7_fin _ _ _ _ fin None _ _ _ _ HIa). intros E; contradiction. }
  assert (Hfin : fin = Some []).
  { destruct HIa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). exact (Hf Hs). }
  destruct (Z.eq_dec flush Z_FINISH) as [Ef|Nf].
  2: { exists s, (set_z_msg (rzcall inb 0 (Zlength inb) tin aout (Zlength O) adler msg) (Some Z_STREAM_ERROR)),
         Z_STREAM_ERROR.
       split.
       { rewrite c_deflate_stages, (Iapi7_bad_state W3 hinv7 [] wrap D O fin s tin (Zlength O) adler HF HIa).
         replace (flush >? Z_BLOCK) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold Z_BLOCK; lia).
         replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
         unfold c_deflate_entry. rewrite Hs.
         replace (flush =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; exact Nf).
         reflexivity. }
       split; [reflexivity|].
       split.
       { unfold call_ok7, rzcall, set_z_msg; cbn [z_in z_next_in z_avail_in z_total_in z_avail_out z_out z_total_out].
         rewrite Zlength_nil. pose proof (Zlength_nonneg inb).
         split; [reflexivity|]. split; [lia|]. split; [lia|].
         split; [unfold u64; rewrite Z.mod_small by lia; lia|].
         split; [lia|]. split; [lia|]. split; [lia|constructor]. }
       split; [cbn; auto|].
       exists fin. cbn [rzcall set_z_msg z_next_in z_out z_total_in z_total_out z_adler].
       rewrite sublist_00, !app_nil_r. exact HIa. }
  subst flush.
  destruct (Z.eq_dec (Zlength inb) 0) as [E0|N0].
  - apply (Gen fin HIa). intros R HR. rewrite Hfin in HR. injection HR as <-. split; [reflexivity|].
    apply Zlength_nil_inv; exact E0.
  - destruct (finish_input CN wrap D O fin s tin (Zlength O) adler inb aout msg HIa Hs
                ltac:(pose proof (Zlength_nonneg inb); lia) Ha Ho) as (s' & z' & code & E & G & A & C & fin' & HI').
    exists s', z', code. split; [exact E|]. split; [exact G|]. split; [exact C|].
    split; [rewrite A; auto|]. exists fin'; exact HI'.
Qed.

(** ** The invariant: [Iapi7] of the round trips with no dictionary, any [fin] (FINISH_STATE has [Some []]), the
    output kept short (DetTheory2Inv.Iapi7_shrink; total_out is only counted, DetShift.tout_shift), no gzip header,
    strm->adler 32 bits. *)
Theorem any_calls_thm : any_calls_stmt.
Proof.
  pose proof Zlib.proof.roundtrip.RTK7Nocut.comp_nocut7 as CN.
  destruct Zlib.proof.deflate.DetShift.tout_shift as [TSD _].
  exists (fun s tin adler => exists fin wrap D O,
            Iapi7 W3 hinv7 [] wrap D O fin s tin (Zlength O) adler /\ Zlength O <= 18 /\ d_gzhead s = None /\
            0 <= adler < 4294967296).
  constructor.
  - (* deflateInit2 *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z s z' _ _ _ _ E.
    rewrite (Zlib.proof.deflate.LTApiInit.init_shape level 8 wbits mem strategy a1 a2 a3 a4 a5 z) in E.
    destruct (Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy) eqn:P; [|discriminate].
    destruct a1; [|discriminate]. destruct (a2 && a3 && a4 && a5); [|discriminate].
    destruct (Iapi7_init level 8 wbits mem strategy z P) as (s0 & z0 & E0 & Hgz & Hz0 & HI0).
    rewrite E0 in E. injection E as <- <-. subst z0. cbn [z_total_in z_adler].
    exists None, (Zlib.proof.deflate.LawFacts.wrap_of wbits), [], [].
    split; [exact HI0|]. split; [cbn; lia|]. split; [exact Hgz|].
    destruct (_ =? 2); lia.
  - (* strm->adler *)
    intros s tin adler (fin & wrap & D & O & _ & _ & _ & A). exact A.
  - (* no gzip header *)
    intros s tin adler (fin & wrap & D & O & _ & _ & G & _). exact G.
  - (* deflate *)
    intros s tin adler inb aout tout flush msg (fin & wrap & D & O & HIa & LO & Hgz & Ha) Hf Hb Hl Htin Htl Hao Ht.
    pose proof (Zlib.proof.deflate.DetTheory2.Iapi7_tin wrap D O fin s tin (Zlength O) adler HIa) as HtD.
    pose proof (Zlength_nonneg inb) as Hl0.
    destruct (Z_le_gt_dec 0 flush) as [F0|F0]; [destruct (Z_le_gt_dec flush 5) as [F5|F5]|].
    + rewrite (Zlib.proof.deflate.DetTheory.zcall_shift inb 0 (Zlength inb) tin aout (Zlength O) tout adler msg Ht),
        TSD, Zlib.proof.deflate.DetTheory2.zcall_r.
      destruct (call_any7 CN fin wrap D O s tin adler inb aout flush msg HIa (conj F0 F5) Hb Hl ltac:(lia) Hao
                  ltac:(lia)) as (s' & z' & code & E & G & C & A & fin' & HI').
      rewrite E. cbn [option_map]. exists s', (zsh (tout - Zlength O) z'), code. unfold rsh; cbn [fst snd].
      split; [reflexivity|].
      split; [apply (Zlib.proof.deflate.DetTheory2.call_ok7_okw inb 0 aout tin (Zlength O) tout z' C); lia|].
      destruct (Iapi7_shrink wrap _ _ _ s' _ _ _ HI') as (O' & HO' & LO'); [rewrite G; exact Hgz|].
      unfold zsh, set_z_total_out; cbn [z_total_in z_adler].
      exists fin', wrap, (D ++ sublist 0 (z_next_in z') inb), O'. split; [exact HO'|]. split; [exact LO'|]. split; [rewrite G; exact Hgz|].
      apply A; exact Ha.
    + (* flush > Z_BLOCK: Z_STREAM_ERROR, nothing changed *)
      exists s, (Zlib.proof.deflate.LawFacts.zcall inb 0 (Zlength inb) tin aout tout adler msg), Z_STREAM_ERROR.
      split.
      { unfold c_deflate. replace (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)) with true; [reflexivity|].
        symmetry. apply orb_true_iff. left. apply orb_true_iff. right. apply Z.gtb_lt. unfold Z_BLOCK. lia. }
      split.
      { pose proof (proj1 (Zlib.proof.deflate.DetTheory.call_okw_none inb 0 aout tin tout adler msg None
                             ltac:(lia) ltac:(lia) Ht)) as C.
        rewrite Z.sub_0_r in C. exact C. }
      exists fin, wrap, D, O. auto.
    + (* flush < 0: Z_STREAM_ERROR, nothing changed *)
      exists s, (Zlib.proof.deflate.LawFacts.zcall inb 0 (Zlength inb) tin aout tout adler msg), Z_STREAM_ERROR.
      split.
      { unfold c_deflate. replace (bad_state s || (flush >? Z_BLOCK) || (flush <? 0)) with true; [reflexivity|].
        symmetry. apply orb_true_iff. right. apply Z.ltb_lt. lia. }
      split.
      { pose proof (proj1 (Zlib.proof.deflate.DetTheory.call_okw_none inb 0 aout tin tout adler msg None
                             ltac:(lia) ltac:(lia) Ht)) as C.
        rewrite Z.sub_0_r in C. exact C. }
      exists fin, wrap, D, O. auto.
Qed.

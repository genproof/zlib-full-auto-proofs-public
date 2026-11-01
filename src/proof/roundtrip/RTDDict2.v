(* RT-D part DICT over interface v2 (RTDV2.v, Krt2): deflateSetDictionary (the loop:
   RTDDictLoop.v, with RTDDictIns.v / RTDDictFill.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Export Zlib.proof.roundtrip.RTDLTApiInit.
Require Import Zlib.proof.roundtrip.RTDLTCHuffKit Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDLTCSpecs2 Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCStored2 Zlib.proof.roundtrip.RTDLTCFast2 Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCHuff2 Zlib.proof.roundtrip.RTDLTCRle2 Zlib.proof.roundtrip.RTDLTCLive2 Zlib.proof.roundtrip.RTDLTCInit Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCDict3 Zlib.proof.roundtrip.RTDLTCStillFill Zlib.proof.roundtrip.RTDLTCStillStored Zlib.proof.roundtrip.RTDLTCStillFast Zlib.proof.roundtrip.RTDLTCStillSlow Zlib.proof.roundtrip.RTDLTCStillHuff Zlib.proof.roundtrip.RTDLTCStillRle Zlib.proof.roundtrip.RTDLTCore.
Require Import Zlib.proof.roundtrip.RTDLTHdrKit Zlib.proof.roundtrip.RTDLTHdrStages Zlib.proof.roundtrip.RTDLTHdr.
Require Import Zlib.proof.roundtrip.RTDDictLoop.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The deflate laws' facts for W3 and hinv (copies of the bodies of RTDLTCore.core_theory /
    RTDLTHdr.hdr_theory, whose statements are existential) *)

Lemma dict_W3_facts : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts W3.
Proof.
  intros Hov.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok Htf Hroom) as Hfbo. pose proof fpend2_ok as Hfp.
  pose proof fill_ok as Hfill. destruct lm_ok as [Hins Hlm].
  exact (Build_core_facts W3 W3_prm W3_pos W3_frame W3_init W3_tune W3_dict
           (core_compress3 Hfill Hins Hlm Htal Hfbo Hfp) (W3_still Hfill Hins Hlm Htal Hfbo Hfp)
           (core_live3 Hfp) W3_full W3_params).
Qed.

Section Hdr.
Open Scope cmodel_scope.
Lemma dict_hdr_facts : hdr_facts hinv.
Proof.
  split.
  - exact hinv_frame.
  - exact hinv_status.
  - intros s z H k [Hp [Ho [P0 [Hs [Hbv [Hav [Ht [Hok Hcase]]]]]]]].
    assert (Hav' : 0 <= z_avail_out z) by lia.
    rewrite hdr_stages_eq.
    destruct Hcase as [[Hst [Hw [EH ->]]] | [[Hst [Hw [EH ->]]] | Hi]].
    + (* INIT: zlib header or raw *)
      destruct (zlib_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw) as [s1 [z1 [r1 [E [Es Hpost]]]]].
      rewrite E. subst H. destruct r1 as [c|].
      * exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
      * cbn [then_stage bind]. rewrite (proj1 (busy_rest s1 z1 Es)).
        exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* GZIP *)
      rewrite zlib_id by (rewrite Hst; discriminate). cbn [then_stage bind].
      assert (EH' : H = gz_hdr_bytes (d_gzhead s) (xfl_byte s)) by (rewrite EH; unfold hdr_bytes; rewrite Hw; reflexivity).
      rewrite EH'.
      destruct (gzip_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw Hok) as [s1 [z1 [r1 [E Hr]]]].
      rewrite E. destruct Hr as [[-> Hg] | [Es Hpost]].
      * cbn [then_stage bind]. apply chain_extra. exact Hg.
      * destruct r1 as [c|].
        -- exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
        -- cbn [then_stage bind]. rewrite (proj2 (busy_rest s1 z1 Es)).
           exists s1, z1, None. split; [reflexivity|exact Hpost].
    + (* resume in the middle of a gzip header *)
      pose proof (hinv_gent s z H k Hp Ho P0 Hs Hbv Hav' Ht Hi) as Hg.
      destruct (hinv_status _ _ _ _ Hi) as [_ [_ [Hst _]]].
      assert (N1 : d_status s <> INIT_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      assert (N2 : d_status s <> GZIP_STATE) by (destruct Hst as [S|[S|[S|S]]]; rewrite S; discriminate).
      rewrite zlib_id by assumption. cbn [then_stage bind]. rewrite gzip_id by assumption. cbn [then_stage bind].
      destruct Hst as [S|[S|[S|S]]]; rewrite S in Hg.
      * apply chain_extra. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_name. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply chain_comment. exact Hg.
      * unfold from_extra. rewrite extra_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_name. rewrite name_id by (rewrite S; discriminate). cbn [then_stage bind].
        unfold from_comment. rewrite comment_id by (rewrite S; discriminate). cbn [then_stage bind].
        apply hcrc_stage. exact Hg.
Qed.
End Hdr.

(** ** Blocks without data (the blocks a raw stream may have emitted before deflateSetDictionary) are valid
    after any history *)

Lemma lz_copy_len : forall n dist out, Zlength (F.lz_copy n dist out) = Zlength out + Z.of_nat n.
Proof.
  induction n as [|n IH]; intros dist out; cbn [F.lz_copy]; [lia|].
  rewrite IH, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma sym_data_len : forall out sy, Zlength out <= Zlength (F.sym_data out sy).
Proof.
  intros out [b|len dist]; cbn [F.sym_data].
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite lz_copy_len. lia.
Qed.

Lemma syms_data_len : forall syms out, Zlength out <= Zlength (F.syms_data out syms).
Proof.
  induction syms as [|sy r IH]; intros out; unfold F.syms_data in *; cbn [fold_left]; [lia|].
  specialize (IH (F.sym_data out sy)). pose proof (sym_data_len out sy). lia.
Qed.

Lemma block_data_len : forall out b, Zlength out <= Zlength (F.block_data out b).
Proof.
  intros out [bs|syms|nlen ndist cl toks syms]; cbn [F.block_data].
  - rewrite Zlength_app. pose proof (Zlength_nonneg bs). lia.
  - apply syms_data_len.
  - apply syms_data_len.
Qed.

Lemma expand_len : forall bs out, Zlength out <= Zlength (F.expand out bs).
Proof.
  induction bs as [|b r IH]; intros out; unfold F.expand in *; cbn [fold_left]; [lia|].
  specialize (IH (F.block_data out b)). pose proof (block_data_len out b). lia.
Qed.

Lemma syms_nil : forall wmax ll dl syms,
  F.syms_ok wmax ll dl [] syms -> F.syms_data [] syms = [] -> syms = [].
Proof.
  intros wmax ll dl [|sy r]; [reflexivity|]. intros [Hs _] E.
  exfalso. unfold F.syms_data in E. cbn [fold_left] in E.
  pose proof (syms_data_len r (F.sym_data [] sy)) as L. unfold F.syms_data in L. rewrite E in L.
  destruct sy as [b|len dist]; cbn [F.sym_ok F.sym_data] in *.
  - rewrite Zlength_nil in L. cbn in L. lia.
  - rewrite Zlength_nil in Hs. lia.
Qed.

Lemma block_nil : forall wmax b h,
  F.block_ok wmax [] b -> F.block_data [] b = [] -> F.block_ok wmax h b /\ F.block_data h b = h.
Proof.
  intros wmax [bs|syms|nlen ndist cl toks syms] h Hb E; cbn [F.block_ok F.block_data] in *.
  - destruct bs; [|discriminate]. rewrite app_nil_r. split; [exact Hb|reflexivity].
  - rewrite (syms_nil _ _ _ _ Hb E). split; [exact I|reflexivity].
  - destruct Hb as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    rewrite (syms_nil _ _ _ _ A10 E). split; [|reflexivity].
    repeat (split; [assumption|]). exact I.
Qed.

Lemma blocks_nil : forall wmax bs h,
  F.blocks_ok wmax [] bs -> F.expand [] bs = [] -> F.blocks_ok wmax h bs /\ F.expand h bs = h.
Proof.
  intros wmax bs. induction bs as [|b r IH]; intros h Hb E; [split; [exact I|reflexivity]|].
  destruct Hb as [Hb Hr]. unfold F.expand in *. cbn [fold_left] in *.
  assert (Eb : F.block_data [] b = []).
  { pose proof (expand_len r (F.block_data [] b)) as L. unfold F.expand in L. rewrite E in L.
    rewrite Zlength_nil in L. apply Zlength_nil_inv. pose proof (Zlength_nonneg (F.block_data [] b)). lia. }
  rewrite Eb in Hr, E. destruct (block_nil wmax b h Hb Eb) as [Hb' Eb'].
  destruct (IH h Hr E) as [Hr' Er']. split; [split; [exact Hb'|rewrite Eb'; exact Hr']|rewrite Eb'; exact Er'].
Qed.

(** ** deflateSetDictionary keeps Krt2 *)

Theorem rtd_dict_ok2 : Zlib.proof.huffman.Overlay.overlay_statement -> fill_fspec -> ins_fspec2 ->
  kf_dict_stmt Krt2.
Proof.
  intros Hov Hff Hins wrap s tin tout adler d ain aout msg s' z' code [HI0 HK] Hd Hdl Hain Haout E Hc Hcw.
  pose proof (dict_W3_facts Hov) as HC. pose proof dict_hdr_facts as HH.
  destruct (api_dict W3 hinv wrap s tin tout adler d ain aout msg HC HH HI0 Hd Hdl Hain Haout)
    as (s1 & z1 & code1 & E1 & G1 & _ & _ & _ & HI1).
  change (zcall [] 0 ain tin aout tout adler msg) with (rzcall [] 0 ain tin aout tout adler msg) in E1.
  rewrite E in E1. injection E1 as Es Ez Ec. subst s1 z1 code1.
  pose proof HI0 as (HW & Hok & Hwr & Hw2 & Hbd & Hdl0 & Hlfr & Hgz & Hto & HbO & HbD & Htin & Hfin & Hdz & Hph).
  rewrite Zlength_nil in Htin.
  destruct (Hdz eq_refl) as (Hla & Hsb & Hs00). pose proof (Hs00 eq_refl) as Hss0.
  assert (Hbs0 : d_block_start s = 0) by lia.
  assert (Htin0 : tin = 0) by lia. subst tin.
  assert (Hb : bad_state s = false) by exact (Iapi_bad_state W3 hinv _ _ _ _ _ _ _ _ _ HH HI0).
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
  destruct Hcase as [(Hst & -> & Hdw) | B].
  { (* gzip: Z_STREAM_ERROR, nothing changes *)
    unfold c_deflateSetDictionary in E. rewrite Hb, Hdw in E. cbn in E. injection E as <- <- <-.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HI1|exact HK]. }
  assert (Hx : 0 <= d_wrap s <= 1 /\ d_wrap s = wrap /\ (d_wrap s = 1 -> d_status s = INIT_STATE) /\
               adler_pre (d_wrap s) adler /\ (d_status s = BUSY_STATE -> wrap = 0)).
  { destruct B as [(Hst & Hw1 & Hdw & P0) | (Hst & -> & Hdw & _)].
    - destruct P0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Had).
      split; [lia|]. split; [exact Hdw|]. split; [intros; exact Hst|]. split.
      + unfold adler_pre. split; [|intros; lia]. intros Hw. rewrite Hdw in Hw. rewrite (Had Hw).
        unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence.
      + intros Hb'. rewrite Hst in Hb'. discriminate.
    - split; [lia|]. split; [exact Hdw|]. split; [intros; lia|].
      split; [unfold adler_pre; split; intros; lia|]. auto. }
  clear B. destruct Hx as (Hw1 & Hdw & Hinit & Hadp & Hbusy).
  assert (Htot : 0 <= z_total_in (rzcall [] 0 ain 0 aout tout adler msg) <= 1099511627776) by (cbn; lia).
  destruct (W3_dict s (rzcall [] 0 ain 0 aout tout adler msg) d HW Hw1 Hb Hinit Hss0 Hla Hbs0 Hd Hdl Htot Hadp)
    as (s2 & z2 & k & E2 & HW' & Hae & Hoe & Hsp & Hla' & Hsb' & _ & _ & _ & _).
  rewrite E in E2. injection E2 as Es2 Ez2 Ec2. subst s2 z2 code.
  destruct (dict_f Hff Hins s _ d s' z' (proj1 (proj1 HW)) Hb Hinit Hw1 Hss0 Hla Hbs0 Hd Hdl Htot Hadp E)
    as (Kw & Etr & _ & Hma' & _ & _ & Hch1 & Hch2).
  rewrite (proj2 (Z.eqb_neq wrap 2)) by lia.
  split; [exact (proj1 Hsp)|]. split; [exact G1|].
  rewrite (proj2 (Z.eqb_neq wrap 2)) in HI1 by lia.
  split; [exact HI1|].
  destruct Hae as (Hst' & _ & Hgz' & _).
  destruct Hoe as (Hotr & _ & Hopo).
  destruct HK as (Hgz0 & BS & syms0 & [Hkd Hkh] & Hph0).
  split; [intros Hn2; rewrite Hgz'; exact (Hgz0 Hn2)|].
  pose proof HW' as [[HWs' _] _]. pose proof HWs' as (_ & _ & _ & _ & _ & _ & _ & syms' & Hwt').
  destruct (W_empty s' syms' HWs' Hwt' Hla' Hsb') as [_ ->].
  pose proof Hkd as (_ & _ & _ & Hbok & Hexp & _ & _).
  assert (Hexp0 : F.expand [] BS = []) by (rewrite Hexp, Hss0, Hla, Hbs0; reflexivity).
  destruct (blocks_nil _ BS d Hbok Hexp0) as [Hbok' Hexp'].
  assert (Hlev : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
  assert (Hmat : d_matches s' = d_matches s) by (unfold d_matches; rewrite Etr; reflexivity).
  exists BS, [].
  split; [split|].
  - unfold kdata2. rewrite app_nil_r.
    split; [exact Kw|].
    split; [unfold kmatch; rewrite Hma'; discriminate|].
    split; [exact Hwt'|].
    split; [rewrite (proj1 Hsp); exact Hbok'|].
    split; [rewrite Hexp', Hla', <- Hsb', sublist_same by lia; reflexivity|].
    split; [exact I|].
    cbn [map]. unfold F.syms_data. cbn [fold_left]. rewrite Hexp', Hla', Hma', <- Hsb'.
    destruct (d_level s' =? 0); rewrite sublist_same by lia; reflexivity.
  - unfold khash. split.
    + pose proof (proj1 (proj1 HW)) as (_ & _ & _ & _ & Hwh & _). unfold whash in Hwh.
      rewrite Hlev, Hmat. destruct (d_level s =? 0).
      * destruct Hwh as [[A1 A2]|[[A1 A2]|A1]].
        -- left. split; [exact A1|exact (Hch1 A2)].
        -- right; left. split; [exact A1|exact (Hch2 A2)].
        -- right; right. exact A1.
      * destruct Hwh as [_ A2]. exact (Hch1 A2).
    + intros _ Hl. rewrite Hla' in Hl. unfold MIN_MATCH in Hl. lia.
  - assert (Hbi' : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid; rewrite Hotr; reflexivity).
    destruct Hph0 as [P | [(Pst & HDR & Hh & Ha) | (Pst & _)]].
    + left. rewrite Hst', Hbi'. exact P.
    + right; left. split; [rewrite Hst'; exact Pst|]. exists HDR.
      pose proof (Hbusy Pst) as Hw0.
      split; [unfold khdr in *; rewrite Hw0 in Hh |- *; exact Hh|].
      unfold allbits, pend, bibits, d_pending, d_bi_valid in *. rewrite Hotr, Hopo. exact Ha.
    + exfalso. specialize (Hfin Pst). discriminate.
Qed.

(** ** Interface v1: Krt and Krt2 agree on the states without data (everything in blocks) *)

Lemma kdata_kdata2 : forall dict D BS syms x,
  d_strstart x = d_block_start x -> d_match_available x = 0 ->
  (kdata dict D BS syms x <-> kdata2 dict D BS syms x).
Proof.
  intros dict D BS syms x Hsb Hma. unfold kdata, kdata2. cbv zeta.
  replace (Zlength (dict ++ D) - (d_strstart x + d_lookahead x) + d_strstart x - d_match_available x)
    with (Zlength (dict ++ D) - (d_strstart x + d_lookahead x) +
          (if d_level x =? 0 then d_block_start x else d_strstart x - d_match_available x))
    by (destruct (d_level x =? 0); lia).
  tauto.
Qed.

Lemma KF_KF2 : forall dict wrap O fin x tin tout adler,
  Iapi W3 hinv dict wrap [] O fin x tin tout adler ->
  (KF dict wrap [] O fin x tin tout adler <-> KF2 dict wrap [] O fin x tin tout adler).
Proof.
  intros dict wrap O fin x tin tout adler HI.
  destruct HI as ([[HW _] _] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdz & _).
  destruct (Hdz eq_refl) as (Hla & Hsb & _).
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & syms0 & Hwt).
  destruct (W_empty x syms0 HW Hwt Hla Hsb) as [Hma _].
  unfold KF, KF2, kcore, kcore2. split.
  - intros (G & BS & syms & [Kd Kh] & P). split; [exact G|]. exists BS, syms.
    split; [split; [apply kdata_kdata2; assumption|exact Kh]|exact P].
  - intros (G & BS & syms & [Kd Kh] & P). split; [exact G|]. exists BS, syms.
    split; [split; [apply kdata_kdata2 in Kd; assumption|exact Kh]|exact P].
Qed.

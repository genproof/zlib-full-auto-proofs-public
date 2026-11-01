(* The round trips without the limits of deflate_roundtrip: deflateSetDictionary with a dictionary of up to 2^32 - 1
   bytes keeps K7 (RTK7Defs.v); the window gets its last w_size bytes, the Adler-32 and the history are of the whole
   dictionary. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Import Zlib.proof.roundtrip.RTDLTCDictKit Zlib.proof.roundtrip.RTDLTCDictFrame Zlib.proof.roundtrip.RTDLTCDictIns.
Require Import Zlib.proof.roundtrip.RTDLTCDictProj Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCFill.
Require Import Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDDictIns Zlib.proof.roundtrip.RTDDictFill.
Require Import Zlib.proof.roundtrip.RTDDictLoop Zlib.proof.roundtrip.RTDDict2 Zlib.proof.roundtrip.RTDDict3.
Require Import Zlib.proof.roundtrip.RTDFill Zlib.proof.roundtrip.RTDLm2.
Import ListNotations.
Local Open Scope Z_scope.

(** RTDDictLoop.dict_f for a dictionary of up to 2^32 - 1 bytes: when it is longer than the window, the C code
    reads only its last w_size bytes, so the fill and the loop see at most w_size bytes and the proof is the
    same *)
Lemma dict_f7 (Hff : fill_fspec) (Hins : ins_fspec2) : forall s z d s' z',
    W s -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) -> 0 <= d_wrap s <= 1 ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 4294967295 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
    c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) ->
    kwin d s' /\ d_tr s' = d_tr s /\ d_lookahead s' = 0 /\ d_match_available s' = 0 /\ d_strstart s' = d_block_start s' /\
    d_strstart s' = Z.min (Zlength d) (d_w_size s) /\
    (chain_ok s -> chain_hok s') /\ (chain_ok (slide_hc s) -> chain_hok (slide_hc s')).
Proof.
  intros s z d s' z' HW Hbad Hst Hwrap Hss Hla Hbs Hbytes Hlen Htot Hadl E.
  pose proof HW as (Hprm & Hws & Hwp & Hww & Hwh & Hwm & Hl0 & syms & Hwt).
  assert (Ec : (d_wrap s =? 2) || ((d_wrap s =? 1) && negb (d_status s =? INIT_STATE)) || negb (d_lookahead s =? 0)
               = false).
  { rewrite Hla. destruct (Z.eqb_spec (d_wrap s) 1) as [E1|E1].
    - rewrite (Hst E1), E1. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (d_wrap s) 2)) by lia. reflexivity. }
  unfold c_deflateSetDictionary in E.
  rewrite Hbad in E. cbv zeta in E. rewrite Ec in E.
  cbv beta iota zeta in E.
  set (z1 := if d_wrap s =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) d) else z) in E.
  set (a1 := if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z).
  assert (Ez1 : z1 = mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z) (z_avail_out z)
                          (z_total_out z) a1 (z_msg z)).
  { subst z1 a1. destruct (Z.eqb_spec (d_wrap s) 1) as [E1|E1].
    - rewrite Zlib.proof.adler32.Model.adler32_z_val_ref by (apply Hadl; exact E1). destruct z; reflexivity.
    - destruct z; reflexivity. }
  rewrite Ez1 in E. cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in E.
  clear Ez1 z1.
  pose proof Hprm as (Pwb & Pws & Pwm & Phb & Phs & Phm & Psh & _).
  assert (Hw512 : 512 <= d_w_size s <= 32768).
  { rewrite Pws. split.
    - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hh256 : 256 <= d_hash_size s <= 65536).
  { rewrite Phs. split.
    - change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
    - change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia. }
  pose proof Hwp as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof Hws as (V1 & V2 & V3 & V4 & V5).
  assert (Hins0 : d_insert s = 0) by lia.
  match type of E with bind ?e _ = _ =>
    assert (Hbr : exists s2 off len, e = Some (s2, off, len) /\
      prm s2 /\ wstruct s2 /\ wpos s2 /\ wwin s2 /\ d_insert s2 = 0 /\ d_block_start s2 = 0 /\
      d_wrap s2 = 0 /\ d_strstart s2 = 0 /\ d_lookahead s2 = 0 /\ fw_keep s2 = fw_keep (set_d_wrap s 0) /\
      d_prev s2 = d_prev s /\
      (d_head s2 = d_head s \/ d_head s2 = repeat 0 (Z.to_nat (d_hash_size s))) /\
      len = Z.min (Zlength d) (d_w_size s) /\ off = Zlength d - len /\
      d_window s2 = d_window s /\ d_ins_h s2 = d_ins_h s) end.
  { autorewrite with dproj.
    assert (Hpre : forall s2, d_prev s2 = d_prev s -> d_head s2 = d_head s \/
                     d_head s2 = repeat 0 (Z.to_nat (d_hash_size s)) ->
                   fw_keep s2 = fw_keep (set_d_wrap s 0) -> d_insert s2 = 0 -> d_block_start s2 = 0 ->
                   d_wrap s2 = 0 -> d_strstart s2 = 0 -> d_lookahead s2 = 0 -> d_high_water s2 = d_high_water s ->
                   d_window s2 = d_window s ->
                   prm s2 /\ wstruct s2 /\ wpos s2 /\ wwin s2).
    { intros s2 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10.
      assert (Ew : d_w_size s2 = d_w_size s) by exact (f_equal d_w_size E3).
      assert (Eh : d_hash_size s2 = d_hash_size s) by exact (f_equal d_hash_size E3).
      assert (Ews : d_window_size s2 = d_window_size s) by exact (f_equal d_window_size E3).
      split.
      { exact (prm_keep _ _ E3 Hprm). }
      split.
      { unfold wstruct. rewrite E10, Ew, Ews, E1, Eh. split; [exact V1|]. split; [exact V2|].
        split; [exact V3|]. split; [exact V4|]. destruct E2 as [E2|E2]; rewrite E2; [exact V5|].
        apply Zlength_repeat; lia. }
      split.
      { unfold wpos. rewrite E4, E5, E7, E8, E9, Ews, Ew. unfold MAX_DIST. lia. }
      { pose proof Hww as Hww2. unfold wwin in *. rewrite E7, E8, E9, E10. rewrite Hss, Hla in Hww2. exact Hww2. } }
    destruct (Z.geb_spec (Zlength d) (d_w_size s)) as [Hge|Hlt].
    - destruct (Z.eqb_spec (d_wrap s) 0) as [Ew0|Ew0].
      + rewrite clear_hash_ok by (autorewrite with dproj; lia). rewrite !bind_Some.
        eexists _, _, _. split; [reflexivity|].
        br_fin Hpre.
      + rewrite !bind_Some. eexists _, _, _. split; [reflexivity|]. br_fin Hpre.
    - eexists _, _, _. split; [reflexivity|]. br_fin Hpre. }
  destruct Hbr as (s2 & off & len & Ebr & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14
                   & B15 & B16).
  rewrite Ebr, bind_Some in E. cbv beta iota in E.
  set (zd2 := mkST d off len (z_total_in z) (z_out z) (z_avail_out z) (z_total_out z) a1 (z_msg z)) in E.
  assert (Hz2 : zin_in zd2).
  { unfold zin_in; subst zd2; cbn [z_in z_next_in z_avail_in z_total_in]. split; [exact Hbytes|].
    pose proof (Zlength_nonneg d). lia. }
  assert (Ew2 : d_w_size s2 = d_w_size s) by exact (f_equal d_w_size B10).
  assert (Eh2 : d_hash_size s2 = d_hash_size s) by exact (f_equal d_hash_size B10).
  destruct (fill_step fill_ok s2 zd2 B1 B2 B3 B4 B5 B7 ltac:(subst zd2; cbn [z_avail_in]; lia) Hz2
              ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia)) as
    (s3 & k1 & Ef1 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
  change (mkST (z_in zd2) (z_next_in zd2 + k1) (z_avail_in zd2 - k1) (z_total_in zd2 + k1) (z_out zd2)
            (z_avail_out zd2) (z_total_out zd2) (z_adler zd2) (z_msg zd2)) with (zadv zd2 k1) in Ef1.
  rewrite Ef1, bind_Some in E. cbv beta iota in E.
  (* the hash consistency before the loop, from empty chains *)
  set (c1 := chains 0 (d_head s2) (d_prev s2)).
  set (c2 := heads_le (d_w_size s2) (d_head s2)).
  assert (Hc1h : c1 -> chain_hok s2).
  { intros [C _]. apply chain_hok_nil. intros b Hb. destruct B2 as (_ & _ & _ & _ & L5).
    destruct (C b ltac:(lia)) as [Z0|Z0]; [exact Z0|lia]. }
  assert (Hhs2 : 0 <= d_hash_size s2) by lia.
  assert (HL2 : Zlength (d_head s2) = d_hash_size s2) by (destruct B2 as (_ & _ & _ & _ & L5); exact L5).
  destruct (fill_kw Hff s2 zd2 s3 k1 (repeat 0 (Z.to_nat (d_hash_size s2))) B1 B2 B3 B4 B5 B7
              ltac:(subst zd2; cbn [z_avail_in]; lia) Hz2 ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia)
              ltac:(apply Zlength_repeat; lia) (chain_ok_zeros s2 Hhs2) Ef1) as (FK1 & _ & FK3).
  assert (HJF : JF s2 zd2 c1 c2 (s3, zadv zd2 k1)).
  { split; [|split].
    - unfold Jl. rewrite R9, R11, B8, B9.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
      split; [rewrite R10; exact B6|]. split; [rewrite (f_equal d_wrap R6 : d_wrap s3 = _); exact B7|].
      split; [exact R6|]. split; [lia|]. split; [f_equal; lia|].
      split; [intros Hl; destruct R13; lia|].
      split; [intros C; rewrite R7, R8; exact C|].
      intros C; rewrite R7, (f_equal d_w_size R6 : d_w_size s3 = _); exact C.
    - assert (K0 : kwin [] s2) by (unfold kwin; rewrite B8, B9; split; [rewrite Zlength_nil; lia|intros; lia]).
      specialize (FK1 [] K0). rewrite app_nil_l in FK1.
      rewrite R9, R11, B8, B9. replace (z_next_in zd2 + (0 + (0 + k1))) with (z_next_in zd2 + k1) by lia.
      exact FK1.
    - intros C. split.
      + destruct (fill_kw Hff s2 zd2 s3 k1 (d_head s2) B1 B2 B3 B4 B5 B7
                    ltac:(subst zd2; cbn [z_avail_in]; lia) Hz2 ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia)
                    HL2) as (_ & FC & _).
        { rewrite set_head_eta. destruct B1 as (A1 & A2 & A3 & _).
          apply (chain_ok_of_chains s2 0); try lia; first [exact C | exact A2 | exact A3 | exact HL2]. }
        { exact Ef1. }
        rewrite set_head_eta, <- R7, set_head_eta in FC. exact (FC (Hc1h C)).
      + intros Hl. apply FK3; [exact Hl|]. rewrite R11, B9 in Hl. unfold MIN_MATCH in Hl. lia. }
  destruct (loop FUEL sd_body (s3, zadv zd2 k1)) as [[sF zdF]|] eqn:Eloop; [|discriminate].
  rewrite bind_Some in E. cbv beta iota in E.
  destruct (sdf_loop s2 zd2 c1 c2 Hff Hins Hz2 ltac:(subst zd2; cbn [z_avail_in]; lia)
              ltac:(subst zd2; cbn [z_avail_in z_total_in]; lia) _ _ HJF Eloop) as [JFF HlaF].
  injection E as Es Ez. clear Ez.
  destruct JFF as [JF1 [JF2 JF3]].
  destruct JF1 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  cbn [fst] in HlaF.
  pose proof F3 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  assert (Hn : d_strstart sF + d_lookahead sF = len).
  { unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. subst zd2. cbn [z_avail_in] in F9, F11.
    specialize (F11 ltac:(lia)). lia. }
  assert (Hu : u32 (d_strstart sF + d_lookahead sF) = d_strstart sF + d_lookahead sF).
  { unfold u32. apply Z.mod_small. lia. }
  rewrite Hu in Es.
  assert (Ek : fw_keep sF = fw_keep (set_d_wrap s 0)) by (rewrite F8; exact B10).
  assert (K3 : d_w_size sF = d_w_size s) by exact (f_equal d_w_size Ek).
  assert (K4 : d_hash_size sF = d_hash_size s) by exact (f_equal d_hash_size Ek).
  subst s'.
  assert (Hlen0 : 0 <= len <= Zlength d) by lia.
  split.
  { (* the window *)
    destruct JF2 as [W1 W2]. unfold kwin. autorewrite with dproj. rewrite Z.add_0_r, Hn.
    split; [lia|]. intros i Hi. rewrite (W2 i ltac:(lia)).
    subst zd2. cbn [z_next_in z_in] in *. rewrite Hn in *.
    rewrite Zlength_sublist by lia. rewrite Znth_sublist by lia. f_equal. lia. }
  autorewrite with dproj.
  split; [exact (f_equal d_tr Ek)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [lia|].
  split.
  { intros Hch.
    assert (C : c1).
    { subst c1. destruct B12 as [Eh|Eh]; rewrite Eh.
      - apply chains_of_chain_ok; [exact Hch|exact Hss|exact V5].
      - split; [|intros; lia]. intros i Hi. left. rewrite Znth_repeat'; [reflexivity|].
        rewrite Zlength_repeat in Hi by lia. rewrite Z2Nat.id by lia. lia. }
    apply (chain_hok_mono sF); [exact (proj1 (JF3 C))|..]; autorewrite with dproj; try reflexivity; lia. }
  { intros Hch.
    assert (C : c2).
    { subst c2. rewrite Ew2. destruct B12 as [Eh|Eh]; rewrite Eh.
      - apply heads_le_of_slide; [exact Hch|exact Hss|exact V5].
      - intros i Hi. rewrite Znth_repeat'; [lia|]. rewrite Zlength_repeat in Hi by lia. lia. }
    apply slide_chain_hok; autorewrite with dproj.
    - exact (F13 C).
    - destruct F2 as (_ & _ & _ & _ & L5). exact L5. }
Qed.

(* nothing produced: the empty output is a prefix of some header of [khdr], for any dictionary *)
Lemma khdr_ex7 : forall dict wrap x, 9 <= d_w_bits x <= 15 ->
  exists HDR, khdr dict wrap x HDR /\ [] = sublist 0 0 HDR.
Proof.
  intros dict wrap x Hwb. unfold khdr.
  destruct (Z.eqb_spec wrap 0) as [E0|E0].
  - exists []. split; reflexivity.
  - destruct (Z.eqb_spec wrap 1) as [E1|E1].
    + destruct (zflg_exists (d_w_bits x) (negb match dict with [] => true | _ => false end) Hwb) as [flg Hf'].
      eexists. split; [exists flg; split; [exact Hf'|reflexivity]|].
      rewrite sublist_nil'; reflexivity.
    + eexists. split; [exists 0; split; [left; reflexivity|reflexivity]|].
      rewrite sublist_nil'; reflexivity.
Qed.

(** deflateSetDictionary right after deflateInit2 (or after deflate() calls without data on a raw stream):
    the safety half from cf7_dict, the functional half (the window holds the last bytes of the dictionary, the
    history is the whole dictionary) from dict_f7, as RTDDict2.rtd_dict_ok2 for short dictionaries *)
Theorem rtk7_dict_ok : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts7 W3 -> kf7_dict_stmt K7.
Proof.
  intros Hov HC wrap s tin tout adler d ain aout msg s' z' code HK Hd Hdl Hain Haout E Hc Hcw.
  pose proof (proj1 rtd_lm_ok2) as Hins. pose proof rtd_fill_ok as Hff.
  unfold K7, Stuck7 in HK.
  destruct HK as [[HI0 HK] | (_ & R & Hfn & _)]; [|discriminate].
  pose proof HI0 as Hcp. unfold Iapi7 in Hcp.
  destruct Hcp as (HW & Hok & Hwr & Hw2 & Hbd & Hdl0 & Hlfr & Hgz & Hto & HbO & HbD & HDl & Htin & Hfin & Hdz & Hph).
  destruct Htin as (k0 & Hk0 & Htin). rewrite Zlength_nil in Hk0, Htin.
  assert (Hk00 : k0 = 0) by lia. subst k0. change (u64 (0 + 0)) with 0 in Htin. subst tin.
  destruct (Hdz eq_refl) as (Hla & Hsb & Hs00). pose proof (Hs00 eq_refl) as Hss0.
  assert (Hbs0 : d_block_start s = 0) by lia.
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
  assert (Hb : bad_state s = false).
  { unfold bad_state, c_deflateStateCheck, status_ok.
    destruct Hcase as [(Hst & _)|[(Hst & _)|(Hst & _)]]; rewrite Hst; reflexivity. }
  destruct Hcase as [(Hst & -> & Hdw) | B].
  { (* gzip: Z_STREAM_ERROR, nothing changes *)
    unfold c_deflateSetDictionary in E. rewrite Hb, Hdw in E. cbn in E. injection E as <- <- <-.
    split; [reflexivity|]. split; [reflexivity|]. unfold K7. left. split; [exact HI0|exact HK]. }
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
  destruct Hx as (Hw1 & Hdw & Hinit & Hadp & Hbusy).
  destruct (cf7_dict W3 HC s (rzcall [] 0 ain 0 aout tout adler msg) d HW Hw1 Hb Hinit Hss0 Hla Hbs0 Hd Hdl
              ltac:(cbn; lia) Hadp)
    as (s2 & z2 & k & E2 & HW' & Hae & Hoe & Hsp & Hla' & Hsb' & Hs0' & Hsn' & Hk & Hz').
  rewrite E in E2. injection E2 as Es2 Ez2 Ec2. subst s2 z2 code.
  assert (Htot : 0 <= z_total_in (rzcall [] 0 ain 0 aout tout adler msg) <= 1099511627776) by (cbn; lia).
  destruct (dict_f7 Hff Hins s _ d s' z' (proj1 (proj1 HW)) Hb Hinit Hw1 Hss0 Hla Hbs0 Hd Hdl Htot Hadp E)
    as (Kw & Etr & _ & Hma' & _ & _ & Hch1 & Hch2).
  rewrite (proj2 (Z.eqb_neq wrap 2)) by lia.
  destruct Hae as (Hast & Haw & Hagz & Hagi & Half & Ham).
  destruct Hoe as (Hotr & Hopbm & Hopo).
  split; [exact (proj1 Hsp)|]. split; [exact Hagz|].
  assert (Hpend' : pend s' = pend s) by (unfold pend, d_pending; rewrite Hotr, Hopo; reflexivity).
  assert (Hpe' : d_pending s' = d_pending s) by (unfold d_pending; rewrite Hotr; reflexivity).
  assert (Hbi' : d_bi_valid s' = d_bi_valid s) by (unfold d_bi_valid; rewrite Hotr; reflexivity).
  unfold K7. left. split.
  - (* the safety half *)
    assert (Hok' : outok s').
    { unfold outok, d_pb, d_pending in *. rewrite Hotr, Hopbm, Hopo.
      destruct Hsp as (_ & _ & _ & _ & -> & _). exact Hok. }
    subst z'. cbn [z_total_in z_total_out z_adler rzcall].
    unfold Iapi7.
    split; [exact HW'|]. split; [exact Hok'|]. split; [lia|]. split; [intros; lia|].
    split; [exact Hd|]. split; [exact Hdl|]. split; [rewrite Half; lia|].
    split; [rewrite Hagz; exact Hgz|]. split; [exact Hto|]. split; [exact HbO|]. split; [exact HbD|].
    split; [rewrite Zlength_nil; lia|].
    split; [exists k; split; [lia|rewrite Zlength_nil; reflexivity]|].
    split; [rewrite Hast; intros Hf; destruct B as [(Hst & _)|(Hst & _)]; rewrite Hst in Hf; discriminate|].
    split; [intros _; split; [exact Hla'|split; [exact Hsb'|intros Hdn; apply Hs0'; exact Hdn]]|].
    destruct B as [(Hst & Hwl & _ & P0) | (Hst & -> & _ & Hne)].
    + left. destruct P0 as (_ & _ & _ & _ & Hpe & Hbi & Hsn & _ & _ & _ & Had).
      unfold ph0. rewrite Hast, Haw, Hdw.
      split; [left; split; [exact Hst|lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite Hpe'; exact Hpe|]. split; [rewrite Hbi'; exact Hbi|].
      split; [rewrite Hsn'; exact Hsn|]. split; [exact Hla'|]. split; [exact Hsb'|].
      split; [exact Hs0'|].
      intros Hw. rewrite (Had Hw), Hw. reflexivity.
    + right. split; [rewrite Half; exact Hne|]. right; left. unfold ph2.
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
  - (* the functional half *)
    destruct HK as (Hgz0 & BS & syms0 & [Hkd Hkh] & Hph0).
    split; [intros Hn2; rewrite Hagz; exact (Hgz0 Hn2)|].
    pose proof HW' as [[HWs' _] _]. pose proof HWs' as (_ & _ & _ & _ & _ & _ & _ & syms' & Hwt').
    destruct (W_empty s' syms' HWs' Hwt' Hla' Hsb') as [_ ->].
    pose proof Hkd as (_ & _ & _ & Hbok & Hexp & _ & _).
    assert (Hexp0 : F.expand [] BS = []) by (rewrite Hexp, Hss0, Hla, Hbs0; reflexivity).
    destruct (blocks_nil _ BS d Hbok Hexp0) as [Hbok' Hexp'].
    assert (Hlev : d_level s' = d_level s) by (unfold d_level; rewrite Etr; reflexivity).
    assert (Hmat : d_matches s' = d_matches s) by (unfold d_matches; rewrite Etr; reflexivity).
    exists BS, [].
    split; [split|].
    + unfold kdata3. rewrite app_nil_r.
      split; [exact Kw|].
      split; [unfold kmatch3; rewrite Hma'; discriminate|].
      split; [exact Hwt'|].
      split; [rewrite (proj1 Hsp); exact Hbok'|].
      split; [rewrite Hexp', Hla', <- Hsb', sublist_same by lia; reflexivity|].
      split; [exact I|].
      cbn [map]. unfold F.syms_data. cbn [fold_left]. rewrite Hexp', Hla', Hma', <- Hsb'.
      destruct (d_level s' =? 0); rewrite sublist_same by lia; reflexivity.
    + unfold khash. split.
      * pose proof (proj1 (proj1 HW)) as (_ & _ & _ & _ & Hwh & _). unfold whash in Hwh.
        rewrite Hlev, Hmat. destruct (d_level s =? 0).
        -- destruct Hwh as [[A1 A2]|[[A1 A2]|A1]].
           ++ left. split; [exact A1|exact (Hch1 A2)].
           ++ right; left. split; [exact A1|exact (Hch2 A2)].
           ++ right; right. exact A1.
        -- destruct Hwh as [_ A2]. exact (Hch1 A2).
      * intros _ Hl. rewrite Hla' in Hl. unfold MIN_MATCH in Hl. lia.
    + destruct Hph0 as [(Pst & Pfi & PBS & Pbi & _) | [(Pst & HDR & Hh & Ha) | (Pst & _)]].
      * left. rewrite Hast, Hbi'.
        split; [exact Pst|]. split; [exact Pfi|]. split; [exact PBS|]. split; [exact Pbi|].
        assert (Hpe0 : d_pending s = 0).
        { destruct B as [(_ & _ & _ & P0) | (Hst & _)]; [destruct P0 as (_ & _ & _ & _ & Hp & _); exact Hp|].
          contradiction. }
        assert (Hp0 : pend s' = []).
        { rewrite Hpend'. unfold pend. rewrite Hpe0, Z.add_0_r. apply sublist_nil'. reflexivity. }
        rewrite Hp0. cbn [app]. rewrite Zlength_nil.
        apply khdr_ex7. destruct (cf7_prm W3 HC s' HW') as (A & _). exact A.
      * right; left. split; [rewrite Hast; exact Pst|]. exists HDR.
        pose proof (Hbusy Pst) as Hw0.
        split; [unfold khdr in *; rewrite Hw0 in Hh |- *; exact Hh|].
        unfold allbits, pend, bibits, d_pending, d_bi_valid in *. rewrite Hotr, Hopo. exact Ha.
      * exfalso. specialize (Hfin Pst). discriminate.
Qed.

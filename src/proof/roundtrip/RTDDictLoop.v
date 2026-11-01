(* RT-D part DICT: the loop [while (s->lookahead >= MIN_MATCH) { insert; fill_window }] of
   deflateSetDictionary, functionally: the deflate laws' invariant [Jl] (RTDLTCDict.v) with the window contents
   (the bytes of the dictionary read so far) and, when the chains started empty, their hash consistency. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Import Zlib.proof.roundtrip.RTDLTCDictKit Zlib.proof.roundtrip.RTDLTCDictFrame Zlib.proof.roundtrip.RTDLTCDictIns.
Require Import Zlib.proof.roundtrip.RTDLTCDictProj Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCFill.
Require Import Zlib.proof.roundtrip.RTDDictIns Zlib.proof.roundtrip.RTDDictFill.
Import ListNotations.
Local Open Scope Z_scope.

Lemma set_head_eta x : set_d_head x (d_head x) = x.
Proof. destruct x; reflexivity. Qed.

Lemma chain_ok_zeros x : 0 <= d_hash_size x ->
  chain_ok (set_d_head x (repeat 0 (Z.to_nat (d_hash_size x)))).
Proof.
  intros Hh. exists (fun v => v = 0). split; [|split].
  - intros v ->. left. reflexivity.
  - intros h Hr. autorewrite with dproj in *. rewrite Znth_repeat'; [reflexivity|]. lia.
  - intros q -> Hq. lia.
Qed.

(* the head table empty (all NIL): the chains are trivially hash-consistent *)
Lemma chain_hok_nil x :
  (forall b, 0 <= b < d_hash_size x -> Znth b (d_head x) = 0) -> chain_hok x.
Proof.
  intros H0 b Hb. exists (fun v => v = 0). split; [apply H0; exact Hb|]. intros q -> Hq. lia.
Qed.

Lemma kwin_eq W x y :
  d_window y = d_window x -> d_strstart y + d_lookahead y = d_strstart x + d_lookahead x -> kwin W x -> kwin W y.
Proof. intros Ew Es [K1 K2]. unfold kwin. rewrite Ew, Es. split; [exact K1|exact K2]. Qed.

Section Loop.
Variable s2 : dstate.
Variable zd2 : strm.
Variable c1 c2 : Prop.

Definition JF (a : dstate * strm) : Prop :=
  let (x, zd) := a in
  Jl s2 zd2 c1 c2 (x, zd) /\
  kwin (sublist (z_next_in zd2) (z_next_in zd2 + (d_strstart x + d_lookahead x)) (z_in zd2)) x /\
  (c1 -> chain_hok x /\ (MIN_MATCH <= d_lookahead x -> primed x (d_strstart x))).

Lemma sdf_step (Hff : fill_fspec) (Hins : ins_fspec2) :
  zin_in zd2 -> z_avail_in zd2 <= d_w_size s2 -> z_total_in zd2 + z_avail_in zd2 < 18446744073709551616 ->
  forall a r, JF a -> sd_body a = Some r ->
  match r with inl a' => JF a' | inr b => JF b /\ d_lookahead (fst b) < MIN_MATCH end.
Proof.
  intros Hz2 Hav2 Htot2 [s zd] r [HJ [Hkw Hfc]] Hr.
  pose proof HJ as HJ'.
  destruct HJ' as (Hprm & Hws & Hwp & Hww & Hins0 & Hbs & Hwr & Hkeep & Hn & Ezd & Hmin & Hc1 & Hc2).
  unfold sd_body in Hr.
  destruct (Z.geb_spec (d_lookahead s) MIN_MATCH) as [Hge|Hlt].
  2:{ injection Hr as <-. split; [split; [exact HJ|split; assumption]|cbn [fst]; lia]. }
  pose proof Hwp as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  pose proof Hws as (V1 & V2 & V3 & V4 & V5).
  assert (Ew : d_w_size s = d_w_size s2) by exact (f_equal d_w_size Hkeep).
  assert (Hw512 : 512 <= d_w_size s <= 32768).
  { destruct Hprm as (Pwb & Pws & _). rewrite Pws. split.
    - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  unfold MIN_MATCH in Hge.
  assert (Eu : u32 (d_lookahead s - (MIN_MATCH - 1)) = d_lookahead s - 2).
  { unfold u32, MIN_MATCH. apply Z.mod_small. lia. }
  rewrite Eu in Hr.
  destruct (sd_ins_ok s (d_strstart s) (d_lookahead s - 2) Hprm Hws ltac:(lia) ltac:(lia) ltac:(lia))
    as (h & P & H & Eloop & LP & LH & Hlt' & Hch').
  { intros i Hi. apply Hww. lia. }
  (* the hash consistency after the insertions (when the chains started empty) *)
  assert (Hhok3 : c1 -> chain_hok (shf (set_d_head (set_d_prev (set_d_ins_h s h) P) H)
                                      (d_strstart s + (d_lookahead s - 2)) (d_strstart s + (d_lookahead s - 2) + 2))).
  { intros C. destruct (Hfc C) as [Hhok Hpr].
    assert (Hm : chain_hok (shf s (d_strstart s) (d_strstart s + (d_lookahead s - 2) + 2))).
    { apply (chain_hok_mono s); [exact Hhok|..]; unfold shf; autorewrite with dproj; try reflexivity; lia. }
    exact (sd_ins_hok Hins s (d_strstart s) (d_lookahead s - 2) _ Hprm Hws ltac:(lia) ltac:(lia) ltac:(lia)
             (fun i Hi => Hww i ltac:(lia)) Hins0 Hbs ltac:(lia) (Hc1 C) Hm
             (Hpr ltac:(unfold MIN_MATCH; lia)) Eloop). }
  rewrite Eloop, bind_Some in Hr. cbv beta iota zeta in Hr.
  set (s3 := set_d_lookahead (set_d_strstart (set_d_head (set_d_prev (set_d_ins_h s h) P) H)
                               (d_strstart s + (d_lookahead s - 2))) (MIN_MATCH - 1)) in Hr.
  assert (Hprm3 : prm s3) by exact Hprm.
  assert (Hws3 : wstruct s3).
  { subst s3. unfold wstruct. autorewrite with dproj. split; [exact V1|]. split; [exact V2|].
    split; [exact V3|]. split; lia. }
  assert (Hwp3 : wpos s3).
  { subst s3. unfold wpos. autorewrite with dproj. unfold MIN_MATCH. lia. }
  assert (Hww3 : wwin s3).
  { subst s3. unfold wwin. autorewrite with dproj. intros i Hi. apply Hww. unfold MIN_MATCH in Hi. lia. }
  assert (Hi3 : d_insert s3 = 0) by (subst s3; autorewrite with dproj; exact Hins0).
  assert (Hwr3 : d_wrap s3 = 0) by (subst s3; autorewrite with dproj; exact Hwr).
  subst zd.
  destruct (fill_step fill_ok s3 (zadv zd2 (d_strstart s + d_lookahead s)) Hprm3 Hws3 Hwp3 Hww3 Hi3 Hwr3)
    as (s' & k & Efill & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13).
  { subst s3. autorewrite with dproj. cbn [zadv z_avail_in]. unfold MIN_MATCH. lia. }
  { apply zadv_zin; [exact Hz2|lia|exact Htot2]. }
  { cbn [zadv z_avail_in z_total_in]. lia. }
  change (mkST _ _ _ _ _ _ _ _ _) with (zadv (zadv zd2 (d_strstart s + d_lookahead s)) k) in Efill.
  assert (Hhs : 0 <= d_hash_size s3).
  { subst s3; autorewrite with dproj. destruct Hprm as (_ & _ & _ & _ & -> & _). apply Z.pow_nonneg; lia. }
  destruct (fill_kw Hff s3 (zadv zd2 (d_strstart s + d_lookahead s)) s' k (repeat 0 (Z.to_nat (d_hash_size s3)))
              Hprm3 Hws3 Hwp3 Hww3 Hi3 Hwr3) as (FK1 & _ & FK3).
  { subst s3. autorewrite with dproj. cbn [zadv z_avail_in]. unfold MIN_MATCH. lia. }
  { apply zadv_zin; [exact Hz2|lia|exact Htot2]. }
  { cbn [zadv z_avail_in z_total_in]. lia. }
  { apply Zlength_repeat. exact Hhs. }
  { apply chain_ok_zeros. exact Hhs. }
  { exact Efill. }
  rewrite Efill, bind_Some in Hr. injection Hr as <-.
  rewrite zadv_zadv.
  subst s3. autorewrite with dproj in R6, R7, R8, R9, R10, R11. unfold MIN_MATCH in R11.
  cbn [zadv z_avail_in] in R12, R13.
  assert (Ew' : d_w_size s' = d_w_size s) by exact (f_equal d_w_size R6).
  destruct Hz2 as (Z1 & Z2 & Z3 & Z4 & Z5).
  split; [|split].
  - (* Jl, as RTDLTCDict.sd_loop *)
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    split; [lia|]. split; [rewrite (f_equal d_wrap R6 : d_wrap s' = _); exact Hwr|].
    split; [rewrite R6, fw_keep_ins; exact Hkeep|].
    split; [lia|]. split; [f_equal; lia|].
    split; [intros Hl; destruct R13 as [R13|R13]; lia|].
    split.
    + intros C. rewrite R7, R8, R9. apply Hch'. exact (Hc1 C).
    + intros C. rewrite R7, Ew'.
      destruct (sd_ins_heads s (d_strstart s) (d_lookahead s - 2) (fun v => v <= d_w_size s)
                  Hprm Hws ltac:(lia) ltac:(lia) ltac:(lia)) as (h' & P' & H' & Eloop' & HQ).
      { intros i Hi. apply Hww. lia. }
      { exact (Hc2 C). }
      { intros p Hp. cbv beta. lia. }
      rewrite Eloop in Eloop'.
      apply (f_equal (fun o => match o with Some r => d_head (fst r) | None => nil end)) in Eloop'.
      cbv beta iota in Eloop'. cbn [fst] in Eloop'. autorewrite with dproj in Eloop'. subst H'. exact HQ.
  - (* the window *)
    specialize (FK1 _ ltac:(apply (kwin_eq _ s); [autorewrite with dproj; reflexivity
                                                 |autorewrite with dproj; unfold MIN_MATCH; lia|exact Hkw])).
    cbn [zadv z_next_in z_in] in FK1. rewrite sublist_rejoin in FK1 by lia.
    replace (z_next_in zd2 + (d_strstart s' + d_lookahead s')) with
      (z_next_in zd2 + (d_strstart s + d_lookahead s) + k) by lia.
    exact FK1.
  - intros C. split.
    + destruct (fill_kw Hff _ (zadv zd2 (d_strstart s + d_lookahead s)) s' k
                  (d_head (set_d_lookahead (set_d_strstart (set_d_head (set_d_prev (set_d_ins_h s h) P) H)
                               (d_strstart s + (d_lookahead s - 2))) (MIN_MATCH - 1)))
                  Hprm3 Hws3 Hwp3 Hww3 Hi3 Hwr3) as (_ & FC & _).
      { autorewrite with dproj. cbn [zadv z_avail_in]. unfold MIN_MATCH. lia. }
      { apply zadv_zin; [split; auto|lia|exact Htot2]. }
      { cbn [zadv z_avail_in z_total_in]. lia. }
      { autorewrite with dproj. lia. }
      { rewrite set_head_eta. apply (chain_ok_of_chains _ (d_strstart s + (d_lookahead s - 2)));
          autorewrite with dproj; try lia;
          first [exact (Hch' (Hc1 C)) | destruct Hprm as (A1 & A2 & A3 & _); first [exact A2 | exact A3 | lia]]. }
      { exact Efill. }
      autorewrite with dproj in FC.
      replace (set_d_head s' H) with s' in FC by (rewrite <- R7; symmetry; apply set_head_eta).
      apply FC.
      eapply chain_hok_mono; [exact (Hhok3 C)|..]; unfold shf; autorewrite with dproj; try reflexivity; unfold MIN_MATCH; lia.
    + intros Hla. apply FK3; [exact Hla|unfold MIN_MATCH in Hla; lia].
Qed.

Lemma sdf_loop (Hff : fill_fspec) (Hins : ins_fspec2) :
  zin_in zd2 -> z_avail_in zd2 <= d_w_size s2 -> z_total_in zd2 + z_avail_in zd2 < 18446744073709551616 ->
  forall a b, JF a -> loop FUEL sd_body a = Some b -> JF b /\ d_lookahead (fst b) < MIN_MATCH.
Proof.
  intros Hz Hav Ht a b Ha E. apply loop_runs in E.
  induction E as [a r Hb | a a' r Hb Hr IH].
  - exact (sdf_step Hff Hins Hz Hav Ht a (inr r) Ha Hb).
  - apply IH. exact (sdf_step Hff Hins Hz Hav Ht a (inl a') Ha Hb).
Qed.

End Loop.

Lemma slide_chain_hok x :
  heads_le (d_w_size x) (d_head x) -> Zlength (d_head x) = d_hash_size x -> chain_hok (slide_hc x).
Proof.
  intros Hle HL. apply chain_hok_nil. intros b Hb. unfold slide_hc in *. autorewrite with dproj in *.
  rewrite Znth_map by lia. unfold slide_entry.
  specialize (Hle b ltac:(lia)). unfold NIL. destruct (Z.geb_spec (Znth b (d_head x)) (d_w_size x)); lia.
Qed.

(** deflateSetDictionary from strstart = lookahead = block_start = 0 (the safety run: RTDLTCDict3.dict_ok3):
    the window holds the last min(dictLength, w_size) bytes of the dictionary, all of it in the "blocks" part
    (strstart = block_start, lookahead 0), and the chains are hash-consistent if they were valid before *)
Lemma dict_f (Hff : fill_fspec) (Hins : ins_fspec2) : forall s z d s' z',
    W s -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) -> 0 <= d_wrap s <= 1 ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 32768 -> 0 <= z_total_in z <= 1099511627776 -> adler_pre (d_wrap s) (z_adler z) ->
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

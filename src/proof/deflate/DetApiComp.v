(** * deflate() on [Iapi] without its size limits: stage 8, the compression stage

    [LTApiComp.comp_stage_ok] (with the block_done branch [LTApiBd.bd_tail_ok]) for [MidW] (DetApiMid.v), by
    [cf_compress_wide] / [cf_still_wide] (DetWide.v) instead of cf_compress / cf_still; strm->adler stays below
    2^32 (raw: unchanged; zlib / gzip: the checksum of the data). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetApiMid.
Require Import Zlib.proof.deflate.LTApiComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** strm->adler after the compression function reads [X]: unchanged for a raw stream, else the checksum of the
    data, below 2^32 either way. *)
Lemma cw_adler_range : forall wrap D a X, 0 <= wrap <= 2 -> 0 <= a < 4294967296 ->
  chk_ok wrap (D ++ X) (adler_upd wrap a X) -> bytes (D ++ X) -> 0 <= adler_upd wrap a X < 4294967296.
Proof.
  intros wrap D a X Hw Ha Hc Hb. destruct (Z.eq_dec wrap 0) as [->|Hn].
  - exact Ha.
  - assert (E : 2 ^ 32 = 4294967296) by reflexivity. rewrite <- E.
    apply (chk_ok_range wrap (D ++ X)); auto; lia.
Qed.

(** [LTApiComp.cs_mid_after] for [MidW]: the invariant after the compression function, the data grown by the
    [k] bytes consumed, the output by [x]; strm->adler stays below 2^32. *)
Lemma csw_mid_after : forall W HI dict wrap D O inb nin aout tin tout flush s z s3 z' k x,
  MidW W HI dict wrap D O inb nin aout tin tout flush s z -> bytes inb ->
  d_pending s = 0 -> d_last_flush s <> -2 ->
  ph2 dict wrap (D ++ sublist nin (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z) ->
  zstep wrap z z' k x -> bytes x -> 0 <= z_avail_out z' ->
  W s3 -> outok s3 -> d_wrap s3 = wrap -> d_gzhead s3 = d_gzhead s -> d_bi_valid s3 <= 7 ->
  (d_last_flush s3 = d_last_flush s \/ d_last_flush s3 = -1) ->
  (d_status s3 = BUSY_STATE \/
   (d_status s3 = FINISH_STATE /\ d_lookahead s3 = 0 /\ d_sym_next s3 = 0 /\ flush = Z_FINISH /\
    z_avail_in z' = 0)) ->
  ((D ++ sublist nin (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
   d_lookahead s3 = 0 /\ d_strstart s3 = d_block_start s3 /\ (dict = [] -> d_strstart s3 = 0)) ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s3 z' /\
  (0 <= z_adler z < 4294967296 -> 0 <= z_adler z' < 4294967296).
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z s3 z' k x
    HM Hbin Hpend Hlf2 Hph Hzs Hbx Hao' HW3 Hok3 Hwr3 Hgz3 Hbi3 Hlf3 Hst3 Hdz3.
  destruct HM as [Hz [Hnin [HDb [Haout [HOb HIa]]]]].
  destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
  destruct HIa as (HW & Hok & Hwr & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HtinR & Hfin & _).
  destruct Hzs as (Ein & Hk & En & Eai & Eti & Ead & Eo & Exle & Eao & Eto & Emsg).
  destruct Hph as (_ & _ & _ & HOne & Hchk & H & body & Hhg & HOH).
  rewrite cs_pend_nil, app_nil_r in HOH by exact Hpend.
  rewrite Hin in *.
  set (n := z_next_in z) in *.
  pose proof (Zlength_nonneg D). pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg dict).
  pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg (z_out z)).
  assert (Hx : Zlength x = z_avail_out z - z_avail_out z') by (rewrite Eao; lia).
  assert (HlD1 : Zlength (D ++ sublist nin n inb) = Zlength D + (n - nin))
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (Hti' : z_total_in z' = z_total_in z + k).
  { rewrite Eti. unfold u64. apply Z.mod_small. lia. }
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Eto. unfold u64. apply Z.mod_small. rewrite Zlength_app in Htout. lia. }
  assert (HD2 : D ++ sublist nin (n + k) inb = (D ++ sublist nin n inb) ++ sublist n (n + k) inb).
  { rewrite <- app_assoc, <- (sublist_split nin n (n + k)) by lia. reflexivity. }
  assert (HbX : bytes (sublist n (n + k) inb)) by (apply Forall_sublist; exact Hbin).
  assert (Hchk2 : chk_ok wrap ((D ++ sublist nin n inb) ++ sublist n (n + k) inb)
                    (adler_upd wrap (z_adler z) (sublist n (n + k) inb))).
  { apply chk_ok_upd; assumption. }
  split.
  2:{ intros Ha. rewrite Ead. apply (cw_adler_range wrap (D ++ sublist nin n inb)); auto.
      apply cs_bytes_app; assumption. }
  split; [|split; [exact Hnin|split; [exact HDb|split; [exact Haout|split; [exact HOb|]]]]].
  { (* zrunw *)
    unfold zrunw. rewrite Ein, En, Eai, Hti', Eo, Eao, Zlength_app, Hx.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [rewrite Hto', Hx; lia|]. apply cs_bytes_app; assumption. }
  rewrite En, HD2, Eo, Hti', Hto', Ead.
  split; [exact HW3|]. split; [exact Hok3|]. split; [exact Hwr|]. split; [exact Hw2|]. split; [exact Hbd|].
  split; [exact Hdl|]. split; [destruct Hlf3 as [-> | ->]; lia|].
  split; [rewrite Hgz3; exact Hgz|].
  split; [rewrite Htout, !Zlength_app; lia|].
  split; [rewrite app_assoc; apply cs_bytes_app; assumption|].
  split; [apply cs_bytes_app; assumption|].
  split; [rewrite Zlength_app, (Zlength_sublist n (n + k)) by lia; lia|].
  split.
  { intros HF. destruct Hst3 as [HB | (_ & _ & _ & Hfl & Hai')].
    - rewrite HB in HF. discriminate.
    - unfold fin_of. rewrite Hfl, Z.eqb_refl. rewrite En, Eai in *. f_equal. apply sublist_nil_gen. lia. }
  split; [exact Hdz3|].
  right. split; [destruct Hlf3 as [-> | ->]; [exact Hlf2|discriminate]|].
  assert (HO2 : wrap <> 0 -> (O ++ z_out z ++ x) <> []).
  { intros Hw0 Hnil. apply (HOne Hw0). rewrite app_assoc in Hnil. apply app_eq_nil in Hnil. tauto. }
  assert (HOH2 : (O ++ z_out z ++ x) ++ pend s3 = H ++ (body ++ x ++ pend s3)).
  { rewrite app_assoc, HOH, <- !app_assoc. reflexivity. }
  destruct Hst3 as [HB | (HF & Hla & Hsn & _ & _)].
  - right; left. split; [exact HB|]. split; [exact Hwr3|]. split; [exact Hbi3|]. split; [exact HO2|].
    split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|exact HOH2].
  - right; right. split; [exact HF|]. split; [exact Hla|]. split; [exact Hsn|]. split; [exact Hbi3|].
    split; [exact HO2|]. split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|].
    left. split; [exact Hwr3|exact HOH2].
Qed.

(** [LTApiBd.bd_tail_ok_gen] for [MidW] (by [flush_pending_wide]): the block_done branch; strm->adler is not
    changed. *)
Lemma bdw_tail_ok_gen : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  (forall a H k, ~ HI s a H k) ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    z_adler z' = z_adler z /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z CF M NHI Hst Hq Hsym Hla Hss Hai Hf1 Hf2 Hfr.
  destruct (midw_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ M) as [Hao1 Hto1].
  destruct M as (Zr & Nn & Sz1 & Sa & Sz2 & I).
  destruct I as (HW & HO & Hw & Hw2 & Hbd & Hld & Hlf & Hgz & Htout & HbO & HbD & Htin & Hfin & Hdz & Hph).
  assert (P2 : d_last_flush s <> -2 /\
    ph2 dict wrap (D ++ sublist nin (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z)).
  { destruct Hph as [P0 | [Hne [P1 | [P2 | P3]]]].
    - exfalso. destruct P0 as [[[E _]|[E _]] _]; rewrite Hst in E; discriminate.
    - exfalso. destruct P1 as (_ & _ & _ & _ & _ & H & k & HH & _). exact (NHI _ _ _ HH).
    - auto.
    - exfalso. destruct P3 as [E _]. rewrite Hst in E. discriminate. }
  clear Hph. destruct P2 as (Hne & _ & Hdw & _ & HOne & Hchk & H & body & Hhg & Hpend).
  destruct (bd_first_ok W s flush CF HW HO Hq Hsym Hla Hss)
    as (s2 & E2 & W2 & O2 & B2 & S2 & Wr2 & G2 & L2 & La2 & Ss2 & St2).
  destruct Zr as (Zin & Hni & Hai' & Hti & Hao0 & Hzo & Hto & Hbz).
  assert (Hzo0 : 0 <= Zlength (z_out z)) by apply Zlength_nonneg.
  assert (HO0 : 0 <= Zlength O) by apply Zlength_nonneg.
  assert (Htout' : z_total_out z = Zlength O + Zlength (z_out z)) by (rewrite Htout, Zlength_app; reflexivity).
  destruct (flush_pending_wide s2 z O2 B2 Hao1 Hto1)
    as (s3 & x & E3 & Hp & Hx & Bx & O3 & C3 & A3 & B3 & Pd3 & _).
  destruct A3 as (A31 & A32 & A33 & _ & A35 & _).
  assert (W3 : W s3) by exact (cf_frame W CF _ _ W2 C3).
  destruct (core_eq_fields _ _ C3) as (_ & _ & _ & _ & F35 & F36 & F37 & _).
  assert (La3 : d_lookahead s3 = 0) by congruence.
  assert (Ss3 : d_strstart s3 = d_block_start s3) by congruence.
  assert (St3 : d_strstart s3 = d_strstart s \/ d_strstart s3 = 0) by (destruct St2; [left|right]; congruence).
  set (z3 := mkST (z_in z) (z_next_in z) (z_avail_in z) (z_total_in z) (z_out z ++ x)
                  (z_avail_out z - Zlength x) (z_total_out z + Zlength x) (z_adler z) (z_msg z)) in E3.
  assert (Hps : pend s = []).
  { destruct Hq as (Q1 & Q2 & _). unfold pend. rewrite Q1, Q2. apply sublist_nil. }
  rewrite Hps, app_nil_r in Hpend.
  (* the state after the call, whichever way it ends *)
  assert (MID : forall s4, W s4 -> outok s4 -> d_status s4 = BUSY_STATE -> d_wrap s4 = wrap ->
      d_gzhead s4 = d_gzhead s -> -2 <= d_last_flush s4 <= 5 -> d_last_flush s4 <> -2 -> d_bi_valid s4 <= 7 ->
      pend s4 = pend s3 -> d_lookahead s4 = 0 -> d_strstart s4 = d_block_start s4 ->
      (d_strstart s4 = d_strstart s \/ d_strstart s4 = 0) ->
      MidW W HI dict wrap D O inb nin aout tin tout flush s4 z3).
  { intros s4 W4 O4 S4 Wr4 G4 L4 L4' B4 P4 La4 Ss4 St4.
    assert (Hx0 : 0 <= Zlength x) by apply Zlength_nonneg.
    split; [|split; [exact Nn|split; [exact Sz1|split; [exact Sa|split; [exact Sz2|]]]]].
    { unfold zrunw, z3; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out].
      rewrite Zlength_app. split; [exact Zin|]. split; [exact Hni|]. split; [exact Hai'|].
      split; [exact Hti|]. split; [lia|]. split; [lia|]. split; [lia|].
      apply Forall_app; auto. }
    assert (Hfz : fin_of flush inb z3 = fin_of flush inb z) by reflexivity.
    rewrite Hfz. unfold Iapi, z3.
    cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler].
    rewrite app_assoc.
    split; [exact W4|]. split; [exact O4|]. split; [exact Hw|]. split; [exact Hw2|]. split; [exact Hbd|].
    split; [exact Hld|]. split; [exact L4|]. split; [rewrite G4; exact Hgz|].
    split; [rewrite Zlength_app; lia|]. split; [apply Forall_app; auto|]. split; [exact HbD|].
    split; [exact Htin|]. split; [rewrite S4; intro E; discriminate|].
    split; [intros Hn; split; [assumption|split; [assumption|]];
            intros Hdn; destruct St4 as [E|E]; [rewrite E; exact (proj2 (proj2 (Hdz Hn)) Hdn)|exact E]|].
    right. split; [exact L4'|]. right; left.
    split; [exact S4|]. split; [exact Wr4|]. split; [exact B4|].
    split; [intros Hw0; specialize (HOne Hw0); intro E; apply app_eq_nil in E; tauto|].
    split; [exact Hchk|].
    exists H, (body ++ pend s2). split; [exact Hhg|].
    rewrite P4, <- app_assoc, <- Hp, Hpend, app_assoc. reflexivity. }
  unfold bd_tail.
  match goal with |- context [bind ?X _] => assert (E2' : X = Some s2) by exact E2 end.
  rewrite E2'. cbn [bind]. rewrite E3. cbn [bind].
  destruct (Z.eqb_spec (z_avail_out z3) 0) as [Ez|Ez];
    change (z_avail_out z3) with (z_avail_out z - Zlength x) in Ez.
  - exists (set_d_last_flush s3 (-1)), z3, (Some Z_OK). split; [reflexivity|].
    change (d_gzhead (set_d_last_flush s3 (-1))) with (d_gzhead s3).
    split; [congruence|]. split; [|split; [cbn; congruence|split; [reflexivity|left; reflexivity]]].
    apply MID.
    + exact (cf_frame W CF _ _ W3 (bd_core_eq_lf s3 (-1))).
    + exact (bd_outok_lf s3 (-1) O3).
    + cbn. congruence.
    + cbn. congruence.
    + cbn. congruence.
    + cbn. lia.
    + cbn. lia.
    + change (d_bi_valid (set_d_last_flush s3 (-1))) with (d_bi_valid s3). lia.
    + reflexivity.
    + exact La3.
    + exact Ss3.
    + exact St3.
  - exists s3, z3, None. split; [reflexivity|].
    split; [congruence|]. split; [|split; [congruence|split; [reflexivity|right; split; [reflexivity|lia]]]].
    apply MID; try assumption; try congruence; try lia.
Qed.

(** [LTApiBd.bd_tail_ok] for [MidW]. *)
Lemma bdw_tail_ok : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  d_status s = BUSY_STATE -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  z_avail_in z = 0 -> flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
  exists s' z' o, bd_tail s z flush = Some (s', z', o) /\ d_gzhead s' = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s' z' /\ d_status s' = BUSY_STATE /\
    z_adler z' = z_adler z /\
    (o = Some Z_OK \/ (o = None /\ d_pending s' = 0)).
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z CF HF M Hst.
  apply (bdw_tail_ok_gen W HI dict wrap D O inb nin aout tin tout flush s z CF M); [|exact Hst].
  intros a H k HH. destruct (hf_status HI HF s a H k HH) as (_ & _ & Hs & _).
  rewrite Hst in Hs. destruct Hs as [E|[E|[E|E]]]; discriminate.
Qed.

(** ** The compression stage *)

Lemma compw_stage_ok : forall W HI dict wrap D O inb nin aout tin tout flush s z,
  core_facts W -> cf_compress_wide W -> cf_still_wide W -> hdr_facts HI -> bytes inb ->
  MidW W HI dict wrap D O inb nin aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\ d_gzhead s3 = d_gzhead s /\
    MidW W HI dict wrap D O inb nin aout tin tout flush s3 z3 /\
    (0 <= z_adler z < 4294967296 -> 0 <= z_adler z3 < 4294967296) /\
    match o with
    | Some c => c = Z_OK
    | None => d_pending s3 = 0 /\ (flush = Z_FINISH -> d_status s3 = FINISH_STATE) /\
              (d_status s3 = BUSY_STATE \/ (d_status s3 = FINISH_STATE /\ z_avail_in z3 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb nin aout tin tout flush s z HC HCW HSW HH Hbin HM Hpend Hfl Hst.
  pose proof HM as HM0.
  destruct HM as [Hz [Hnin [HDb [Haout [HOb HIa]]]]].
  destruct HIa as (HW & Hok & Hwr & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HtinR & Hfin & Hdz & Hph).
  destruct Hph as [Hp0 | [Hlf2 [Hp1 | [Hp2 | Hp3]]]].
  - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|[Hst _]]; cs_states.
  - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
    destruct (hf_status _ HH _ _ _ _ HHI) as (_ & _ & Hs & _).
    destruct Hst as [Hst|[Hst _]]; cs_states.
  - (* BUSY *)
    pose proof Hp2 as Hp2'.
    destruct Hp2' as (HB & Hwrs & Hbi & _ & Hchk & _).
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    2: { exists s, z, None. split; [reflexivity|]. split; [reflexivity|]. split; [exact HM0|].
         split; [exact (fun Ha => Ha)|].
         split; [exact Hpend|]. split; [|left; exact HB].
         intros H4. exfalso. rewrite H4, HB in Hc. simpl in Hc. rewrite orb_true_r in Hc. discriminate. }
    pose proof (midw_zwide _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hbin) as Hzw.
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (HCW s z flush HW Hok Hq Hfl Hzw ltac:(lia) Hadp)
      as (s' & z' & bs & evs & Hcf & Hcp).
    rewrite Hcf. cbn [bind].
    destruct Hcp as (HW' & Hok' & _ & Hapi & (k & x & Hzs & Hbx & Hubk) & _ & Hev & Hbs).
    destruct Hapi as (Ast & Awr & Agz & _ & Alf & _).
    rewrite Hwrs in Hzs, Awr.
    assert (Hao' : 0 <= z_avail_out z') by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&_); lia).
    assert (Hdz3 : (D ++ sublist nin (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
                   d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (dict = [] -> d_strstart s' = 0)).
    { intros Hnil.
      assert (HdzO : D ++ sublist nin (z_next_in z) inb = [] ->
                     d_lookahead s = 0 /\ d_strstart s = d_block_start s)
        by (intros E; destruct (Hdz E) as (A & B & _); split; assumption).
      destruct (cs_dz W s s' k evs flush (D ++ sublist nin (z_next_in z) inb)
                  (sublist (z_next_in z) (z_next_in z + k) inb) HC HW HW' Hev Hubk
                  ltac:(destruct Hzs as (_ & Hk & _); rewrite Zlength_sublist; lia) HdzO Hnil) as [La Ss].
      split; [exact La|]. split; [exact Ss|].
      intros Hd0.
      apply app_eq_nil in Hnil as [HD0 Hx0].
      destruct (Hdz HD0) as (La0 & Ss0 & S00).
      assert (Hk0 : k = 0).
      { destruct Hzs as (_ & Hk & _). pose proof (f_equal (@Zlength Z) Hx0) as L.
        rewrite Zlength_nil, Zlength_sublist in L by lia. lia. }
      apply (HSW s z flush s' z' bs HW Hok Hq Hfl Hzw ltac:(lia) Hadp Hcf).
      - unfold ub; lia.
      - exact (S00 Hd0).
      - destruct Hzs as (_ & _ & En & _). lia. }
    destruct bs.
    + (* need_more *)
      assert (Hnm : d_bi_valid s' <= 7) by apply Hbs.
      destruct (z_avail_out z' =? 0).
      * edestruct (csw_mid_after W HI dict wrap D O inb nin aout tin tout flush s z (set_d_last_flush s' (-1))) as [HMa Hada];
          [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz|exact Hnm|right; reflexivity
          |left; rewrite <- HB; exact Ast|exact Hdz3|].
        -- eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_lf].
        -- eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact HMa|].
           split; [exact Hada|reflexivity].
      * edestruct (csw_mid_after W HI dict wrap D O inb nin aout tin tout flush s z (s')) as [HMa Hada];
          [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'|exact HW'|exact Hok'|exact Awr|exact Agz|exact Hnm|left; exact Alf
          |left; rewrite <- HB; exact Ast|exact Hdz3|].
        eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact HMa|].
        split; [exact Hada|reflexivity].
    + (* block_done *)
      destruct Hbs as (_ & Hf0 & Hf4 & Hai0 & Hub & Hq' & Hsn).
      destruct (csw_mid_after W HI dict wrap D O inb nin aout tin tout flush s z s' z' k x
                  HM0 Hbin Hpend Hlf2 Hp2 Hzs Hbx Hao' HW' Hok' Awr Agz ltac:(apply Hq') (or_introl Alf)
                  (or_introl (eq_trans Ast HB)) Hdz3) as [HM' Had'].
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla Hss].
      destruct (bdw_tail_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HH HM' ltac:(rewrite Ast; exact HB)
                  Hq' Hsn Hla Hss Hai0 Hf0 Hf4 Hfl)
        as (s'' & z'' & o & Hbt & Hgz'' & HM'' & Hst'' & Had'' & Ho).
      exists s'', z'', o. split; [exact Hbt|]. split; [rewrite Hgz''; exact Agz|]. split; [exact HM''|].
      split; [rewrite Had''; exact Had'|].
      destruct Ho as [-> | [-> Hp]]; [reflexivity|].
      split; [exact Hp|]. split; [intros; contradiction|left; exact Hst''].
    + (* finish_started *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hbi0 & Hao0 & _).
      rewrite Hao0, Z.eqb_refl.
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla _].
      edestruct (csw_mid_after W HI dict wrap D O inb nin aout tin tout flush s z (set_d_last_flush (set_d_status s' FINISH_STATE) (-1))) as [HMa Hada];
        [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
        |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |right; reflexivity
        |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
        |exact Hdz3|].
      * eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_status_lf].
      * change (d_bi_valid s' <= 7). lia.
      * eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact HMa|].
        split; [exact Hada|reflexivity].
    + (* finish_done *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hq' & Hbi0).
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla _].
      edestruct (csw_mid_after W HI dict wrap D O inb nin aout tin tout flush s z (set_d_status s' FINISH_STATE)) as [HMa Hada];
        [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
        |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |left; exact Alf
        |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
        |exact Hdz3|].
      * eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_status].
      * change (d_bi_valid s' <= 7). lia.
      * eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact HMa|].
        split; [exact Hada|].
        split; [apply Hq'|]. split; [intros; reflexivity|right; split; [reflexivity|exact Hai0]].
  - (* FINISH: nothing to compress *)
    destruct Hp3 as (HF & Hla & _).
    destruct Hst as [HB | [_ Hai0]]; [exfalso; rewrite HB in HF; cs_states|].
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    { exfalso. rewrite Hai0, Hla, HF in Hc. simpl in Hc. rewrite andb_false_r in Hc. discriminate. }
    exists s, z, None. split; [reflexivity|]. split; [reflexivity|]. split; [exact HM0|].
    split; [exact (fun Ha => Ha)|].
    split; [exact Hpend|]. split; [intros; exact HF|right; split; [exact HF|exact Hai0]].
Qed.

(* The compression stage of deflate() (c_deflate_compress) on the streams of RTK7Defs when the compression
   functions end as LTDefs.cpost says (never in deflate_stored's old defect RTK7Defs.stored_cut, which fix F9
   removes): the stage runs and keeps Mid7, w_bits, and strm->adler below 2^32.  RTK7DComp.comp_stage_ex7 with
   the stuck alternative excluded; used by RTK7Api to show that every deflate() call on Iapi7 is defined. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DComp.
Require Import Zlib.proof.roundtrip.RTK7DStoredW.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The loops of the model must never be unfolded (binary fuel): only [bind] is. *)
Local Strategy expand [bind].
Local Strategy opaque [loop loop2].

(* flush_pending only writes to next_out: strm->adler is unchanged *)
Lemma fp_adler7 : forall s z s' z', c_flush_pending s z = Some (s', z') -> z_adler z' = z_adler z.
Proof.
  intros s z s' z' H. unfold c_flush_pending, out_put in H. wdec; reflexivity.
Qed.

(* the tail of the stage after a block_done (bd_tail: an empty block or _tr_align, then flush_pending) keeps
   w_bits and strm->adler *)
Lemma bd_tail_keep7 : forall s z flush s' z' o, bd_tail s z flush = Some (s', z', o) ->
  d_w_bits s' = d_w_bits s /\ z_adler z' = z_adler z.
Proof.
  intros s z flush s' z' o H. unfold bd_tail in H.
  match type of H with bind ?X _ = _ => destruct X as [s1|] eqn:E1; [|discriminate H] end.
  cbn [bind] in H.
  destruct (c_flush_pending s1 z) as [[s2 z2]|] eqn:E2; [|discriminate H]. cbn [bind] in H.
  assert (W1 : d_w_bits s1 = d_w_bits s).
  { unfold c_clear_hash in E1. wdec; wclose. }
  pose proof (wb_flush_pending _ _ _ _ E2) as W2. pose proof (fp_adler7 _ _ _ _ E2) as A2.
  destruct (z_avail_out z2 =? 0); injection H as <- <- <-; cbn; split; congruence.
Qed.

(* strm->adler after the stage, from the check value Mid7 keeps once the header is written (ph2, ph3): below
   2^32 for zlib and gzip streams; a raw stream ([wrap] 0) keeps the value it had *)
Lemma mid7_adler_range : forall W HI dict wrap D O inb aout tin tout flush s z a,
  hdr_facts7 HI -> Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  (d_status s = BUSY_STATE \/ d_status s = FINISH_STATE) ->
  (wrap = 0 -> z_adler z = a) -> 0 <= a < 4294967296 -> 0 <= z_adler z < 4294967296.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z a HH HM Hst Hw0 Ha.
  destruct HM as (_ & _ & _ & _ & _ & HIa).
  destruct HIa as (_ & _ & Hwr & _ & _ & _ & _ & _ & _ & _ & HbD & _ & _ & _ & _ & Hph).
  assert (Hchk : chk_ok wrap (D ++ sublist 0 (z_next_in z) inb) (z_adler z)).
  { destruct Hph as [Hp0 | [_ [Hp1 | [Hp2 | Hp3]]]].
    - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|Hst]; cs_states7.
    - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
      destruct (hf7_status HI HH _ _ _ _ HHI) as (_ & _ & Hs & _).
      destruct Hst as [Hst|Hst]; cs_states7.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 Hp2))))).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hp3)))))). }
  destruct (Z.eq_dec wrap 0) as [E|Hn]; [rewrite (Hw0 E); exact Ha|].
  assert (E : 2 ^ 32 = 4294967296) by reflexivity. rewrite <- E.
  apply (chk_ok_range wrap _ _ ltac:(lia) Hchk HbD).
Qed.

Lemma comp_stage_ex7n : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts7 W -> hdr_facts7 HI -> bytes inb ->
  (forall s z flush,
    W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_ok7 z ->
    0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs) ->
  Mid7 W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\
    d_gzhead s3 = d_gzhead s /\ d_w_bits s3 = d_w_bits s /\
    Mid7 W HI dict wrap D O inb aout tin tout flush s3 z3 /\
    (0 <= z_adler z < 4294967296 -> 0 <= z_adler z3 < 4294967296) /\
    match o with
    | Some c => c = Z_OK
    | None => d_pending s3 = 0 /\ (flush = Z_FINISH -> d_status s3 = FINISH_STATE) /\
              (d_status s3 = BUSY_STATE \/ (d_status s3 = FINISH_STATE /\ z_avail_in z3 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z HC HH Hbin HCP HM Hpend Hfl Hst.
  pose proof HM as HM0.
  destruct HM as [Hz [Hil [HDil [Hal [HOal HIa]]]]].
  destruct HIa as (HW & Hok & Hwr & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HDl & HtinR & Hfin & Hdz & Hph).
  destruct Hph as [Hp0 | [Hlf2 [Hp1 | [Hp2 | Hp3]]]].
  - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|[Hst _]]; cs_states7.
  - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
    destruct (hf7_status HI HH _ _ _ _ HHI) as (_ & _ & Hs & _).
    destruct Hst as [Hst|[Hst _]]; cs_states7.
  - (* BUSY *)
    pose proof Hp2 as Hp2'.
    destruct Hp2' as (HB & Hwrs & Hbi & _ & Hchk & _).
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    2: { exists s, z, None. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
         split; [exact HM0|]. split; [intros Ha; exact Ha|].
         split; [exact Hpend|]. split; [|left; exact HB].
         intros H4. exfalso. rewrite H4, HB in Hc. simpl in Hc. rewrite orb_true_r in Hc. discriminate. }
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    pose proof (mid7_zin_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hbin) as Hzin.
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (HCP s z flush HW Hok Hq Hfl Hzin ltac:(lia) Hadp) as (s' & z' & bs & evs & Hcf & Hcp).
    rewrite Hcf. cbn [bind].
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    destruct Hcp as (HW' & Hok' & Hprm & Hapi & (k & x & Hzs & Hbx & Hubk) & _ & Hev & Hbs).
    assert (Hwb : d_w_bits s' = d_w_bits s) by apply Hprm.
    destruct Hapi as (Ast & Awr & Agz & _ & Alf & _).
    rewrite Hwrs in Hzs, Awr.
    assert (Had0 : wrap = 0 -> z_adler z' = z_adler z).
    { intros E. destruct Hzs as (_ & _ & _ & _ & _ & Ead & _). rewrite Ead, E. reflexivity. }
    assert (Hao' : 0 <= z_avail_out z') by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&_); lia).
    assert (Hdz3 : (D ++ sublist 0 (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
                   d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (dict = [] -> d_strstart s' = 0)).
    { intros Hnil.
      assert (HdzO : D ++ sublist 0 (z_next_in z) inb = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s)
        by (intros E; destruct (Hdz E) as (A & B & _); split; assumption).
      destruct (cs_dz7 W s s' k evs flush (D ++ sublist 0 (z_next_in z) inb)
                  (sublist (z_next_in z) (z_next_in z + k) inb) HC HW HW' Hev Hubk
                  ltac:(destruct Hzs as (_ & Hk & _); rewrite Zlength_sublist; lia) HdzO Hnil) as [La Ss].
      split; [exact La|]. split; [exact Ss|].
      intros Hd0.
      apply app_eq_nil in Hnil as [HD0 Hx0].
      destruct (Hdz HD0) as (La0 & Ss0 & S00).
      assert (Hk0 : k = 0).
      { destruct Hzs as (_ & Hk & _). pose proof (f_equal (@Zlength Z) Hx0) as L.
        rewrite Zlength_nil, Zlength_sublist in L by lia. lia. }
      apply (cf7_still W HC s z flush s' z' bs HW Hok Hq Hfl Hzin ltac:(lia) Hadp Hcf).
      - unfold ub; lia.
      - exact (S00 Hd0).
      - destruct Hzs as (_ & _ & En & _). lia. }
    destruct bs.
    + (* need_more *)
      assert (Hnm : d_bi_valid s' <= 7) by apply Hbs.
      destruct (z_avail_out z' =? 0).
      * assert (HM3 : Mid7 W HI dict wrap D O inb aout tin tout flush (set_d_last_flush s' (-1)) z').
        { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
            |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz|exact Hnm|right; reflexivity
            |left; rewrite <- HB; exact Ast|exact Hdz3].
          eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_lf]. }
        eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact Hwb|].
        split; [exact HM3|]. split; [|reflexivity].
        intros Ha. apply (mid7_adler_range _ _ _ _ _ _ _ _ _ _ _ _ _ (z_adler z) HH HM3); [|exact Had0|exact Ha].
        left. rewrite <- HB. exact Ast.
      * assert (HM3 : Mid7 W HI dict wrap D O inb aout tin tout flush s' z').
        { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
            |exact Hbx|exact Hao'|exact HW'|exact Hok'|exact Awr|exact Agz|exact Hnm|left; exact Alf
            |left; rewrite <- HB; exact Ast|exact Hdz3]. }
        eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact Hwb|].
        split; [exact HM3|]. split; [|reflexivity].
        intros Ha. apply (mid7_adler_range _ _ _ _ _ _ _ _ _ _ _ _ _ (z_adler z) HH HM3); [|exact Had0|exact Ha].
        left. rewrite <- HB. exact Ast.
    + (* block_done *)
      destruct Hbs as (_ & Hf0 & Hf4 & Hai0 & Hub & Hq' & Hsn).
      assert (HM' : Mid7 W HI dict wrap D O inb aout tin tout flush s' z').
      { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'|exact HW'|exact Hok'|exact Awr|exact Agz|apply Hq'|left; exact Alf
          |left; rewrite <- HB; exact Ast|exact Hdz3]. }
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla Hss].
      destruct (bd_tail_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ HC HH HM' ltac:(rewrite Ast; exact HB) Hq' Hsn Hla Hss
                  Hai0 Hf0 Hf4 Hfl)
        as (s'' & z'' & o & Hbt & Hgz'' & HM'' & Hst'' & Ho).
      destruct (bd_tail_keep7 _ _ _ _ _ _ Hbt) as [Hwb'' Had''].
      exists s'', z'', o. split; [exact Hbt|]. split; [rewrite Hgz''; exact Agz|].
      split; [congruence|]. split; [exact HM''|].
      split.
      { intros Ha. apply (mid7_adler_range _ _ _ _ _ _ _ _ _ _ _ _ _ (z_adler z) HH HM''); [left; exact Hst''| |exact Ha].
        intros E. rewrite Had''. exact (Had0 E). }
      destruct Ho as [-> | [-> Hp]]; [reflexivity|].
      split; [exact Hp|]. split; [intros; contradiction|left; exact Hst''].
    + (* finish_started *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hbi0 & Hao0 & _).
      rewrite Hao0, Z.eqb_refl.
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla _].
      assert (HM3 : Mid7 W HI dict wrap D O inb aout tin tout flush
                      (set_d_last_flush (set_d_status s' FINISH_STATE) (-1)) z').
      { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |right; reflexivity
          |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
          |exact Hdz3].
        * eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_status_lf].
        * change (d_bi_valid s' <= 7). lia. }
      eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact Hwb|].
      split; [exact HM3|]. split; [|reflexivity].
      intros Ha. apply (mid7_adler_range _ _ _ _ _ _ _ _ _ _ _ _ _ (z_adler z) HH HM3); [|exact Had0|exact Ha].
      right. reflexivity.
    + (* finish_done *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hq' & Hbi0).
      destruct (cs_ub0_7 _ _ HC HW' Hub) as [Hla _].
      assert (HM3 : Mid7 W HI dict wrap D O inb aout tin tout flush (set_d_status s' FINISH_STATE) z').
      { eapply cs_mid_after7; [exact HM0|exact Hbin|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |left; exact Alf
          |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
          |exact Hdz3].
        -- eapply (cf7_frame _ HC); [exact HW'|apply cs_core_eq_status].
        -- change (d_bi_valid s' <= 7). lia. }
      eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [exact Hwb|].
      split; [exact HM3|].
      split.
      { intros Ha. apply (mid7_adler_range _ _ _ _ _ _ _ _ _ _ _ _ _ (z_adler z) HH HM3); [|exact Had0|exact Ha].
        right. reflexivity. }
      split; [apply Hq'|]. split; [intros; reflexivity|right; split; [reflexivity|exact Hai0]].
  - (* FINISH: nothing to compress *)
    destruct Hp3 as (HF & Hla & _).
    destruct Hst as [HB | [_ Hai0]]; [exfalso; rewrite HB in HF; cs_states7|].
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    { exfalso. rewrite Hai0, Hla, HF in Hc. simpl in Hc. rewrite andb_false_r in Hc. discriminate. }
    exists s, z, None. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact HM0|]. split; [intros Ha; exact Ha|].
    split; [exact Hpend|]. split; [intros; exact HF|right; split; [exact HF|exact Hai0]].
Qed.

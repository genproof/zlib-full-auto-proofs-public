(* RT-D part DEFLATE: copy of RTDLTApiComp.v with the output space bound aout <= 2097152 (kfacts) instead of 1048576. *)
(** * deflate_api theory: stage 8 of deflate(), the compression stage

    [c_deflate_compress] after the header stages (BUSY, or FINISH with all input consumed; nothing pending): the
    compression function by [cf_compress] ([cpost]), the status FINISH for finish_started / finish_done, the
    block_done branch by [bd_tail_ok]; Z_OK, or on to the trailer with nothing pending. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDfXBd.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Helpers *)

(** status / last_flush change nothing [core_eq] sees. *)
Lemma cs_core_eq_status : forall s x, core_eq s (set_d_status s x).
Proof. intros s x. split; [reflexivity|split; [reflexivity|split; reflexivity]]. Qed.

Lemma cs_core_eq_lf : forall s x, core_eq s (set_d_last_flush s x).
Proof. intros s x. split; [reflexivity|split; [reflexivity|split; reflexivity]]. Qed.

Lemma cs_core_eq_status_lf : forall s x y, core_eq s (set_d_last_flush (set_d_status s x) y).
Proof. intros s x y. split; [reflexivity|split; [reflexivity|split; reflexivity]]. Qed.

Lemma cs_pend_nil : forall s, d_pending s = 0 -> pend s = [].
Proof. intros s H. unfold pend. rewrite H, Z.add_0_r. apply sublist_nil. Qed.

Lemma cs_bytes_app : forall a b, bytes a -> bytes b -> bytes (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app; auto. Qed.

(** [ub s = 0] on a state of the invariant: nothing in the lookahead, all in blocks. *)
Lemma cs_ub0 : forall W s, core_facts W -> W s -> ub s = 0 ->
  d_lookahead s = 0 /\ d_strstart s = d_block_start s.
Proof.
  intros W s HC HW Hub. pose proof (cf_pos _ HC s HW) as Hp. unfold ub in Hub. lia.
Qed.

(** The blocks emitted cover a nonnegative number of bytes. *)
Lemma cs_sum_len_nonneg : forall s flush evs, prm s -> Forall (ev_ok s flush) evs -> 0 <= sum_len evs.
Proof.
  intros s flush evs HP HF. unfold sum_len.
  induction HF as [|e evs He HF IH]; cbn [fold_right]; [lia|].
  destruct e as [g t syms buf sl last | g len last]; cbn [ev_len ev_ok] in *.
  - destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _).
    destruct buf as [b|].
    + destruct Hbuf as (Hz & _). pose proof (Zlength_nonneg b). lia.
    + destruct HP as (Hwb & Hws & _).
      assert (2 ^ 9 <= 2 ^ d_w_bits s) by (apply Z.pow_le_mono_r; lia).
      unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hbuf. cbn in *. lia.
  - destruct He as (_ & Hl & _). lia.
Qed.

(** Without data consumed so far and in the call, the state after the compression function has everything
    read in blocks ([ub = 0]). *)
Lemma cs_dz : forall W s s' k evs flush (Dz X : list Z), core_facts W -> W s -> W s' -> Forall (ev_ok s flush) evs ->
  k + ub s = sum_len evs + ub s' -> Zlength X = k ->
  (Dz = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s) ->
  Dz ++ X = [] -> d_lookahead s' = 0 /\ d_strstart s' = d_block_start s'.
Proof.
  intros W s s' k evs flush Dz X HC HW HW' Hev Hub HX Hdz Hnil.
  apply app_eq_nil in Hnil as [-> ->]. rewrite Zlength_nil in HX. subst k.
  destruct (Hdz eq_refl) as [La Ss].
  pose proof (cs_sum_len_nonneg s flush evs (cf_prm _ HC s HW) Hev).
  pose proof (cf_pos _ HC s' HW'). unfold ub in *. lia.
Qed.

(** The invariant after the compression function: the data grew by the [k] bytes consumed, the output by [x]. *)
Lemma cs_mid_after : forall W HI dict wrap D O inb aout tin tout flush s z s3 z' k x,
  Mid W HI dict wrap D O inb aout tin tout flush s z -> bytes inb -> aout <= 2097152 ->
  d_pending s = 0 -> d_last_flush s <> -2 ->
  ph2 dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) s (z_total_in z) (z_adler z) ->
  zstep wrap z z' k x -> bytes x -> 0 <= z_avail_out z' ->
  W s3 -> outok s3 -> d_wrap s3 = wrap -> d_gzhead s3 = d_gzhead s -> d_bi_valid s3 <= 7 ->
  (d_last_flush s3 = d_last_flush s \/ d_last_flush s3 = -1) ->
  (d_status s3 = BUSY_STATE \/
   (d_status s3 = FINISH_STATE /\ d_lookahead s3 = 0 /\ d_sym_next s3 = 0 /\ flush = Z_FINISH /\
    z_avail_in z' = 0)) ->
  ((D ++ sublist 0 (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
   d_lookahead s3 = 0 /\ d_strstart s3 = d_block_start s3 /\ (dict = [] -> d_strstart s3 = 0)) ->
  Mid W HI dict wrap D O inb aout tin tout flush s3 z'.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z s3 z' k x
    HM Hbin Haout Hpend Hlf2 Hph Hzs Hbx Hao' HW3 Hok3 Hwr3 Hgz3 Hbi3 Hlf3 Hst3 Hdz3.
  destruct HM as [Hz [HDb [HOb HIa]]].
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
  assert (HlD1 : Zlength (D ++ sublist 0 n inb) = Zlength D + n)
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (Hti' : z_total_in z' = z_total_in z + k).
  { rewrite Eti. unfold u64. apply Z.mod_small. lia. }
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Eto. unfold u64. apply Z.mod_small. rewrite Zlength_app in Htout. lia. }
  assert (HD2 : D ++ sublist 0 (n + k) inb = (D ++ sublist 0 n inb) ++ sublist n (n + k) inb).
  { rewrite <- app_assoc, <- (sublist_split 0 n (n + k)) by lia. reflexivity. }
  assert (HbX : bytes (sublist n (n + k) inb)) by (apply Forall_sublist; exact Hbin).
  split; [|split; [exact HDb|split; [exact HOb|]]].
  { (* zrun *)
    unfold zrun. rewrite Ein, En, Eai, Hti', Eo, Eao, Zlength_app, Hx.
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
  assert (Hchk2 : chk_ok wrap ((D ++ sublist 0 n inb) ++ sublist n (n + k) inb)
                    (adler_upd wrap (z_adler z) (sublist n (n + k) inb))).
  { apply chk_ok_upd; assumption. }
  assert (HOH2 : (O ++ z_out z ++ x) ++ pend s3 = H ++ (body ++ x ++ pend s3)).
  { rewrite app_assoc, HOH, <- !app_assoc. reflexivity. }
  destruct Hst3 as [HB | (HF & Hla & Hsn & _ & _)].
  - right; left. split; [exact HB|]. split; [exact Hwr3|]. split; [exact Hbi3|]. split; [exact HO2|].
    split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|exact HOH2].
  - right; right. split; [exact HF|]. split; [exact Hla|]. split; [exact Hsn|]. split; [exact Hbi3|].
    split; [exact HO2|]. split; [exact Hchk2|]. exists H, (body ++ x ++ pend s3). split; [exact Hhg|].
    left. split; [exact Hwr3|exact HOH2].
Qed.

Ltac cs_states := unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE,
  BUSY_STATE, FINISH_STATE in *; lia.

(** The compression stage: [cf_compress] ([cpost]) and the block_done branch ([bd_tail_ok]). *)
Lemma comp_stage_ok : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W -> hdr_facts HI -> bytes inb ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> 0 <= flush <= 5 -> aout <= 2097152 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  exists s3 z3 o, c_deflate_compress s z flush = Some (s3, z3, o) /\ d_gzhead s3 = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s3 z3 /\
    match o with
    | Some c => c = Z_OK
    | None => d_pending s3 = 0 /\ (flush = Z_FINISH -> d_status s3 = FINISH_STATE) /\
              (d_status s3 = BUSY_STATE \/ (d_status s3 = FINISH_STATE /\ z_avail_in z3 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z HC HH Hbin HM Hpend Hfl Haout Hst.
  pose proof HM as HM0.
  destruct HM as [Hz [HDb [HOb HIa]]].
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
         split; [exact Hpend|]. split; [|left; exact HB].
         intros H4. exfalso. rewrite H4, HB in Hc. simpl in Hc. rewrite orb_true_r in Hc. discriminate. }
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    assert (Hzin : zin_ok z).
    { pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg D). pose proof (Zlength_nonneg O).
      rewrite Zlength_app, Zlength_sublist in HtinR by lia. rewrite Zlength_app in Htout.
      unfold zin_ok. rewrite Hin. split; [exact Hbin|]. lia. }
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (cf_compress W HC s z flush HW Hok Hq Hfl Hzin ltac:(lia) Hadp)
      as (s' & z' & bs & evs & Hcf & Hcp).
    rewrite Hcf. cbn [bind].
    destruct Hcp as (HW' & Hok' & _ & Hapi & (k & x & Hzs & Hbx & Hubk) & _ & Hev & Hbs).
    destruct Hapi as (Ast & Awr & Agz & _ & Alf & _).
    rewrite Hwrs in Hzs, Awr.
    assert (Hao' : 0 <= z_avail_out z') by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&_); lia).
    assert (Hdz3 : (D ++ sublist 0 (z_next_in z) inb) ++ sublist (z_next_in z) (z_next_in z + k) inb = [] ->
                   d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\ (dict = [] -> d_strstart s' = 0)).
    { intros Hnil.
      assert (HdzO : D ++ sublist 0 (z_next_in z) inb = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s)
        by (intros E; destruct (Hdz E) as (A & B & _); split; assumption).
      destruct (cs_dz W s s' k evs flush (D ++ sublist 0 (z_next_in z) inb)
                  (sublist (z_next_in z) (z_next_in z + k) inb) HC HW HW' Hev Hubk
                  ltac:(destruct Hzs as (_ & Hk & _); rewrite Zlength_sublist; lia) HdzO Hnil) as [La Ss].
      split; [exact La|]. split; [exact Ss|].
      intros Hd0.
      apply app_eq_nil in Hnil as [HD0 Hx0].
      destruct (Hdz HD0) as (La0 & Ss0 & S00).
      assert (Hk0 : k = 0).
      { destruct Hzs as (_ & Hk & _). pose proof (f_equal (@Zlength Z) Hx0) as L.
        rewrite Zlength_nil, Zlength_sublist in L by lia. lia. }
      apply (cf_still W HC s z flush s' z' bs HW Hok Hq Hfl Hzin ltac:(lia) Hadp Hcf).
      - unfold ub; lia.
      - exact (S00 Hd0).
      - destruct Hzs as (_ & _ & En & _). lia. }
    destruct bs.
    + (* need_more *)
      assert (Hnm : d_bi_valid s' <= 7) by apply Hbs.
      destruct (z_avail_out z' =? 0); (eexists _, _, _; split; [reflexivity|]); split; try exact Agz;
        (split; [|reflexivity]);
        (eapply cs_mid_after; [exact HM0|exact Hbin|exact Haout|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| | |exact Awr|exact Agz|exact Hnm| |left; rewrite <- HB; exact Ast|exact Hdz3]);
        try exact HW'; try exact Hok'; try (left; exact Alf); try (right; reflexivity).
      eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_lf].
    + (* block_done *)
      destruct Hbs as (_ & Hf0 & Hf4 & Hai0 & Hub & Hq' & Hsn).
      assert (HM' : Mid W HI dict wrap D O inb aout tin tout flush s' z').
      { eapply cs_mid_after; [exact HM0|exact Hbin|exact Haout|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'|exact HW'|exact Hok'|exact Awr|exact Agz|apply Hq'|left; exact Alf
          |left; rewrite <- HB; exact Ast|exact Hdz3]. }
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla Hss].
      assert (HBt := ltac:(first [exact (bd_tail_ok _ _ _ _ _ _ _ _ _ _ _ _ _ HC HH HM')
                                 | exact (bd_tail_ok _ _ _ _ _ _ _ _ _ _ _ _ _ HC HM')])).
      destruct (HBt ltac:(rewrite Ast; exact HB) Hq' Hsn Hla Hss Hai0 Hf0 Hf4 Hfl Haout)
        as (s'' & z'' & o & Hbt & Hgz'' & HM'' & Hst'' & Ho).
      exists s'', z'', o. split; [exact Hbt|]. split; [rewrite Hgz''; exact Agz|]. split; [exact HM''|].
      destruct Ho as [-> | [-> Hp]]; [reflexivity|].
      split; [exact Hp|]. split; [intros; contradiction|left; exact Hst''].
    + (* finish_started *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hbi0 & Hao0 & _).
      rewrite Hao0, Z.eqb_refl.
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla _].
      eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split; [|reflexivity].
      eapply cs_mid_after; [exact HM0|exact Hbin|exact Haout|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
        |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |right; reflexivity
        |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
        |exact Hdz3].
      * eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_status_lf].
      * change (d_bi_valid s' <= 7). lia.
    + (* finish_done *)
      destruct Hbs as (_ & Hf4 & Hai0 & Hub & Hsn & Hq' & Hbi0).
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla _].
      eexists _, _, _. split; [reflexivity|]. split; [exact Agz|]. split.
      * eapply cs_mid_after; [exact HM0|exact Hbin|exact Haout|exact Hpend|exact Hlf2|exact Hp2|exact Hzs
          |exact Hbx|exact Hao'| |exact Hok'|exact Awr|exact Agz| |left; exact Alf
          |right; split; [reflexivity|split; [exact Hla|split; [exact Hsn|split; [exact Hf4|exact Hai0]]]]
          |exact Hdz3].
        -- eapply (cf_frame _ HC); [exact HW'|apply cs_core_eq_status].
        -- change (d_bi_valid s' <= 7). lia.
      * split; [apply Hq'|]. split; [intros; reflexivity|right; split; [reflexivity|exact Hai0]].
  - (* FINISH: nothing to compress *)
    destruct Hp3 as (HF & Hla & _).
    destruct Hst as [HB | [_ Hai0]]; [exfalso; rewrite HB in HF; cs_states|].
    unfold c_deflate_compress.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    { exfalso. rewrite Hai0, Hla, HF in Hc. simpl in Hc. rewrite andb_false_r in Hc. discriminate. }
    exists s, z, None. split; [reflexivity|]. split; [reflexivity|]. split; [exact HM0|].
    split; [exact Hpend|]. split; [intros; exact HF|right; split; [exact HF|exact Hai0]].
Qed.

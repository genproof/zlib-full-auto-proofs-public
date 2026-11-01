(* RT-D part DEFLATE, stage 8 of deflate(): the compression stage (c_deflate_compress: the
   compression function, the block_done tail) keeps KMid (design: RTDDgDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDgDefs.
Require Import Zlib.proof.roundtrip.RTDDgCompKit Zlib.proof.roundtrip.RTDDfXComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Bits *)
Lemma kc_bits_le_len : forall v n, 0 <= n -> Zlength (F.bits_le v n) = n.
Proof. intros v n H. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma kc_bb_app : forall a b, F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. intros a b. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma kc_bb_len : forall l, Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  change (F.bytes_bits (a :: l)) with (F.bits_le a 8 ++ F.bytes_bits l).
  rewrite Zlength_app, IH, kc_bits_le_len, !Zlength_cons by lia. lia.
Qed.

(** enc_from of a concatenation: the first part is not final *)
Lemma kc_enc_from_app : forall BS BS' q fin, (fin = true -> BS' <> []) ->
  enc_from q (BS ++ BS') fin = enc_from q BS false ++ enc_from (q + Zlength (enc_from q BS false)) BS' fin.
Proof.
  induction BS as [|b r IH]; intros BS' q fin Hf.
  - cbn [app enc_from]. rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - cbn [app enc_from andb].
    replace (fin && match r ++ BS' with [] => true | _ => false end) with false.
    2: { destruct fin; [|reflexivity]. destruct (r ++ BS') eqn:E; [|reflexivity].
         apply app_eq_nil in E as [_ E]. exfalso. exact (Hf eq_refl E). }
    rewrite IH by exact Hf. rewrite <- app_assoc. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
Qed.

Lemma kc_enc_join : forall BS BS' fin, (fin = true -> BS' <> []) ->
  enc_from 0 BS false ++ enc_out (Zlength (enc_from 0 BS false)) BS' fin = enc_out 0 (BS ++ BS') fin.
Proof.
  intros BS BS' fin Hf. unfold enc_out. rewrite (kc_enc_from_app BS BS' 0 fin Hf), Z.add_0_l.
  destruct fin; [|reflexivity].
  rewrite <- app_assoc, Zlength_app, Z.add_0_l. reflexivity.
Qed.

Lemma kc_allbits_step : forall O s x s' tail, pend s = [] ->
  F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ tail ->
  allbits (O ++ x) s' = allbits O s ++ tail.
Proof.
  intros O s x s' tail Hp E. unfold allbits. rewrite Hp, app_nil_r, <- app_assoc, !kc_bb_app.
  rewrite <- app_assoc, <- kc_bb_app, E, app_assoc. reflexivity.
Qed.

Lemma kc_pos8 : forall O s HDR BS, pend s = [] -> 0 <= d_bi_valid s ->
  allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false ->
  (Zlength (enc_from 0 BS false) - d_bi_valid s) mod 8 = 0.
Proof.
  intros O s HDR BS Hp Hb E. apply (f_equal (@Zlength bool)) in E.
  unfold allbits, bibits in E. rewrite Hp, app_nil_r, !Zlength_app, !kc_bb_len, kc_bits_le_len in E by exact Hb.
  change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s) in E.
  replace (Zlength (enc_from 0 BS false) - d_bi_valid s) with ((Zlength O - Zlength HDR) * 8) by lia.
  apply Z_mod_mult.
Qed.

(** ** The state setters of the stage change nothing the invariant reads *)
Lemma kc_allbits_status : forall O s v, allbits O (set_d_status s v) = allbits O s.
Proof. intros O [] v. reflexivity. Qed.

Lemma kc_allbits_lf : forall O s v, allbits O (set_d_last_flush s v) = allbits O s.
Proof. intros O [] v. reflexivity. Qed.

Lemma kc_khdr : forall dict wrap s s' HDR, d_w_bits s' = d_w_bits s -> d_gzhead s' = d_gzhead s ->
  khdr dict wrap s HDR -> khdr dict wrap s' HDR.
Proof. intros dict wrap s s' HDR E1 E2 H. unfold khdr in *. rewrite E1, E2. exact H. Qed.

(** ** The data *)
Lemma kc_data : forall dict D BS syms s, kcore3 dict D BS syms s ->
  d_lookahead s = 0 -> d_strstart s = d_block_start s -> F.data dict BS = D.
Proof.
  intros dict D BS syms s [(_ & _ & _ & _ & Hx & _) _] Hla Hss. cbv zeta in Hx.
  rewrite Hla, Hss, Z.add_0_r, Z.sub_add, sublist_same in Hx by reflexivity.
  unfold F.data. rewrite Hx, Zlength_app. pose proof (Zlength_nonneg dict). rewrite sublist_app2 by lia.
  rewrite Z.sub_diag, Z.add_simpl_l. apply sublist_same; reflexivity.
Qed.

Lemma kc_D : forall (D inb : list Z) n k, 0 <= n -> 0 <= k -> n + k <= Zlength inb ->
  (D ++ sublist 0 n inb) ++ sublist n (n + k) inb = D ++ sublist 0 (n + k) inb.
Proof. intros. rewrite <- app_assoc, <- (sublist_split 0 n (n + k)) by lia. reflexivity. Qed.

(** ** KMid from its parts *)
Lemma kc_kmid_busy : forall dict wrap D O inb s z BS syms HDR,
  (wrap <> 2 -> d_gzhead s = None) -> d_status s = BUSY_STATE ->
  kcore3 dict (D ++ sublist 0 (z_next_in z) inb) BS syms s -> khdr dict wrap s HDR ->
  allbits (O ++ z_out z) s = F.bytes_bits HDR ++ enc_from 0 BS false -> KMid dict wrap D O inb s z.
Proof.
  intros dict wrap D O inb s z BS syms HDR Hg Hs Hk Hh Hb. unfold KMid, KFd, KF2g.
  split; [split; [exact Hg|]|intros N; contradiction].
  exists BS, syms. split; [exact Hk|]. right; left. split; [exact Hs|]. exists HDR. split; assumption.
Qed.

Lemma kc_kmid_finish : forall dict wrap D O inb s z BS syms HDR,
  (wrap <> 2 -> d_gzhead s = None) -> d_status s = FINISH_STATE -> d_wrap s = wrap -> BS <> [] ->
  d_lookahead s = 0 -> d_strstart s = d_block_start s ->
  kcore3 dict (D ++ sublist 0 (z_next_in z) inb) BS syms s -> khdr dict wrap s HDR ->
  allbits (O ++ z_out z) s = F.bytes_bits HDR ++ enc_out 0 BS true -> KMid dict wrap D O inb s z.
Proof.
  intros dict wrap D O inb s z BS syms HDR Hg Hs Hw Hne Hla Hss Hk Hh Hb. unfold KMid, KFd, KF2g.
  split; [split; [exact Hg|]|intros _ N; contradiction].
  exists BS, syms. split; [exact Hk|]. right; right. split; [exact Hs|]. split; [exact Hne|].
  split; [exact (kc_data _ _ _ _ _ Hk Hla Hss)|].
  exists HDR. split; [exact Hh|]. left. split; assumption.
Qed.

Lemma kf_comp_ok : Zlib.proof.huffman.Overlay.overlay_statement ->
  writer_fspec -> stored_block_fspec -> align_fspec -> fpend_fspec2 -> compf_fspec3 ->
  forall dict wrap D O inb aout tin tout flush s z s3 z3 o,
  bytes inb ->
  Mid W3 hinv dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  d_pending s = 0 -> 0 <= flush <= 5 -> aout <= 2097152 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_compress s z flush = Some (s3, z3, o) ->
  d_w_bits s3 = d_w_bits s /\ KMid dict wrap D O inb s3 z3.
Proof.
  intros Hov Hwr Hsb Hal Hfp Hcf dict wrap D O inb aout tin tout flush s z s3 z3 o Hbin HM HK Hpend Hfl Haout Hst Hrun.
  pose proof (W3_facts Hov) as HC. pose proof hinv_facts as HH.
  pose proof HM as HM0.
  destruct HM as [Hz [HDb [HOb HIa]]].
  destruct HIa as (HW & Hok & Hwr0 & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HtinR & Hfin & Hdz & Hph).
  destruct Hph as [Hp0 | [Hlf2 [Hp1 | [Hp2 | Hp3]]]].
  - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|[Hst _]]; cs_states.
  - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
    destruct (hf_status _ HH _ _ _ _ HHI) as (_ & _ & Hs & _).
    destruct Hst as [Hst|[Hst _]]; cs_states.
  - (* BUSY *)
    pose proof Hp2 as Hp2'.
    destruct Hp2' as (HB & Hwrs & Hbi & _ & Hchk & _).
    unfold c_deflate_compress in Hrun.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    2: { injection Hrun as <- <- <-. split; [reflexivity|exact HK]. }
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    assert (Hzin : zin_ok z).
    { pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg D). pose proof (Zlength_nonneg O).
      rewrite Zlength_app, Zlength_sublist in HtinR by lia. rewrite Zlength_app in Htout.
      unfold zin_ok. rewrite Hin. split; [exact Hbin|]. lia. }
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (cf_compress W3 HC s z flush HW Hok Hq Hfl Hzin ltac:(lia) Hadp)
      as (s' & z' & bs & evs & Hcf' & Hcp).
    rewrite Hcf' in Hrun. cbn [bind] in Hrun.
    destruct Hcp as (HW' & Hok' & Hsp & Hapi & _ & _ & Hev & Hbs).
    destruct Hapi as (Ast & Awr & Agz & _ & Alf & _).
    destruct Hsp as (Hwb & _).
    (* the functional invariant at the start *)
    destruct HK as [[Hg0 (BS & syms & Hk & Hcase)] _].
    destruct Hcase as [(N & _) | [(_ & HDR & Hhdr & Hall) | (N & _)]]; [contradiction | | rewrite HB in N; discriminate].
    set (n := z_next_in z) in *.
    set (p := Zlength (enc_from 0 BS false)).
    assert (Hps : pend s = []) by (apply cs_pend_nil; exact Hpend).
    assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Hok as (_ & (B & _) & _); exact (proj1 B)).
    assert (Hp8 : (p - d_bi_valid s) mod 8 = 0) by (exact (kc_pos8 _ _ _ _ Hps Hbv0 Hall)).
    destruct (Hcf (fn_of s) s z flush s' z' bs dict (D ++ sublist 0 n inb) BS syms p HW Hok Hq Hfl Hzin
                ltac:(rewrite Hwrs; lia) Hadp eq_refl Hbd HbD Hk (Zlength_nonneg _) Hp8 Hcf')
      as (k & x & BS' & syms' & Hzs & Hk' & Hbits & Hfne).
    pose proof Hzs as (Ein & Hkr & En & _).
    change (z_next_in z) with n in Hk', En. rewrite Hin in Hk'. rewrite (kc_D D inb n k ltac:(lia) ltac:(lia) ltac:(lia)) in Hk'.
    rewrite <- En in Hk'.
    assert (Hall' := kc_allbits_step (O ++ z_out z) s x s' _ Hps Hbits).
    rewrite Hall, <- (app_assoc (F.bytes_bits HDR)) in Hall'. unfold p in Hall'.
    assert (Hout : O ++ z_out z' = (O ++ z_out z) ++ x) by (destruct Hzs as (_&_&_&_&_&_&Eo&_); rewrite Eo, app_assoc; reflexivity).
    rewrite <- Hout in Hall'.
    assert (Hg' : wrap <> 2 -> d_gzhead s' = None) by (rewrite Agz; exact Hg0).
    assert (Hh' : khdr dict wrap s' HDR) by (exact (kc_khdr _ _ _ _ _ Hwb Agz Hhdr)).
    destruct bs; cbn [fin_bs] in Hall', Hfne.
    + (* need_more *)
      rewrite (kc_enc_join BS BS' false ltac:(discriminate)) in Hall'.
      destruct (z_avail_out z' =? 0); injection Hrun as <- <- <-; (split; [cbn; exact Hwb|]).
      all: apply (kc_kmid_busy dict wrap D O inb _ z' (BS ++ BS') syms' HDR); try assumption;
        cbn; rewrite Ast; exact HB.
    + (* block_done *)
      destruct Hbs as (_ & Hf0 & Hf4 & _ & Hub & Hq' & Hsn).
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla Hss].
      rewrite (kc_enc_join BS BS' false ltac:(discriminate)) in Hall'.
      change (bd_tail s' z' flush = Some (s3, z3, o)) in Hrun.
      assert (Hx : Zlength x <= z_avail_out z /\ z_avail_out z' = z_avail_out z - Zlength x /\
                   z_total_out z' = u64 (z_total_out z + Zlength x))
        by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&Eto&_); auto).
      destruct Hx as (Exle & Eao & Eto).
      pose proof (Zlength_nonneg x). pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)).
      rewrite Zlength_app in Htout.
      assert (Hto' : z_total_out z' = z_total_out z + Zlength x) by (rewrite Eto; unfold u64; apply Z.mod_small; lia).
      destruct Hzin as (_ & _ & _ & _ & Hao1 & _).
      destruct (kbd_ok kfull_ok Hwr Hsb Hal Hfp dict (D ++ sublist 0 (z_next_in z') inb) (O ++ z_out z') (BS ++ BS')
                  syms' HDR s' z' flush s3 z3 o HW' Hok' Hq' Hsn Hla Hss Hf0 Hf4 Hfl ltac:(lia) ltac:(lia) Hk' Hall' Hrun)
        as (x2 & BS2 & syms2 & Hzo2 & Hs3 & _ & Hg3 & Hw3 & Hk3 & Hall3).
      destruct Hzo2 as (_ & En2 & _ & _ & _ & _ & Eo2 & _).
      split; [congruence|].
      apply (kc_kmid_busy dict wrap D O inb s3 z3 ((BS ++ BS') ++ BS2) syms2 HDR).
      * rewrite Hg3, Agz. exact Hg0.
      * rewrite Hs3, Ast. exact HB.
      * rewrite En2. exact Hk3.
      * apply (kc_khdr dict wrap s s3 HDR ltac:(congruence) ltac:(congruence) Hhdr).
      * rewrite Eo2, app_assoc. exact Hall3.
    + (* finish_started *)
      destruct Hbs as (_ & _ & _ & Hub & _ & _ & Hao0 & _).
      rewrite Hao0, Z.eqb_refl in Hrun. injection Hrun as <- <- <-.
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla Hss].
      rewrite (kc_enc_join BS BS' true Hfne) in Hall'.
      assert (Hne : BS ++ BS' <> []) by (intro E; apply app_eq_nil in E; exact (Hfne eq_refl (proj2 E))).
      split; [cbn; exact Hwb|].
      apply (kc_kmid_finish dict wrap D O inb _ z' (BS ++ BS') syms' HDR); try assumption; cbn; try reflexivity;
        congruence.
    + (* finish_done *)
      destruct Hbs as (_ & _ & _ & Hub & _).
      injection Hrun as <- <- <-.
      destruct (cs_ub0 _ _ HC HW' Hub) as [Hla Hss].
      rewrite (kc_enc_join BS BS' true Hfne) in Hall'.
      assert (Hne : BS ++ BS' <> []) by (intro E; apply app_eq_nil in E; exact (Hfne eq_refl (proj2 E))).
      split; [cbn; exact Hwb|].
      apply (kc_kmid_finish dict wrap D O inb _ z' (BS ++ BS') syms' HDR); try assumption; cbn; try reflexivity;
        congruence.
  - (* FINISH: nothing to compress *)
    destruct Hp3 as (HF & Hla & _).
    destruct Hst as [HB | [_ Hai0]]; [exfalso; rewrite HB in HF; cs_states|].
    unfold c_deflate_compress in Hrun.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    { exfalso. rewrite Hai0, Hla, HF in Hc. simpl in Hc. rewrite andb_false_r in Hc. discriminate. }
    injection Hrun as <- <- <-. split; [reflexivity|exact HK].
Qed.

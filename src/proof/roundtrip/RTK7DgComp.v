(* The compression stage of deflate() keeps KMid (the functional half), or ends in stuck7 when deflate_stored
   meets its defect: RTDDgComp.kf_comp_ok (with RTDDgCompKit) for Mid7, fpend_fspec7 and comp_fspec7. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTK7DMid.
Require Import Zlib.proof.roundtrip.RTDDgCompKit Zlib.proof.roundtrip.RTDDgComp Zlib.proof.roundtrip.RTDDfXComp.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The block_done tail on any output space of a uInt *)

(* RTDDgCompKit.kbd_stmt for a stream of zout_ok7 (instead of avail_out <= 2^30, total_out <= 2^40) *)
Definition kbd_stmt7 : Prop :=
  forall dict D O BS syms HDR s z flush s' z' o,
    W3 s -> outok s -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
    zout_ok7 z ->
    kcore3 dict D BS syms s ->
    allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false ->
    bd_tail s z flush = Some (s', z', o) ->
    exists x BS' syms',
      zout_only z z' x /\
      d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\
      d_w_bits s' = d_w_bits s /\
      kcore3 dict D (BS ++ BS') syms' s' /\
      allbits (O ++ x) s' = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false.

(* RTDDgCompKit.kbd_ok with flush_pending_ok7 and fpend_fspec7 at the final flush_pending *)
Lemma kbd_ok7 : writer_fspec -> stored_block_fspec -> align_fspec -> fpend_fspec7 -> kbd_stmt7.
Proof.
  intros _ SB AL FP dict D O BS syms HDR s z flush s' z' o HW Ho Hq Hsym Hla Hss Hf1 Hf2 Hfr Hzo HK HA Hbd.
  set (p := Zlength (enc_from 0 BS false)).
  assert (Hps : pend s = []).
  { destruct Hq as (Q1 & Q2 & _). unfold pend. rewrite Q1, Q2. apply sublist_nil. }
  assert (Hbo : bits_ok (tr_out (d_tr s))) by exact (proj1 (proj2 Ho)).
  assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Hbo as [? _]; unfold d_bi_valid; lia).
  assert (HL : 8 * Zlength O + d_bi_valid s = 8 * Zlength HDR + p).
  { apply (f_equal (@Zlength bool)) in HA. unfold allbits in HA.
    rewrite Hps, app_nil_r, !Zlength_app, !kbd_bytes_bits_len in HA. unfold bibits in HA.
    rewrite kbd_bits_le_len in HA by exact Hbv0. exact HA. }
  assert (Hp0 : 0 <= p) by (unfold p; apply Zlength_nonneg).
  assert (Hpm : (p - o_bi_valid (tr_out (d_tr s))) mod 8 = 0).
  { change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s).
    replace (p - d_bi_valid s) with ((Zlength O - Zlength HDR) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hob : obits (tr_out (d_tr s)) = bibits s).
  { unfold obits, bibits, d_bi_valid. destruct Hq as (Q1 & _).
    change (o_pending (tr_out (d_tr s))) with (d_pending s). rewrite Q1, sublist_nil. reflexivity. }
  assert (HA0 : allbits O s = F.bytes_bits O ++ bibits s).
  { rewrite kbd_allbits_po0 by exact (proj1 (proj2 Hq)). rewrite Hob. reflexivity. }
  (* the bits after one more block b appended by the writer *)
  assert (HB : forall s1 b, d_po s1 = 0 ->
      obits (tr_out (d_tr s1)) = obits (tr_out (d_tr s)) ++ F.enc_block p false b ->
      allbits O s1 = F.bytes_bits HDR ++ enc_from 0 (BS ++ [b]) false).
  { intros s1 b P1 E1. rewrite kbd_allbits_po0 by exact P1. rewrite E1, Hob, app_assoc, <- HA0, HA.
    rewrite kbd_enc_from_snoc, <- app_assoc. reflexivity. }
  unfold bd_tail in Hbd.
  match type of Hbd with @eq _ (bind ?X _) _ =>
    assert (S1 : exists s2 BS', X = Some s2 /\ outok s2 /\ d_bi_valid s2 <= 7 /\
      d_status s2 = d_status s /\ d_wrap s2 = d_wrap s /\ d_gzhead s2 = d_gzhead s /\
      d_w_bits s2 = d_w_bits s /\ kcore3 dict D (BS ++ BS') syms s2 /\
      allbits O s2 = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false) end.
  { pose proof (W3_prm s HW) as HP.
    destruct (flush =? Z_PARTIAL_FLUSH).
    - destruct (tr_align_ok s HP Ho Hq Hsym) as (om & E & O1 & C1 & A1 & P1 & B1 & _).
      destruct om as [o1 m1].
      destruct (AL _ _ o1 m1 p Hbo E) as (_ & _ & Eo).
      rewrite E. cbn [bind]. exists (set_d_out s (o1, m1)), [F.Fixed []].
      destruct A1 as (A1 & A2 & A3 & _).
      destruct (core_eq_fields _ _ C1) as (_ & _ & Fw & _).
      split; [reflexivity|]. split; [exact O1|]. split; [exact B1|].
      do 4 (split; [assumption|]). split.
      + apply kbd_kcore3_snoc; [exact (kcore3_frame _ _ _ _ _ _ C1 HK)|exact I|reflexivity].
      + apply HB; [exact P1|exact Eo].
    - destruct (flush =? Z_BLOCK); cbn [negb].
      + exists s, []. rewrite app_nil_r. split; [reflexivity|]. split; [exact Ho|].
        split; [exact (proj2 (proj2 Hq))|]. do 4 (split; [reflexivity|]). split; [exact HK|exact HA].
      + destruct (stored_empty_ok s HP Ho Hq Hsym) as (om & E & O1 & C1 & A1 & P1 & B1 & _).
        destruct om as [o1 m1].
        destruct (SB _ _ [] 0 0 o1 m1 p Hbo ltac:(lia) ltac:(lia) (or_introl eq_refl)
                    ltac:(rewrite sublist_nil; constructor) Hp0 Hpm E) as (_ & _ & Eo).
        rewrite E. cbn [bind].
        set (s1 := set_d_out s (o1, m1)) in *.
        assert (K1 : kcore3 dict D (BS ++ [F.Stored (sublist 0 0 [])]) syms s1).
        { apply kbd_kcore3_snoc; [exact (kcore3_frame _ _ _ _ _ _ C1 HK)| |].
          - rewrite sublist_nil. cbn. split; [lia|constructor].
          - rewrite sublist_nil. cbn. apply app_nil_r. }
        assert (AB1 : allbits O s1 = F.bytes_bits HDR ++ enc_from 0 (BS ++ [F.Stored (sublist 0 0 [])]) false).
        { apply HB; [exact P1|exact Eo]. }
        destruct A1 as (A1 & A2 & A3 & _).
        destruct (core_eq_fields _ _ C1) as (_ & _ & Fw & _ & Fb & Fs & Fl & _ & Fn & _).
        destruct (flush =? Z_FULL_FLUSH).
        * assert (W1 : W3 s1) by exact (W3_frame s s1 HW C1).
          assert (Hws : wstruct s1) by (destruct W1 as [[[_ [X _]] _] _]; exact X).
          rewrite (Zlib.proof.roundtrip.RTDLTCMisc.clear_hash_eq s1 (W3_prm s1 W1) Hws). cbn [bind].
          change (d_lookahead (set_d_slid (set_d_head s1 (repeat 0 (Z.to_nat (d_hash_size s1)))) 0))
            with (d_lookahead s1).
          rewrite Fl, Hla. cbn [Z.eqb].
          exists (full_reset (set_d_slid (set_d_head s1 (repeat 0 (Z.to_nat (d_hash_size s1)))) 0)),
            [F.Stored (sublist 0 0 [])].
          split; [reflexivity|]. split; [exact O1|]. split; [change (d_bi_valid s1 <= 7); lia|].
          do 4 (split; [assumption|]). split.
          -- apply kfull_ok; [exact W1|congruence|congruence|congruence|exact K1].
          -- exact AB1.
        * exists s1, [F.Stored (sublist 0 0 [])].
          split; [reflexivity|]. split; [exact O1|]. split; [lia|].
          do 4 (split; [assumption|]). split; [exact K1|exact AB1]. }
  destruct S1 as (s2 & BS' & E1 & O2 & B2 & St2 & Wr2 & G2 & Wb2 & K2 & A2).
  rewrite E1 in Hbd. cbn [bind] in Hbd.
  pose proof Hzo as (Hao & Hto & Hta).
  destruct (flush_pending_ok7 s2 z O2 B2 Hao Hto Hta) as (s3 & x & E3 & _ & _ & _ & O3 & C3 & A3 & _).
  destruct (FP s2 z _ _ O2 Hzo ltac:(left; lia) E3) as (x' & Zx & Bx).
  rewrite E3 in Hbd. cbn [bind] in Hbd.
  destruct A3 as (A31 & A32 & A33 & _).
  destruct (core_eq_fields _ _ C3) as (_ & _ & Fw3 & _).
  assert (K3 : kcore3 dict D (BS ++ BS') syms s3) by exact (kcore3_frame _ _ _ _ _ _ C3 K2).
  assert (AB3 : allbits (O ++ x') s3 = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false).
  { rewrite <- A2. unfold allbits. rewrite <- app_assoc, !kbd_bytes_bits_app, <- !app_assoc.
    f_equal. rewrite <- Bx, kbd_bytes_bits_app, <- app_assoc. reflexivity. }
  exists x', BS', syms.
  destruct (_ =? 0); inversion Hbd; subst; clear Hbd.
  - split; [exact Zx|]. cbn [d_status d_wrap d_gzhead d_w_bits set_d_last_flush].
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [exact (kcore3_frame _ _ _ _ _ _ (kbd_core_eq_lf s3 (-1)) K3)|exact AB3].
  - split; [exact Zx|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [exact K3|exact AB3].
Qed.

(* RTDDfXComp.cs_ub0 from core_facts7 *)
Lemma kc7_ub0 : forall W s, core_facts7 W -> W s -> ub s = 0 ->
  d_lookahead s = 0 /\ d_strstart s = d_block_start s.
Proof.
  intros W s HC HW Hub. pose proof (cf7_pos _ HC s HW) as Hp. unfold ub in Hub. lia.
Qed.

(** ** The stage *)
Lemma kf_comp_ok7 : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts7 W3 -> hdr_facts7 hinv7 ->
  writer_fspec -> stored_block_fspec -> align_fspec -> fpend_fspec7 -> compf_fspec7 ->
  forall dict wrap D O inb aout tin tout flush s z s3 z3 o,
  bytes inb ->
  Mid7 W3 hinv7 dict wrap D O inb aout tin tout flush s z ->
  KMid dict wrap D O inb s z ->
  d_pending s = 0 -> 0 <= flush <= 5 ->
  (d_status s = BUSY_STATE \/ (d_status s = FINISH_STATE /\ z_avail_in z = 0)) ->
  c_deflate_compress s z flush = Some (s3, z3, o) ->
  (d_w_bits s3 = d_w_bits s /\ KMid dict wrap D O inb s3 z3) \/ stuck7 flush s3 z3.
Proof.
  intros _ HC HH Hwr Hsb Hal Hfp Hcf dict wrap D O inb aout tin tout flush s z s3 z3 o Hbin HM HK Hpend Hfl Hst
    Hrun.
  pose proof HM as HM0.
  destruct HM as [Hz [_ [_ [_ [_ HIa]]]]].
  destruct HIa as (HW & Hok & Hwr0 & Hw2 & Hbd & Hdl & Hlf & Hgz & Htout & HbO & HbD & HDl & Htin & Hfin & Hdz
                   & Hph).
  destruct Hph as [Hp0 | [Hlf2 [Hp1 | [Hp2 | Hp3]]]].
  - exfalso. destruct Hp0 as [[[Hs _]|[Hs _]] _]; destruct Hst as [Hst|[Hst _]]; cs_states.
  - exfalso. destruct Hp1 as (_ & _ & _ & _ & _ & H & k & HHI & _).
    destruct (hf7_status _ HH _ _ _ _ HHI) as (_ & _ & Hs & _).
    destruct Hst as [Hst|[Hst _]]; cs_states.
  - (* BUSY *)
    pose proof Hp2 as Hp2'.
    destruct Hp2' as (HB & Hwrs & Hbi & _ & Hchk & _).
    unfold c_deflate_compress in Hrun.
    destruct (negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
              (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE))) eqn:Hc.
    2: { injection Hrun as <- <- <-. left. split; [reflexivity|exact HK]. }
    pose proof (mid7_zin_ok7 _ _ _ _ _ _ _ _ _ _ _ _ _ HM0 Hbin) as Hzin.
    destruct Hz as (Hin & Hn & Hai & Hti & Hao & Hzo & Hto & Hbo).
    assert (Hq : quiet s).
    { split; [exact Hpend|split; [|exact Hbi]]. destruct Hok as (_ & _ & _ & _ & _ & Hpo). auto. }
    assert (Hadp : adler_pre (d_wrap s) (z_adler z)).
    { rewrite Hwrs. eapply chk_ok_pre; eassumption. }
    destruct (cf7_compress W3 HC s z flush HW Hok Hq Hfl Hzin ltac:(lia) Hadp)
      as (s' & z' & bs & evs & Hcf' & Hcp).
    rewrite Hcf' in Hrun. cbn [bind] in Hrun.
    (* the defect of deflate_stored: a final block with input left, the stream ends in FINISH_STATE *)
    assert (Hcut : stored_cut s z' flush bs -> stuck7 flush s3 z3).
    { intros (_ & Hff & Hbs & Ha). subst bs. injection Hrun as <- <- <-.
      split; [exact Hff|]. split; [destruct s'; reflexivity|exact Ha]. }
    destruct Hcp as [Hcp | Hcp]; [|right; exact (Hcut Hcp)].
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
      as [(k & x & BS' & syms' & Hzs & Hk' & Hbits & Hfne) | Hsc]; [|right; exact (Hcut Hsc)].
    left.
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
      destruct (kc7_ub0 _ _ HC HW' Hub) as [Hla Hss].
      rewrite (kc_enc_join BS BS' false ltac:(discriminate)) in Hall'.
      change (bd_tail s' z' flush = Some (s3, z3, o)) in Hrun.
      assert (Hx : Zlength x <= z_avail_out z /\ z_avail_out z' = z_avail_out z - Zlength x /\
                   z_total_out z' = u64 (z_total_out z + Zlength x))
        by (destruct Hzs as (_&_&_&_&_&_&_&Exle&Eao&Eto&_); auto).
      destruct Hx as (Exle & Eao & Eto).
      pose proof (Zlength_nonneg x).
      destruct Hzin as (_ & _ & _ & _ & Hao1 & _ & Hto1 & Hto2).
      assert (Hto' : z_total_out z' = z_total_out z + Zlength x) by (rewrite Eto; unfold u64; apply Z.mod_small; lia).
      assert (Hzo' : zout_ok7 z') by (unfold zout_ok7; lia).
      destruct (kbd_ok7 Hwr Hsb Hal Hfp dict (D ++ sublist 0 (z_next_in z') inb) (O ++ z_out z') (BS ++ BS')
                  syms' HDR s' z' flush s3 z3 o HW' Hok' Hq' Hsn Hla Hss Hf0 Hf4 Hfl Hzo' Hk' Hall' Hrun)
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
      destruct (kc7_ub0 _ _ HC HW' Hub) as [Hla Hss].
      rewrite (kc_enc_join BS BS' true Hfne) in Hall'.
      assert (Hne : BS ++ BS' <> []) by (intro E; apply app_eq_nil in E; exact (Hfne eq_refl (proj2 E))).
      split; [cbn; exact Hwb|].
      apply (kc_kmid_finish dict wrap D O inb _ z' (BS ++ BS') syms' HDR); try assumption; cbn; try reflexivity;
        congruence.
    + (* finish_done *)
      destruct Hbs as (_ & _ & _ & Hub & _).
      injection Hrun as <- <- <-.
      destruct (kc7_ub0 _ _ HC HW' Hub) as [Hla Hss].
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
    injection Hrun as <- <- <-. left. split; [reflexivity|exact HK].
Qed.

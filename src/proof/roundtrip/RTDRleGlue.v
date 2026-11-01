(* RT-D part RLE: the glue.  From the part statements of RTDRleKit.v (and the Qed safety parts of
   RTDLTCRle*.v) to comp_fspec 4 c_deflate_rle: the main loop by the measure avail_in + lookahead (as
   RTDLTCRleGlue.rloop_ok), with the functional invariant [GF] composed piece by piece ([FStep], [gf_comp]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The functional invariant from the start (s0, z0) of the call *)
Definition GF (s0 : dstate) (z0 : strm) (dict D : list Z) (BS : list F.block) (p : Z)
    (s : dstate) (z : strm) (fin : bool) : Prop :=
  exists k X BS' syms,
    zstep (d_wrap s0) z0 z k X /\ wtrees s syms /\
    rkt dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS ++ BS') syms s /\
    F.bytes_bits (X ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' fin /\
    (fin = true -> BS' <> []).

(** A functional step from (s, z) to (s', z'), for any history and any aligned bit position. *)
Definition FStep (dict : list Z) (s : dstate) (z : strm) (s' : dstate) (z' : strm) (fin : bool) : Prop :=
  forall Dh BSh syms p',
    Forall F.byte_ok dict -> bytes Dh -> wtrees s syms -> rkt dict Dh BSh syms s ->
    0 <= p' -> (p' - d_bi_valid s) mod 8 = 0 ->
    exists k x BS'' syms',
      zstep (d_wrap s) z z' k x /\ wtrees s' syms' /\
      rkt dict (Dh ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) (BSh ++ BS'') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p' BS'' fin /\
      (fin = true -> BS'' <> []).

Lemma gf_bv s : outok s -> 0 <= d_bi_valid s.
Proof.
  intros (_ & Hb & _). destruct Hb as (B1 & _). unfold d_bi_valid. lia.
Qed.

Lemma gf_init s0 z0 dict D BS syms p :
  zall z0 -> adler_ok (d_wrap s0) (z_adler z0) -> quiet s0 ->
  wtrees s0 syms -> rkt dict D BS syms s0 -> GF s0 z0 dict D BS p s0 z0 false.
Proof.
  intros Hz Ha Hq Hw Hk. exists 0, [], [], syms.
  split; [apply zstep_refl; auto|]. split; [exact Hw|].
  rewrite Z.add_0_r, sublist_nil, !app_nil_r. split; [exact Hk|].
  rewrite rk_quiet_pend by exact Hq. cbn. split; [reflexivity|discriminate].
Qed.

Lemma gf_comp s0 z0 dict D BS p s z s' z' fin :
  zin_in z0 -> adler_ok (d_wrap s0) (z_adler z0) -> d_wrap s = d_wrap s0 -> quiet s ->
  0 <= d_bi_valid s0 -> 0 <= d_bi_valid s -> 0 <= p -> (p - d_bi_valid s0) mod 8 = 0 ->
  Forall F.byte_ok dict -> bytes D ->
  GF s0 z0 dict D BS p s z false -> FStep dict s z s' z' fin -> GF s0 z0 dict D BS p s' z' fin.
Proof.
  intros Hz0 Ha0 Hw Hq Hb0 Hb Hp Hpm Hd HD (k & X & BS' & syms & Z & RW & RK & Bits & _) Hst.
  pose proof Hz0 as (Hin & Hn & Hav & Hl & Ht).
  pose proof Z as (Z1 & Z2 & Z3 & Z4 & _).
  rewrite rk_quiet_pend, app_nil_r in Bits by exact Hq.
  assert (HDh : bytes (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0))).
  { apply Forall_app. split; [exact HD|apply bytes_sublist; exact Hin]. }
  set (p' := p + Zlength (enc_from p BS' false)).
  assert (Hp' : 0 <= p') by (unfold p'; pose proof (Zlength_nonneg (enc_from p BS' false)); lia).
  assert (Hpm' : (p' - d_bi_valid s) mod 8 = 0)
    by (unfold p'; eapply rk_bitpos_aligned; [exact Hb0|exact Hb|exact Hpm|exact Bits]).
  destruct (Hst _ _ _ _ Hd HDh RW RK Hp' Hpm') as (k' & x & BS'' & syms' & Z' & RW' & RK' & Bits' & F').
  rewrite Hw in Z'.
  pose proof Z' as (Y1 & Y2 & Y3 & Y4 & _).
  exists (k + k'), (X ++ x), (BS' ++ BS''), syms'.
  split; [exact (zstep_trans _ _ _ _ _ _ _ _ Hz0 Ha0 Z Z')|].
  split; [exact RW'|].
  split.
  - rewrite Z3, Z1 in RK'. rewrite rk_hist_app in RK' by lia. rewrite <- app_assoc in RK'. exact RK'.
  - split.
    + rewrite <- app_assoc, rk_bytes_bits_app, <- app_assoc, Bits'.
      rewrite app_assoc, Bits, <- app_assoc.
      rewrite (rk_enc_out_app p BS' BS'' fin F'). reflexivity.
    + intros Ef E. apply app_eq_nil in E. destruct E as [_ E]. exact (F' Ef E).
Qed.

(** ** The functional steps of the pieces *)

Lemma fs_refill (Hrf : rfrefill_stmt) dict s z flush r :
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
  c_refill need_rle flush s z = Some r -> FStep dict s z (fst (rst r)) (snd (rst r)) false.
Proof.
  intros HW Ho Hq Hz Ha Hfn Hfl E Dh BSh syms p' Hd HDh RW RK Hp Hpm.
  destruct (Hrf s z flush r dict Dh BSh syms HW Ho Hq Hz Ha Hfn Hfl RW RK E) as (k & Z & RW' & RK' & Ep & Eb).
  exists k, [], [], syms. split; [exact Z|]. split; [exact RW'|]. split; [rewrite app_nil_r; exact RK'|].
  rewrite Ep, Eb, rk_quiet_pend by exact Hq. cbn. split; [rewrite !app_nil_r; reflexivity|discriminate].
Qed.

(** after the refill: scan, branch, bflush *)
Lemma fs_step (Hsc : rfscan_stmt) (Hli : rflit_stmt) (Hdi : rfdist_stmt) (Hbf : rfbflush_stmt)
    dict s z flush s2 s3 bf syms3 r :
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
  rready s -> 1 <= d_lookahead s ->
  rscan s = Some s2 -> RSC s s2 -> rbranch s2 = Some (s3, bf) -> RTS s3 syms3 bf -> d_wrap s3 = d_wrap s ->
  c_bflush s3 z bf = Some r -> FStep dict s z (fst (rst r)) (snd (rst r)) false.
Proof.
  intros HW Ho Hq Hz Ha Hfn Hfl Hr Hla E2 (ml & Es2 & Hml & Hmll & Hms) E3 HTS Hw3 Er
    Dh BSh syms p' Hd HDh RW RK Hp Hpm.
  assert (Hb : exists syms4, RTS s3 syms4 bf /\ rkt dict Dh BSh syms4 s3 /\ bibits s3 = bibits s /\ pend s3 = pend s).
  { revert E3. subst s2. unfold rbranch. rewrite fk_match_length_match_length. intros E3.
    destruct (ml >=? MIN_MATCH) eqn:Em.
    - apply Z.geb_le in Em.
      assert (Heq := Hsc s (set_d_match_length s ml) HW Hfn Hr Hla E2).
      rewrite fk_match_length_match_length in Heq. specialize (Heq Em).
      apply (Hdi s ml s3 bf dict Dh BSh syms); auto; lia.
    - rewrite Z.geb_leb in Em. apply Z.leb_gt in Em.
      apply (Hli s ml s3 bf dict Dh BSh syms); auto; lia. }
  destruct Hb as (syms4 & HTS4 & RK3 & Eb3 & Ep3).
  assert (Hbv : d_bi_valid s3 = d_bi_valid s).
  { assert (L := f_equal (@Zlength bool) Eb3). unfold bibits in L.
    rewrite !rk_Zlength_bits_le in L; [exact L| |].
    - exact (gf_bv s Ho).
    - destruct HTS4 as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho3 & _) & _). exact (gf_bv s3 Ho3). }
  assert (Ha3 : adler_ok (d_wrap s3) (z_adler z)) by (rewrite Hw3; exact Ha).
  rewrite <- Hbv in Hpm.
  destruct (Hbf s3 z flush syms4 bf r dict Dh BSh p' HTS4 Hz Ha3 Hfl Hd HDh RK3 Hp Hpm Er)
    as (x & BS'' & syms' & Z & RW' & RK' & Bits).
  exists 0, x, BS'', syms'. rewrite Hw3 in Z. split; [exact Z|]. split; [exact RW'|].
  split; [rewrite Z.add_0_r, sublist_nil, app_nil_r; exact RK'|].
  rewrite Eb3 in Bits. split; [exact Bits|discriminate].
Qed.

(** ** The loop *)
Section Loop.
Variables (Hrf : rfrefill_stmt) (Hsc : rfscan_stmt) (Hli : rflit_stmt) (Hdi : rfdist_stmt)
  (Hbf : rfbflush_stmt) (Hre : rrefill_stmt) (Hsc0 : rscan_stmt) (Hli0 : rlit_stmt) (Hdi0 : rdist_stmt)
  (Hbf0 : rbflush_stmt).
Variables (s0 : dstate) (z0 : strm) (flush : Z) (dict D : list Z) (BS : list F.block) (p : Z)
  (syms0 : list (Z * Z)).
Hypotheses (HW0 : W s0) (Ho0 : outok s0) (Hq0 : quiet s0) (Hz0 : zall z0) (Ha0 : adler_ok (d_wrap s0) (z_adler z0))
  (Hfn0 : fn_of s0 = 4) (Hfl : 0 <= flush <= 5) (Hd : Forall F.byte_ok dict) (HD : bytes D) (Hp : 0 <= p)
  (Hpm : (p - d_bi_valid s0) mod 8 = 0) (Hwt0 : wtrees s0 syms0) (Hk0 : rkt dict D BS syms0 s0).

Definition gI (a : dstate * strm) : Prop :=
  (exists evs, FI s0 z0 flush (fst a) (snd a) evs) /\ GF s0 z0 dict D BS p (fst a) (snd a) false.

Definition gQ (r : dexit) : Prop :=
  let '(s, z, o) := r in
  rloop_res s0 z0 flush r /\ GF s0 z0 dict D BS p s z false /\
  match o with Some bs => bs = need_more | None => True end.

Lemma g_comp s z s' z' evs :
  FI s0 z0 flush s z evs -> GF s0 z0 dict D BS p s z false -> FStep dict s z s' z' false ->
  GF s0 z0 dict D BS p s' z' false.
Proof.
  intros HFI HG Hst. destruct (rFI_parts _ _ _ _ _ _ HFI Hfn0) as (HW & Ho & Hq & Hz & Ha & Hfn).
  assert (E : d_wrap s = d_wrap s0) by (destruct (rFI_sp _ _ _ _ _ _ HFI) as (_ & (_ & E & _)); exact E).
  exact (gf_comp s0 z0 dict D BS p s z s' z' false (proj1 Hz0) Ha0 E Hq (gf_bv s0 Ho0) (gf_bv s Ho) Hp Hpm
           Hd HD HG Hst).
Qed.

Lemma g_loop : exists r, loop FUEL (rle_body flush) (s0, z0) = Some r /\ gQ r.
Proof.
  apply (rg_loop_measure (rle_body flush) gI gQ (fun a => z_avail_in (snd a) + d_lookahead (fst a))).
  - intros [s z] ((evs & HFI) & HG). cbn [fst snd] in *.
    destruct (rFI_parts _ _ _ _ _ _ HFI Hfn0) as (HW & Ho & Hq & Hz & Ha & Hfn).
    split.
    { destruct HW as (_ & _ & (Hl & _) & _). destruct Hz as ((_ & _ & Hai & _) & _). lia. }
    destruct (Hre s z flush HW Ho Hq Hz Ha Hfn Hfl) as (r1 & E1 & H1).
    pose proof (fs_refill Hrf dict s z flush r1 HW Ho Hq Hz Ha Hfn Hfl E1) as F1.
    unfold rle_body. rewrite E1. cbn [bind].
    destruct r1 as [[s1 z1]|[[s1 z1] [bs|]]]; cbn [rst fst snd] in F1.
    + destruct H1 as (HFI1 & Hr1 & Hla1 & Hm1).
      assert (HFI01 : FI s0 z0 flush s1 z1 (evs ++ [])) by (eapply rg_FI_trans; eauto).
      assert (HG1 := g_comp s z s1 z1 evs HFI HG F1).
      destruct (rFI_parts _ _ _ _ _ _ HFI1 Hfn) as (HW1 & Ho1 & Hq1 & Hz1 & Ha1 & Hfn1).
      (* the step, as rstep_ok *)
      destruct (Hsc0 s1 HW1 Hfn1 Hr1 Hla1) as (s2 & E2 & HRSC).
      pose proof HRSC as (ml & -> & Hml & Hmll & Hms).
      assert (Hb : exists s3 bf syms3,
                 rbranch (set_d_match_length s1 ml) = Some (s3, bf) /\ RTS s3 syms3 bf /\ fr s1 s3 /\
                 d_lookahead s3 < d_lookahead s1).
      { unfold rbranch. rewrite fk_match_length_match_length.
        destruct (ml >=? MIN_MATCH) eqn:Em.
        - apply Z.geb_le in Em. apply (Hdi0 s1 ml); auto. lia.
        - rewrite Z.geb_leb in Em. apply Z.leb_gt in Em. apply (Hli0 s1 ml); auto. lia. }
      destruct Hb as (s3 & bf & syms3 & E3 & HTS & Hfr & Hlt).
      assert (Hwr : d_wrap s3 = d_wrap s1) by (destruct Hfr as (_ & (_ & E & _) & _); exact E).
      assert (Ha3 : adler_ok (d_wrap s3) (z_adler z1)) by (rewrite Hwr; exact Ha1).
      destruct (Hbf0 s3 z1 flush syms3 bf HTS Hz1 Ha3 Hfl) as (r & Er & Hr').
      pose proof (fs_step Hsc Hli Hdi Hbf dict s1 z1 flush _ s3 bf syms3 r HW1 Ho1 Hq1 Hz1 Ha1 Hfn1 Hfl
                    Hr1 Hla1 E2 HRSC E3 HTS Hwr Er) as F2.
      assert (Es : rle_step s1 z1 = Some r).
      { rewrite rle_step_eq, E2. cbn [bind]. rewrite E3. exact Er. }
      rewrite Es.
      destruct r as [[s' z']|[[s' z'] o]]; cbn [rst fst snd] in F2.
      * destruct Hr' as ((evs2 & HFI2) & El & Ea).
        assert (HFI2' : FI s1 z1 flush s' z' evs2) by (eapply rg_FI_fr; eauto).
        right. exists (s', z'). split; [reflexivity|]. cbn [fst snd]. split; [split|lia].
        -- exists (evs ++ ([] ++ evs2)).
           eapply rg_FI_trans; [exact Hz0|exact Ha0|exact HFI|].
           eapply rg_FI_trans; [exact Hz|exact Ha|exact HFI1|exact HFI2'].
        -- exact (g_comp s1 z1 s' z' _ HFI01 HG1 F2).
      * destruct Hr' as (Ho' & evs2 & Hc2 & Hb2).
        assert (Hc2' : crel s1 z1 flush s' z' evs2) by (eapply rg_crel_fr; eauto).
        assert (Hb2' : bpost s1 z1 flush s' z' need_more evs2) by (eapply rg_bpost_fr; eauto).
        left. exists (s', z', o). split; [reflexivity|]. subst o. split.
        -- cbv beta iota delta [rloop_res]. exists (evs ++ ([] ++ evs2)). split.
           ++ eapply rg_crel_trans; [exact Hz0|exact Ha0|apply rFI_crel; exact HFI|].
              eapply rg_crel_trans; [exact Hz|exact Ha|apply rFI_crel; exact HFI1|exact Hc2'].
           ++ destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1). destruct (rFI_sp _ _ _ _ _ _ HFI1) as (P2 & A2).
              eapply (rg_bpost_start s0 s z0 z); [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|].
              eapply rg_bpost_start; [exact P2|exact A2|constructor|exact Hb2'].
        -- split; [exact (g_comp s1 z1 s' z' _ HFI01 HG1 F2)|reflexivity].
    + destruct H1 as (-> & Hc1 & Hb1). left. exists (s1, z1, Some need_more). split; [reflexivity|].
      split.
      * cbv beta iota delta [rloop_res]. exists (evs ++ []). split.
        -- eapply rg_crel_trans; [exact Hz0|exact Ha0|apply rFI_crel; exact HFI|exact Hc1].
        -- destruct (rFI_sp _ _ _ _ _ _ HFI) as (P1 & A1).
           eapply rg_bpost_start; [exact P1|exact A1|apply (rFI_last _ _ _ _ _ _ HFI)|exact Hb1].
      * split; [exact (g_comp s z s1 z1 evs HFI HG F1)|reflexivity].
    + destruct H1 as (HFI1 & H1). left. exists (s1, z1, None). split; [reflexivity|].
      split.
      * cbv beta iota delta [rloop_res]. exists (evs ++ []). split; [|exact H1].
        eapply rg_FI_trans; [exact Hz0|exact Ha0|exact HFI|exact HFI1].
      * split; [exact (g_comp s z s1 z1 evs HFI HG F1)|exact I].
  - split; [exists []; cbn [fst snd]; apply FI_refl; auto|].
    cbn [fst snd]. exact (gf_init s0 z0 dict D BS syms0 p Hz0 Ha0 Hq0 Hwt0 Hk0).
  - cbn [fst snd]. destruct HW0 as (Hp0 & (_ & _ & Hws & _) & (_ & Hss & Hsl & _) & _).
    pose proof (rprm_w_bound s0 Hp0) as Hw.
    destruct Hz0 as ((_ & _ & Hai & _) & _). change (Z.of_nat FUEL) with 40. lia.
Qed.
End Loop.

Lemma fs_tail (Hta : rftail_stmt) dict s z flush s' z' bs :
  W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 ->
  0 <= flush <= 5 -> flush <> Z_NO_FLUSH ->
  d_lookahead s = 0 -> z_avail_in z = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
  c_deflate_tail (set_d_insert s 0) z flush = Some (s', z', bs) -> FStep dict s z s' z' (fin_bs bs).
Proof.
  intros HW Ho Hq Hz Ha Hfn Hfl Hnf Hla Hai Hss E Dh BSh syms p' Hd HDh RW RK Hp Hpm.
  destruct (Hta s z flush s' z' bs dict Dh BSh syms p' HW Ho Hq Hz Ha Hfn Hfl Hnf Hla Hai Hss Hd HDh RW RK Hp Hpm E)
    as (x & BS' & syms' & Z & RW' & RK' & Bits & F).
  exists 0, x, BS', syms'. split; [exact Z|]. split; [exact RW'|].
  split; [rewrite Z.add_0_r, sublist_nil, app_nil_r; exact RK'|]. auto.
Qed.

Lemma rle_unfold s z flush r : loop FUEL (rle_body flush) (s, z) = Some r ->
  c_deflate_rle s z flush =
    match r with
    | (s1, z1, Some b) => Some (s1, z1, b)
    | (s1, z1, None) => c_deflate_tail (set_d_insert s1 0) z1 flush
    end.
Proof. intros H. unfold c_deflate_rle. rewrite H. destruct r as [[? ?] [?|]]; reflexivity. Qed.

Local Strategy opaque [loop loop2 c_deflate_tail rle_body].

Lemma W3_W s : W3 s -> W s.
Proof. intros [[H _] _]. exact H. Qed.

(** ** deflate_rle from the parts *)
Theorem rle_assembly :
  rfrefill_stmt -> rfscan_stmt -> rflit_stmt -> rfdist_stmt -> rfbflush_stmt -> rftail_stmt ->
  rrefill_stmt -> rscan_stmt -> rlit_stmt -> rdist_stmt -> rbflush_stmt -> rle_spec ->
  comp_fspec 4 c_deflate_rle.
Proof.
  intros Hrf Hsc Hli Hdi Hbf Hta Hre Hsc0 Hli0 Hdi0 Hbf0 Hrle
    s z flush s' z' bs dict D BS syms p HW3 Ho Hq Hfl Hzi Hwr Hapre Hfn Hd HD Hk Hp Hpm E.
  pose proof (W3_W s HW3) as HW.
  pose proof (adler_pre_ok _ _ Hapre) as Ha.
  pose proof (zin_ok_zall z Hzi) as Hz.
  apply (rk_kcore_rkt dict D BS syms s HW Hfn) in Hk. destruct Hk as [Hk Hwt].
  (* the safety facts of the whole run *)
  destruct (Hrle s z flush (conj HW (conj Ho (conj Hq (conj Hfl (conj Hzi (conj Hwr Ha)))))) Hfn)
    as (s'' & z'' & bs'' & evs'' & E'' & Hc'').
  rewrite E in E''. injection E'' as <- <- <-.
  destruct Hc'' as (HW' & _ & Hsp & _).
  assert (Hfn' : fn_of s' = 4) by (rewrite (fn_of_prm s s' Hsp); exact Hfn).
  assert (HG : GF s z dict D BS p s' z' (fin_bs bs)).
  { destruct (g_loop Hrf Hsc Hli Hdi Hbf Hre Hsc0 Hli0 Hdi0 Hbf0 s z flush dict D BS p syms HW Ho Hq Hz Ha Hfn
                Hfl Hd HD Hp Hpm Hwt Hk) as ([[s1 z1] o] & El & HQ).
    rewrite (rle_unfold s z flush _ El) in E.
    destruct HQ as (HR & HG1 & Ho1).
    destruct o as [bs1|].
    - injection E as -> -> ->. rewrite Ho1. exact HG1.
    - destruct HR as (evs & HFI & Hla & Hai & Hnf & Hss).
      destruct (rFI_parts _ _ _ _ _ _ HFI Hfn) as (HW1 & Ho1' & Hq1 & Hz1 & Ha1 & Hfn1).
      assert (Ew : d_wrap s1 = d_wrap s) by (destruct (rFI_sp _ _ _ _ _ _ HFI) as (_ & (_ & Ew & _)); exact Ew).
      apply (gf_comp s z dict D BS p s1 z1 s' z' (fin_bs bs) (proj1 Hz) Ha Ew Hq1 (gf_bv s Ho) (gf_bv s1 Ho1')
               Hp Hpm Hd HD HG1).
      exact (fs_tail Hta dict s1 z1 flush s' z' bs HW1 Ho1' Hq1 Hz1 Ha1 Hfn1 Hfl Hnf Hla Hai Hss E). }
  destruct HG as (k & X & BS' & syms' & Z & RW & RK & Bits & F).
  exists k, X, BS', syms'. split; [exact Z|]. split; [|split; [exact Bits|exact F]].
  apply (rk_kcore_rkt _ _ _ _ _ HW' Hfn'). split; [exact RK|exact RW].
Qed.

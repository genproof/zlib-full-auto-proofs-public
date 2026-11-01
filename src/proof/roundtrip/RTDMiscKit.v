(* RT-D part MISC: the kit of deflateInit2_, deflateTune, deflateSetHeader.
   The deflate laws' facts for the witnesses W3 / hinv (copies of the bodies of RTDLTCore.core_theory /
   RTDLTHdr.hdr_theory, whose statements are existential), and the frames of the functional invariant. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Export Zlib.proof.roundtrip.RTDLTApiInit.
Require Import Zlib.proof.roundtrip.RTDLTCHuffKit Zlib.proof.roundtrip.RTDLTCMisc Zlib.proof.roundtrip.RTDLTCSpecs2 Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCStored2 Zlib.proof.roundtrip.RTDLTCFast2 Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCHuff2 Zlib.proof.roundtrip.RTDLTCRle2 Zlib.proof.roundtrip.RTDLTCLive2 Zlib.proof.roundtrip.RTDLTCInit Zlib.proof.roundtrip.RTDLTCDict Zlib.proof.roundtrip.RTDLTCDict3 Zlib.proof.roundtrip.RTDLTCStillFill Zlib.proof.roundtrip.RTDLTCStillStored Zlib.proof.roundtrip.RTDLTCStillFast Zlib.proof.roundtrip.RTDLTCStillSlow Zlib.proof.roundtrip.RTDLTCStillHuff Zlib.proof.roundtrip.RTDLTCStillRle Zlib.proof.roundtrip.RTDLTCore.
Require Import Zlib.proof.roundtrip.RTDLTHdrKit Zlib.proof.roundtrip.RTDLTHdrStages Zlib.proof.roundtrip.RTDLTHdr.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The deflate laws' facts for W3 and hinv *)

Lemma misc_W3_facts : Zlib.proof.huffman.Overlay.overlay_statement -> core_facts W3.
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
Lemma misc_hdr_facts : hdr_facts hinv.
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

(** ** A fresh state (deflateInit2_): nothing in the window, no symbol, the chains empty *)

Lemma misc_chain_hok0 : forall s, chain_ok s -> d_strstart s = 0 -> chain_hok s.
Proof.
  intros s [G (G1 & G2 & _)] H0 b Hb. exists (fun q => q = 0). split.
  - destruct (G1 _ (G2 b Hb)) as [E|E]; [exact E|lia].
  - intros q -> Hq. lia.
Qed.

Lemma misc_khash0 : forall s, W s -> d_strstart s = 0 -> d_lookahead s = 0 -> khash s.
Proof.
  intros s HW Hss Hla. destruct HW as (_ & _ & _ & _ & Hh & _).
  unfold khash, whash in *. split.
  - destruct (d_level s =? 0).
    + destruct Hh as [[A B]|[[A B]|A]].
      * left. split; [exact A|]. apply misc_chain_hok0; assumption.
      * right; left. split; [exact A|]. apply misc_chain_hok0; [exact B|exact Hss].
      * right; right. exact A.
    + destruct Hh as [_ B]. apply misc_chain_hok0; assumption.
  - intros _ Hl. unfold MIN_MATCH in Hl. lia.
Qed.

Lemma misc_wtrees0 : forall s, W s -> d_sym_next s = 0 -> wtrees s [].
Proof.
  intros s HW Hsn. destruct HW as (_ & _ & _ & _ & _ & _ & _ & syms & Ht).
  assert (E : syms = []).
  { destruct Ht as ((_ & _ & Hn & _) & _). unfold d_sym_next in Hsn.
    destruct syms as [|x r]; [reflexivity|]. rewrite Zlength_cons in Hn.
    pose proof (Zlength_nonneg r). lia. }
  subst syms. exact Ht.
Qed.

Lemma misc_kwin0 : forall s, d_strstart s = 0 -> d_lookahead s = 0 -> kwin [] s.
Proof.
  intros s Hss Hla. unfold kwin. rewrite Hss, Hla. split; [cbn; lia|]. intros i Hi. lia.
Qed.

Lemma misc_kmatch0 : forall s, d_match_available s = 0 -> kmatch s.
Proof. intros s H E. lia. Qed.

Lemma misc_kcore0 : forall s, W s -> d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
  d_sym_next s = 0 -> kcore [] [] [] [] s /\ kcore2 [] [] [] [] s.
Proof.
  intros s HW Hss Hla Hbs Hsn.
  pose proof (W_ma0 s HW Hss) as Hma.
  pose proof (misc_khash0 s HW Hss Hla) as Hh.
  pose proof (misc_wtrees0 s HW Hsn) as Ht.
  pose proof (misc_kwin0 s Hss Hla) as Hw.
  pose proof (misc_kmatch0 s Hma) as Hm.
  split; split; try exact Hh; [unfold kdata|unfold kdata2]; cbn zeta; rewrite ?app_nil_r;
    rewrite ?Hss, ?Hla, ?Hbs, ?Hma;
    (split; [exact Hw|]); (split; [exact Hm|]); (split; [exact Ht|]);
    (split; [exact I|]); cbn; try (destruct (d_level s =? 0)); repeat split.
Qed.

(** ** deflateInit2_ *)
Lemma misc_init : Zlib.proof.huffman.Overlay.overlay_statement ->
  forall level method wbits mem strategy a1 a2 a3 a4 a5 z s z',
    rs32 level -> rs32 method -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', Z_OK) ->
    d_w_bits s = rwbe wbits /\ d_gzhead s = None /\
    Iapi W3 hinv [] (rwrap_of wbits) [] [] None s (z_total_in z') (z_total_out z') (z_adler z') /\
    W3 s /\ d_strstart s = 0 /\ d_lookahead s = 0 /\ d_block_start s = 0 /\ d_sym_next s = 0 /\
    d_bi_valid s = 0 /\ d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE.
Proof.
  intros Hov level method wbits mem strategy a1 a2 a3 a4 a5 z s z' H1 H2 H3 H4 H5 E.
  pose proof (misc_W3_facts Hov) as CF. pose proof misc_hdr_facts as HF.
  destruct (api_init W3 hinv level method wbits mem strategy a1 a2 a3 a4 a5 z CF HF H1 H2 H3 H4 H5) as [_ B].
  destruct (B _ _ _ E) as (_ & _ & B3). destruct (B3 eq_refl) as (s0 & Es & Hgz & _ & HI).
  injection Es as <-.
  rewrite init_shape in E. destruct (params_ok level method wbits mem strategy) eqn:P; [|discriminate].
  destruct (W3_init level method wbits mem strategy z P)
    as (s1 & z1 & E1 & HW & _ & Hst & _ & _ & _ & _ & _ & _ & Hbv & Hss & Hla & Hbs & Hsn & _ & _ & Hwb & _).
  assert (Es1 : s1 = s).
  { destruct a1; [|discriminate]. destruct (a2 && a3 && a4 && a5); [|discriminate]. rewrite E1 in E. congruence. }
  subst s1.
  split.
  { rewrite Hwb. unfold params_ok in P.
    repeat match type of P with (_ && _) = true => apply andb_prop in P; destruct P as [P ?] end.
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
    unfold rwbe. change (rwb_of wbits) with (wb_of wbits).
    destruct (Z.eqb_spec (wb_of wbits) 8); lia. }
  split; [exact Hgz|]. split; [exact HI|]. split; [exact HW|].
  do 5 (split; [assumption|]).
  rewrite Hst. destruct (wrap_of wbits =? 2); split; discriminate.
Qed.

(** ** deflateTune: only the configuration fields change *)
Lemma misc_KF_tune : forall dict wrap D O fin s tin tout adler g l n c,
  KF dict wrap D O fin s tin tout adler -> KF dict wrap D O fin (tune_set s g l n c) tin tout adler.
Proof. intros dict wrap D O fin s tin tout adler g l n c H. destruct s. exact H. Qed.

Lemma misc_KF2_tune : forall dict wrap D O fin s tin tout adler g l n c,
  KF2 dict wrap D O fin s tin tout adler -> KF2 dict wrap D O fin (tune_set s g l n c) tin tout adler.
Proof. intros dict wrap D O fin s tin tout adler g l n c H. destruct s. exact H. Qed.

Lemma misc_tune : Zlib.proof.huffman.Overlay.overlay_statement ->
  forall wrap s tin tout adler good lazy nice chain z s' z' code,
    Iapi W3 hinv [] wrap [] [] None s tin tout adler -> rs32 good -> rs32 lazy -> rs32 nice -> rs32 chain ->
    c_deflateTune s z good lazy nice chain = Some (s', z', code) ->
    s' = tune_set s good lazy nice chain /\ d_w_bits s' = d_w_bits s /\ d_gzhead s' = d_gzhead s /\
    Iapi W3 hinv [] wrap [] [] None s' tin tout adler.
Proof.
  intros Hov wrap s tin tout adler good lazy nice chain z s' z' code HI H1 H2 H3 H4 E.
  pose proof (misc_W3_facts Hov) as CF. pose proof misc_hdr_facts as HF.
  destruct (api_tune W3 hinv wrap s tin tout adler good lazy nice chain z CF HF HI H1 H2 H3 H4)
    as (s1 & E1 & Hg & _ & HI1).
  rewrite E1 in E. injection E as <- _ _.
  unfold c_deflateTune in E1.
  rewrite (Iapi_bad_state W3 hinv _ _ _ _ _ _ _ _ _ HF HI) in E1. injection E1 as <-.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hg|exact HI1].
Qed.

(** ** deflateSetHeader *)
Lemma misc_status_O0 : forall W HI dict D fin s tin tout adler,
  Iapi W HI dict 2 D [] fin s tin tout adler -> d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE.
Proof.
  intros W HI dict D fin s tin tout adler HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as [[[-> _] | [-> _]] _]; split; discriminate.
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - destruct P2 as (_ & _ & _ & Hne & _). exfalso. apply (Hne ltac:(discriminate)). reflexivity.
  - destruct P3 as (_ & _ & _ & _ & Hne & _). exfalso. apply (Hne ltac:(discriminate)). reflexivity.
Qed.

Lemma misc_head_iapi : Zlib.proof.huffman.Overlay.overlay_statement ->
  forall dict s tin tout adler h,
    Iapi W3 hinv dict 2 [] [] None s tin tout adler -> rhdr_ok h ->
    Iapi W3 hinv dict 2 [] [] None (set_d_gzhead s (Some h)) tin tout adler.
Proof.
  intros Hov dict s tin tout adler h HI Hh.
  pose proof (misc_W3_facts Hov) as CF. pose proof misc_hdr_facts as HF.
  exact (proj2 (proj1 (api_head W3 hinv dict 2 s tin tout adler h (mkST [] 0 0 0 [] 0 0 0 None) CF HF HI Hh)
                 eq_refl)).
Qed.

Lemma misc_kcore_gzhead : forall dict D BS syms s g,
  kcore dict D BS syms s -> kcore dict D BS syms (set_d_gzhead s g).
Proof. intros dict D BS syms s g H. destruct s. exact H. Qed.

Lemma misc_kcore2_gzhead : forall dict D BS syms s g,
  kcore2 dict D BS syms s -> kcore2 dict D BS syms (set_d_gzhead s g).
Proof. intros dict D BS syms s g H. destruct s. exact H. Qed.

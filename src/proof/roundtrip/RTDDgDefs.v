(* RT-D part DEFLATE: the definitions shared by the stage lemmas of deflate() over interface v3
   (RTDV3.v: kmatch3 / kdata3 / kcore3).  The v2 definitions with kcore3 in place of kcore2.

   - [hinv_facts]: the header invariant of the deflate laws (RTDLTHdrKit.hinv) has [hdr_facts].
   - [KF2g] = RTDV2.KF2 with kcore3; [KFd] = KF2g /\ [hpre] (while the header is not complete, the bytes produced
     and pending are a prefix of a header of [khdr]); [KFd_KF3]: KFd is RTDV3.KF3.  [Krtd] = Iapi W3 hinv /\ KFd.
   - [KMid]: KFd of the data consumed and the output produced so far, inside a call.
   - [kcore3_frame]: kcore3 only reads what [core_eq] keeps.
   The deflate laws' stage lemmas come from the RTDDfX files (copies of the RTDLTApi files for aout <= 2097152). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV3.
Require Export Zlib.proof.roundtrip.RTDDfXDeflate.
Require Export Zlib.proof.roundtrip.RTDLTHdrKit.
Require Import Zlib.proof.roundtrip.RTDLTHdrStages Zlib.proof.roundtrip.RTDLTHdr.
Require Import Zlib.proof.roundtrip.RTDLTCMisc.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The header invariant *)
Lemma hinv_facts : hdr_facts hinv.
Proof.
  split.
  - exact hinv_frame.
  - exact hinv_status.
  - intros s z H k [Hp [Ho [P0 [Hs [Hbv [Hav [Ht [Hok Hcase]]]]]]]].
    assert (Hav' : 0 <= z_avail_out z) by lia.
    rewrite hdr_stages_eq.
    destruct Hcase as [[Hst [Hw [EH ->]]] | [[Hst [Hw [EH ->]]] | Hi]].
    + destruct (zlib_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw) as [s1 [z1 [r1 [E [Es Hpost]]]]].
      rewrite E. subst H. destruct r1 as [c|].
      * exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
      * cbn [then_stage bind]. rewrite (proj1 (busy_rest s1 z1 Es)).
        exists s1, z1, None. split; [reflexivity|exact Hpost].
    + rewrite zlib_id by (rewrite Hst; discriminate). cbn [then_stage bind].
      assert (EH' : H = gz_hdr_bytes (d_gzhead s) (xfl_byte s)) by (rewrite EH; unfold hdr_bytes; rewrite Hw; reflexivity).
      rewrite EH'.
      destruct (gzip_stage s z Hp Ho P0 Hs Hbv Hav' Ht Hst Hw Hok) as [s1 [z1 [r1 [E Hr]]]].
      rewrite E. destruct Hr as [[-> Hg] | [Es Hpost]].
      * cbn [then_stage bind]. apply chain_extra. exact Hg.
      * destruct r1 as [c|].
        -- exists s1, z1, (Some c). split; [reflexivity|exact Hpost].
        -- cbn [then_stage bind]. rewrite (proj2 (busy_rest s1 z1 Es)).
           exists s1, z1, None. split; [reflexivity|exact Hpost].
    + pose proof (hinv_gent s z H k Hp Ho P0 Hs Hbv Hav' Ht Hi) as Hg.
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

(** ** The invariant *)

(* the bytes [OP] produced and pending are the first bytes of a header deflate may write *)
Definition hpre (dict : list Z) (wrap : Z) (s : dstate) (OP : list Z) : Prop :=
  exists HDR, khdr dict wrap s HDR /\ OP = sublist 0 (Zlength OP) HDR.

(* KF2 with kcore3 *)
Definition KF2g : rinv := fun dict wrap D O fin s tin tout adler =>
  (wrap <> 2 -> d_gzhead s = None) /\
  exists BS syms,
    kcore3 dict D BS syms s /\
    ((d_status s <> BUSY_STATE /\ d_status s <> FINISH_STATE /\ BS = [] /\ d_bi_valid s = 0) \/
     (d_status s = BUSY_STATE /\
      exists HDR, khdr dict wrap s HDR /\ allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false) \/
     (d_status s = FINISH_STATE /\ BS <> [] /\ F.data dict BS = D /\
      exists HDR, khdr dict wrap s HDR /\
        ((d_wrap s = wrap /\ allbits O s = F.bytes_bits HDR ++ enc_out 0 BS true) \/
         (0 < wrap /\ d_wrap s = - wrap /\ d_bi_valid s = 0 /\
          O ++ pend s = HDR ++ F.deflate_bytes BS ++ ftrailer wrap D)))).

Definition KFd : rinv := fun dict wrap D O fin s tin tout adler =>
  KF2g dict wrap D O fin s tin tout adler /\
  (d_status s <> BUSY_STATE -> d_status s <> FINISH_STATE -> hpre dict wrap s (O ++ pend s)).

Definition Krtd : rinv := fun dict wrap D O fin s tin tout adler =>
  Iapi W3 hinv dict wrap D O fin s tin tout adler /\ KFd dict wrap D O fin s tin tout adler.

Lemma KFd_KF3 : forall dict wrap D O fin s tin tout adler,
  KFd dict wrap D O fin s tin tout adler <-> KF3 dict wrap D O fin s tin tout adler.
Proof.
  intros dict wrap D O fin s tin tout adler. unfold KFd, KF2g, KF3, hpre. split.
  - intros [[Hg (BS & syms & Hk & P)] Hh]. split; [exact Hg|]. exists BS, syms. split; [exact Hk|].
    destruct P as [(A1 & A2 & A3 & A4)|P]; [left; exact (conj A1 (conj A2 (conj A3 (conj A4 (Hh A1 A2)))))|right; exact P].
  - intros [Hg (BS & syms & Hk & P)]. split.
    + split; [exact Hg|]. exists BS, syms. split; [exact Hk|].
      destruct P as [(A1 & A2 & A3 & A4 & _)|P]; [left; tauto|right; exact P].
    + intros N1 N2. destruct P as [(_ & _ & _ & _ & X)|[(E & _)|(E & _)]]; [exact X|contradiction|contradiction].
Qed.

(* inside a call offered [inb]: KFd of the data consumed and the output produced so far *)
Definition KMid (dict : list Z) (wrap : Z) (D O inb : list Z) (s : dstate) (z : strm) : Prop :=
  KFd dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) None s 0 0 0.

Lemma KF2g_args : forall dict wrap D O fin s tin tout adler fin' tin' tout' adler',
  KF2g dict wrap D O fin s tin tout adler -> KF2g dict wrap D O fin' s tin' tout' adler'.
Proof. intros. exact H. Qed.

Lemma KFd_args : forall dict wrap D O fin s tin tout adler fin' tin' tout' adler',
  KFd dict wrap D O fin s tin tout adler -> KFd dict wrap D O fin' s tin' tout' adler'.
Proof. intros. exact H. Qed.

(** ** kcore3 only reads the fields [core_eq] keeps *)
Lemma kcore3_transfer : forall dict D BS syms s s',
  wsame s s' -> d_ins_h s' = d_ins_h s -> kcore3 dict D BS syms s -> kcore3 dict D BS syms s'.
Proof.
  intros dict D BS syms s s' HS Hih HK. destruct HS.
  unfold kcore3, kdata3, kwin, kmatch3, khash, chain_hok, h3, primed, update_hash, wtrees, tree_ok,
    sym_ok, lim, slide_hc, fn_of, MAX_DIST in *.
  unfold d_L, d_level, d_strategy, d_matches, d_sym_next in *.
  cbn [d_strstart d_w_size d_hash_size d_head d_prev d_w_mask d_window d_hash_shift d_hash_mask d_tr
       d_lookahead d_ins_h set_d_prev set_d_head] in *.
  rewrite ?ws_wsize, ?ws_wbits, ?ws_wmask, ?ws_window, ?ws_prev, ?ws_head, ?ws_hsize,
    ?ws_hmask, ?ws_hshift, ?ws_bs, ?ws_ml, ?ws_ma, ?ws_ss, ?ws_ms, ?ws_la, ?ws_ins, ?Hih,
    ?ws_lt, ?ws_dt, ?ws_blt, ?ws_wk, ?ws_sn, ?ws_mt, ?ws_lb, ?ws_lv, ?ws_st, ?ws_obl, ?ws_pbl.
  unfold sym_region, d_L, d_sym_next in ws_sym. rewrite ws_sn, ws_lb in ws_sym.
  destruct HK as [(A1 & A2 & (T & B1 & B2 & B3 & B4) & A4) A5].
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
  rewrite T3 in ws_sym. injection ws_sym as E1 E2.
  split; [|exact A5]. split; [exact A1|]. split; [exact A2|]. split; [|exact A4].
  split; [|exact (conj B1 (conj B2 (conj B3 B4)))].
  refine (conj T1 (conj T2 (conj T3 (conj T4 (conj _ (conj _ T7)))))); [rewrite E1; exact T5 | rewrite E2; exact T6].
Qed.

Lemma kcore3_frame : forall dict D BS syms s s',
  core_eq s s' -> kcore3 dict D BS syms s -> kcore3 dict D BS syms s'.
Proof.
  intros dict D BS syms s s' He. apply kcore3_transfer; [exact (wsame_core_eq s s' He)|].
  exact (f_equal (fun x => d_ins_h x) (proj1 He)).
Qed.

(** ** The compression function of the state, whichever it is *)
Definition compf_fspec3 : Prop := forall f, comp_fspec3 f c_compress_func.

Lemma compf_of :
  comp_fspec3 0 c_deflate_stored -> comp_fspec3 1 c_deflate_fast -> comp_fspec3 2 c_deflate_slow ->
  comp_fspec3 3 c_deflate_huff -> comp_fspec3 4 c_deflate_rle -> compf_fspec3.
Proof.
  intros H0 H1 H2 H3 H4 f s z flush s' z' bs dict D BS syms p HW Ho Hq Hfl Hz Hw Ha Hfn Hdi HD HK Hp Hp8 R.
  rewrite (compress_dispatch s z flush (W3_prm s HW)) in R.
  destruct (Z.eqb_spec (fn_of s) 0) as [E0|N0]; [eapply H0; eauto|].
  destruct (Z.eqb_spec (fn_of s) 1) as [E1|N1]; [eapply H1; eauto|].
  destruct (Z.eqb_spec (fn_of s) 2) as [E2|N2]; [eapply H2; eauto|].
  destruct (Z.eqb_spec (fn_of s) 3) as [E3|N3]; [eapply H3; eauto|].
  assert (E4 : fn_of s = 4).
  { destruct (W3_prm s HW) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _).
    unfold fn_of in *.
    destruct (Z.eqb_spec (d_level s) 0); [congruence|].
    destruct (d_strategy s =? Z_HUFFMAN_ONLY); [congruence|].
    destruct (d_strategy s =? Z_RLE); [reflexivity|].
    exfalso. assert (Hc : forall l, 1 <= l <= 9 -> cfg_f l = 1 \/ cfg_f l = 2).
    { intros l Hl'.
      assert (l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst l; vm_compute; auto. }
    destruct (Hc (d_level s) ltac:(lia)); congruence. }
  eapply H4; eauto.
Qed.

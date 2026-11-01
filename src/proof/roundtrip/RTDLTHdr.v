(** * The model theory of the deflate laws, header part: the zlib / gzip header stages of deflate()
    (interface RTDLTIface.hdr_facts).

    Choose the invariant [HI s a H k] of a stream in the middle of the gzip header [H] (status EXTRA, NAME,
    COMMENT or HCRC, [k] header bytes handed to pending_buf, strm->adler = [a]: the CRC-32 of those bytes when
    the header has a header CRC) and prove [hdr_facts HI].  [HI] is [RTDLTHdrKit.hinv]; the stages are proved in
    RTDLTHdrStages.v (with RTDLTHdrExtra.v and RTDLTHdrStr.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTIface.
Require Import Zlib.proof.roundtrip.RTDLTHdrKit Zlib.proof.roundtrip.RTDLTHdrStages.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma hinv_status : forall s a H k, hinv s a H k ->
  d_wrap s = 2 /\ (exists h, d_gzhead s = Some h) /\
  (d_status s = EXTRA_STATE \/ d_status s = NAME_STATE \/ d_status s = COMMENT_STATE \/
   d_status s = HCRC_STATE) /\
  (exists xfl, H = gz_hdr_bytes (d_gzhead s) xfl) /\ 10 <= k < Zlength H.
Proof.
  intros s a H k [Hw [h [xfl [Eh [Hok [EH [Hst [Hidx [Ek Ea]]]]]]]]].
  split; [exact Hw|]. split; [exists h; exact Eh|].
  split; [destruct Hst as [[S _]|[[S _]|[[S _]|[S _]]]]; auto|].
  split; [exists xfl; rewrite Eh; exact EH|].
  pose proof (gz_extra_len_eq h Hok) as Le.
  assert (LH : Zlength H = 10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) +
                           Zlength (cstr_bytes (gz_comment h)) + Zlength (gz_crc_bytes h xfl)).
  { rewrite EH, gz_hdr_split, !Zlength_app, gz_pre_len. lia. }
  pose proof (Zlength_nonneg (gz_extra_bytes h)). pose proof (Zlength_nonneg (cstr_bytes (gz_name h))).
  pose proof (Zlength_nonneg (cstr_bytes (gz_comment h))). pose proof (Zlength_nonneg (gz_crc_bytes h xfl)).
  destruct Hst as [[S [Hx Hg]]|[[S Hn]|[[S Hc]|[S Hh]]]]; rewrite S in Hidx, Ek.
  - change (gpos h EXTRA_STATE (d_gzindex s))
      with (10 + match gz_extra h with Some _ => 2 + d_gzindex s | None => 0 end) in Ek.
    change (gidx_ok h EXTRA_STATE (d_gzindex s))
      with (match gz_extra h with Some _ => 0 <= d_gzindex s <= gz_extra_len h | None => d_gzindex s = 0 end)
      in Hidx.
    destruct (gz_extra h); [|contradiction]. lia.
  - change (gpos h NAME_STATE (d_gzindex s)) with (10 + Zlength (gz_extra_bytes h) + d_gzindex s) in Ek.
    change (gidx_ok h NAME_STATE (d_gzindex s))
      with (match gz_name h with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end) in Hidx.
    destruct (gz_name h); [|contradiction]. cbn [cstr_bytes] in *. lia.
  - change (gpos h COMMENT_STATE (d_gzindex s))
      with (10 + Zlength (gz_extra_bytes h) + Zlength (cstr_bytes (gz_name h)) + d_gzindex s) in Ek.
    change (gidx_ok h COMMENT_STATE (d_gzindex s))
      with (match gz_comment h with Some l => 0 <= d_gzindex s < Zlength l | None => d_gzindex s = 0 end)
      in Hidx.
    destruct (gz_comment h); [|contradiction]. cbn [cstr_bytes] in *. lia.
  - change (gpos h HCRC_STATE (d_gzindex s)) with (Zlength (gz_body h 0)) in Ek.
    rewrite gz_body_len in Ek.
    assert (Zlength (gz_crc_bytes h xfl) = 2).
    { unfold gz_crc_bytes. destruct (gz_hcrc h =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity]. }
    lia.
Qed.

Lemma hinv_frame : forall s s' a H k, hinv s a H k ->
  d_status s' = d_status s -> d_gzindex s' = d_gzindex s -> d_gzhead s' = d_gzhead s ->
  d_wrap s' = d_wrap s -> d_pending_buf_size s' = d_pending_buf_size s -> hinv s' a H k.
Proof.
  intros s s' a H k Hi E1 E2 E3 E4 _. unfold hinv in *. rewrite E1, E2, E3, E4. exact Hi.
Qed.

Lemma hinv_gent : forall s z H k,
  prm s -> outok s -> d_pending s = 0 -> d_sym_next s = 0 -> d_bi_valid s = 0 ->
  0 <= z_avail_out z -> 0 <= z_total_out z <= 1099511627776 ->
  hinv s (z_adler z) H k -> gent s z H k (d_status s) s z.
Proof.
  intros s z H k Hp Ho P0 Hs Hbv Hav Ht Hi.
  destruct (hinv_status _ _ _ _ Hi) as [_ [_ [_ [_ Hk]]]].
  destruct Hi as [Hw [h [xfl [Eh [Hok [EH [Hst [Hidx [Ek Ea]]]]]]]]].
  split; [reflexivity|]. split; [exact Hw|]. exists h, xfl.
  split; [exact Eh|]. split; [exact Hok|]. split; [exact EH|]. split; [exact Hidx|].
  rewrite <- Ek. split; [|exact Ea].
  apply hmid_init_k; auto. lia.
Qed.

Theorem hdr_theory : exists HI, hdr_facts HI.
Proof.
  exists hinv. split.
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

(* One pass of inflate_fast's loop (one symbol) against the abstract decoder's steps of that symbol. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastKit.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastIterKit.
Import ListNotations.
Local Open Scope Z_scope.


(* One pass of the loop: refill, the literal/length code, then by its op the literal, the end of the block, an
   invalid code, or a length (its extra bits, refill, the distance code, its extra bits, the copy).  Each case is a
   lemma of SISimFastIterKit.v over the machines after each piece (fat) and the abstract trace of the symbol. *)
Lemma sf_iter : fwalk_stmt -> fcopy_stmt -> fmatch_stmt -> fiter_stmt.
Proof.
  intros W C M. unfold fiter_stmt.
  intros src P0 O0 m a Hb Hm Ha Hq HO Hs Hw Haw Hbits Hnx Hout.
  enough (G: forall go m', fast_iter lenfix_list distfix_list m = (go, m') -> fpost src P0 O0 m a go m').
  { destruct (fast_iter lenfix_list distfix_list m) as [go m'] eqn:EF. exact (G go m' eq_refl). }
  intros go m' EF. rewrite DK.fast_iter_eq in EF.
  (* the tables and the facts of the invariant at LEN *)
  assert (Hdm: decode_mode (i_mode (a_s a))) by (unfold decode_mode; right; left; exact Ha).
  destruct (s3_len _ (aw_s3 _ _ Haw) Hdm) as (szL & _ & TVL & LOK).
  destruct (md_tables _ (aw_md _ _ Haw) Hdm) as [_ (szD & _ & TVD)].
  pose proof (aw_dtab _ _ Haw Hdm) as DOK.
  assert (Hsane: i_sane (m_s m) = 1) by (rewrite (se_sane _ _ Hs); apply (sw_sane _ (aw_swf _ _ Haw))).
  pose proof (se_codes _ _ Hs) as Ecodes.
  pose proof (se_lencode _ _ Hs) as Elc. pose proof (se_lenbits _ _ Hs) as Elb.
  pose proof (se_distcode _ _ Hs) as Edc. pose proof (se_distbits _ _ Hs) as Edb.
  unfold tvalid_b in TVL, TVD.
  rewrite <- Elc, <- Elb in TVL. apply (tvalid_g_codes _ _ (m_s m)) in TVL; [|congruence].
  rewrite <- Edc, <- Edb in TVD. apply (tvalid_g_codes _ _ (m_s m)) in TVD; [|congruence].
  destruct a as [sa qa Oa]. unfold a_mode in Ha.
  cbn [a_s a_q a_O] in Ha, Hq, HO, Hs, Hdm, LOK, DOK, Ecodes, Elc, Elb, Edc, Edb. subst qa.
  (* refill, the literal/length code *)
  pose proof (fat_init _ _ _ Hb) as F0.
  pose proof (fat_facts _ _ _ _ _ _ _ F0) as (Hb0 & _).
  assert (R1: m_bits m < 15 -> m_nx m + 2 <= Zlength (m_inp m)) by lia.
  destruct (fat_refill_v _ _ _ _ _ _ _ F0 Hbits R1) as (m1 & nx1 & b1 & Em1 & F1 & HR1). clear R1.
  rewrite Em1 in EF.
  destruct (adecode lenfix_list distfix_list src (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) len_islink (mq P0 m))
    as [here l] eqn:E1.
  assert (B1: 15 <= b1) by (destruct HR1; lia).
  destruct (fat_walk_v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W F1 B1 TVL (or_introl (conj eq_refl (conj eq_refl eq_refl))) E1)
    as (m2 & EW & F2 & Hl & Eok & Fok & (i & Hi & Ei)).
  unfold DK.lwalk in EF. rewrite EW in EF. change (DK.fdisp (m_s m) here m2 = (go, m')) in EF.
  assert (E1a: adecode lenfix_list distfix_list src sa (i_lencode sa) (i_lenbits sa) len_islink (mq P0 m) = (here, l)).
  { rewrite <- E1. apply adecode_eq; congruence. }
  destruct (ar_walk (m_bits m) (m_nx m) (Zlength (m_inp m)) b1 nx1 l ltac:(lia) Hnx Hl HR1) as (Ar1 & Ar2 & Ar3 & Ar4).
  pose proof (fat_q _ _ _ _ _ _ _ F2) as Q2.
  pose proof F2 as (_ & _ & _ & _ & _ & O2).
  apply final_ok_LENS in Fok.
  destruct Fok as [[Hop Hv]|[[Hop Hv]|[Hop|[H64 H48]]]].
  - (* a literal *)
    unfold DK.fdisp in EF. rewrite Hop, Z.eqb_refl in EF. injection EF as <- <-. rewrite O2.
    apply (close_go _ _ _ _ _ _ _ _ _ _ _
             (at_lit src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) sa (mq P0 m) Oa here l Ha E1a Hop ltac:(lia) ltac:(rewrite HO, Zlength_app; lia)) F2 Ar2 Ar3).
    + cbn [a_O]. rewrite HO, app_assoc. reflexivity.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    + reflexivity.
    + do 3 eexists. reflexivity.
  - (* a length *)
    destruct (op_code (e_op here) ltac:(lia)) as (L15 & L16 & L32 & L64 & L0).
    assert (Hlok: e_val here + 2 ^ Z.land (e_op here) 15 - 1 <= 258).
    { assert (Ea: here = tab_entry lenfix_list distfix_list sa (i_lencode sa) i).
      { rewrite Ei, Elc. apply tab_entry_codes. exact Ecodes. }
      pose proof (LOK i Hi) as Lk. rewrite <- Ea in Lk. rewrite L15. apply Lk. lia. }
    unfold DK.fdisp in EF. rewrite (proj2 (Z.eqb_neq _ _) L0), (proj2 (Z.eqb_neq _ _) L16) in EF.
    cbn [negb] in EF. unfold DK.flen in EF.
    assert (He1: 0 <= Z.land (e_op here) 15 <= 5) by lia.
    destruct (ar_lenx (m_bits m) (m_nx m) (Zlength (m_inp m)) b1 nx1 l (Z.land (e_op here) 15) 0 0
                ltac:(lia) Hnx Hl He1 HR1 Ar1) as (P3 & _).
    destruct (fat_lenx _ _ _ _ _ _ _ here F2 Eok ltac:(lia) ltac:(lia) P3) as (m3 & nx3 & b3 & EL & F3 & HL3).
    clear P3. rewrite EL in EF. lazy beta iota zeta in EF.
    destruct (ar_lenx (m_bits m) (m_nx m) (Zlength (m_inp m)) b1 nx1 l (Z.land (e_op here) 15) nx3 b3
                ltac:(lia) Hnx Hl He1 HR1 Ar1) as (_ & Ar5). destruct (Ar5 HL3) as (Ar6 & P4). clear Ar5.
    destruct (fat_refill_v _ _ _ _ _ _ _ F3 ltac:(lia) P4) as (m4 & nx4 & b4 & Em4 & F4 & HR4). clear P4.
    rewrite Em4 in EF.
    destruct (adecode lenfix_list distfix_list src (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m)) dist_islink
                (mq P0 m + l + Z.land (e_op here) 15)) as [here2 l2] eqn:E2.
    assert (B4: 15 <= b4) by (destruct HR4; lia).
    destruct (fat_walk_v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W F4 B4 TVD (or_intror (conj eq_refl (conj eq_refl eq_refl))) E2)
      as (m5 & EW2 & F5 & Hl2 & Eok2 & Fok2 & _).
    unfold DK.dwalk in EF. rewrite EW2 in EF. lazy beta iota zeta in EF.
    pose proof (fat_q _ _ _ _ _ _ _ F5) as Q5.
    assert (E2a: adecode lenfix_list distfix_list src sa (i_distcode sa) (i_distbits sa) dist_islink
                   (mq P0 m + l + Z.land (e_op here) 15) = (here2, l2)).
    { rewrite <- E2. apply adecode_eq; congruence. }
    assert (Hd: dist_ok here2) by (pose proof (DOK src (mq P0 m + l + Z.land (e_op here) 15)) as D; rewrite E2a in D; exact D).
    destruct (at_len src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) sa (mq P0 m) Oa here l here2 l2 Ha E1a
                L0 L32 L64 ltac:(lia) ltac:(lia) E2a ltac:(lia) ltac:(lia)) as [AB AOK].
    apply final_ok_DISTS in Fok2.
    destruct Fok2 as [[Hop2 Hv2]|[H64' H48']].
    + (* a distance *)
      destruct (op_code (e_op here2) Hop2) as (M15 & M16 & M32 & M64 & M0).
      rewrite (proj2 (Z.eqb_neq _ _) M16) in EF. cbn [negb] in EF. lazy beta iota zeta in EF.
      assert (He2: 0 <= Z.land (e_op here2) 15 <= 13) by lia.
      assert (Hdok: e_val here2 + 2 ^ Z.land (e_op here2) 15 - 1 <= 32768) by (apply Hd; exact M16).
      destruct (ar_dist (m_bits m) (m_nx m) (Zlength (m_inp m)) b1 nx1 l (Z.land (e_op here) 15) nx3 b3 nx4 b4 l2
                  (Z.land (e_op here2) 15) ltac:(lia) Hnx Hl He1 Hl2 He2 HR1 Ar1 HL3 HR4)
        as (Ar7 & Ar8 & Ar9 & P5 & P5').
      destruct (fat_distx _ _ _ _ _ _ _ here2 F5 ltac:(lia) ltac:(lia) P5 P5') as (m6 & nx6 & b6 & EXd & F6 & HX6).
      clear P5 P5'. rewrite EXd in EF. lazy beta iota zeta in EF.
      destruct (ar_distx (m_bits m) (m_nx m) b4 nx4 l2 (Z.land (e_op here2) 15) nx6 b6 He2 Ar7 Ar8 Ar9 HX6)
        as (Ar10 & Ar11).
      pose proof (fat_q _ _ _ _ _ _ _ F6) as Q6.
      pose proof (sik_sbits_range src (mq P0 m + l) (Z.land (e_op here) 15) ltac:(lia)) as S1.
      pose proof (sik_sbits_range src (mq P0 m + l + Z.land (e_op here) 15 + l2) (Z.land (e_op here2) 15) ltac:(lia)) as S2.
      assert (P1: 2 ^ Z.land (e_op here) 15 <= 32) by (change 32 with (2 ^ 5); apply Z.pow_le_mono_r; lia).
      apply (close_dist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C M (AOK M64 ltac:(lia) ltac:(lia)) F6 Ar10 Ar11);
        [| |exact Hw|exact Hsane|exact HO|exact Hout|exact EF].
      * rewrite u32_small; lia.
      * rewrite u32_small; lia.
    + (* an invalid distance code *)
      destruct (op_invalid _ H64' H48') as (_ & H16' & _).
      rewrite H16', Z.eqb_refl in EF. cbn [negb] in EF. injection EF as <- <-.
      destruct (AB H64') as (a' & Ar & Am & AO).
      destruct (ar_dist (m_bits m) (m_nx m) (Zlength (m_inp m)) b1 nx1 l (Z.land (e_op here) 15) nx3 b3 nx4 b4 l2 0
                  ltac:(lia) Hnx Hl He1 Hl2 ltac:(lia) HR1 Ar1 HL3 HR4) as (_ & Ar8 & Ar9 & _).
      apply (close_bad _ _ _ _ _ _ _ _ _ _ _ Ar F5 Ar8 Ar9); [rewrite AO, HO; reflexivity|exact Am].
  - (* the end of the block *)
    unfold DK.fdisp in EF. rewrite Hop in EF.
    replace (96 =? 0) with false in EF by reflexivity. replace (Z.land 96 16 =? 0) with true in EF by reflexivity.
    replace (Z.land 96 32 =? 0) with false in EF by reflexivity. cbn [negb] in EF. injection EF as <- <-.
    apply (close_type _ _ _ _ _ _ _ _ _ _ (at_eob src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) sa (mq P0 m) Oa here l Ha E1a Hop ltac:(lia))
             F2 Ar2 Ar3).
    + cbn [a_O]. rewrite HO. reflexivity.
    + reflexivity.
    + do 3 eexists. reflexivity.
  - (* an invalid code *)
    destruct (op_invalid _ H64 H48) as (H0 & H16 & H32).
    unfold DK.fdisp in EF. rewrite (proj2 (Z.eqb_neq _ _) H0), H16, H32, Z.eqb_refl in EF. cbn [negb] in EF.
    injection EF as <- <-.
    destruct (at_lbad src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) sa (mq P0 m) Oa here l Ha E1a H0 H32 H64 ltac:(lia))
      as (a' & Ar & Am & AO).
    apply (close_bad _ _ _ _ _ _ _ _ _ _ _ Ar F2 Ar2 Ar3); [rewrite AO, HO; reflexivity|exact Am].
Qed.

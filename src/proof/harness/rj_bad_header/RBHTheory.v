(* Law rj_bad_header, the pure part: one inflate() call (the model run2 of src/proof/inflate/Model2.v) on a
   stream just after inflateInit2_(strm, w) with a zlib wrapper (w = 0, 8..15, or those plus 32), whose input
   starts with two bytes CMF, FLG that break RFC 1950 2.2 (and are not the gzip magic 1f 8b when w selects
   gzip detection too), stops in BAD: it returns Z_DATA_ERROR, writes no output and leaves total_out as it
   was.  The HEAD case pulls exactly the two bytes, the header tests of c_HEAD2 reject them, BAD returns
   Z_DATA_ERROR, and inf_leave neither updates the window (no output, wsize 0) nor counts output. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

(* the harness's test: CMF*256 + FLG not a multiple of 31, CM not 8, CINFO above 7, or CINFO + 8 above
   the window size low (when low is not 0) *)
Definition rbh_bad (low cmf flg: Z) : Prop :=
  (cmf * 256 + flg) mod 31 <> 0 \/ Z.land cmf 15 <> 8 \/ 7 < Z.shiftr cmf 4 \/
  (low <> 0 /\ low < Z.shiftr cmf 4 + 8).

(* the windowBits of the law: the zlib wrapper, with or without gzip detection *)
Definition rbh_wbits (w: Z) : Prop :=
  0 <= w <= 47 /\ Z.land w 16 = 0 /\ (Z.land w 15 = 0 \/ 8 <= Z.land w 15).

(* NEEDBITS(16) from an empty bit buffer at the start of the input pulls the first two bytes *)
Lemma rbh_needbits: forall m,
  m_bits m = 0 -> m_hold m = 0 -> m_nx m = 0 -> 2 <= Zlength (m_inp m) ->
  0 <= Znth 0 (m_inp m) < 256 -> 0 <= Znth 1 (m_inp m) < 256 ->
  needbits 16 m = set_m_bits (set_m_hold (set_m_nx m 2) (Znth 0 (m_inp m) + Znth 1 (m_inp m) * 256)) 16.
Proof.
  intros [s h inp aout nx ow hold bits min mout ret lv ad msg tin tout snx sow]; simpl.
  intros -> -> -> Hl H0 H1.
  unfold needbits, needbits_f, m_have, pull, u64, u32; simpl.
  replace (Zlength inp - 0 =? 0) with false by lia.
  rewrite !Z.mod_small by lia. simpl.
  replace (Zlength inp - 1 =? 0) with false by lia.
  change (Z.pow_pos 2 8) with 256.
  replace (0 + Znth 0 inp * 1 + Znth 1 inp * 256) with (Znth 0 inp + Znth 1 inp * 256) by lia.
  reflexivity.
Qed.

(* the case HEAD on such a header: BAD (incorrect header check, unknown method or invalid window size) *)
Lemma rbh_head: forall m,
  i_mode (m_s m) = HEAD -> (i_wrap (m_s m) = 5 \/ i_wrap (m_s m) = 7) -> i_head (m_s m) = false ->
  m_bits m = 0 -> m_hold m = 0 -> m_nx m = 0 -> m_leave m = 0 -> 2 <= Zlength (m_inp m) ->
  0 <= Znth 0 (m_inp m) < 256 -> 0 <= Znth 1 (m_inp m) < 256 ->
  rbh_bad (i_wbits (m_s m)) (Znth 0 (m_inp m)) (Znth 1 (m_inp m)) ->
  (i_wrap (m_s m) = 5 \/ Znth 0 (m_inp m) <> 31 \/ Znth 1 (m_inp m) <> 139) ->
  exists e, c_HEAD2 m = IBrk (set_bad (needbits 16 m) e) \/
            c_HEAD2 m = IBrk (set_bad (dropbits 4 (needbits 16 m)) e).
Proof.
  intros m Hmode Hwrap Hhead Hbits Hhold Hnx Hlv Hlen H0 H1 Hbad Hgz.
  set (b0 := Znth 0 (m_inp m)) in *. set (b1 := Znth 1 (m_inp m)) in *.
  unfold c_HEAD2.
  replace (i_wrap (m_s m) =? 0) with false by (destruct Hwrap as [-> | ->]; reflexivity).
  rewrite (rbh_needbits m Hbits Hhold Hnx Hlen H0 H1).
  fold b0 b1.
  set (m1 := set_m_bits (set_m_hold (set_m_nx m 2) (b0 + b1 * 256)) 16).
  change (m_leave m1) with (m_leave m). change (m_s m1) with (m_s m). change (m_hold m1) with (b0 + b1 * 256).
  rewrite Hhead, Hlv. change (0 =? 1) with false. cbv iota.
  set (H := b0 + b1 * 256) in *.
  assert (Hgz': (negb (Z.land (i_wrap (m_s m)) 2 =? 0) && (H =? 35615))%bool = false).
  { destruct Hwrap as [Hw | Hw]; rewrite Hw; [reflexivity | ].
    destruct Hgz as [Hg | Hg]; [rewrite Hw in Hg; discriminate | ].
    simpl. apply Z.eqb_neq. subst H. lia. }
  rewrite Hgz'.
  replace (Z.land (i_wrap (m_s m)) 1 =? 0) with false by (destruct Hwrap as [-> | ->]; reflexivity).
  change (m_hold (dropbits 4 m1)) with (Z.shiftr H 4).
  change (i_wbits (m_s (dropbits 4 m1))) with (i_wbits (m_s m)).
  set (low := i_wbits (m_s m)) in *.
  assert (E1: H mod 256 * 256 + Z.shiftr H 8 = b0 * 256 + b1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst H. Z.div_mod_to_equations. lia. }
  assert (E2: H mod 16 = Z.land b0 15).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. subst H.
    Z.div_mod_to_equations. lia. }
  assert (E3: Z.shiftr H 4 mod 16 = Z.shiftr b0 4).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. subst H. Z.div_mod_to_equations. lia. }
  change (m_hold m1) with H. rewrite E1, E2, E3. simpl orb.
  destruct ((b0 * 256 + b1) mod 31 =? 0) eqn:C1; simpl negb; cbv iota.
  2: { exists M_hdr_check. left. reflexivity. }
  destruct (Z.land b0 15 =? 8) eqn:C2; simpl negb; cbv iota.
  2: { exists M_method. left. reflexivity. }
  apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
  replace ((15 <? Z.shiftr b0 4 + 8) || negb (low =? 0) && (low <? Z.shiftr b0 4 + 8))%bool with true.
  { exists M_wsize. right. reflexivity. }
  symmetry. destruct Hbad as [B | [B | [B | [B1 B2]]]]; [ contradiction | contradiction | | ].
  - apply orb_true_intro. left. apply Z.ltb_lt. lia.
  - apply orb_true_intro. right. apply andb_true_intro. split.
    + apply negb_true_iff. apply Z.eqb_neq. exact B1.
    + apply Z.ltb_lt. exact B2.
Qed.

(* the case BAD returns Z_DATA_ERROR through inf_leave *)
Lemma rbh_step_bad: forall flush fx dx m, i_mode (m_s m) = BAD ->
  stepf2 flush fx dx m = IBrk (set_leave (set_m_ret m Z_DATA_ERROR)).
Proof. intros flush fx dx m H. unfold stepf2, step2, m_mode. rewrite H. reflexivity. Qed.

(* inf_leave after an error without output: the return value, no output, total_out unchanged *)
Lemma rbh_leave_fin: forall flush m,
  m_ret m = Z_DATA_ERROR -> m_ow m = [] -> m_out m = m_aout m ->
  r_ret (leave_fin flush m) = Z_DATA_ERROR /\ m_ow (r_m (leave_fin flush m)) = [] /\
  m_tout (r_m (leave_fin flush m)) = u64 (m_tout m).
Proof.
  intros flush m H1 H2 H3.
  unfold leave_fin. cbv zeta.
  set (U := if leave_ok flush m then _ else _).
  assert (U1: m_out U = m_out m /\ m_aout U = m_aout m /\ m_ow U = m_ow m /\ m_ret U = m_ret m /\
              m_tout U = m_tout m).
  { unfold U. destruct (leave_ok flush m); repeat split; reflexivity. }
  destruct U1 as (U1 & U2 & U3 & U4 & U5).
  clearbody U.
  assert (E: u32 (m_out U - m_left U) = 0).
  { unfold m_left. rewrite U1, U2, U3, H2, H3. change (Zlength (@nil Z)) with 0.
    rewrite Z.sub_0_r, Z.sub_diag. reflexivity. }
  rewrite E. change (negb (0 =? 0)) with false. rewrite andb_false_r. cbn [r_ret r_m].
  rewrite Z.add_0_r.
  unfold set_m_tout, set_m_tin, upd_s, set_m_s. cbn [m_ret m_ow m_tout]. rewrite U4, U3, U5, H1, H2.
  rewrite andb_false_r. auto.
Qed.

(* the case HEAD as in rbh_head, for every wrap the state can have after inflateInit2_ with a zlib wrapper:
   with fix F8 the windowBits 0, 16 and 32 (window size from the header) add bit 3, so wrap is 5, 7, 13 or 15;
   bit 3 plays no part in the header tests *)
Lemma rbh_head8: forall m,
  i_mode (m_s m) = HEAD ->
  (i_wrap (m_s m) = 5 \/ i_wrap (m_s m) = 7 \/ i_wrap (m_s m) = 13 \/ i_wrap (m_s m) = 15) ->
  i_head (m_s m) = false ->
  m_bits m = 0 -> m_hold m = 0 -> m_nx m = 0 -> m_leave m = 0 -> 2 <= Zlength (m_inp m) ->
  0 <= Znth 0 (m_inp m) < 256 -> 0 <= Znth 1 (m_inp m) < 256 ->
  rbh_bad (i_wbits (m_s m)) (Znth 0 (m_inp m)) (Znth 1 (m_inp m)) ->
  (Z.land (i_wrap (m_s m)) 2 = 0 \/ Znth 0 (m_inp m) <> 31 \/ Znth 1 (m_inp m) <> 139) ->
  exists e, c_HEAD2 m = IBrk (set_bad (needbits 16 m) e) \/
            c_HEAD2 m = IBrk (set_bad (dropbits 4 (needbits 16 m)) e).
Proof.
  intros m Hmode Hwrap Hhead Hbits Hhold Hnx Hlv Hlen H0 H1 Hbad Hgz.
  set (b0 := Znth 0 (m_inp m)) in *. set (b1 := Znth 1 (m_inp m)) in *.
  unfold c_HEAD2.
  replace (i_wrap (m_s m) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (rbh_needbits m Hbits Hhold Hnx Hlen H0 H1).
  fold b0 b1.
  set (m1 := set_m_bits (set_m_hold (set_m_nx m 2) (b0 + b1 * 256)) 16).
  change (m_leave m1) with (m_leave m). change (m_s m1) with (m_s m). change (m_hold m1) with (b0 + b1 * 256).
  rewrite Hhead, Hlv. change (0 =? 1) with false. cbv iota.
  set (H := b0 + b1 * 256) in *.
  assert (Hgz': (negb (Z.land (i_wrap (m_s m)) 2 =? 0) && (H =? 35615))%bool = false).
  { destruct Hgz as [Hg | Hg]; [rewrite Hg; reflexivity | ].
    rewrite andb_comm. replace (H =? 35615) with false; [reflexivity | ].
    symmetry. apply Z.eqb_neq. subst H. lia. }
  rewrite Hgz'.
  replace (Z.land (i_wrap (m_s m)) 1 =? 0) with false
    by (destruct Hwrap as [-> | [-> | [-> | ->]]]; reflexivity).
  change (m_hold (dropbits 4 m1)) with (Z.shiftr H 4).
  change (i_wbits (m_s (dropbits 4 m1))) with (i_wbits (m_s m)).
  set (low := i_wbits (m_s m)) in *.
  assert (E1: H mod 256 * 256 + Z.shiftr H 8 = b0 * 256 + b1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst H. Z.div_mod_to_equations. lia. }
  assert (E2: H mod 16 = Z.land b0 15).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. subst H.
    Z.div_mod_to_equations. lia. }
  assert (E3: Z.shiftr H 4 mod 16 = Z.shiftr b0 4).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. subst H. Z.div_mod_to_equations. lia. }
  change (m_hold m1) with H. rewrite E1, E2, E3. simpl orb.
  destruct ((b0 * 256 + b1) mod 31 =? 0) eqn:C1; simpl negb; cbv iota.
  2: { exists M_hdr_check. left. reflexivity. }
  destruct (Z.land b0 15 =? 8) eqn:C2; simpl negb; cbv iota.
  2: { exists M_method. left. reflexivity. }
  apply Z.eqb_eq in C1. apply Z.eqb_eq in C2.
  replace ((15 <? Z.shiftr b0 4 + 8) || negb (low =? 0) && (low <? Z.shiftr b0 4 + 8))%bool with true.
  { exists M_wsize. right. reflexivity. }
  symmetry. destruct Hbad as [B | [B | [B | [B1 B2]]]]; [ contradiction | contradiction | | ].
  - apply orb_true_intro. left. apply Z.ltb_lt. lia.
  - apply orb_true_intro. right. apply andb_true_intro. split.
    + apply negb_true_iff. apply Z.eqb_neq. exact B1.
    + apply Z.ltb_lt. exact B2.
Qed.

(* the state after inflateInit2_(strm, w) for the windowBits of the law: in HEAD with an empty bit buffer and no
   window, wbits the low four bits of w, wrap 5 or 7 (gzip detection only with w >= 32) plus bit 3 when the
   window size comes from the header *)
Lemma rbh_init: forall sp w, rbh_wbits w ->
  let s := l_s (init_live sp w) in
  i_mode s = HEAD /\ (i_wrap s = 5 \/ i_wrap s = 7 \/ i_wrap s = 13 \/ i_wrap s = 15) /\
  (Z.land (i_wrap s) 2 = 0 \/ 32 <= w) /\ i_head s = false /\ i_wbits s = Z.land w 15 /\
  i_wsize s = 0 /\ i_hold s = 0 /\ i_bits s = 0.
Proof.
  intros sp w [Hw0 [Hw16 Hw15]]. unfold init_live; cbn [l_s].
  assert (Hc: w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15 \/ w = 16 \/ w = 17 \/ w = 18 \/ w = 19 \/ w = 20 \/ w = 21 \/ w = 22 \/ w = 23 \/ w = 24 \/ w = 25 \/ w = 26 \/ w = 27 \/ w = 28 \/ w = 29 \/ w = 30 \/ w = 31 \/ w = 32 \/ w = 33 \/ w = 34 \/ w = 35 \/ w = 36 \/ w = 37 \/ w = 38 \/ w = 39 \/ w = 40 \/ w = 41 \/ w = 42 \/ w = 43 \/ w = 44 \/ w = 45 \/ w = 46 \/ w = 47) by lia.
  repeat destruct Hc as [-> | Hc]; try (subst w); cbv in Hw16, Hw15;
    first [ discriminate Hw16 | exfalso; destruct Hw15 as [Hx | Hx]; [discriminate Hx | apply Hx; reflexivity]
          | vm_compute; repeat split;
            first [ reflexivity | lia | left; reflexivity | right; intro; discriminate ] ].
Qed.

Lemma rbh_theory: forall flush fx dx z sp w inp res,
  rbh_wbits w -> 2 <= Zlength inp ->
  0 <= Znth 0 inp < 256 -> 0 <= Znth 1 inp < 256 ->
  rbh_bad (Z.land w 15) (Znth 0 inp) (Znth 1 inp) ->
  (w < 32 \/ Znth 0 inp <> 31 \/ Znth 1 inp <> 139) ->
  zf_tout z = 0 ->
  run2 flush fx dx (m_init z (init_live sp w) inp) res ->
  r_ret res = Z_DATA_ERROR /\ m_ow (r_m res) = [] /\ m_tout (r_m res) = 0.
Proof.
  intros flush fx dx z sp w inp res Hw Hlen H0 H1 Hbad Hgz Htout [o [Hl Ho]].
  set (m0 := m_init z (init_live sp w) inp) in *.
  destruct (rbh_init sp w Hw) as (Hmode & Hwrap & Hw2 & Hhead & Hwbits & Hwsize & Hhold & Hbits).
  assert (Hm0: m_s m0 = l_s (init_live sp w) /\
               m_bits m0 = 0 /\ m_hold m0 = 0 /\ m_nx m0 = 0 /\ m_leave m0 = 0 /\ m_inp m0 = inp /\
               m_ow m0 = [] /\ m_out m0 = zf_ao z /\ m_aout m0 = zf_ao z /\ m_ret m0 = Z_OK /\
               m_tout m0 = zf_tout z).
  { unfold m0, m_init. rewrite Hmode. cbn -[init_live]. rewrite Hhold, Hbits. repeat split; reflexivity. }
  destruct Hm0 as (Hs0 & Hbits0 & Hhold0 & Hnx & Hlv & Hinp & How & Hout & Haout & Hret & Htout0).
  rewrite <- Hs0 in Hmode, Hwrap, Hw2, Hhead, Hwbits, Hwsize.
  clearbody m0. subst inp. clear Hs0 Hhold Hbits.
  assert (Hstep: exists m1, stepf2 flush fx dx m0 = IBrk m1 /\ i_mode (m_s m1) = BAD /\ m_leave m1 = 0 /\
                 i_wsize (m_s m1) = 0 /\ m_ow m1 = [] /\ m_out m1 = zf_ao z /\ m_aout m1 = zf_ao z /\
                 m_tout m1 = zf_tout z /\ m_ret m1 = Z_OK).
  { unfold stepf2, step2, m_mode. rewrite Hmode. change (HEAD =? HEAD) with true. cbv iota.
    destruct (rbh_head8 m0) as [e [E | E]]; try assumption.
    - rewrite Hwbits. exact Hbad.
    - destruct Hw2 as [Hw2 | Hw32]; auto.
      destruct Hgz as [Hg | Hg]; [lia | auto].
    - rewrite E. eexists; split; [reflexivity | ].
      rewrite (rbh_needbits m0) by assumption.
      unfold set_bad, set_mode, upd_s. cbn -[Znth Zlength]. auto 10.
    - rewrite E. eexists; split; [reflexivity | ].
      rewrite (rbh_needbits m0) by assumption.
      unfold set_bad, set_mode, upd_s, dropbits. cbn -[Znth Zlength]. auto 10. }
  destruct Hstep as (m1 & E1 & Hmode1 & Hlv1 & Hws1 & How1 & Hout1 & Haout1 & Htout1 & Hret1).
  pose proof (rbh_step_bad flush fx dx m1 Hmode1) as E2.
  set (m2 := set_leave (set_m_ret m1 Z_DATA_ERROR)) in *.
  inversion Hl as [? ? ? Hs1 | ? ? Hs1 Hlv' | ? ? ? Hs1 Hlv' Hl']; subst; rewrite E1 in Hs1;
    [ discriminate | inversion Hs1; subst; rewrite Hlv1 in Hlv'; discriminate | ].
  inversion Hs1; subst m'. clear Hs1 Hl.
  inversion Hl' as [? ? ? Hs2 | ? ? Hs2 Hlv2 | ? ? ? Hs2 Hlv2 _]; subst; rewrite E2 in Hs2;
    [ discriminate | | inversion Hs2; subst; contradiction ].
  inversion Hs2; subst m'. clear Hs2 Hl'.
  inversion Ho as [Hok _ | ]; subst.
  - exfalso. revert Hok. unfold leave_ok, m_left, m2, set_leave, set_m_ret, set_m_leave; cbn -[Zlength].
    rewrite Hws1, How1, Hout1, Haout1. change (Zlength (@nil Z)) with 0.
    replace (zf_ao z =? zf_ao z - 0) with true by lia. simpl. discriminate.
  - destruct (rbh_leave_fin flush m2) as (R1 & R2 & R3).
    + reflexivity.
    + exact How1.
    + unfold m2. cbn. rewrite Hout1, Haout1. reflexivity.
    + split; [exact R1 | split; [exact R2 | ]]. rewrite R3. unfold m2. cbn. rewrite Htout1, Htout. reflexivity.
Qed.

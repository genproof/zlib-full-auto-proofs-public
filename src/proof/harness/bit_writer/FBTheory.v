(* Law rj_far_back: the theory (FBFacts.v), from the fixed-block run theory (FRFacts.v) with the tail TFar. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.FBFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* a boolean property checked on the integers a .. a + n - 1 holds on that range *)
Lemma fb_range_check : forall (f: Z -> bool) a n,
  forallb f (map (fun i => a + Z.of_nat i) (seq 0 n)) = true -> forall x, a <= x < a + Z.of_nat n -> f x = true.
Proof.
  intros f a n H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff.
  exists (Z.to_nat (x - a)). split; [lia|]. apply in_seq. lia.
Qed.

Definition fb_lbits_code (lc: Z) : list bool :=
  if lc <? 280 then bits_msb (lc - 256) 7 else bits_msb (192 + lc - 280) 8.

Definition bl_eqb (a b: list bool) : bool := if list_eq_dec bool_dec a b then true else false.

(* the harness's codes are the fixed codes (RFC 1951 3.2.6) and its extra bit counts and distance bases are
   those of 3.2.5, on all 29 length codes and 30 distance codes *)
Lemma fb_len_code : forall lc, 257 <= lc <= 285 ->
  fb_lbits_code lc = send_sym fixed_ll lc /\ fb_lbits lc = Znth (lc - 257) len_extra.
Proof.
  intros lc Hlc.
  assert (H := fb_range_check
    (fun lc => andb (bl_eqb (fb_lbits_code lc) (send_sym fixed_ll lc)) (fb_lbits lc =? Znth (lc - 257) len_extra))
    257 29 ltac:(vm_compute; reflexivity) lc ltac:(lia)).
  apply andb_prop in H as [H1 H2]. unfold bl_eqb in H1.
  destruct list_eq_dec; [|discriminate]. split; [auto | lia].
Qed.

Lemma fb_dist_code : forall dc, 0 <= dc <= 29 ->
  bits_msb dc 5 = send_sym fixed_dl dc /\ fb_dbits dc = Znth dc dist_extra /\
  (if 4 <=? dc then Z.shiftl (Z.lor 2 (Z.land dc 1)) (fb_dbits dc) + 1 else dc + 1) = Znth dc dist_base.
Proof.
  intros dc Hdc.
  assert (H := fb_range_check
    (fun dc => andb (andb (bl_eqb (bits_msb dc 5) (send_sym fixed_dl dc)) (fb_dbits dc =? Znth dc dist_extra))
       ((if 4 <=? dc then Z.shiftl (Z.lor 2 (Z.land dc 1)) (fb_dbits dc) + 1 else dc + 1) =? Znth dc dist_base))
    0 30 ltac:(vm_compute; reflexivity) dc ltac:(lia)).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. unfold bl_eqb in H1.
  destruct list_eq_dec; [|discriminate]. split; [auto | lia].
Qed.

(* the harness's distance is the distance of the code dc with the extra bits extra mod 2^bits *)
Lemma fb_dist_eq : forall dc extra, 0 <= dc <= 29 ->
  fb_dist dc extra = Znth dc dist_base + extra mod 2 ^ Znth dc dist_extra.
Proof.
  intros dc extra Hdc. destruct (fb_dist_code dc Hdc) as (_ & Hb & Hd).
  unfold fb_dist. rewrite <- Hb, <- Hd.
  assert (0 <= fb_dbits dc) by (unfold fb_dbits; destruct (Z.leb_spec 4 dc); Z.to_euclidean_division_equations; lia).
  destruct (4 <=? dc) eqn:E.
  - rewrite <- Z.land_ones by lia. rewrite Z.ones_equiv. unfold Z.pred. reflexivity.
  - unfold fb_dbits. rewrite E. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Lemma fb_bits_le_len : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, length_seq. lia.
Qed.

Lemma fb_bits_le_mod : forall v n, 0 <= n -> bits_le v n = bits_le (v mod 2 ^ n) n.
Proof.
  intros v n Hn. unfold bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite Z.mod_pow2_bits_low; auto. lia.
Qed.

Lemma fb_lit_len : forall l, 0 <= l < 256 -> Zlength (send_sym fixed_ll l) <= 9.
Proof.
  intros l Hl. unfold send_sym, bits_msb. rewrite Zlength_rev.
  assert (H := fb_range_check (fun l => andb (Znth l fixed_ll <=? 9) (0 <=? Znth l fixed_ll)) 0 256
    ltac:(vm_compute; reflexivity) l ltac:(lia)).
  apply andb_prop in H as [H1 H2]. rewrite fb_bits_le_len; lia.
Qed.

Lemma fb_lits_len : forall lits, Forall (fun l => 0 <= l < 256) lits ->
  Zlength (concat (map (send_sym fixed_ll) lits)) <= 9 * Zlength lits.
Proof.
  induction lits; intros H; simpl. { rewrite Zlength_nil. lia. }
  inversion H; subst. rewrite Zlength_app, Zlength_cons. specialize (IHlits H3).
  pose proof (fb_lit_len a H2). lia.
Qed.

(* the run context of the stream main writes: its literals, then the length code lc with the extra bits lx and
   the distance code dc with the extra bits extra, each cut to its width *)
Definition fb_ctx (S0: list Z) (fin: Z) (lits: list Z) (lc lx dc extra: Z) : frc :=
  FRC (fb_bytes S0 fin lits lc lx dc extra) lits
    (TFar lc (lx mod 2 ^ Znth (lc - 257) len_extra) dc (extra mod 2 ^ Znth dc dist_extra)).

(* main's stream is a fixed block of the literals and the far reference; it ends well before 2^32 - 1 bytes *)
Lemma fb_fr_ok : fb_bits_stmt -> forall S0 fin lits lc lx dc extra, fb_ok S0 fin lits lc lx dc extra ->
  let C := fb_ctx S0 fin lits lc lx dc extra in
  fr_ok C /\ fr_end C < 8 * Int.max_unsigned.
Proof.
  intros Hbits S0 fin lits lc lx dc extra Hok. pose proof (Hbits _ _ _ _ _ _ _ Hok) as HB. cbv zeta in HB |- *.
  destruct HB as (HlenS & HbS & HlenB & HB).
  destruct Hok as (Hfin & Hlits & Hnlits & Hlc & Hlx & Hdc & Hext & Hfar & HS0 & HnS0).
  destruct (fb_len_code lc Hlc) as [Hc1 Hc2]. destruct (fb_dist_code dc Hdc) as (Hd1 & Hd2 & _).
  rewrite (fb_dist_eq dc extra Hdc) in Hfar.
  assert (Hlb: 0 <= fb_lbits lc <= 5)
    by (clear - Hlc; unfold fb_lbits; destruct (Z.leb_spec 265 lc), (Z.leb_spec lc 284); cbn [andb];
        Z.to_euclidean_division_equations; lia).
  assert (Hdb: 0 <= fb_dbits dc <= 13)
    by (clear - Hdc; unfold fb_dbits; destruct (Z.leb_spec 4 dc); Z.to_euclidean_division_equations; lia).
  assert (Hcl: Zlength (send_sym fixed_ll lc) <= 8).
  { rewrite <- Hc1. unfold fb_lbits_code, bits_msb.
    destruct (lc <? 280); rewrite Zlength_rev, fb_bits_le_len; lia. }
  assert (Hdl: Zlength (send_sym fixed_dl dc) = 5) by (rewrite <- Hd1; unfold bits_msb; rewrite Zlength_rev, fb_bits_le_len; lia).
  set (C := fb_ctx S0 fin lits lc lx dc extra).
  set (B := fb_bits fin lits lc lx dc extra) in *.
  assert (HL: Forall (fun l => 0 <= l < 256) lits) by (eapply Forall_impl; [|exact Hlits]; simpl; rep_lia).
  assert (HBeq: B = bits_le fin 1 ++ [true; false] ++ fr_body C).
  { subst B C. unfold fb_bits, fr_body, fb_ctx. simpl fr_lits. simpl fr_tail. unfold tail_bits.
    change (if lc <? 280 then bits_msb (lc - 256) 7 else bits_msb (192 + lc - 280) 8) with (fb_lbits_code lc).
    rewrite Hc1, Hd1, <- Hc2, <- Hd2, <- !fb_bits_le_mod by lia. reflexivity. }
  assert (Hend: fr_end C = Zlength B).
  { rewrite HBeq, !Zlength_app, fb_bits_le_len by lia. unfold fr_end. rewrite Zlength_cons, Zlength_cons, Zlength_nil. lia. }
  assert (Hbody: Zlength (fr_body C) <= 9 * Zlength lits + 31).
  { unfold fr_body, fb_ctx. simpl fr_lits. simpl fr_tail. unfold tail_bits.
    rewrite !Zlength_app, !fb_bits_le_len by lia. pose proof (fb_lits_len lits HL). lia. }
  assert (HB3: 3 <= Zlength B) by (rewrite <- Hend; unfold fr_end; pose proof (Zlength_nonneg (fr_body C)); lia).
  assert (HbitsS: Zlength (bytes_bits (fb_bytes S0 fin lits lc lx dc extra)) = 8 * Zlength S0).
  { clear - HlenS HbS. rewrite <- HlenS. revert HbS. generalize (fb_bytes S0 fin lits lc lx dc extra).
    induction l; intros H; [reflexivity|]. inversion H; subst. unfold bytes_bits in *. cbn [flat_map].
    rewrite Zlength_app, fb_bits_le_len, Zlength_cons, IHl by (auto; lia). lia. }
  split; [|unfold fr_end; rep_lia].
  assert (Hpos: forall k, 0 <= k -> 0 < 2 ^ k) by (intros; apply Z.pow_pos_nonneg; lia).
  unfold fr_ok. change (fr_src C) with (fb_bytes S0 fin lits lc lx dc extra). change (fr_lits C) with lits.
  set (X := bytes_bits (fb_bytes S0 fin lits lc lx dc extra)) in *.
  split; [exact HbS|]. split; [exact HL|]. split; [rep_lia|]. split.
  { change (fr_tail C) with (TFar lc (lx mod 2 ^ Znth (lc - 257) len_extra) dc (extra mod 2 ^ Znth dc dist_extra)).
    simpl tail_ok. rewrite <- Hc2, <- Hd2 in *.
    pose proof (Z.mod_pos_bound lx (2 ^ fb_lbits lc) (Hpos (fb_lbits lc) ltac:(lia))).
    pose proof (Z.mod_pos_bound extra (2 ^ fb_dbits dc) (Hpos (fb_dbits dc) ltac:(lia))). lia. }
  split; [lia|].
  assert (Hfin1: bits_le fin 1 = [Z.testbit fin 0]) by reflexivity.
  assert (HlB: Zlength B = 3 + Zlength (fr_body C)) by (unfold fr_end in Hend; lia).
  split.
  - rewrite <- (sublist_sublist0 3 (Zlength B) 1 X) by lia. rewrite HB, HBeq, Hfin1. list_solve.
  - rewrite Hend, <- (sublist_sublist0 (Zlength B) (Zlength B) 3 X) by lia. rewrite HB, HlB, HBeq, Hfin1.
    list_solve.
Qed.

(* The two calls.  The first one keeps the run invariant (or fails to allocate the window).  The second one is
   offered all the rest of the stream up to 2^32 - 1 bytes, which covers the far reference, and more output space
   than the literals, and Z_TREES is excluded: none of the reasons fr_stop to return early applies, so it returns
   Z_DATA_ERROR or Z_MEM_ERROR; the output stays within the literals by fr_out. *)
Lemma fb_theory : fr_theory_stmt -> fb_bits_stmt -> fb_theory_stmt.
Proof.
  intros [I HI] Hbits. unfold fb_theory_stmt.
  intros S0 fin lits lc lx dc extra w sp L z take flush res Hok Hw HL HLok Hz Htake Hfl Hrun.
  set (S := fb_bytes S0 fin lits lc lx dc extra) in *.
  destruct (fb_fr_ok Hbits S0 fin lits lc lx dc extra Hok) as [HC Hend].
  set (C := fb_ctx S0 fin lits lc lx dc extra) in *.
  assert (HCS: fr_src C = S) by reflexivity.
  assert (HCL: fr_lits C = lits) by reflexivity.
  assert (HendS: fr_end C <= 8 * Zlength S) by (destruct HC as (_ & _ & _ & _ & H & _); rewrite HCS in H; exact H).
  assert (HI0: I C 0 [] (l_s L)) by (rewrite HL; apply (fr_init _ HI); auto).
  assert (Hlen1: Zlength (sublist 0 take S) = take) by (rewrite Zlength_sublist; lia).
  pose proof (fr_call _ HI C 0 [] L z (sublist 0 take S) flush res HC HI0 HLok Hz ltac:(lia)
    ltac:(rewrite HCS; lia) ltac:(rewrite HCS, Hlen1; reflexivity) ltac:(lia) Hfl Hrun) as Hpost.
  destruct Hpost as (Hsnx & Hsow & Hao & _ & Hcases). rewrite Hlen1 in Hsnx.
  (* after a first call that kept the invariant *)
  assert (Hnext: I C (0 + m_snx (r_m res)) ([] ++ m_ow (r_m res)) (m_s (r_m res)) ->
    Zlength (m_ow (r_m res)) <= Zlength lits /\ m_sow (r_m res) = Zlength (m_ow (r_m res)) /\
    0 <= m_snx (r_m res) <= take /\
    forall L' z' flush' res',
      let read := m_snx (r_m res) in
      let inp := sublist read (read + Z.min (Zlength S - read) Int.max_unsigned) S in
      l_s L' = m_s (r_m res) -> live_ok L' -> zf_ok z' -> Zlength lits + 1 <= zf_ao z' ->
      Int.min_signed <= flush' <= Int.max_signed -> flush' <> Z_TREES ->
      run2 flush' lenfix_list distfix_list (m_init z' L' inp) res' ->
      r_ret res' = Z_MEM_ERROR \/
      (r_ret res' = Z_DATA_ERROR /\ m_sow (r_m res') = Zlength (m_ow (r_m res')) /\
       Zlength (m_ow (r_m res)) + Zlength (m_ow (r_m res')) <= Zlength lits)).
  { intros HI1. rewrite Z.add_0_l, app_nil_l in HI1.
    pose proof (fr_out _ HI _ _ _ _ HI1) as Hout1. rewrite HCL in Hout1.
    split; [exact Hout1|]. split; [exact Hsow|]. split; [lia|].
    intros L' z' flush' res' read inp HL' HL'ok Hz' Hao' Hfl' Hnt Hrun'.
    assert (Hlen2: Zlength inp = Z.min (Zlength S - read) Int.max_unsigned)
      by (subst inp read; rewrite Zlength_sublist; rep_lia).
    assert (HI2: I C read (m_ow (r_m res)) (l_s L')) by (rewrite HL'; exact HI1).
    pose proof (fr_call _ HI C read (m_ow (r_m res)) L' z' inp flush' res' HC HI2 HL'ok Hz' ltac:(subst read; lia)
      ltac:(rewrite HCS, Hlen2; rep_lia) ltac:(rewrite HCS, Hlen2; reflexivity) ltac:(rewrite Hlen2; lia)
      Hfl' Hrun') as Hpost2.
    destruct Hpost2 as (Hsnx2 & Hsow2 & Hao2 & _ & Hcases2).
    destruct Hcases2 as [(Hret & HI3) | [(Hret & _) | (Hret & Hstop & HI3)]].
    - right. split; [exact Hret|]. split; [exact Hsow2|].
      pose proof (fr_out _ HI _ _ _ _ HI3) as Hout. rewrite HCL, Zlength_app in Hout. exact Hout.
    - left. exact Hret.
    - exfalso. pose proof (fr_out _ HI _ _ _ _ HI3) as Hout. rewrite HCL, Zlength_app in Hout.
      unfold fr_stop in Hstop. rewrite HCL in Hstop.
      destruct Hstop as [(Htr & _) | [(Hfull & _) | Hshort]].
      + exact (Hnt Htr).
      + pose proof (Zlength_nonneg (m_ow (r_m res))). lia.
      + rewrite Hlen2 in Hshort. subst read. rep_lia. }
  destruct Hcases as [(Hret & HI1) | [(Hret & _) | (Hret & _ & HI1)]].
  - right. exact (Hnext HI1).
  - left. exact Hret.
  - right. exact (Hnext HI1).
Qed.

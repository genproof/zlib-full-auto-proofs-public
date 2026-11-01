(* The fixed-block run theory (FRDefs.v): reading the input bit by bit (one fixed code by the slow path's lookup1,
   NEEDBITS of extra bits) and the meaning of the fixed tables' entries. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.rfc1951.DecFastIter Zlib.proof.rfc1951.DecFastWalk Zlib.proof.rfc1951.DecKit
  Zlib.proof.rfc1951.TabDec Zlib.proof.rfc1951.DecDecNeed.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The fixed tables                                                                               *)

(* the two fixed tables of the slow path: lencode / 9 root bits for the literal/length code, distcode / 5 for
   the distance code *)
Definition fb_tab (t: tref) (rb kind: Z) (lens: list Z) : Prop :=
  (t = TLenfix /\ rb = 9 /\ kind = LENS /\ lens = fixed_ll) \/
  (t = TDistfix /\ rb = 5 /\ kind = DISTS /\ lens = fixed_dl).

(* no entry of the fixed tables is a link (their codes are at most as long as the root) *)
Lemma fb_nolink_ll : forallb (fun e => negb (ref.is_link (e_op e))) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fb_nolink_dl : forallb (fun e => negb (ref.is_link (e_op e))) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fb_len_ll : Zlength lenfix_list = 512.
Proof. vm_compute. reflexivity. Qed.
Lemma fb_len_dl : Zlength distfix_list = 32.
Proof. vm_compute. reflexivity. Qed.

(* the fixed code lengths: 7 to 9 bits (literal/length), 5 bits (distance) *)
Lemma fb_lens_ll : forallb (fun l => andb (7 <=? l) (l <=? 9)) fixed_ll = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fb_lens_dl : forallb (fun l => l =? 5) fixed_dl = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fb_forallb_Znth {A} {d: Inhabitant A} (f: A -> bool) l i :
  forallb f l = true -> 0 <= i < Zlength l -> f (Znth i l) = true.
Proof. intros H Hi. rewrite forallb_forall in H. apply H, Znth_In, Hi. Qed.

Lemma fb_tab_facts t rb kind lens : fb_tab t rb kind lens ->
  (forall s, tdec s t rb kind lens) /\
  (forall s i, 0 <= i < 2 ^ rb -> ref.is_link (e_op (tab_entry lenfix_list distfix_list s t i)) = false) /\
  (forall sy, 0 <= sy < Zlength lens -> 5 <= Znth sy lens <= 9) /\ 1 <= rb <= 9.
Proof.
  intros [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
  - split; [intro s; apply tabdec_fixed|]. split.
    + intros s i Hi. cbn [tab_entry]. apply negb_true_iff.
      apply (fb_forallb_Znth (fun e => negb (ref.is_link (e_op e))) lenfix_list i fb_nolink_ll).
      rewrite fb_len_ll. change (2 ^ 9) with 512 in Hi. lia.
    + split; [|lia]. intros sy Hsy. pose proof (fb_forallb_Znth _ _ sy fb_lens_ll Hsy) as H.
      cbv beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
  - split; [intro s; apply tabdec_fixed|]. split.
    + intros s i Hi. cbn [tab_entry]. apply negb_true_iff.
      apply (fb_forallb_Znth (fun e => negb (ref.is_link (e_op e))) distfix_list i fb_nolink_dl).
      rewrite fb_len_dl. change (2 ^ 5) with 32 in Hi. lia.
    + split; [|lia]. intros sy Hsy. pose proof (fb_forallb_Znth _ _ sy fb_lens_dl Hsy) as H.
      cbv beta in H. apply Z.eqb_eq in H. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The root entry of the bit buffer                                                               *)

(* the bit buffer holds b bits from the code of sy on: with the whole code (b >= its length) the root entry is
   the entry of sy, of its length; with a part of it, the root entry needs more than b bits *)
Lemma fb_entry (G: dctx) c h b s t rb kind lens sy :
  fb_tab t rb kind lens -> hold_ok G c h b -> 0 <= sy < Zlength lens ->
  8 * c - b + Znth sy lens <= 8 * Zlength (dc_src G) ->
  sublist (8 * c - b) (8 * c - b + Znth sy lens) (sbits G) = send_sym lens sy ->
  (Znth sy lens <= b ->
   e_bits (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb)) = Znth sy lens /\
   ref.means_symbol kind sy (e_op (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb)))
     (e_val (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb))) = true) /\
  (b < Znth sy lens -> b < e_bits (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb))).
Proof.
  intros HT Hh Hsy Hend Hsb.
  destruct (fb_tab_facts _ _ _ _ HT) as (TD & NL & LN & RB).
  specialize (LN sy Hsy).
  destruct (TD s) as (_ & Tfull & Tpart & _).
  set (e := tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb)).
  assert (NLe: ref.is_link (e_op e) = false) by (apply NL; apply Z.mod_pos_bound; lia).
  split.
  - intros Hle. pose proof (dfw_hold_split G c h b lens sy Hh ltac:(lia) Hsb) as Hsplit.
    destruct (Tfull sy Hsy ltac:(lia) _ (dfw_bval_nonneg (sublist (8 * c - b + Znth sy lens) (8 * c) (sbits G))))
      as (op & val & Tw & Ms).
    rewrite <- Hsplit in Tw. unfold twalk in Tw. fold e in Tw. rewrite NLe in Tw.
    injection Tw as -> -> ->. auto.
  - intros Hlt. pose proof Hh as (Hb & Hc & Hhv).
    assert (HL: Zlength (sbits G) = 8 * Zlength (dc_src G)) by apply dfw_bytes_bits_len.
    assert (Hpat: h mod 2 ^ b = ref.reverse_bits (code lens sy) (Znth sy lens) mod 2 ^ b).
    { rewrite <- dfw_bval_msb by lia. fold (send_sym lens sy). rewrite <- Hsb.
      rewrite (sublist_split (8 * c - b) (8 * c) (8 * c - b + Znth sy lens)) by lia.
      rewrite dfw_bval_app. rewrite Zlength_sublist by lia.
      replace (8 * c - (8 * c - b)) with b by lia. rewrite <- Hhv.
      rewrite Z.mul_comm. rewrite Z_mod_plus_full. reflexivity. }
    assert (Hh0: 0 <= h) by (rewrite Hhv; apply dfw_bval_nonneg).
    pose proof (Tpart sy Hsy ltac:(lia) b h ltac:(lia) Hh0 Hpat) as P. cbv zeta in P. fold e in P.
    destruct P as [P|[P _]]; [exact P|congruence].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* PULLBYTE and the lookup loop                                                                   *)

Lemma fb_pull C pos inp m :
  fr_in C pos inp -> fr_buf C pos inp m -> m_have m <> 0 -> m_bits m + 8 <= 64 ->
  fr_buf C pos inp (pull m) /\ m_bits (pull m) = m_bits m + 8 /\ m_s (pull m) = m_s m /\
  m_leave (pull m) = m_leave m /\ m_nx (pull m) = m_nx m + 1 /\
  pull m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (m_hold (pull m))) (m_bits (pull m)).
Proof.
  intros (BO & Hpos & Hlen & Hinp) (Hi & Hnx & Hh) Hhave Hb.
  unfold m_have in Hhave. rewrite Hi in Hhave.
  pose proof Hh as (Hb0 & _ & _).
  assert (Hc: pos + m_nx m < Zlength (dc_src (fr_g C))) by (cbn [dc_src fr_g]; lia).
  pose proof (dk_pull dkit (fr_g C) _ _ _ Hh Hc Hb BO) as P.
  assert (ZB: Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src (fr_g C))).
  { cbn [dc_src fr_g]. rewrite Hi, Hinp. rewrite Znth_sublist by lia. f_equal. lia. }
  unfold pull. cbn [m_inp m_nx m_hold m_bits m_s m_leave set_m_nx set_m_hold set_m_bits].
  rewrite ZB. unfold u32, u64. rewrite (Z.mod_small (m_bits m + 8)) by lia.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|reflexivity]]]]].
  unfold fr_buf. cbn [m_inp m_nx m_hold m_bits set_m_nx set_m_hold set_m_bits].
  split; [exact Hi|]. split; [lia|].
  replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia. exact P.
Qed.

Lemma fb_lk1 C pos inp t rb kind lens sy q :
  fr_in C pos inp -> fb_tab t rb kind lens -> 0 <= sy < Zlength lens ->
  q + Znth sy lens <= 8 * Zlength (fr_src C) ->
  sublist q (q + Znth sy lens) (bytes_bits (fr_src C)) = send_sym lens sy ->
  forall k m, fr_buf C pos inp m -> 8 * (pos + m_nx m) - m_bits m = q -> m_bits m < Znth sy lens + 8 ->
  (1 <= k)%nat -> Znth sy lens <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k lenfix_list distfix_list t rb m in
  exists nx h b lv,
    m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_nx m <= nx <= Zlength inp /\ hold_ok (fr_g C) (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
    (ok = true -> lv = m_leave m /\ e_bits here = Znth sy lens /\ Znth sy lens <= b < Znth sy lens + 8 /\
                  ref.means_symbol kind sy (e_op here) (e_val here) = true) /\
    (ok = false -> lv = 1 /\ nx = Zlength inp /\ b < Znth sy lens).
Proof.
  intros Hin HT Hsy Hend Hsb.
  assert (HL9: Znth sy lens <= 9) by (destruct (fb_tab_facts _ _ _ _ HT) as (_ & _ & LN & _); apply LN in Hsy; lia).
  induction k as [|k IH]; intros m Hbuf Hq Hb8 Hk Hfu; [lia|].
  pose proof Hbuf as (Hi & Hnx & Hh).
  pose proof Hh as (Hb0 & _ & _).
  assert (Hq': 8 * (pos + m_nx m) - m_bits m = q) by exact Hq.
  rewrite <- Hq in Hend, Hsb.
  destruct (fb_entry (fr_g C) (pos + m_nx m) (m_hold m) (m_bits m) (m_s m) t rb kind lens sy HT Hh Hsy Hend Hsb)
    as [EF EP].
  cbn [lookup1_f]. unfold bitsn.
  destruct (Z.leb_spec (e_bits (tab_entry lenfix_list distfix_list (m_s m) t (m_hold m mod 2 ^ rb))) (m_bits m))
    as [Hst|Hst].
  - assert (HLb: Znth sy lens <= m_bits m) by (destruct (Z.lt_ge_cases (m_bits m) (Znth sy lens)) as [X|X];
      [apply EP in X; lia|exact X]).
    destruct (EF HLb) as [E1 E2].
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [exact Hh|]. split; [exact Hq'|].
    split; [|discriminate]. intros _. split; [reflexivity|]. split; [exact E1|]. split; [lia|exact E2].
  - assert (HLb: m_bits m < Znth sy lens) by (destruct (Z.lt_ge_cases (m_bits m) (Znth sy lens)) as [X|X];
      [exact X|apply EF in X; lia]).
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
      split; [lia|]. split; [exact Hh|]. split; [exact Hq'|].
      split; [discriminate|]. intros _. unfold m_have in H0. rewrite Hi in H0. split; [reflexivity|]. lia.
    + destruct (fb_pull C pos inp m Hin Hbuf H0 ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
      assert (Hk': (1 <= k)%nat) by (destruct k; [cbn in Hfu; lia|lia]).
      rewrite Hq in Hend, Hsb.
      specialize (IH (pull m) C1 ltac:(rewrite C2, C5; lia) ltac:(lia) Hk' ltac:(rewrite C2; lia)).
      destruct (lookup1_f k lenfix_list distfix_list t rb (pull m)) as [[here m'] ok].
      destruct IH as (nx & h & b & lv & E & R1 & R2 & R3 & R4 & R5).
      exists nx, h, b, lv. split.
      { rewrite E, C6. destruct m; reflexivity. }
      rewrite C5, C4 in *. split; [lia|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|exact R5].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS                                                                                       *)

Lemma fb_need_gen C pos inp n v q k m :
  fr_in C pos inp -> fr_buf C pos inp m -> q = 8 * (pos + m_nx m) - m_bits m -> m_leave m = 0 ->
  1 <= n <= 15 -> 0 <= v < 2 ^ n ->
  sublist q (q + n) (bytes_bits (fr_src C)) = bits_le v n -> q + n <= 8 * Zlength (fr_src C) ->
  m_bits m < n + 8 -> n <= m_bits m + 8 * Z.of_nat k ->
  exists nx h b lv,
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_nx m <= nx <= Zlength inp /\ hold_ok (fr_g C) (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
    ((lv = 1 /\ nx = Zlength inp /\ b < n) \/ (lv = 0 /\ n <= b < n + 8 /\ h mod 2 ^ n = v)).
Proof.
  intros HC. revert m. induction k as [|k IH]; intros m HB Hq HL Hn Hv HS Hsl Hb Hk.
  - pose proof HB as (Hi & Hnx & HO).
    exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [exact HO|]. split; [lia|]. right. split; [lia|]. split; [lia|].
    rewrite (dk_bitsn dkit _ _ _ _ n HO) by lia. rewrite <- Hq. change (sbits (fr_g C)) with (bytes_bits (fr_src C)).
    rewrite HS. rewrite need_bval_bits_le by lia. apply Z.mod_small. lia.
  - cbn [needbits_f]. pose proof HB as (Hi & Hnx & HO).
    pose proof HO as (HO1 & HO2 & HO3).
    destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * unfold m_have in H0. rewrite Hi in H0.
        exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. split; [exact HO|]. split; [lia|]. left. split; [lia|]. split; lia.
      * destruct (fb_pull C pos inp m HC HB H0 ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
        destruct (IH (pull m) C1 ltac:(rewrite C2, C5; lia) ltac:(rewrite C4; exact HL) Hn Hv HS Hsl
                   ltac:(lia) ltac:(lia)) as (nx & h & b & lv & E & R1 & R2 & R3 & R4).
        rewrite E. exists nx, h, b, lv. split; [rewrite C6; destruct m; reflexivity|].
        rewrite C5 in R1. split; [lia|]. split; [exact R2|]. split; [exact R3|]. exact R4.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. split; [exact HO|]. split; [lia|]. right. split; [lia|]. split; [lia|].
      rewrite (dk_bitsn dkit _ _ _ _ n HO) by lia. rewrite <- Hq.
      change (sbits (fr_g C)) with (bytes_bits (fr_src C)). rewrite HS.
      rewrite need_bval_bits_le by lia. apply Z.mod_small. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invalid symbols: 286, 287 (literal/length), 30, 31 (distance) mean "invalid code" (op 64)  *)

Lemma fb_ms_invalid type sy op val :
  ((type = LENS /\ (sy = 286 \/ sy = 287)) \/ (type = DISTS /\ (sy = 30 \/ sy = 31))) ->
  ref.means_symbol type sy op val = (Z.land op 112 =? 64).
Proof. intros [[-> [-> | ->]] | [-> [-> | ->]]]; reflexivity. Qed.

Lemma fr_bits : fr_bits_stmt.
Proof.
  constructor.
  - intros C pos inp m t rb kind lens sy Hin Hbuf HT Hsy Hb8 q Hend Hsb.
    destruct (fb_tab_facts _ _ _ _ HT) as (_ & _ & LN & _).
    specialize (LN sy Hsy). pose proof Hbuf as (_ & _ & (Hb0 & _)).
    unfold lookup1.
    exact (fb_lk1 C pos inp t rb kind lens sy q Hin HT Hsy Hend Hsb 3 m Hbuf eq_refl ltac:(lia) ltac:(lia)
             ltac:(cbn; lia)).
  - intros C pos inp m n v Hin Hbuf HL Hn Hv Hb8 q Hend Hsb.
    pose proof Hbuf as (_ & _ & (Hb0 & _)).
    destruct (fb_need_gen C pos inp n v q 4 m Hin Hbuf eq_refl HL Hn Hv Hsb Hend ltac:(lia) ltac:(cbn; lia))
      as (nx & h & b & lv & E & R).
    unfold needbits. rewrite E. exists nx, h, b.
    replace (m_leave (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv)) with lv
      by (destruct m; reflexivity).
    split; [reflexivity|]. exact R.
  - exact ms_lit.
  - exact ms_len.
  - exact ms_dist.
  - intros type sy op val Hts H. rewrite (fb_ms_invalid type sy op val Hts) in H. apply Z.eqb_eq, H.
Qed.

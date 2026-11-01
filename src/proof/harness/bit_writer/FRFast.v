(* The fixed-block run theory (FRDefs.v): LEN's fast path, inflate_fast over the fixed tables (literals, then the
   tail's invalid element inside inflate_fast, or back to LEN).

   The loop of inflate_fast (Model.fast_loop) is followed at literal boundaries (`fri`: before literal j, its
   code at the bit position fr_lpos C j, the output so far the first j literals), as DecFast.dfast_loop does for
   a general stream; each pass (DecFastKit.fast_iter_eq) writes literal j, or at the tail stops at the error
   (`frb`): TLL is an invalid literal/length code (F_ll_code), TDCode an invalid distance code (F_d_code), TFar a
   distance beyond the output and the window (F_far).  The bit reading is DecFastIter's (`rs`, rs_refill,
   rs_walk, rs_lenx, rs_distx), the fixed tables' walk DecFastWalk.dfw. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.DecFastKit Zlib.proof.rfc1951.DecFastIter
  Zlib.proof.rfc1951.DecFastWalk Zlib.proof.rfc1951.DecFast Zlib.proof.rfc1951.TabDec
  Zlib.proof.inflate.FixedValid2.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* small facts                                                                                    *)

(* a length with its extra bits is at most 258, a distance with its extra bits at most 32768 *)
Lemma fr_len_max : forall i, 0 <= i <= 28 -> Znth i len_base + 2 ^ Znth i len_extra <= 259.
Proof.
  intros i Hi.
  assert (Ch: chk_upto (fun i => Znth i len_base + 2 ^ Znth i len_extra <=? 259) 29 0 = true)
    by (vm_compute; reflexivity).
  apply Z.leb_le. apply (chk_upto_ok _ _ _ Ch). cbn. lia.
Qed.

Lemma fr_dist_max : forall d, 0 <= d <= 29 -> Znth d dist_base + 2 ^ Znth d dist_extra <= 32769.
Proof.
  intros d Hd.
  assert (Ch: chk_upto (fun d => Znth d dist_base + 2 ^ Znth d dist_extra <=? 32769) 30 0 = true)
    by (vm_compute; reflexivity).
  apply Z.leb_le. apply (chk_upto_ok _ _ _ Ch). cbn. lia.
Qed.

(* an invalid code's entry (op & 112 = 64): not a literal, not a length or distance, not the end of block *)
Lemma fr_land112 : forall op, Z.land op 112 = 64 ->
  (op =? 0) = false /\ (Z.land op 16 =? 0) = true /\ (Z.land op 32 =? 0) = true.
Proof.
  intros op H. split; [|split].
  - apply Z.eqb_neq. intros ->. discriminate H.
  - apply Z.eqb_eq. change 16 with (Z.land 112 16). rewrite Z.land_assoc, H. reflexivity.
  - apply Z.eqb_eq. change 32 with (Z.land 112 32). rewrite Z.land_assoc, H. reflexivity.
Qed.

Lemma fr_rs_setow : forall G pos m0 ow q m ow', rs G pos m0 ow q m -> rs G pos m0 ow' q (set_m_ow m ow').
Proof.
  intros G pos m0 ow q m ow' (nx & h & b & -> & R). exists nx, h, b. split; [reflexivity | exact R].
Qed.

Lemma fr_rs_m0 : forall G pos m0 ow q m, rs G pos m0 ow q m -> m_inp m = m_inp m0 /\ m_aout m = m_aout m0.
Proof. intros G pos m0 ow q m (nx & h & b & -> & _). split; reflexivity. Qed.

(* fr_at at LEN, and how to build fr_at at LEN and at BAD *)
Lemma fr_at_len : forall C s c h b out, fr_at C s c h b out -> i_mode s = LEN ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ b <= 8 /\
  exists j, 0 <= j <= fr_n C /\ 8 * c - b = fr_lpos C j /\ out = fr_lit C j.
Proof.
  intros C s c h b out H HM. unfold fr_at in H. cbv zeta in H. rewrite HM in H.
  destruct H as [[E _]|[Hh H]]; [unfold LEN, BAD in E; lia|].
  destruct H as [(E & _)|[(E & _)|(Hf & H)]]; [unfold LEN, HEAD in E; lia|unfold LEN, TYPEDO in E; lia|].
  destruct H as [(_ & Hb & J)|H]; [auto|].
  exfalso.
  repeat (destruct H as [H|H]; [destruct H as [E _]; revert E; unfold LEN, LIT, LENEXT, DIST, DISTEXT; lia|]).
  destruct H as [E _]; revert E; unfold LEN, MATCH; lia.
Qed.

Lemma fr_at_len_mk : forall C s c h b out j,
  hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = LEN -> b <= 8 -> 0 <= j <= fr_n C ->
  8 * c - b = fr_lpos C j -> out = fr_lit C j -> fr_at C s c h b out.
Proof.
  intros C s c h b out j Hh Hf HM Hb Hj Hq Ho. unfold fr_at. cbv zeta. rewrite HM.
  right. split; [exact Hh|]. right; right. split; [exact Hf|]. left.
  split; [right; reflexivity|]. split; [exact Hb|]. exists j. auto.
Qed.

Lemma fr_at_bad_mk : forall C s c h b out,
  i_mode s = BAD -> Zlength out <= fr_n C -> fr_at C s c h b out.
Proof. intros. unfold fr_at. cbv zeta. left. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the loop of inflate_fast from m0 = restore m at LEN                                            *)

Section Fast.
Variables (C: frc) (pos: Z) (ob: list Z) (m0: mst).
Context (Hlay: fr_layout_stmt) (Hbit: fr_bits_stmt) (Hok: fr_ok C).
Context (Hpos: 0 <= pos) (Hnx0: 0 <= m_nx m0).
Context (Hlen: pos + Zlength (m_inp m0) <= Zlength (fr_src C)).
Context (Hinp: m_inp m0 = sublist pos (pos + Zlength (m_inp m0)) (fr_src C)).
Context (Hfix: fr_fixed (m_s m0)) (Hwh: i_whave (m_s m0) <= Zlength ob) (Hsane: i_sane (m_s m0) = 1).

(* the bit position at the entry *)
Definition fq0 : Z := 8 * (pos + m_nx m0) - m_bits m0.

(* before literal j (j = n: before the tail) *)
Definition fri (j: Z) (mm: mst) : Prop :=
  0 <= j <= fr_n C /\ rs (fr_g C) pos m0 (m_ow mm) (fr_lpos C j) mm /\ ob ++ m_ow mm = fr_lit C j /\
  fq0 <= fr_lpos C j /\ Zlength (m_ow mm) <= m_aout m0.

(* the error inside the tail, all the literals written *)
Definition frb (mb: mst) : Prop :=
  exists mm e q, mb = set_bad mm e /\ rs (fr_g C) pos m0 (m_ow mm) q mm /\ fq0 <= q /\
    ob ++ m_ow mm = fr_lits C /\ Zlength (m_ow mm) <= m_aout m0.

Lemma fr_iter_lit : forall j mm, fri j mm -> j < fr_n C ->
  m_nx mm + 6 <= Zlength (m_inp m0) -> Zlength (m_ow mm) + 258 <= m_aout m0 ->
  let '(go, mm') := fast_iter lenfix_list distfix_list mm in
  go = true /\ fri (j + 1) mm' /\ Zlength (m_ow mm) < Zlength (m_ow mm').
Proof using Hlay Hok Hpos Hnx0 Hlen Hinp Hfix.
  intros j mm (Hj & R & Ho & Hq0 & Ha) Hjn Hnx Hout.
  destruct (Hlay C Hok) as (Lj & L0 & Lpos & Llit & Lall & Lend & Ltail & Lll & Ldl & Lllr & Ldlr & Lext & Ldext).
  destruct (Lj j ltac:(lia)) as (Hb & Hp1 & Hsub & Hl1).
  destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R) as (Q & B & N & Ow & Ss & Hh).
  rewrite fast_iter_eq, Ss.
  destruct (rs_refill (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R) as [R1 B1]; [unfold Lim; lia|].
  destruct (lwalk (m_s m0) (refill2 mm)) as [here m2] eqn:EW. unfold lwalk in EW.
  destruct Hfix as (F1 & F2 & F3 & F4). rewrite F1, F2 in EW.
  set (sy := Znth j (fr_lits C)) in *.
  pose proof (Lllr sy ltac:(lia)) as Lsy.
  rewrite Hp1 in Hsub.
  destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ LENS len_link TLenfix 9 fixed_ll sy here m2
              dfw R1 (proj1 (tabdec_fixed _)) (proj1 (tvalid_fixed2 _)) (or_introl (conj eq_refl eq_refl))
              ltac:(lia) ltac:(lia) ltac:(lia) Hsub EW) as (Hms & R2 & B2).
  apply ms_lit in Hms; [|lia]. destruct Hms as [Hop Hval].
  destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R2) as (_ & _ & _ & Ow2 & _).
  unfold fdisp. rewrite Hop. cbn [Z.eqb]. cbv beta iota.
  rewrite Hval, Z.mod_small by lia. rewrite Ow2.
  split; [reflexivity|]. split.
  - unfold fri. split; [lia|]. split; [|split; [|split]].
    + rewrite ow_set. apply fr_rs_setow with (ow := m_ow mm). rewrite Hp1. exact R2.
    + rewrite ow_set, app_assoc, Ho, Hl1. reflexivity.
    + lia.
    + rewrite ow_set, Zlength_app, Zlength_cons, Zlength_nil. lia.
  - rewrite ow_set, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

(* at the tail, the pass stops at the error *)
Lemma fr_iter_tail : forall mm, fri (fr_n C) mm -> m_nx mm + 6 <= Zlength (m_inp m0) ->
  let '(go, mm') := fast_iter lenfix_list distfix_list mm in go = false /\ frb mm'.
Proof using Hlay Hbit Hok Hpos Hnx0 Hlen Hinp Hfix Hwh Hsane.
  intros mm (Hj & R & Ho & Hq0 & Ha) Hnx.
  destruct (Hlay C Hok) as (Lj & L0 & Lpos & Llit & Lall & Lend & Ltail & Lll & Ldl & Lllr & Ldlr & Lext & Ldext).
  rewrite Lall in Ho.
  assert (Hn: Zlength (ob ++ m_ow mm) = fr_n C) by (rewrite Ho; reflexivity).
  rewrite Zlength_app in Hn.
  pose proof (Zlength_nonneg ob). pose proof (Zlength_nonneg (m_ow mm)).
  change (fr_lpos C (fr_n C)) with (fr_tpos C) in *.
  set (t := fr_tpos C) in *.
  destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R) as (Q & B & N & _ & Ss & Hh).
  assert (HL: t + 48 <= Lim pos m0) by (unfold Lim; lia).
  rewrite fast_iter_eq, Ss.
  destruct (rs_refill (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R) as [R1 B1]; [lia|].
  destruct (lwalk (m_s m0) (refill2 mm)) as [here m2] eqn:EW. unfold lwalk in EW.
  destruct Hfix as (F1 & F2 & F3 & F4). rewrite F1, F2 in EW.
  pose proof Hok as (_ & _ & _ & Htl & _).
  cbv zeta in Ltail. revert Htl Ltail. destruct (fr_tail C) as [w|w|lc lx dc dx] eqn:ET; intros Htl Ltail;
    cbn [tail_ok] in Htl.
  - (* TLL: an invalid literal/length code *)
    destruct Ltail as (E1 & S1). rewrite E1 in S1.
    pose proof (Lllr (286 + w) ltac:(lia)) as L1.
    destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ LENS len_link TLenfix 9 fixed_ll
                (286 + w) here m2 dfw R1 (proj1 (tabdec_fixed _)) (proj1 (tvalid_fixed2 _))
                (or_introl (conj eq_refl eq_refl)) ltac:(lia) ltac:(lia) ltac:(lia) S1 EW) as (Hms & R2 & B2).
    pose proof (fb_ms_bad Hbit LENS (286 + w) _ _ ltac:(left; split; [reflexivity|lia]) Hms) as H112.
    destruct (fr_land112 _ H112) as (E0 & E16 & E32).
    unfold fdisp. rewrite E0, E16, E32. cbv beta iota delta [negb].
    destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R2) as (_ & _ & _ & Ow2 & _).
    split; [reflexivity|]. exists m2, F_ll_code, (t + Znth (286 + w) fixed_ll).
    rewrite Ow2. split; [reflexivity|]. split; [exact R2|]. split; [lia|]. split; assumption.
  - (* TDCode: the length code 257, then an invalid distance code *)
    destruct Ltail as (E1 & S1 & S2). rewrite E1 in S2.
    pose proof (Lllr 257 ltac:(lia)) as L1. pose proof (Ldlr (30 + w) ltac:(lia)) as L2.
    destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ LENS len_link TLenfix 9 fixed_ll
                257 here m2 dfw R1 (proj1 (tabdec_fixed _)) (proj1 (tvalid_fixed2 _))
                (or_introl (conj eq_refl eq_refl)) ltac:(lia) ltac:(lia) ltac:(lia) S1 EW) as (Hms & R2 & B2).
    destruct (ms_len 0 _ _ ltac:(lia) Hms) as [Hop Hval].
    assert (Ee: Znth 0 len_extra = 0) by reflexivity.
    assert (Eb: Znth 0 len_base = 3) by reflexivity.
    rewrite Ee in Hop. rewrite Eb in Hval.
    assert (Hop': e_op here = 16) by (rewrite Hop; reflexivity).
    unfold fdisp. rewrite Hop'. change (16 =? 0) with false. change (Z.land 16 16 =? 0) with false.
    cbv beta iota delta [negb].
    unfold flen. destruct (lenx here m2) as [len' m3] eqn:EL.
    assert (S0: sublist (t + Znth 257 fixed_ll) (t + Znth 257 fixed_ll + 0) (sbits (fr_g C)) = bits_le (3 - 3) 0)
      by (rewrite Z.add_0_r, sublist_nil; reflexivity).
    destruct (rs_lenx (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ here 0 3 3 len' m3 R2 Hop Hval
                ltac:(lia) ltac:(cbn; lia) ltac:(lia) S0 ltac:(lia) EL) as [-> R3].
    rewrite Z.add_0_r in R3.
    cbv beta iota.
    destruct (rs_refill (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R3) as [R4 B4]; [lia|].
    destruct (dwalk (m_s m0) (refill2 m3)) as [here2 m5] eqn:EDW. unfold dwalk in EDW. rewrite F3, F4 in EDW.
    destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ DISTS dist_link TDistfix 5 fixed_dl
                (30 + w) here2 m5 dfw R4 (proj2 (tabdec_fixed _)) (proj2 (tvalid_fixed2 _))
                (or_intror (conj eq_refl eq_refl)) ltac:(lia) ltac:(lia) ltac:(lia) S2 EDW) as (Hms2 & R5 & B5).
    pose proof (fb_ms_bad Hbit DISTS (30 + w) _ _ ltac:(right; split; [reflexivity|lia]) Hms2) as H112.
    destruct (fr_land112 _ H112) as (_ & E16 & _).
    cbv beta iota. rewrite E16. cbv beta iota delta [negb].
    destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R5) as (_ & _ & _ & Ow5 & _).
    split; [reflexivity|]. exists m5, F_d_code, (t + Znth 257 fixed_ll + Znth (30 + w) fixed_dl).
    rewrite Ow5. split; [reflexivity|]. split; [exact R5|]. split; [lia|]. split; assumption.
  - (* TFar: a length, then a distance beyond the output and the window *)
    destruct Htl as (Hlc & Hlx & Hdc & Hdx & Hfar).
    destruct Ltail as (E1 & S1 & S2 & S3 & S4).
    set (i := lc - 257) in *. set (e := Znth i len_extra) in *. set (base := Znth i len_base) in *.
    set (de := Znth dc dist_extra) in *. set (db := Znth dc dist_base) in *.
    pose proof (Lllr lc ltac:(lia)) as L1. pose proof (Ldlr dc ltac:(lia)) as L2.
    destruct (Lext i ltac:(lia)) as [Le Lb]. destruct (Ldext dc ltac:(lia)) as [Lde Ldb].
    pose proof (fr_len_max i ltac:(lia)) as Lm. pose proof (fr_dist_max dc ltac:(lia)) as Dm.
    fold e base in Lm. fold de db in Dm.
    rewrite L2 in S3, S4, E1. rewrite E1 in S4.
    destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ LENS len_link TLenfix 9 fixed_ll
                lc here m2 dfw R1 (proj1 (tabdec_fixed _)) (proj1 (tvalid_fixed2 _))
                (or_introl (conj eq_refl eq_refl)) ltac:(lia) ltac:(lia) ltac:(lia) S1 EW) as (Hms & R2 & B2).
    replace lc with (257 + i) in Hms by (unfold i; lia).
    destruct (ms_len i _ _ ltac:(lia) Hms) as [Hop Hval]. fold e base in Hop, Hval.
    destruct (land15 e) as (_ & Hl16 & Hl0); [lia|].
    unfold fdisp. rewrite Hop, Hl0.
    replace (Z.land (16 + e) 16 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hl16).
    cbv beta iota delta [negb].
    unfold flen. destruct (lenx here m2) as [len' m3] eqn:EL.
    assert (S2': sublist (t + Znth lc fixed_ll) (t + Znth lc fixed_ll + e) (sbits (fr_g C)) = bits_le (base + lx - base) e)
      by (replace (base + lx - base) with lx by lia; exact S2).
    destruct (rs_lenx (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ here e base (base + lx) len' m3 R2 Hop Hval
                ltac:(lia) ltac:(lia) ltac:(lia) S2' ltac:(lia) EL) as [-> R3].
    cbv beta iota.
    destruct (rs_refill (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R3) as [R4 B4]; [lia|].
    destruct (dwalk (m_s m0) (refill2 m3)) as [here2 m5] eqn:EDW. unfold dwalk in EDW. rewrite F3, F4 in EDW.
    destruct (rs_walk (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ DISTS dist_link TDistfix 5 fixed_dl
                dc here2 m5 dfw R4 (proj2 (tabdec_fixed _)) (proj2 (tvalid_fixed2 _))
                (or_intror (conj eq_refl eq_refl)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite L2; exact S3) EDW)
      as (Hms2 & R5 & B5).
    destruct (ms_dist dc _ _ ltac:(lia) Hms2) as [Hop2 Hval2]. fold de db in Hop2, Hval2.
    destruct (land15 de) as (_ & Hd16 & _); [lia|].
    cbv beta iota. rewrite Hop2.
    replace (Z.land (16 + de) 16 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd16).
    cbv beta iota delta [negb].
    destruct (distx here2 m5) as [dist' m6] eqn:EDX.
    rewrite L2 in R5.
    assert (S4': sublist (t + Znth lc fixed_ll + e + 5) (t + Znth lc fixed_ll + e + 5 + de) (sbits (fr_g C))
                 = bits_le (db + dx - db) de)
      by (replace (db + dx - db) with dx by lia; exact S4).
    destruct (rs_distx (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ here2 de db (db + dx) dist' m6 R5 Hop2 Hval2
                ltac:(lia) ltac:(lia) ltac:(lia) S4' ltac:(lia) EDX) as [-> R6].
    cbv beta iota.
    destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen Hinp _ _ _ R6) as (_ & _ & _ & Ow6 & _).
    unfold fcopy. cbv zeta. rewrite Ow6, Hsane.
    replace (Zlength (m_ow mm) <? db + dx) with true by (symmetry; apply Z.ltb_lt; unfold fr_n in Hn; lia).
    replace (i_whave (m_s m0) <? db + dx - Zlength (m_ow mm)) with true
      by (symmetry; apply Z.ltb_lt; unfold fr_n in Hn; lia).
    change (negb (1 =? 0)) with true. cbv beta iota delta [andb].
    split; [reflexivity|]. exists m6, F_far, (t + Znth lc fixed_ll + e + 5 + de).
    rewrite Ow6. split; [reflexivity|]. split; [exact R6|]. split; [lia|]. split; assumption.
Qed.

(* the loop (fuel above the output space left: each pass that goes on writes a byte) stops before a literal or
   at the error *)
Lemma fr_loop : forall n j mm, fri j mm ->
  m_nx mm + 6 <= Zlength (m_inp m0) -> Zlength (m_ow mm) + 258 <= m_aout m0 ->
  m_aout m0 - Zlength (m_ow mm) < Z.of_nat n ->
  let mf := fast_loop lenfix_list distfix_list n mm in (exists j', fri j' mf) \/ frb mf.
Proof using Hlay Hbit Hok Hpos Hnx0 Hlen Hinp Hfix Hwh Hsane.
  induction n as [|n IH]; intros j mm F Hn Ho Hf; cbv zeta.
  - simpl in Hf. lia.
  - cbn [fast_loop].
    pose proof F as (Hj & _).
    destruct (Z.lt_ge_cases j (fr_n C)) as [Hjn|Hjn].
    + pose proof (fr_iter_lit j mm F Hjn Hn Ho) as IT.
      destruct (fast_iter lenfix_list distfix_list mm) as [go m1].
      destruct IT as (-> & F1 & Hg).
      pose proof F1 as (_ & R1 & _).
      destruct (fr_rs_m0 _ _ _ _ _ _ R1) as [Ei Ea]. rewrite Ei, Ea.
      destruct (m_nx m1 <? Zlength (m_inp m0) - 5) eqn:C1; cbn [andb];
        [destruct (Zlength (m_ow m1) <? m_aout m0 - 257) eqn:C2|].
      * apply Z.ltb_lt in C1, C2. apply (IH (j + 1) m1); auto; lia.
      * left. exists (j + 1). exact F1.
      * left. exists (j + 1). exact F1.
    + assert (Ej: j = fr_n C) by lia. subst j.
      pose proof (fr_iter_tail mm F Hn) as IT.
      destruct (fast_iter lenfix_list distfix_list mm) as [go m1].
      destruct IT as (-> & B1). cbn [andb]. right. exact B1.
Qed.

End Fast.


(* ---------------------------------------------------------------------------------------------- *)
(* the end of inflate_fast: the unused bytes given back, RESTORE                                  *)

(* the machine inflate_fast returns, from the one its loop stopped at *)
Lemma fr_fin_fields : forall X, let mf := restore (ftail X) in let len := Z.shiftr (m_bits X) 3 in
  m_nx mf = m_nx X - len /\ m_ow mf = m_ow X /\ m_hold mf = m_hold X mod 2 ^ (m_bits X - len * 8) /\
  m_bits mf = m_bits X - len * 8 /\
  m_inp mf = m_inp X /\ m_in mf = m_in X /\ m_aout mf = m_aout X /\ m_out mf = m_out X /\
  m_leave mf = m_leave X /\ m_ret mf = m_ret X /\
  m_s mf = set_i_bits (set_i_hold (m_s X) (m_hold X mod 2 ^ (m_bits X - len * 8))) (m_bits X - len * 8).
Proof. intros X. repeat split. Qed.

Lemma fr_rs_fields : forall G pos m0 ow q m, rs G pos m0 ow q m ->
  m_inp m = m_inp m0 /\ m_in m = m_in m0 /\ m_aout m = m_aout m0 /\ m_out m = m_out m0 /\
  m_leave m = m_leave m0 /\ m_ret m = m_ret m0 /\ m_s m = m_s m0.
Proof. intros G pos m0 ow q m (nx & h & b & -> & _). repeat split. Qed.

Lemma fr_bad_fields : forall X e,
  m_nx (set_bad X e) = m_nx X /\ m_ow (set_bad X e) = m_ow X /\ m_hold (set_bad X e) = m_hold X /\
  m_bits (set_bad X e) = m_bits X /\
  m_inp (set_bad X e) = m_inp X /\ m_in (set_bad X e) = m_in X /\ m_aout (set_bad X e) = m_aout X /\
  m_out (set_bad X e) = m_out X /\ m_leave (set_bad X e) = m_leave X /\ m_ret (set_bad X e) = m_ret X /\
  m_s (set_bad X e) = set_i_mode (m_s X) BAD.
Proof. intros X e. repeat split. Qed.

Lemma fr_restore_fields : forall m,
  m_nx (restore m) = m_nx m /\ m_ow (restore m) = m_ow m /\ m_hold (restore m) = m_hold m /\
  m_bits (restore m) = m_bits m /\
  m_inp (restore m) = m_inp m /\ m_in (restore m) = m_in m /\ m_aout (restore m) = m_aout m /\
  m_out (restore m) = m_out m /\ m_leave (restore m) = m_leave m /\ m_ret (restore m) = m_ret m /\
  m_s (restore m) = set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m).
Proof. intros m. repeat split. Qed.

(* the bytes given back: nothing before the call's input (the entry had bits < 8 and the loop only goes on) *)
Lemma fr_back : forall pos nx0 b0 nx b q, 0 <= nx0 -> 0 <= b0 < 8 -> 0 <= b ->
  8 * (pos + nx0) - b0 <= q -> 8 * (pos + nx) - b = q -> 0 <= nx - Z.shiftr b 3 <= nx.
Proof.
  intros pos nx0 b0 nx b q H1 H2 H3 H4 H5. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_mod b 8 ltac:(lia)). pose proof (Z.mod_pos_bound b 8 ltac:(lia)).
  pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fr_fast : fr_layout_stmt -> fr_bits_stmt -> fr_fast_stmt.
Proof.
  intros Hlay Hbit C pos inp ob L z m Hctx K HM Hh Hlf Hb.
  destruct Hctx as (Hok & Hpos & Hlen & Hinp & _ & Hlive & _).
  destruct K as [[Mi Min Ma Mo Mnx Mow Mwin Mwh Mat] Mlv Mret].
  destruct (fr_at_len C _ _ _ _ _ Mat HM) as (Hho & Hfx & _ & j & Hj & Hq & Hout).
  assert (Hsane: i_sane (m_s m) = 1).
  { destruct Mwin as (_ & _ & _ & _ & _ & _ & E). rewrite E. destruct Hlive as (_ & Hsw & _). apply (sw_sane _ Hsw). }
  unfold m_have, m_left in Hh, Hlf.
  destruct (fr_restore_fields m) as (Enx & Eow & Ehold & Ebits & Einp & Ein & Eaout & Eout & Elv & Eret & Es).
  set (m0 := restore m) in *.
  assert (Hnx0: 0 <= m_nx m0) by lia.
  assert (Hlen0: pos + Zlength (m_inp m0) <= Zlength (fr_src C)) by (rewrite Einp, Mi; exact Hlen).
  assert (Hinp0: m_inp m0 = sublist pos (pos + Zlength (m_inp m0)) (fr_src C)) by (rewrite Einp, Mi; exact Hinp).
  assert (Hfix0: fr_fixed (m_s m0)) by (rewrite Es; exact Hfx).
  assert (Hwh0: i_whave (m_s m0) <= Zlength ob).
  { rewrite Es. destruct Mwin as (_ & E & _). cbn [i_whave set_i_bits set_i_hold]. rewrite E. exact Mwh. }
  assert (Hsane0: i_sane (m_s m0) = 1) by (rewrite Es; exact Hsane).
  assert (F0: fri C pos ob m0 j m0).
  { split; [lia|]. split; [|split; [|split]].
    - exists (m_nx m0), (m_hold m0), (m_bits m0). split; [apply fset_self|].
      rewrite Enx, Ehold, Ebits. split; [exact Hho|]. split; [destruct Hho; lia|].
      split; [rewrite Einp, Mi; lia | exact Hq].
    - rewrite Eow. exact Hout.
    - unfold fq0. rewrite Enx, Ebits. lia.
    - rewrite Eow, Eaout, Ma. exact Mow. }
  assert (A1: m_nx m0 + 6 <= Zlength (m_inp m0)) by (rewrite Enx, Einp; lia).
  assert (A2: Zlength (m_ow m0) + 258 <= m_aout m0) by (rewrite Eow, Eaout; lia).
  assert (A3: m_aout m0 - Zlength (m_ow m0) < Z.of_nat (Z.to_nat (m_aout m0) + 1)).
  { pose proof (Zlength_nonneg (m_ow m0)). rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  pose proof (fr_loop C pos ob m0 Hlay Hbit Hok Hpos Hnx0 Hlen0 Hinp0 Hfix0 Hwh0 Hsane0
                (Z.to_nat (m_aout m0) + 1) j m0 F0 A1 A2 A3) as LP.
  cbv zeta in LP |- *. rewrite fast_eq.
  set (mf := fast_loop lenfix_list distfix_list (Z.to_nat (m_aout m0) + 1) m0) in *. clearbody mf.
  destruct LP as [(j' & Hj' & R & Ho & Hq0 & Ha) | (mm & e & q & -> & R & Hq0 & Ho & Ha)].
  - (* back to LEN before literal j' *)
    destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen0 Hinp0 _ _ _ R)
      as (Q & B & N & _ & Ss & Hh2).
    destruct (fr_rs_fields _ _ _ _ _ _ R) as (Fi & Fin & Fa & Fo & Fl & Fr & _).
    destruct (fr_fin_fields mf) as (Gnx & Gow & Ghold & Gbits & Gi & Gin & Ga & Go & Gl & Gr & Gs).
    pose proof (tail_hold dkit (fr_g C) (pos + m_nx mf) (m_hold mf) (m_bits mf) Hh2) as (T1 & T2 & T3).
    unfold fq0 in Hq0. rewrite Enx, Ebits in Hq0.
    pose proof (fr_back pos (m_nx m) (m_bits m) (m_nx mf) (m_bits mf) _ ltac:(lia) ltac:(destruct Hho; lia)
                  ltac:(lia) Hq0 Q) as BK.
    set (mf' := restore (ftail mf)) in *.
    assert (Md: m_mode mf' = LEN).
    { unfold m_mode. rewrite Gs, Ss, Es. exact HM. }
    rewrite Md. replace (LEN =? Zlib.proof.inflate.Model.TYPE) with false by reflexivity.
    constructor; [constructor| |].
    + rewrite Gi, Fi, Einp. exact Mi.
    + rewrite Gin, Fin, Ein. exact Min.
    + rewrite Ga, Fa, Eaout. exact Ma.
    + rewrite Go, Fo, Eout. exact Mo.
    + rewrite Gnx. rewrite Einp, Mi in N. lia.
    + rewrite Gow. rewrite Eaout, Ma in Ha. exact Ha.
    + rewrite Gs, Ss, Es. exact Mwin.
    + exact Mwh.
    + apply (fr_at_len_mk C _ _ _ _ _ j').
      * rewrite Gnx, Ghold, Gbits. replace (pos + (m_nx mf - Z.shiftr (m_bits mf) 3))
          with (pos + m_nx mf - Z.shiftr (m_bits mf) 3) by lia. exact T1.
      * rewrite Gs, Ss, Es. exact Hfx.
      * exact Md.
      * rewrite Gbits. lia.
      * exact Hj'.
      * rewrite Gnx, Gbits. lia.
      * rewrite Gow. exact Ho.
    + rewrite Gl, Fl, Elv. exact Mlv.
    + rewrite Gr, Fr, Eret. exact Mret.
  - (* the error *)
    destruct (rs_q (fr_g C) pos m0 dkit (proj1 Hok) Hpos Hnx0 Hlen0 Hinp0 _ _ _ R)
      as (Q & B & N & _ & Ss & Hh2).
    destruct (fr_rs_fields _ _ _ _ _ _ R) as (Fi & Fin & Fa & Fo & Fl & Fr & _).
    destruct (fr_bad_fields mm e) as (Bnx & Bow & Bhold & Bbits & Bi & Bin & Ba & Bo & Bl & Br & Bs).
    destruct (fr_fin_fields (set_bad mm e)) as (Gnx & Gow & Ghold & Gbits & Gi & Gin & Ga & Go & Gl & Gr & Gs).
    unfold fq0 in Hq0. rewrite Enx, Ebits in Hq0.
    pose proof (fr_back pos (m_nx m) (m_bits m) (m_nx mm) (m_bits mm) _ ltac:(lia) ltac:(destruct Hho; lia)
                  ltac:(lia) Hq0 Q) as BK.
    set (mf' := restore (ftail (set_bad mm e))) in *.
    assert (Md: m_mode mf' = BAD) by (unfold m_mode; rewrite Gs, Bs; reflexivity).
    rewrite Md. replace (BAD =? Zlib.proof.inflate.Model.TYPE) with false by reflexivity.
    constructor; [constructor| |].
    + rewrite Gi, Bi, Fi, Einp. exact Mi.
    + rewrite Gin, Bin, Fin, Ein. exact Min.
    + rewrite Ga, Ba, Fa, Eaout. exact Ma.
    + rewrite Go, Bo, Fo, Eout. exact Mo.
    + rewrite Gnx, Bnx, Bbits. rewrite Einp, Mi in N. lia.
    + rewrite Gow, Bow. rewrite Eaout, Ma in Ha. exact Ha.
    + rewrite Gs, Bs, Ss, Es. exact Mwin.
    + exact Mwh.
    + apply fr_at_bad_mk; [exact Md|]. rewrite Gow, Bow, Ho. unfold fr_n. lia.
    + rewrite Gl, Bl, Fl, Elv. exact Mlv.
    + rewrite Gr, Br, Fr, Eret. exact Mret.
Qed.

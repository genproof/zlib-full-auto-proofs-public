(* The fixed-block run theory (FRDefs.v): the passes of the tail's modes LENEXT, DIST, DISTEXT, MATCH (the
   invalid distance code, or the distance too far back) and BAD. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* reduce the projections of the machine's and the state's setters (the records stay folded) *)
Ltac fr_simpl := cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg
  m_tin m_tout m_snx m_sow set_m_leave set_m_bits set_m_hold set_m_nx set_m_s set_m_msg set_m_ret m_mode
  upd_s set_mode set_bad dropbits set_leave i_mode i_wsize i_whave i_wnext i_win i_wdata i_wbits i_sane
  i_lencode i_lenbits i_distcode i_distbits i_offset i_extra i_length i_back i_was set_i_mode set_i_back
  set_i_offset set_i_extra set_i_length set_i_was] in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine after a step that only moves in the input or changes the state's decoding fields     *)

Lemma fr_wsame_trans s1 s2 s3 : fr_wsame s1 s2 -> fr_wsame s2 s3 -> fr_wsame s1 s3.
Proof.
  unfold fr_wsame. intros (A1&A2&A3&A4&A5&A6&A7) (B1&B2&B3&B4&B5&B6&B7).
  repeat split; congruence.
Qed.

Lemma frM_mk C pos inp ob L z m m' :
  fr_M C pos inp ob L z m ->
  m_inp m' = m_inp m -> m_in m' = m_in m -> m_aout m' = m_aout m -> m_out m' = m_out m ->
  m_ow m' = m_ow m -> 0 <= m_nx m' <= Zlength inp -> fr_wsame (m_s m) (m_s m') ->
  fr_at C (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m) ->
  fr_M C pos inp ob L z m'.
Proof.
  intros [Hinp Hin Haout Hout Hnx How Hwin Hwh Hat] E1 E2 E3 E4 E5 Hnx' Hw Hat'.
  constructor; try congruence.
  exact (fr_wsame_trans _ _ _ Hwin Hw).
Qed.

(* leaving the loop because the input ran out before the end of the tail *)
Lemma frE_input C pos inp ob L z flush m :
  fr_M C pos inp ob L z m -> m_leave m = 1 -> m_mode m <> BAD -> m_ret m = Z_OK ->
  8 * (pos + Zlength inp) < fr_end C -> fr_E C pos inp ob L z flush m.
Proof.
  intros HM Hl Hb Hr He. constructor; auto. right. split; [exact Hb|]. split; [exact Hr|].
  right. right. exact He.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* fr_at in the tail's modes                                                                      *)

Lemma fr_at_lenext C s c h b out : i_mode s = LENEXT -> fr_at C s c h b out ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ b < 8 /\ out = fr_lits C /\
  ((exists w, fr_tail C = TDCode w /\ 8 * c - b = fr_tpos C + Znth 257 fixed_ll /\ i_extra s = 0) \/
   (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ 8 * c - b = fr_tpos C + Znth lc fixed_ll /\
      i_extra s = Znth (lc - 257) len_extra)).
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[Hfx A]]]]]; [lia|destruct A as [A _]; lia|destruct A as [A _]; lia|].
  destruct A as [[[A|A] _]|[[A _]|[[_ (Hb & Ho & B)]|[[A _]|[[A _]|[A _]]]]]]; try lia.
  auto.
Qed.

Lemma fr_at_dist C s c h b out : i_mode s = DIST -> fr_at C s c h b out ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ b < 8 /\ out = fr_lits C /\
  ((exists w, fr_tail C = TDCode w /\ 8 * c - b = fr_tpos C + Znth 257 fixed_ll) \/
   (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\
      8 * c - b = fr_tpos C + Znth lc fixed_ll + Znth (lc - 257) len_extra)).
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[Hfx A]]]]]; [lia|destruct A as [A _]; lia|destruct A as [A _]; lia|].
  destruct A as [[[A|A] _]|[[A _]|[[A _]|[[_ (Hb & Ho & B)]|[[A _]|[A _]]]]]]; try lia.
  auto.
Qed.

Lemma fr_at_distext C s c h b out : i_mode s = DISTEXT -> fr_at C s c h b out ->
  hold_ok (fr_g C) c h b /\ fr_fixed s /\ (b < 8 \/ b < i_extra s) /\ out = fr_lits C /\
  exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\
    8 * c - b = fr_tpos C + Znth lc fixed_ll + Znth (lc - 257) len_extra + Znth dc fixed_dl /\
    i_offset s = Znth dc dist_base /\ i_extra s = Znth dc dist_extra.
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[Hfx A]]]]]; [lia|destruct A as [A _]; lia|destruct A as [A _]; lia|].
  destruct A as [[[A|A] _]|[[A _]|[[A _]|[[A _]|[[_ (Hb & Ho & B)]|[A _]]]]]]; try lia.
  auto.
Qed.

Lemma fr_at_match C s c h b out : i_mode s = MATCH -> fr_at C s c h b out ->
  out = fr_lits C /\
  exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ i_offset s = Znth dc dist_base + dx.
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[Hfx A]]]]]; [lia|destruct A as [A _]; lia|destruct A as [A _]; lia|].
  destruct A as [[[A|A] _]|[[A _]|[[A _]|[[A _]|[[A _]|[_ B]]]]]]; try lia.
  exact B.
Qed.

(* building fr_at in the tail's modes *)
Lemma fr_at_bad C s c h b out : i_mode s = BAD -> Zlength out <= fr_n C -> fr_at C s c h b out.
Proof. intros. left. auto. Qed.

Lemma fr_at_mk_dist C s c h b : hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = DIST -> b < 8 ->
  ((exists w, fr_tail C = TDCode w /\ 8 * c - b = fr_tpos C + Znth 257 fixed_ll) \/
   (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\
      8 * c - b = fr_tpos C + Znth lc fixed_ll + Znth (lc - 257) len_extra)) ->
  fr_at C s c h b (fr_lits C).
Proof.
  intros Hh Hfx Hm Hb T. right. split; [exact Hh|]. right. right. split; [exact Hfx|].
  right. right. right. left. auto.
Qed.

Lemma fr_at_mk_lenext C s c h b lc lx dc dx : hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = LENEXT ->
  b < 8 -> fr_tail C = TFar lc lx dc dx -> 8 * c - b = fr_tpos C + Znth lc fixed_ll ->
  i_extra s = Znth (lc - 257) len_extra ->
  fr_at C s c h b (fr_lits C).
Proof.
  intros Hh Hfx Hm Hb T Hq He. right. split; [exact Hh|]. right. right. split; [exact Hfx|].
  right. right. left. split; [exact Hm|]. split; [exact Hb|]. split; [reflexivity|].
  right. exists lc, lx, dc, dx. auto.
Qed.

Lemma fr_at_mk_distext C s c h b lc lx dc dx : hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = DISTEXT ->
  (b < 8 \/ b < i_extra s) -> fr_tail C = TFar lc lx dc dx ->
  8 * c - b = fr_tpos C + Znth lc fixed_ll + Znth (lc - 257) len_extra + Znth dc fixed_dl ->
  i_offset s = Znth dc dist_base -> i_extra s = Znth dc dist_extra ->
  fr_at C s c h b (fr_lits C).
Proof.
  intros Hh Hfx Hm Hb T Hq Ho He. right. split; [exact Hh|]. right. right. split; [exact Hfx|].
  right. right. right. right. left. split; [exact Hm|]. split; [exact Hb|]. split; [reflexivity|].
  exists lc, lx, dc, dx. auto.
Qed.

Lemma fr_at_mk_match C s c h b lc lx dc dx : hold_ok (fr_g C) c h b -> fr_fixed s -> i_mode s = MATCH ->
  fr_tail C = TFar lc lx dc dx -> i_offset s = Znth dc dist_base + dx ->
  fr_at C s c h b (fr_lits C).
Proof.
  intros Hh Hfx Hm T Ho. right. split; [exact Hh|]. right. right. split; [exact Hfx|].
  right. right. right. right. right. split; [exact Hm|]. split; [reflexivity|].
  exists lc, lx, dc, dx. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts on the context                                                                           *)

(* the layout of the tail (fr_layout_stmt), the facts the tail's passes use *)
Lemma fr_tail_layout C : fr_layout_stmt -> fr_ok C ->
  fr_tpos C < fr_end C <= 8 * Zlength (fr_src C) /\
  (let t := fr_tpos C in let sb := bytes_bits (fr_src C) in
   match fr_tail C with
   | TLL w => True
   | TDCode w =>
       fr_end C = t + Znth 257 fixed_ll + Znth (30 + w) fixed_dl /\
       sublist (t + Znth 257 fixed_ll) (fr_end C) sb = send_sym fixed_dl (30 + w)
   | TFar lc lx dc dx =>
       let p1 := t + Znth lc fixed_ll in
       let p2 := p1 + Znth (lc - 257) len_extra in
       let p3 := p2 + Znth dc fixed_dl in
       fr_end C = p3 + Znth dc dist_extra /\
       sublist p1 p2 sb = bits_le lx (Znth (lc - 257) len_extra) /\
       sublist p2 p3 sb = send_sym fixed_dl dc /\
       sublist p3 (fr_end C) sb = bits_le dx (Znth dc dist_extra)
   end) /\
  Zlength fixed_dl = 32 /\ (forall sy, 0 <= sy < 32 -> Znth sy fixed_dl = 5) /\
  (forall i, 0 <= i <= 28 -> 0 <= Znth i len_extra <= 5) /\
  (forall d, 0 <= d <= 29 -> 0 <= Znth d dist_extra <= 13).
Proof.
  intros FL Hok.
  destruct (FL C Hok) as (_ & _ & _ & _ & _ & Hte & Htl & _ & Hdl & _ & Hd5 & Hle & Hde).
  split; [exact Hte|]. split.
  - cbv zeta in Htl |- *. destruct (fr_tail C); try tauto.
  - split; [exact Hdl|]. split; [exact Hd5|]. split.
    + intros i Hi. apply (Hle i Hi).
    + intros d Hd. apply (Hde d Hd).
Qed.

(* the entry of a length or distance code: op = 16 + extra (a base), no link, no end/invalid flag *)
Lemma op_base e : 0 <= e <= 13 ->
  Z.land (16 + e) 240 = 16 /\ Z.land (16 + e) 64 = 0 /\ Z.land (16 + e) 15 = e.
Proof.
  intros He.
  assert (e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5 \/ e = 6 \/ e = 7 \/ e = 8 \/ e = 9 \/
          e = 10 \/ e = 11 \/ e = 12 \/ e = 13) as E by lia.
  repeat (destruct E as [-> | E]; [split; [|split]; reflexivity|]).
  subst e. split; [|split]; reflexivity.
Qed.

(* an invalid code's entry (op & 112 = 64): no link, the invalid flag *)
Lemma op_invalid op : Z.land op 112 = 64 -> Z.land op 240 <> 0 /\ Z.land op 64 <> 0.
Proof.
  intros H.
  assert (H64 : Z.land op 64 = 64).
  { change 64 with (Z.land 112 64) at 1. rewrite Z.land_assoc, H. reflexivity. }
  split; [|rewrite H64; discriminate].
  intros H0. assert (Z.land (Z.land op 240) 64 = 0) as E by (rewrite H0; reflexivity).
  rewrite <- Z.land_assoc in E. change (Z.land 240 64) with 64 in E. congruence.
Qed.

Lemma u32_small x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

(* the side conditions of the fr_at_mk_* lemmas: the state's projections *)
Ltac fr_close := try first [assumption | reflexivity | (unfold fr_fixed in *; fr_simpl; assumption) |
                            (fr_simpl; lia)].

(* fr_M of a machine m' derived from m: the side conditions that are projections *)
Ltac fr_mkM m := apply (frM_mk _ _ _ _ _ _ m); fr_simpl; try reflexivity; try lia;
  try match goal with H : fr_M _ _ _ _ _ _ m |- _ => exact H end;
  try (unfold fr_wsame; fr_simpl; repeat split; fail).

(* ---------------------------------------------------------------------------------------------- *)
(* The passes                                                                                     *)

(* BAD: leave with Z_DATA_ERROR *)
Lemma fr_tail_bad : fr_pass (fun md => md = BAD) (fun _ m => c_BAD m).
Proof.
  intros C pos inp ob L z flush m Hctx [[Hinp Hin Haout Hout Hnx How Hwin Hwh Hat] Hlv Hret] Hmd.
  unfold c_BAD, fr_res. right. unfold m_mode in *.
  split; [split|..]; unfold set_leave, m_mode; fr_simpl; auto.
Qed.

(* MATCH: the output is full (all the literals written), or the distance reaches past the window: BAD *)
Lemma fr_tail_match : fr_pass (fun md => md = MATCH) (fun _ m => c_MATCH m).
Proof.
  intros C pos inp ob L z flush m Hctx [HM Hlv Hret] Hmd.
  pose proof HM as [Hinp Hin Haout Hout Hnx How Hwin Hwh Hat].
  destruct (fr_at_match _ _ _ _ _ _ Hmd Hat) as (Ho & lc & lx & dc & dx & Ht & Hoff).
  pose proof Hctx as (Hok & Hp & Hpl & Hinpeq & Hmax & Hlive & Hzf).
  assert (Hfar : Zlength (fr_lits C) < Znth dc dist_base + dx).
  { destruct Hok as (_ & _ & _ & Htl & _). rewrite Ht in Htl. unfold tail_ok in Htl. tauto. }
  assert (Hlen : Zlength ob + Zlength (m_ow m) = Zlength (fr_lits C)) by (rewrite <- Ho, Zlength_app; lia).
  assert (Hao : zf_ao z <= Int.max_unsigned) by (destruct Hzf as (_ & X & _); lia).
  assert (Hsane : i_sane (m_s m) = 1).
  { destruct Hwin as (_ & _ & _ & _ & _ & _ & ->). destruct Hlive as (_ & Hswf & _). apply (sw_sane _ Hswf). }
  assert (Hwh' : i_whave (m_s m) = i_whave (l_s L)) by (destruct Hwin as (_ & X & _); exact X).
  unfold c_MATCH. destruct (m_left m =? 0) eqn:Hl.
  - (* the output space is full: the match is pending *)
    apply Z.eqb_eq in Hl. unfold m_left in Hl. right.
    constructor; unfold set_leave; fr_simpl.
    + destruct HM; constructor; fr_simpl; auto.
    + reflexivity.
    + right. split; [unfold m_mode in *; fr_simpl; rewrite Hmd; unfold MATCH, BAD; lia|].
      split; [exact Hret|]. right. left. split; [lia|]. right. rewrite Ht. split; [exact I | lia].
  - (* the distance is larger than the output: too far back *)
    cbv zeta.
    assert (Hc0 : u32 (m_out m - m_left m) = Zlength (m_ow m)).
    { unfold m_left. rewrite Hout, Haout. replace (zf_ao z - (zf_ao z - Zlength (m_ow m))) with (Zlength (m_ow m)) by lia. apply u32_small. pose proof (Zlength_nonneg (m_ow m)). rep_lia. }
    rewrite Hc0, Hoff.
    pose proof (Zlength_nonneg ob).
    rewrite (proj2 (Z.ltb_lt (Zlength (m_ow m)) _)) by lia.
    rewrite (proj2 (Z.ltb_lt (i_whave (m_s m)) _)) by lia.
    rewrite Hsane. cbn [Z.eqb negb andb].
    left. constructor; [|exact Hlv|exact Hret].
    apply (frM_mk _ _ _ _ _ _ m); try reflexivity; try exact HM; try exact Hnx.
    + unfold fr_wsame. fr_simpl. repeat split.
    + unfold set_bad, set_mode, upd_s. fr_simpl. apply fr_at_bad; [reflexivity|].
      rewrite Ho. unfold fr_n. lia.
Qed.

(* DISTEXT: the distance's extra bits (or the input ends), then MATCH *)
Lemma fr_tail_distext : fr_layout_stmt -> fr_bits_stmt ->
  fr_pass (fun md => md = DISTEXT) (fun _ m => c_DISTEXT m).
Proof.
  intros FL FB C pos inp ob L z flush m Hctx [HM Hlv Hret] Hmd.
  pose proof HM as [Hinp Hin Haout Hout Hnx How Hwin Hwh Hat].
  destruct (fr_at_distext _ _ _ _ _ _ Hmd Hat)
    as (Hh & Hfx & Hb & Ho & lc & lx & dc & dx & Ht & Hq & Hoff & Hex).
  pose proof Hctx as (Hok & Hp & Hpl & Hinpeq & Hmax & Hlive & Hzf).
  pose proof Hok as (Hbo & _ & _ & Htl & _). rewrite Ht in Htl. unfold tail_ok in Htl.
  destruct Htl as (Hlc & Hlx & Hdc & Hdx & Hfar).
  destruct (fr_tail_layout C FL Hok) as (Hte & Hlay & Hdl & Hd5 & Hle & Hde).
  rewrite Ht in Hlay. cbv zeta in Hlay. destruct Hlay as (Hend & _ & _ & Hsub).
  assert (H5 : Znth dc fixed_dl = 5) by (apply Hd5; lia). rewrite H5 in *.
  pose proof (Hde dc Hdc) as Hdeb.
  assert (Hin' : fr_in C pos inp) by (unfold fr_in; auto).
  assert (Hbuf : fr_buf C pos inp m) by (unfold fr_buf; auto).
  unfold c_DISTEXT. cbv zeta. rewrite Hex.
  destruct (Znth dc dist_extra =? 0) eqn:E0; cbn [negb].
  - (* no extra bits: the distance is dist_base[dc] *)
    apply Z.eqb_eq in E0. rewrite E0 in Hdx. change (2 ^ 0) with 1 in Hdx.
    assert (dx = 0) by lia. subst dx.
    apply (fr_tail_match C pos inp ob L z flush (set_mode m MATCH)); [exact Hctx| |reflexivity].
    constructor; [|exact Hlv|exact Hret].
    apply (frM_mk _ _ _ _ _ _ m); try reflexivity; try exact HM; try exact Hnx.
    + unfold fr_wsame. unfold set_mode, upd_s. fr_simpl. repeat split.
    + unfold set_mode, upd_s. fr_simpl. rewrite Ho.
      apply (fr_at_mk_match C _ _ _ _ lc lx dc 0); fr_close.
  - (* NEEDBITS(extra) *)
    apply Z.eqb_neq in E0.
    set (ex := Znth dc dist_extra) in *.
    pose proof (fb_need FB C pos inp m ex dx Hin' Hbuf Hlv) as N; cbv zeta in N.
    destruct N as (nx & h & b & Heq & Hnx' & Hh' & Hq' & Hcase).
    { lia. }
    { lia. }
    { lia. }
    { rewrite Hq. lia. }
    { rewrite Hq. rewrite <- Hend. exact Hsub. }
    destruct Hcase as [(Hl1 & Hnxi & Hbn)|(Hl0 & Hbn & Hv)].
    + (* the input ends *)
      rewrite Hl1. cbn [Z.eqb Pos.eqb]. rewrite Heq, Hl1. right.
      apply frE_input; unfold m_mode; fr_simpl; try reflexivity.
      * fr_mkM m.
        rewrite Ho. apply (fr_at_mk_distext C _ _ _ _ lc lx dc dx); fr_close.
      * unfold m_mode in Hmd. rewrite Hmd. unfold DISTEXT, BAD. lia.
      * exact Hret.
      * lia.
    + (* the distance: dist_base[dc] + dx *)
      rewrite Hl0. cbn [Z.eqb Pos.eqb]. rewrite Heq, Hl0.
      apply (fr_tail_match C pos inp ob L z flush); [exact Hctx| |reflexivity].
      constructor; unfold set_mode, upd_s, bitsn; fr_simpl; [|first [reflexivity|congruence]|first [reflexivity|congruence]].
      fr_mkM m.
      * rewrite Ho. apply (fr_at_mk_match C _ _ _ _ lc lx dc dx); fr_close.
        -- rewrite u32_small by lia. apply (dk_drop dkit); [exact Hh'|lia].
        -- fr_simpl. rewrite Hv, Hoff. apply u32_small.
           assert (1 <= Znth dc dist_base <= 24577).
           { destruct (FL C Hok) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X).
             apply (X dc Hdc). }
           assert (2 ^ ex <= 8192) by (change 8192 with (2 ^ 13); apply Z.pow_le_mono_r; lia).
           pose proof (Z.mod_pos_bound h (2 ^ ex) ltac:(lia)). rep_lia.
Qed.

(* DIST: the distance code (fixed, 5 bits): invalid (30, 31) -> BAD, or dc -> DISTEXT *)
Lemma fr_tail_dist : fr_layout_stmt -> fr_bits_stmt ->
  fr_pass (fun md => md = DIST) (fun _ m => c_DIST lenfix_list distfix_list m).
Proof.
  intros FL FB C pos inp ob L z flush m Hctx [HM Hlv Hret] Hmd.
  pose proof HM as [Hinp Hin Haout Hout Hnx How Hwin Hwh Hat].
  destruct (fr_at_dist _ _ _ _ _ _ Hmd Hat) as (Hh & Hfx & Hb & Ho & T).
  pose proof Hctx as (Hok & Hp & Hpl & Hinpeq & Hmax & Hlive & Hzf).
  destruct (fr_tail_layout C FL Hok) as (Hte & Hlay & Hdl & Hd5 & Hle & Hde).
  assert (Hin' : fr_in C pos inp) by (unfold fr_in; destruct Hok; auto).
  assert (Hbuf : fr_buf C pos inp m) by (unfold fr_buf; auto).
  set (q := 8 * (pos + m_nx m) - m_bits m) in *.
  (* the distance code: 30 + w (TDCode) or dc (TFar) *)
  assert (Hcode : exists sy, 0 <= sy < 32 /\ q + 5 <= fr_end C /\
     sublist q (q + 5) (bytes_bits (fr_src C)) = send_sym fixed_dl sy /\
     ((exists w, fr_tail C = TDCode w /\ sy = 30 + w /\ q = fr_tpos C + Znth 257 fixed_ll) \/
      (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ sy = dc /\
         q = fr_tpos C + Znth lc fixed_ll + Znth (lc - 257) len_extra))).
  { pose proof Hok as (_ & _ & _ & Htl & _).
    destruct T as [(w & Ht & Hq)|(lc & lx & dc & dx & Ht & Hq)];
      rewrite Ht in Hlay, Htl; cbv zeta in Hlay; unfold tail_ok in Htl.
    - destruct Hlay as (Hend & Hsub). exists (30 + w).
      assert (Znth (30 + w) fixed_dl = 5) as H5 by (apply Hd5; lia). rewrite H5 in *.
      split; [lia|]. split; [lia|]. split; [rewrite Hq, <- Hend; exact Hsub|]. left. eauto.
    - destruct Hlay as (Hend & _ & Hsub & _). exists dc.
      assert (Znth dc fixed_dl = 5) as H5 by (apply Hd5; lia). rewrite H5 in *.
      pose proof (Hde dc ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [rewrite Hq; exact Hsub|]. right. eauto 10. }
  clear T. destruct Hcode as (sy & Hsy & Hqe & Hs & Hsyc).
  assert (Hsy5 : Znth sy fixed_dl = 5) by (apply Hd5; lia).
  pose proof Hfx as (_ & _ & Hdcd & Hdb).
  pose proof (fb_lookup FB C pos inp m TDistfix 5 DISTS fixed_dl sy Hin' Hbuf) as LK.
  cbv zeta in LK. fold q in LK. rewrite Hsy5 in LK.
  specialize (LK ltac:(right; auto) ltac:(lia) ltac:(lia) ltac:(lia) Hs).
  unfold c_DIST. cbv zeta. rewrite Hdcd, Hdb.
  destruct (lookup1 lenfix_list distfix_list TDistfix 5 m) as [[here m'] ok].
  destruct LK as (nx & h & b & lv & -> & Hnx' & Hh' & Hq' & Hok1 & Hok0).
  destruct ok.
  - (* the code is read *)
    destruct (Hok1 eq_refl) as (Hlv' & Heb & Hb5 & Hms). clear Hok1 Hok0.
    rewrite Heb.
    destruct Hsyc as [(w & Ht & -> & Hq)|(lc & lx & dc & dx & Ht & -> & Hq)].
    + (* 30, 31: invalid *)
      pose proof (fb_ms_bad FB DISTS (30 + w) (e_op here) (e_val here)) as Hbad.
      destruct (op_invalid (e_op here)) as [H240 H64].
      { apply Hbad; [right; split; [reflexivity|] | exact Hms].
        pose proof Hok as (_ & _ & _ & Htl & _). rewrite Ht in Htl. unfold tail_ok in Htl. lia. }
      rewrite (proj2 (Z.eqb_neq _ _) H240). cbn [negb].
      rewrite (proj2 (Z.eqb_neq _ _) H64). cbn [negb].
      left. constructor; unfold set_bad, set_mode, upd_s; fr_simpl; [|first [reflexivity|congruence]|first [reflexivity|congruence]].
      fr_mkM m.
      * apply fr_at_bad; [reflexivity|]. rewrite Ho. unfold fr_n. lia.
    + (* dc: its base and extra bits *)
      pose proof Hok as (_ & _ & _ & Htl & _). rewrite Ht in Htl. unfold tail_ok in Htl.
      destruct (fb_ms_dist FB dc (e_op here) (e_val here) ltac:(lia) Hms) as [Hop Hval].
      destruct (op_base (Znth dc dist_extra)) as (H240 & H64 & H15); [apply Hde; lia|].
      rewrite Hop, H240. cbn [negb Z.eqb]. rewrite Hop, H64. cbn [negb Z.eqb].
      apply (fr_tail_distext FL FB C pos inp ob L z flush); [exact Hctx| |reflexivity].
      constructor; unfold set_mode, upd_s; fr_simpl; [|first [reflexivity|congruence]|first [reflexivity|congruence]].
      fr_mkM m.
      rewrite Ho, Heb, (u32_small (b - 5)) by lia.
      apply (fr_at_mk_distext C _ _ _ _ lc lx dc dx); fr_close.
      all: fr_simpl; first [apply (dk_drop dkit); [exact Hh'|lia] | exact Hval | rewrite Hop; exact H15].
  - (* the input ends inside the code *)
    destruct (Hok0 eq_refl) as (-> & Hnxi & Hb5). clear Hok1 Hok0.
    cbn [negb]. right.
    apply frE_input; unfold m_mode; fr_simpl; try reflexivity.
    + fr_mkM m.
      rewrite Ho. apply fr_at_mk_dist; fr_close.
      rewrite Hq'. destruct Hsyc as [(w & Ht & _ & Hq)|(lc & lx & dc & dx & Ht & _ & Hq)].
      * left. exists w. auto.
      * right. exists lc, lx, dc, dx. auto.
    + unfold m_mode in *. rewrite Hmd. unfold DIST, BAD. lia.
    + exact Hret.
    + lia.
Qed.

(* LENEXT: the length's extra bits (none for TDCode's 257), or the input ends; then DIST *)
Lemma fr_tail_lenext : fr_layout_stmt -> fr_bits_stmt ->
  fr_pass (fun md => md = LENEXT) (fun _ m => c_LENEXT lenfix_list distfix_list m).
Proof.
  intros FL FB C pos inp ob L z flush m Hctx [HM Hlv Hret] Hmd.
  pose proof HM as [Hinp Hin Haout Hout Hnx How Hwin Hwh Hat].
  destruct (fr_at_lenext _ _ _ _ _ _ Hmd Hat) as (Hh & Hfx & Hb & Ho & T).
  pose proof Hctx as (Hok & Hp & Hpl & Hinpeq & Hmax & Hlive & Hzf).
  destruct (fr_tail_layout C FL Hok) as (Hte & Hlay & Hdl & Hd5 & Hle & Hde).
  assert (Hin' : fr_in C pos inp) by (unfold fr_in; destruct Hok; auto).
  assert (Hbuf : fr_buf C pos inp m) by (unfold fr_buf; auto).
  unfold c_LENEXT. cbv zeta.
  destruct T as [(w & Ht & Hq & Hex)|(lc & lx & dc & dx & Ht & Hq & Hex)].
  - (* TDCode: 257, no extra bits *)
    rewrite Hex. cbn [Z.eqb negb].
    apply (fr_tail_dist FL FB C pos inp ob L z flush); [exact Hctx| |reflexivity].
    constructor; [|exact Hlv|exact Hret].
    fr_mkM m. rewrite Ho. apply fr_at_mk_dist; fr_close.
    left. exists w. split; [exact Ht|]. exact Hq.
  - pose proof Hok as (_ & _ & _ & Htl & _). rewrite Ht in Htl. unfold tail_ok in Htl.
    destruct Htl as (Hlc & Hlx & Hdc & Hdx & Hfar).
    rewrite Ht in Hlay. cbv zeta in Hlay. destruct Hlay as (Hend & Hsub & _).
    assert (H5 : Znth dc fixed_dl = 5) by (apply Hd5; lia). rewrite H5 in *.
    pose proof (Hle (lc - 257) ltac:(lia)) as Hleb. pose proof (Hde dc Hdc) as Hdeb.
    rewrite Hex. set (ex := Znth (lc - 257) len_extra) in *.
    destruct (ex =? 0) eqn:E0; cbn [negb].
    + (* no extra bits *)
      apply Z.eqb_eq in E0.
      apply (fr_tail_dist FL FB C pos inp ob L z flush); [exact Hctx| |reflexivity].
      constructor; [|exact Hlv|exact Hret].
      fr_mkM m. rewrite Ho. apply fr_at_mk_dist; fr_close.
      right. exists lc, lx, dc, dx. split; [exact Ht|]. lia.
    + (* NEEDBITS(extra) *)
      apply Z.eqb_neq in E0.
      pose proof (fb_need FB C pos inp m ex lx Hin' Hbuf Hlv) as N; cbv zeta in N.
      destruct N as (nx & h & b & Heq & Hnx' & Hh' & Hq' & Hcase).
      { lia. }
      { lia. }
      { lia. }
      { rewrite Hq. lia. }
      { rewrite Hq. exact Hsub. }
      destruct Hcase as [(Hl1 & Hnxi & Hbn)|(Hl0 & Hbn & Hv)].
      * (* the input ends *)
        rewrite Hl1. cbn [Z.eqb Pos.eqb]. rewrite Heq, Hl1. right.
        apply frE_input; unfold m_mode; fr_simpl; try reflexivity.
        -- fr_mkM m. rewrite Ho. apply (fr_at_mk_lenext C _ _ _ _ lc lx dc dx); fr_close.
        -- unfold m_mode in *. rewrite Hmd. unfold LENEXT, BAD. lia.
        -- exact Hret.
        -- lia.
      * (* the length's extra bits: to DIST *)
        rewrite Hl0. cbn [Z.eqb Pos.eqb]. rewrite Heq, Hl0.
        apply (fr_tail_dist FL FB C pos inp ob L z flush); [exact Hctx| |reflexivity].
        constructor; unfold set_mode, upd_s; fr_simpl;
          [|first [reflexivity|congruence]|first [reflexivity|congruence]].
        fr_mkM m. rewrite Ho, (u32_small (b - ex)) by lia.
        apply fr_at_mk_dist; fr_close.
        -- apply (dk_drop dkit); [exact Hh'|lia].
        -- right. exists lc, lx, dc, dx. split; [exact Ht|]. lia.
Qed.

Lemma fr_tail_ok : fr_layout_stmt -> fr_bits_stmt -> fr_tail_stmt.
Proof.
  intros FL FB. split; [|split; [|split; [|split]]].
  - exact (fr_tail_lenext FL FB).
  - exact (fr_tail_dist FL FB).
  - exact (fr_tail_distext FL FB).
  - exact fr_tail_match.
  - exact fr_tail_bad.
Qed.

(* RT-D FLUSH part DYN2: proof of [dyn2_facts_stmt] from FlushDyn.dyn_prep / DynSum / BtSpec. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDyn2Defs.
Require Zlib.proof.huffman.FlushDyn Zlib.proof.huffman.DynSum Zlib.proof.huffman.TreeDD Zlib.proof.huffman.RepairBound Zlib.proof.huffman.OverlayDyn Zlib.proof.huffman.FlushStream Zlib.proof.huffman.BtSpec.
Import ListNotations.
Local Open Scope Z_scope.

Module BF := Zlib.proof.huffman.BlockFacts.
Module CT := Zlib.proof.huffman.Cert.
Module FT := Zlib.proof.huffman.FlushTree.
Module FS := Zlib.proof.huffman.FlushStream.
Module FD := Zlib.proof.huffman.FlushDyn.
Module DS := Zlib.proof.huffman.DynSum.
Module BS := Zlib.proof.huffman.BtSpec.
Module Hd := Zlib.proof.huffman.Header.
Module BP := Zlib.proof.huffman.BuildPre.
Module HA := Zlib.proof.huffman.HuffAbs.
Module OD := Zlib.proof.huffman.OverlayDyn.

(** Format's Kraft sum of a prefix as a [zsum]. *)
Lemma d2f_ks_acc : forall l a,
  fold_right (fun l k => if l =? 0 then k else k + 2 ^ (F.MAXLEN - l)) a l = F.kraft_sum l + a.
Proof.
  intros l a. unfold F.kraft_sum. induction l as [|x l IH]; cbn [fold_right]; [lia|].
  rewrite IH. destruct (x =? 0); lia.
Qed.

Lemma d2f_ks_snoc : forall l x,
  F.kraft_sum (l ++ [x]) = F.kraft_sum l + (if x =? 0 then 0 else 2 ^ (15 - x)).
Proof.
  intros l x. unfold F.kraft_sum at 1. rewrite fold_right_app. cbn [fold_right]. rewrite d2f_ks_acc.
  unfold F.MAXLEN. destruct (x =? 0); lia.
Qed.

Lemma d2f_kraft_zsum : forall n l, 0 <= n <= Zlength l ->
  F.kraft_sum (sublist 0 n l) = BF.zsum n (fun c => if Znth c l =? 0 then 0 else 2 ^ (15 - Znth c l)).
Proof.
  intros n l Hn. rewrite <- (Z2Nat.id n) in * by lia. induction (Z.to_nat n) as [|k IH].
  - rewrite sublist_nil. reflexivity.
  - rewrite (sublist_split 0 (Z.of_nat k) (Z.of_nat (S k))) by lia.
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. rewrite (sublist_len_1 (Z.of_nat k)) by lia. rewrite d2f_ks_snoc, IH by lia.
    rewrite !CT.zsum_rs. replace (Z.to_nat (Z.of_nat k + 1)) with (S k) by lia.
    rewrite CT.rs_snoc, Nat2Z.id. reflexivity.
Qed.

(** Kraft equality of a tree built by build_tree, over any prefix past its max code. *)
Lemma d2f_bt_kraft : forall sd t w S F order R t' mc w' n, BS.bt_facts sd t w S F order R t' mc w' ->
  sd_maxlen sd <= 15 -> mc < n <= sd_elems sd ->
  BF.zsum n (fun c => if Znth c (dl t') =? 0 then 0 else 2 ^ (15 - Znth c (dl t'))) = 2 ^ 15.
Proof.
  intros sd t w S F order R t' mc w' n B Hm Hn.
  destruct (BS.bt_S _ _ _ _ _ _ _ _ _ _ B) as [_ [ND [Hr _]]].
  pose proof (BS.bt_len_out _ _ _ _ _ _ _ _ _ _ B) as Hout.
  pose proof (BS.bt_len_in _ _ _ _ _ _ _ _ _ _ B) as Hin.
  destruct (BS.bt_mc _ _ _ _ _ _ _ _ _ _ B) as [Hmc Hmc2].
  assert (HM := Hin mc Hmc).
  unfold BF.zsum. rewrite (FT.zseq_sum_support S); auto.
  - rewrite (FT.sumZ_map_ext' _ (fun x => 2 ^ (15 - sd_maxlen sd) * 2 ^ (sd_maxlen sd - Znth x (dl t')))).
    + rewrite FT.sumZ_map_scal', (BS.bt_kraft _ _ _ _ _ _ _ _ _ _ B), <- Z.pow_add_r by lia. f_equal. lia.
    + intros x i. specialize (Hin x i). destruct (Z.eqb_spec (Znth x (dl t')) 0); [lia|].
      rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - intros x i. specialize (Hmc2 x i). specialize (Hr x i). lia.
  - intros x Hx i. rewrite (Hout x ltac:(lia) i). reflexivity.
Qed.

(** The bit length orders above max_blindex have length 0. *)
Lemma d2f_fmb_zero : forall fuel bl i r, find_max_blindex fuel bl i < r <= i ->
  Znth (Znth r bl_order) (dl bl) = 0.
Proof.
  induction fuel as [|fuel IH]; intros bl i r Hr; cbn [find_max_blindex] in Hr; [lia|].
  destruct (i >=? 3); [|lia].
  destruct (negb (Znth (Znth i bl_order) (dl bl) =? 0)) eqn:E; [lia|].
  destruct (Z.eq_dec r i) as [->|Hne].
  - apply negb_false_iff, Z.eqb_eq in E. exact E.
  - apply (IH bl (i - 1)). lia.
Qed.

Theorem dyn2_facts : dyn2_facts_stmt.
Proof.
  intros t syms sl s' olb slb mbi Hpre Hlev Hfp.
  assert (P := FD.dyn_prep t syms sl Hpre Hlev). rewrite Hfp in P.
  destruct P as [Sl [Fl [ordl [Rl [lt0 [wl [Sd [Fd [ordd [Rd [dt0 [wd [blt [Sb [Fb [ordb [Rb [wb
                 [BL [BD [BB [ELt [EDt [Eblt [Hfcb [Hfcr [Hcnt [Embi _]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  destruct (DS.dyn_sum_holds FD.dyn_prep (Zlib.proof.huffman.TreeDD.tree_dd Zlib.proof.huffman.RepairBound.repair15_bound)
              t syms sl Hpre Hlev) as [s'0 [olb0 [slb0 [mbi0 [ll [dl0 [dd [dd0 [Hh [E D]]]]]]]]]].
  pose proof (DS.ds_prep _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hp0. rewrite Hfp in Hp0.
  injection Hp0 as <- <- <- <-.
  destruct (DS.ds_lists _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Lll [Ldl0 _]].
  destruct (DS.ds_guard _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Gl Gd].
  destruct (DS.ds_lmax _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hlm Hlnz].
  destruct (DS.ds_dmax _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hdm Hdnz].
  pose proof (DS.ds_llen _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hll.
  pose proof (DS.ds_dlen _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hdl.
  destruct (DS.ds_codes _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Cl Cd].
  destruct (DS.ds_kraft _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Kl _].
  destruct (fp_syms _ _ Hpre) as [_ [_ [Hval _]]].
  destruct (fp_bltree _ _ Hpre) as [Hb1 [Hb2 _]].
  unfold END_BLOCK, L_CODES, D_CODES in *.
  set (lmax := tr_lmax s') in *. set (dmax := tr_dmax s') in *.
  set (LT := dl (tr_ltree s')) in *. set (DT := dl (tr_dtree s')) in *.
  set (BLT := tr_bltree s') in *.
  assert (LLT : Zlength LT = HEAP_SIZE) by (rewrite Gl, upd_Znth_Zlength; unfold HEAP_SIZE in *; lia).
  assert (LDT : Zlength DT = 2 * 30 + 1) by (rewrite Gd, upd_Znth_Zlength; lia).
  assert (ELl : forall i, 0 <= i <= lmax -> Znth i LT = Znth i ll)
    by (intros i Hi; rewrite Gl, Hd.Znth_upd_other by lia; reflexivity).
  assert (EDl : forall i, 0 <= i <= dmax -> Znth i DT = Znth i dl0)
    by (intros i Hi; rewrite Gd, Hd.Znth_upd_other by lia; reflexivity).
  assert (GL : Znth (lmax + 1) LT = 65535)
    by (rewrite Gl, upd_Znth_same by (unfold HEAP_SIZE in *; lia); reflexivity).
  assert (GD : Znth (dmax + 1) DT = 65535) by (rewrite Gd, upd_Znth_same by lia; reflexivity).
  assert (RL : forall i, 0 <= i <= lmax -> 0 <= Znth i LT <= 15)
    by (intros i Hi; rewrite ELl by lia; apply Hll; lia).
  assert (RD : forall i, 0 <= i <= dmax -> 0 <= Znth i DT <= 15)
    by (intros i Hi; rewrite EDl by lia; apply Hdl; lia).
  destruct (BS.bt_sizes _ _ _ _ _ _ _ _ _ _ BB) as [SB1 [SB2 _]].
  destruct (FD.bt_lens _ _ _ _ _ _ _ _ _ _ BB ltac:(cbn; unfold MAX_BL_BITS; lia)) as [HBm _].
  cbn [sd_elems static_bl_desc] in HBm. unfold BL_CODES in *.
  assert (RB : forall i, 0 <= i < 19 -> 0 <= Znth i (dl BLT) <= 7).
  { intros i Hi. destruct (in_dec Z.eq_dec i Sb) as [Hin|Hin].
    - pose proof (BS.bt_len_in _ _ _ _ _ _ _ _ _ _ BB i Hin) as A. cbn in A. unfold MAX_BL_BITS in A. lia.
    - rewrite (BS.bt_len_out _ _ _ _ _ _ _ _ _ _ BB i ltac:(cbn; unfold BL_CODES; lia) Hin). lia. }
  assert (HQ : forall q, In q (Header.tree_syms LT lmax ++ Header.tree_syms DT dmax) ->
                 0 <= fst q < 19 /\ code_ok (fc BLT) (dl BLT) (fst q)).
  { intros q Hq.
    assert (Hok : Hd.syms_ok (Header.tree_syms LT lmax ++ Header.tree_syms DT dmax))
      by (apply Hd.syms_ok_app; apply Hd.tree_syms_ok; auto; lia).
    destruct (Hok q Hq) as [Hq1 _]. split; [exact Hq1|].
    apply (BS.bt_codes _ _ _ _ _ _ _ _ _ _ BB).
    destruct (BS.bt_S _ _ _ _ _ _ _ _ _ _ BB) as [ES _]. rewrite ES. apply in_or_app. left.
    apply BP.in_nzl. cbn [sd_elems static_bl_desc]. unfold BL_CODES. split; [lia|].
    rewrite Hcnt by (unfold BL_CODES; lia).
    pose proof (Hd.cnt_nonneg (fst q) (Header.tree_syms LT lmax)).
    pose proof (Hd.cnt_nonneg (fst q) (Header.tree_syms DT dmax)).
    apply in_app_or in Hq. destruct Hq as [Hq|Hq]; apply DS.hdr_cnt_in in Hq; lia. }
  assert (HM : 3 <= mbi <= 18).
  { rewrite Embi. unfold BL_CODES. apply FS.fmb_spec; [lia|cbn; lia|].
    destruct (FS.tree_syms_has_length LT lmax ltac:(lia) RL ltac:(rewrite ELl by lia; exact Hlnz) GL)
      as [v [Hv Hin]].
    destruct (FS.bl_order_small v ltac:(lia)) as [r [Hr Er]]. exists r. split; [lia|]. rewrite Er.
    destruct (HQ (v, 0) ltac:(apply in_or_app; left; exact Hin)) as [_ [A _]]. cbn [fst] in A. lia. }
  split; [lia|]. split; [split; [exact LLT|split; [exact LDT|rewrite SB1, SB2, Eblt, Hfcb, Hb2; lia]]|].
  split; [split; [exact GL|exact GD]|]. split; [exact RL|]. split; [exact RD|].
  split.
  { intros x Hx. destruct (FS.lcode_range x (Hval x Hx)) as [A _]. unfold L_CODES in A.
    pose proof (OD.lfreq_in syms x Hx) as Fp. destruct (Hll (lcode_of x) ltac:(lia)) as [_ [B1 [B2 _]]].
    specialize (B2 Fp). split; [|apply Cl; auto; lia].
    destruct (Z_le_gt_dec (lcode_of x) lmax); [auto|]. exfalso. apply B2, B1. lia. }
  split.
  { intros x Hx Hnz. pose proof (FS.dcode_range x (Hval x Hx) Hnz) as A. unfold FS.dcode_of, D_CODES in A.
    pose proof (OD.dfreq_in syms x Hx Hnz) as Fp. destruct (Hdl (d_code (fst x - 1)) ltac:(lia)) as [_ [B1 B2]].
    specialize (B2 Fp). split; [|apply Cd; auto; lia].
    destruct (Z_le_gt_dec (d_code (fst x - 1)) dmax); [auto|]. exfalso. apply B2, B1. lia. }
  split.
  { pose proof (OD.lfreq_end syms) as Fp. unfold END_BLOCK in Fp.
    destruct (Hll 256 ltac:(lia)) as [_ [_ [B2 _]]]. apply Cl; [lia|]. apply B2. lia. }
  split.
  { rewrite d2f_kraft_zsum by (rewrite LLT; unfold HEAP_SIZE; lia).
    rewrite <- (d2f_bt_kraft _ _ _ _ _ _ _ _ _ _ (lmax + 1) BL) by (cbn; unfold MAX_BITS, L_CODES; lia).
    apply OD.zsum_ext'. intros c Hc. unfold LT. rewrite ELt. cbn [dl set_dl].
    rewrite Hd.Znth_upd_other by lia. reflexivity. }
  split.
  { rewrite d2f_kraft_zsum by (rewrite LDT; lia).
    rewrite <- (d2f_bt_kraft _ _ _ _ _ _ _ _ _ _ (dmax + 1) BD) by (cbn; unfold MAX_BITS, D_CODES; lia).
    apply OD.zsum_ext'. intros c Hc. unfold DT. rewrite EDt. cbn [dl set_dl].
    rewrite Hd.Znth_upd_other by lia. reflexivity. }
  split; [exact RB|].
  split.
  { rewrite d2f_kraft_zsum by (rewrite SB2, Eblt, Hb2; unfold BL_CODES; lia).
    apply (d2f_bt_kraft _ _ _ _ _ _ _ _ _ _ 19 BB); cbn; unfold MAX_BL_BITS, BL_CODES; lia. }
  split; [exact HQ|]. split; [exact HM|].
  intros r Hr. rewrite Embi in Hr. apply (d2f_fmb_zero 20 BLT (BL_CODES - 1)). unfold BL_CODES in *. lia.
Qed.

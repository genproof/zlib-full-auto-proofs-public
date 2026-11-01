(* RT-I, part rti_zdict: small facts for the assembly (ports of harness/inflate_dict ITDict,
   ITD1, ITPost, ITPre lemmas). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtzk_uw_keep: forall s d,
  let s' := updatewindow s d in
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_havedict s' = i_havedict s /\
  i_flags s' = i_flags s /\ i_check s' = i_check s /\ i_total s' = i_total s /\ i_head s' = i_head s /\
  i_wbits s' = i_wbits s /\ i_hold s' = i_hold s /\ i_bits s' = i_bits s /\ i_win s' = i_win s.
Proof.
  intros s d. unfold updatewindow. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; simpl; auto 20.
Qed.

Lemma rtzk_live: forall L, live_ok L -> i_mode (l_s L) = DICT -> live_ok (set_l_s L (d1_ty (l_s L))).
Proof.
  intros L [P [S [MW [HW [S3 [WS [W0 [HD WH]]]]]]]] MD.
  assert (Wne: i_wbits (l_s L) <> 0).
  { intro E. destruct (W0 E) as [W1 _]. destruct (WH E (land3_wrap _ W1)) as [_ M].
    rewrite MD in M. unfold DICT, HEAD, BAD, SYNC, MEM in M. lia. }
  unfold live_ok; cbn [l_sp l_s l_h l_hsh l_xb l_nb l_cb set_l_s].
  unfold d1_ty.
  split; [exact P|]. split.
  { destruct S; constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits
      i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
      i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was set_i_mode set_i_check];
    auto; unfold Zlib.proof.inflate.Model.TYPE, HEAD, SYNC, lrange; rep_lia. }
  split.
  { constructor; cbn [i_mode set_i_mode set_i_check]; unfold decode_mode;
      unfold Zlib.proof.inflate.Model.TYPE, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST, LEN_, LEN, LIT;
      intros; lia. }
  split; [exact HW|]. split.
  { constructor; cbn [i_mode set_i_mode set_i_check]; unfold decode_mode;
      unfold Zlib.proof.inflate.Model.TYPE, HEAD, LENEXT, DISTEXT, LEN_, LEN, DIST, MATCH, LIT; intros; lia. }
  split; [exact WS|].
  cbn [i_wbits i_wrap i_win i_head i_flags i_mode set_i_mode set_i_check].
  split; [intro E; contradiction|]. split; [exact HD|]. intros E; contradiction.
Qed.

Lemma rtzk_fold_ext {A: Type} (f: list Z -> A -> list Z) :
  (forall out a, exists d, f out a = out ++ d) ->
  forall l out, exists d, fold_left f l out = out ++ d.
Proof.
  intros F l; induction l as [|a l IH]; intros out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (F out a) as [d1 E1]; rewrite E1. destruct (IH (out ++ d1)) as [d2 E2].
    exists (d1 ++ d2); rewrite E2, app_assoc; auto.
Qed.

Lemma rtzk_lz_ext : forall n dist out, exists d, lz_copy n dist out = out ++ d.
Proof.
  induction n as [|n IH]; intros dist out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (IH dist (out ++ [Znth (Zlength out - dist) out])) as [d E]; rewrite E.
    exists ([Znth (Zlength out - dist) out] ++ d); rewrite app_assoc; auto.
Qed.

Lemma rtzk_block_ext : forall out b, exists d, block_data out b = out ++ d.
Proof.
  assert (S: forall out syms, exists d, syms_data out syms = out ++ d).
  { intros out syms; unfold syms_data; apply rtzk_fold_ext.
    intros o [b|len dist]; simpl; [exists [b]; auto | apply rtzk_lz_ext]. }
  intros out [bytes|syms|nlen ndist cl toks syms]; simpl; [exists bytes; auto|apply S|apply S].
Qed.

Lemma rtzk_expand_data : forall hist bs, expand hist bs = hist ++ data hist bs.
Proof.
  intros hist bs. unfold data. destruct (rtzk_fold_ext block_data rtzk_block_ext bs hist) as [d E].
  unfold expand; rewrite E. f_equal. rewrite Zlength_app. rewrite sublist_app2 by list_solve.
  rewrite Z.sub_diag. replace (Zlength hist + Zlength d - Zlength hist) with (Zlength d) by lia.
  rewrite sublist_same by lia; auto.
Qed.

Lemma rtzk_bval l : 0 <= bval l < 2 ^ Z.of_nat (length l).
Proof.
  induction l as [|b l IH]; cbn [bval length]; [cbn; lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma rtzk_pack bs : bytes_ok (pack bs).
Proof.
  unfold bytes_ok, pack. rewrite Forall_map, Forall_forall. intros k _.
  pose proof (rtzk_bval (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) as B.
  assert (Lk : (length (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs) <= 8)%nat).
  { unfold sublist. rewrite skipn_length, firstn_length. lia. }
  assert (2 ^ Z.of_nat (length (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) <= 2 ^ 8)
    by (apply Z.pow_le_mono_r; lia).
  change Byte.max_unsigned with 255. change (2 ^ 8) with 256 in *. unfold Basics.compose. lia.
Qed.

Lemma rtzk_be_bytes v n : bytes_ok (be_bytes v n).
Proof.
  unfold bytes_ok, be_bytes, le_bytes. apply Forall_rev. rewrite Forall_map, Forall_forall. intros i _.
  change Byte.max_unsigned with 255. pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256). unfold Basics.compose. lia.
Qed.

Lemma rtzk_hdr wb : 8 <= wb <= 15 -> bytes_ok (zlib_hdr wb 0 true).
Proof.
  intros Hw.
  assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) as Ew by lia.
  destruct Ew as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; unfold bytes_ok; vm_compute;
    repeat constructor; discriminate.
Qed.

Lemma rtzk_len_hdr wb f d : Zlength (zlib_hdr wb f d) = 2.
Proof. unfold zlib_hdr. cbv zeta. rewrite !Zlength_cons, Zlength_nil. reflexivity. Qed.

Lemma rtzk_adler_range d : 0 <= Zlib.proof.adler32.Model.ref_adler32 1 d < 2 ^ 32.
Proof.
  assert (V : Zlib.proof.adler32.Model.adler_valid 1) by (vm_compute; repeat split; congruence).
  destruct (Zlib.proof.adler32.Model.ref_adler32_valid 1 d V) as [R _]. exact R.
Qed.

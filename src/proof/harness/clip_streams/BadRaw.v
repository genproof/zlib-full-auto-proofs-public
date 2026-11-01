(* Law rj_bad_checksum: the raw deflate stream of the blocks (BadKit.rawctx) is a context of the decode theory,
   and its places: at the start of the first block (TYPE right after the header of the true stream) and at the
   end of the stream (CHECK, where the trailer of the true stream starts). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The layout of the true stream                                                                  *)

(* the padding to a byte boundary *)
Lemma br_pad8 p : (p + pad8 p) mod 8 = 0 /\ 0 <= pad8 p < 8.
Proof. unfold pad8. Z.div_mod_to_equations. lia. Qed.

Lemma br_pack_len bs : Zlength (pack bs) = (Zlength bs + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, length_seq.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg bs); lia | lia].
Qed.

(* the deflate stream is padded to whole bytes *)
Lemma br_bits_len bs : Zlength (deflate_bits bs) = 8 * Zlength (deflate_bytes bs).
Proof.
  unfold deflate_bytes. rewrite br_pack_len. unfold deflate_bits.
  rewrite Zlength_app. unfold zeros. rewrite Zlength_repeat' by (pose proof (br_pad8 (Zlength (enc_blocks 0 bs))); lia).
  set (e := Zlength (enc_blocks 0 bs)). destruct (br_pad8 e) as [M R].
  rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
Qed.

(* a non-empty list of blocks has a non-empty deflate stream (each block starts with its BFINAL bit) *)
Lemma br_deflate_len bs : bs <> [] -> 1 <= Zlength (deflate_bytes bs).
Proof.
  intros NE. pose proof (br_bits_len bs) as L. unfold deflate_bits in L.
  destruct bs as [|b r]; [congruence|]. cbn [enc_blocks] in L.
  rewrite !Zlength_app in L. unfold enc_block at 1 in L. rewrite Zlength_cons in L.
  match type of L with context [Z.succ (Zlength ?a) + Zlength ?b + Zlength ?c] =>
    pose proof (Zlength_nonneg a); pose proof (Zlength_nonneg b); pose proof (Zlength_nonneg c) end.
  lia.
Qed.

(* every block has at least one bit: k blocks in, the position moved by at least k *)
Lemma br_epos_ge : forall k bs p, (k <= length bs)%nat -> p + Z.of_nat k <= epos p bs k.
Proof.
  induction k as [|k IH]; intros bs p Hk; [destruct bs; cbn; lia|].
  destruct bs as [|b r]; [cbn in Hk; lia|]. cbn [epos length] in *.
  specialize (IH r (p + Zlength (enc_block p false b)) ltac:(lia)).
  assert (1 <= Zlength (enc_block p false b)).
  { unfold enc_block. rewrite Zlength_cons.
    match goal with |- context [Z.succ (Zlength ?l)] => pose proof (Zlength_nonneg l) end. lia. }
  lia.
Qed.

(* the stream: header, deflate bytes, trailer *)
Lemma br_stream w h bs : exists T,
  stream_bytes w h bs = hdr_bytes w ++ deflate_bytes bs ++ T /\ Zlength T = trl_len w.
Proof.
  destruct w as [|wb fl [i|]|g]; cbn [stream_bytes hdr_bytes trl_len].
  - exists []. rewrite !app_nil_r. split; reflexivity.
  - eexists. rewrite <- !app_assoc. split; [reflexivity|]. reflexivity.
  - eexists. split; [reflexivity|]. reflexivity.
  - eexists. split; [reflexivity|]. reflexivity.
Qed.

(* the facts of the true stream used below *)
Lemma br_layout G : bad_ctx G ->
  8 <= dc_wb G <= 15 /\ dc_hist G = [] /\ wf (2 ^ dc_wb G) [] (dc_bs G) /\
  slen G = hlen G + Zlength (deflate_bytes (dc_bs G)) + trl_len (dc_w G) /\
  tpos G = hlen G + Zlength (deflate_bytes (dc_bs G)) /\ 0 <= hlen G < tpos G /\
  slen G <= Zlength (dc_src G) /\
  sublist (hlen G) (tpos G) (dc_src G) = deflate_bytes (dc_bs G).
Proof.
  intros ((SO & _ & _ & _ & SL & _ & _ & SUB) & HH & _ & _ & _).
  destruct SO as (WB & _ & _ & WF). rewrite HH in WF.
  destruct (br_stream (dc_w G) (dc_hist G) (dc_bs G)) as (T & ST & LT).
  assert (LS: slen G = hlen G + Zlength (deflate_bytes (dc_bs G)) + trl_len (dc_w G)).
  { unfold slen, hlen. rewrite ST, !Zlength_app. lia. }
  pose proof (br_deflate_len (dc_bs G) (proj1 WF)) as DL.
  assert (0 <= hlen G) by (unfold hlen; apply Zlength_nonneg).
  assert (0 <= trl_len (dc_w G)) by (destruct (dc_w G); cbn; lia).
  assert (TP: tpos G = hlen G + Zlength (deflate_bytes (dc_bs G))) by (unfold tpos; lia).
  do 7 (split; [first [exact WB | exact HH | exact WF | exact LS | exact TP | lia | exact SL] |]).
  replace (sublist (hlen G) (tpos G) (dc_src G)) with (sublist (hlen G) (tpos G) (sublist 0 (slen G) (dc_src G)))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite SUB, ST.
  rewrite sublist_app2 by (unfold hlen; split; [apply Zlength_nonneg | lia]).
  fold (hlen G). rewrite Z.sub_diag, TP.
  rewrite sublist_app1 by (try split; lia).
  apply sublist_same; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The raw stream                                                                                 *)

Lemma br_reset2_raw wb : 8 <= wb <= 15 -> reset2_wb (- wb) = Some (0, wb).
Proof.
  intros W. unfold reset2_wb.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite Z.opp_involutive. rewrite (proj2 (Z.leb_le 8 wb)) by lia. rewrite (proj2 (Z.leb_le wb 15)) by lia.
  reflexivity.
Qed.

Lemma bad_raw_ok G src : bad_ctx G -> bad_src G src ->
  dctx_ok7 (rawctx G src) /\ 0 <= hlen G < tpos G /\ slen (rawctx G src) = tpos G - hlen G /\
  full (rawctx G src) = full G /\ D0 G = 8 * hlen G /\ trl_len (dc_w G) <= 8.
Proof.
  intros HG (LS & BS & PRE & _).
  destruct (br_layout G HG) as (WB & HH & WF & SL & TP & HT & SLE & DF).
  assert (SR: slen (rawctx G src) = Zlength (deflate_bytes (dc_bs G))) by reflexivity.
  assert (Zlength (dc_src G) <= 2 ^ 64 - 1) by apply HG.
  assert (0 <= trl_len (dc_w G)) by (destruct (dc_w G); cbn; lia).
  split; [|split; [exact HT|]].
  { unfold dctx_ok7. rewrite SR. unfold rawctx; cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src].
    split; [unfold stream_ok; split; [lia|]; split; [exact I|]; split; [exact I|exact WF]|].
    split; [reflexivity|].
    split; [intros h E; discriminate|].
    split; [intros wb fl did E; discriminate|].
    rewrite Zlength_sublist by lia.
    split; [lia|]. split; [lia|]. split; [apply Forall_sublist; exact BS|].
    rewrite sublist_sublist by lia.
    replace (0 + hlen G) with (hlen G) by lia.
    replace (Zlength (deflate_bytes (dc_bs G)) + hlen G) with (tpos G) by lia.
    replace (sublist (hlen G) (tpos G) src) with (sublist (hlen G) (tpos G) (sublist 0 (tpos G) src))
      by (rewrite sublist_sublist by lia; f_equal; lia).
    rewrite PRE, sublist_sublist by lia. rewrite !Z.add_0_r. exact DF. }
  split; [rewrite SR; lia|].
  split; [unfold full, rawctx; cbn [dc_hist dc_bs]; rewrite HH; reflexivity|].
  split; [reflexivity|]. destruct (dc_w G); cbn; lia.
Qed.

(* right after the header (TYPE, or TYPEDO at the start of a call), at most the header consumed: nothing of the
   blocks read; the raw stream is at its start *)
Lemma bad_raw_type G src s c hold bits out cc : bad_ctx G -> bad_src G src ->
  at_mode G s c hold bits out -> (i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO) ->
  c <= hlen G ->
  c = hlen G /\ bits = 0 /\ hold = 0 /\ out = [] /\
  at_mode (rawctx G src) (set_i_check (set_i_wrap s 0) cc) 0 0 0 [].
Proof.
  intros HG _ (HO & A) MD CH.
  destruct (br_layout G HG) as (WB & HH & WF & SL & TP & HT & SLE & DF).
  assert (AT: at_type G s (8 * c - bits) bits out).
  { unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
      LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
    repeat match goal with H: _ \/ _ |- _ => destruct H end;
      repeat match goal with H: _ /\ _ |- _ => destruct H end;
      first [assumption | exfalso; lia]. }
  destruct AT as (k & K & Q & HOut & B & L).
  destruct HO as (HB & HC & HV).
  assert (k = 0).
  { destruct (Z.eq_dec k 0) as [|NZ]; [assumption|]. exfalso.
    unfold bpos, D0 in Q. fold (hlen G) in Q.
    pose proof (br_epos_ge (Z.to_nat k) (dc_bs G) 0) as E.
    unfold nblk in K. rewrite Zlength_correct in K.
    specialize (E ltac:(lia)). rewrite Z2Nat.id in E by lia. lia. }
  subst k. unfold bpos, D0 in Q. cbn [Z.to_nat] in Q. fold (hlen G) in Q.
  replace (epos 0 (dc_bs G) O) with 0 in Q by (destruct (dc_bs G); reflexivity).
  assert (c = hlen G /\ bits = 0) as [-> ->] by lia.
  split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite HV, Z.sub_0_r, sublist_nil; reflexivity|].
  split; [rewrite HOut; unfold outk; cbn; exact HH|].
  split.
  - unfold hold_ok. split; [lia|]. split; [apply Zlength_nonneg|]. rewrite sublist_nil. reflexivity.
  - right; right; left. split; [exact MD|].
    exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs (rawctx G src))); lia|].
    split; [unfold bpos; cbn [Z.to_nat rawctx dc_bs]; destruct (dc_bs G); reflexivity|].
    split; [reflexivity|]. split; [lia|]. exact L.
Qed.

(* the raw view of the fixed fields *)
Lemma bad_raw_glob G src s cc : bad_ctx G -> glob_ok G s -> i_mode s <> HEAD ->
  glob_ok (rawctx G src) (set_i_check (set_i_wrap s 0) cc).
Proof.
  intros HG ((wb0 & RS & _) & HD & WBR & _) NH.
  destruct (br_layout G HG) as (WB & _).
  split; [|split; [exact HD|split]].
  - exists (dc_wb G). split; [|intros E; contradiction].
    transitivity (Some (reset2_wrap 0 (dc_wb G), dc_wb G)); [exact (init_wrap_wb_of _ _ _ (br_reset2_raw (dc_wb G) WB))|].
    unfold reset2_wrap. replace (dc_wb G =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - intros _. exact (WBR NH).
  - intros E; discriminate.
Qed.

(* CHECK in the raw stream: its end, the bit buffer empty *)
Lemma bad_raw_check G src s c hold bits out : bad_ctx G -> bad_src G src ->
  at_mode (rawctx G src) s c hold bits out -> i_mode s = CHECK ->
  c = tpos G - hlen G /\ bits = 0 /\ hold = 0 /\ out = full G.
Proof.
  intros HG _ (HO & A) MD.
  destruct (br_layout G HG) as (WB & HH & WF & SL & TP & HT & SLE & DF).
  assert (AT: at_check (rawctx G src) s (8 * c - bits) bits out).
  { unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
      LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *.
    repeat match goal with H: _ \/ _ |- _ => destruct H end;
      repeat match goal with H: _ /\ _ |- _ => destruct H end;
      first [assumption | exfalso; lia]. }
  destruct AT as (HOut & _ & Q & _ & _ & B0).
  specialize (B0 eq_refl). subst bits.
  destruct HO as (_ & _ & HV).
  unfold endpos, D0 in Q. cbn [dc_w dc_bs rawctx hdr_bytes] in Q. rewrite br_bits_len in Q.
  rewrite Zlength_nil in Q.
  split; [lia|]. split; [reflexivity|].
  split; [rewrite HV, Z.sub_0_r, sublist_nil; reflexivity|].
  rewrite HOut. unfold full, rawctx; cbn [dc_hist dc_bs]. rewrite HH. reflexivity.
Qed.

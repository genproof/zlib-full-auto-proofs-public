(* Law rfc_stored, main: two facts of the buffer the harness builds (RSModel.rs_src), used where main hands
   it to the inflate loop: its length is the stream object's, and it holds bytes. *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Format.
Require Import Zlib.proof.rfc1951.DecTrl.
Require Import Zlib.proof.harness.rfc_stored.RSModel.
Require Import Zlib.proof.harness.rfc_stored.RSCanon.
Import ListNotations.
Local Open Scope Z_scope.

(* the header has rs_hl wr bytes *)
Lemma rs_hdr_len wr c s0 : 0 <= wr <= 2 -> rs_hl wr <= Zlength s0 -> Zlength (rs_hdr wr c s0) = rs_hl wr.
Proof.
  intros Hwr L. assert (W : wr = 0 \/ wr = 1 \/ wr = 2) by lia.
  destruct W as [ -> | [ -> | -> ] ]; unfold rs_hdr, rs_hl in *; cbn [Z.eqb Pos.eqb] in *; [reflexivity | reflexivity | ].
  rewrite Zlength_app, Zlength_sublist by lia. reflexivity.
Qed.

(* the trailer has rs_tl wr bytes *)
Lemma rs_trl_len wr d : 0 <= wr <= 2 -> Zlength (rs_trl wr d) = rs_tl wr.
Proof.
  intros Hwr. assert (W : wr = 0 \/ wr = 1 \/ wr = 2) by lia.
  destruct W as [ -> | [ -> | -> ] ]; unfold rs_trl, rs_tl; cbn [Z.eqb Pos.eqb]; [reflexivity | | ].
  - unfold be_bytes. rewrite Zlength_rev. apply trl_le_bytes_len. lia.
  - rewrite Zlength_app, !trl_le_bytes_len by lia. reflexivity.
Qed.

Lemma rs_src_len wr c s0 pads lens d:
  0 <= wr <= 2 -> Forall (fun l => 0 <= l <= 65535) lens -> fold_right Z.add 0 lens = Zlength d ->
  rs_slen wr lens d <= Zlength s0 ->
  Zlength (rs_src wr c s0 pads lens d) = Zlength s0.
Proof.
  intros Hwr Hf Hs L. unfold rs_slen in L.
  assert (Hl : 0 <= Zlength lens) by apply Zlength_nonneg.
  assert (Hd : 0 <= Zlength d) by apply Zlength_nonneg.
  assert (Ht : 0 <= rs_tl wr) by (unfold rs_tl; destruct (wr =? 1), (wr =? 2); lia).
  assert (Hh : 0 <= rs_hl wr) by (unfold rs_hl; destruct (wr =? 1), (wr =? 2); lia).
  unfold rs_src, rs_slen. rewrite !Zlength_app, rs_hdr_len, rs_trl_len by lia.
  rewrite (rsc_blocks_len lens pads d) by (split; auto).
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma rs_src_bytes wr window c s0 lens d:
  rs_ok wr window c s0 lens d -> rs_bytes (rs_src wr c s0 (rs_pads wr s0 lens) lens d).
Proof.
  intros (Hwr & Hw & Hc & Hne & Hf & Hs & L & Bs & Bd). unfold rs_slen in L.
  assert (Hl : 1 <= Zlength lens) by (destruct lens; [congruence | rewrite Zlength_cons; pose proof (Zlength_nonneg lens); lia]).
  assert (Hd : 0 <= Zlength d) by apply Zlength_nonneg.
  assert (Ht : 0 <= rs_tl wr) by (unfold rs_tl; destruct (wr =? 1), (wr =? 2); lia).
  assert (Hh : 0 <= rs_hl wr) by (unfold rs_hl; destruct (wr =? 1), (wr =? 2); lia).
  destruct (rsc_wrap wr window c s0 Hwr Hw Hc ltac:(lia) Bs) as (_ & _ & Bh & _).
  unfold rs_src, rs_bytes. rewrite !Forall_app. split; [exact Bh | ]. split; [ | split].
  - apply rsc_blocks_bytes; auto. split; auto.
    unfold rs_pads, rs_bytes. apply Forall_map. apply Forall_forall. intros p _.
    unfold Basics.compose, Znth. destruct (Z_lt_dec p 0) as [Lp | Lp]; [cbv [byte_ok default Inhabitant_Z]; lia | ].
    destruct (Nat.lt_ge_cases (Z.to_nat p) (length s0)) as [Lt | Ge].
    + apply Forall_forall with (l := s0); [exact Bs | apply nth_In; exact Lt].
    + rewrite nth_overflow by exact Ge. cbv [byte_ok Inhabitant_Z]. lia.
  - assert (W : wr = 0 \/ wr = 1 \/ wr = 2) by lia.
    destruct W as [ -> | [ -> | -> ] ]; unfold rs_trl; cbn [Z.eqb Pos.eqb]; [constructor | | ].
    + unfold be_bytes. apply Forall_rev. apply trl_le_bytes_ok.
    + apply Forall_app. split; apply trl_le_bytes_ok.
  - apply Forall_sublist. exact Bs.
Qed.

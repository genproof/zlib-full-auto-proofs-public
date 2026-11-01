(* RT-I part rti_gz_pass: the decode invariant Kd at the TYPE loop head after the gzip header *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma gp_kd_reset2 wb : 9 <= wb <= 15 -> reset2_wb (32 + wb) = Some (7, wb).
Proof.
  intros H. assert (E : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat destruct E as [E|E]; subst wb; reflexivity.
Qed.

Lemma gp_kd_crc0 : Zlib.proof.crc32.Model.ref_crc32 0 [] = 0.
Proof. reflexivity. Qed.

Lemma gp_kd_ok : gp_kd_stmt.
Proof.
  intros gh xfl wb bs O z hd h0 m Hwb HO Hok Ht Hm Hfl Hhh Hck.
  destruct Hm as [I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17].
  set (G := gz_ctx gh xfl wb bs O).
  assert (Hlen : Zlength (gz_bytes (gp_H gh xfl)) <= Zlength O).
  { rewrite HO. unfold stream_bytes, gp_H. rewrite Zlength_app.
    pose proof (Zlength_nonneg (deflate_bytes bs ++ le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (data [] bs)) 4 ++
      le_bytes (Zlength (data [] bs) mod 2 ^ 32) 4)). lia. }
  assert (Hp : gp_p gh xfl 8 = Zlength (gz_bytes (gp_H gh xfl))) by reflexivity.
  assert (HD0 : D0 G = 8 * Zlength (gz_bytes (gp_H gh xfl))) by reflexivity.
  assert (Hsrc : dc_src G = O) by reflexivity.
  assert (Hpr : produced G [] = []) by reflexivity.
  assert (Hmd : m_mode m = Zlib.proof.inflate.Model.TYPE) by exact I11.
  assert (Hac : after_check G (m_mode m) = false) by (rewrite Hmd; reflexivity).
  constructor.
  - exact I1.
  - rewrite I2, I3, I4, I6. split.
    + unfold hold_ok. rewrite Hsrc. split; [|split].
      * pose proof (Zlength_nonneg (gz_bytes (gp_H gh xfl))). lia.
      * lia.
      * rewrite Z.sub_0_r, sublist_nil. reflexivity.
    + right. right. left. split; [left; exact I11|].
      exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs G)); lia|].
      split; [unfold bpos; cbn [Z.to_nat]; rewrite HD0, Hp; destruct (dc_bs G); cbn [epos]; lia|].
      split; [reflexivity|]. split; [lia|]. rewrite I12. reflexivity.
  - split; [|split; [reflexivity|split]].
    + (* inflateInit2(32) stored wrap 7 with bit 3 (fix F8): the context's 32 + wb gives wrap 7, i_wrap is 7 | 8 *)
      exists wb. split; [|intros E; rewrite I11 in E; discriminate].
      right. exists 7. split; [apply gp_kd_reset2; exact Hwb|]. split; [discriminate|]. rewrite I14. reflexivity.
    + intros _. rewrite I16. cbn [dc_wb G gz_ctx]. lia.
    + intros _ _ _. exact Hfl.
  - intros _. left. split; [exact I15|reflexivity].
  - intros _ N1 N2 N3 N4. rewrite I11, I6. cbn -[produced chkv].
    rewrite Hpr. split; [|split].
    + rewrite Hck. reflexivity.
    + rewrite I13. reflexivity.
    + exists []. reflexivity.
  - rewrite Hac, I10, Ht, Hpr. reflexivity.
  - rewrite Hac, I7, I8. reflexivity.
  - rewrite I9, Hmd. reflexivity.
Qed.

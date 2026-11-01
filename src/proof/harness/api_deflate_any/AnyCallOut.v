(* Law api_deflate_any: the output space at deflate's call.  main's output space of [room] bytes was made holding
   any bytes [bs]; after [O] bytes were written at its start it holds [ovals bs O] (AnyKit.v).  deflate gets the
   part after [O] (DetCall2.out_split) and writes its output [zo] at the start of it, leaving the rest of [bs] as it
   was: the space then holds [ovals bs (O ++ zo)].  Like DetCall2.out_join, with the bytes [bs] in the tail instead
   of undefined values. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Zlib.proof.harness.api_deterministic.DetCall2.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DK := Zlib.proof.harness.api_deterministic.DetKit2.
Module DC2 := Zlib.proof.harness.api_deterministic.DetCall2.

(* what deflate gets of the space: the bytes of [bs] after the [O] written *)
Definition orest (room : Z) (bs O : list Z) : list val := map vi (sublist (Zlength O) room bs).

Lemma orest_len (room : Z) (bs O : list Z) :
  Zlength bs = room -> 0 <= Zlength O <= room -> Zlength (orest room bs O) = room - Zlength O.
Proof. intros. unfold orest. rewrite Zlength_map, Zlength_sublist; lia. Qed.

(* before the call: the space as the part kept and the part given to deflate *)
Lemma out_split_bytes (q : val) (room : Z) (bs O : list Z) :
  Zlength bs = room -> 0 <= Zlength O <= room -> field_compatible (tarray tuchar room) [] q ->
  DK.out_at q room (map vi (ovals bs O)) =
  DC2.ohead q room O * data_at Ews (tarray tuchar (room - Zlength O)) (orest room bs O) (offset_val (Zlength O) q) *
  wv_at (DC2.owit room O) (offset_val (Zlength O) q).
Proof.
  intros Hb HO FC. unfold ovals, orest. rewrite map_app, Hb.
  apply DC2.out_split; auto. rewrite Zlength_map, Zlength_sublist; lia.
Qed.

(* after the call: [zo] written at the start of the part given to deflate *)
Lemma out_join_bytes (q : val) (room : Z) (bs O zo : list Z) :
  Zlength bs = room -> Zlength O + Zlength zo <= room -> field_compatible (tarray tuchar room) [] q ->
  DC2.ohead q room O *
  data_at Ews (tarray tuchar (room - Zlength O))
    (map vi zo ++ sublist (Zlength zo) (room - Zlength O) (orest room bs O)) (offset_val (Zlength O) q) *
  wv_at (DC2.owit room O) (offset_val (Zlength O) q)
  |-- DK.out_at q room (map vi (ovals bs (O ++ zo))).
Proof.
  intros Hb H FC. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg zo).
  unfold ovals, orest. rewrite !map_app, <- app_assoc.
  rewrite (DC2.out_split q room O); [| lia | | auto].
  - apply derives_refl'. f_equal. f_equal. f_equal. f_equal.
    rewrite sublist_map, sublist_sublist by lia. rewrite Zlength_app, Hb. f_equal. f_equal; lia.
  - rewrite !Zlength_app, !Zlength_map, !Zlength_sublist by lia. lia.
Qed.

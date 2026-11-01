(* Byte-pointer arithmetic of the checksum loops as array element addresses (VST's loads need the
   address of an element in the form field_address). *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.adler32.Bytes.

(* buf + c (a constant offset). *)
Lemma add_ptr_c {cs: compspecs} p n k c:
  field_compatible (tarray tuchar n) [] p -> 0 <= k + c < n -> 0 <= c <= Int.max_signed ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val k p) (Vint (Int.repr c))) =
  field_address (tarray tuchar n) [ArraySubsc (k + c)] p.
Proof.
  intros FC Hk Hc. rewrite arr_field_address by auto.
  destruct p; try (destruct FC; contradiction). simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. normalize.
  all: try (rewrite Int.signed_repr by rep_lia; f_equal; lia).
Qed.

Lemma offset_field_address {cs: compspecs} p n k:
  field_compatible (tarray tuchar n) [] p -> 0 <= k < n ->
  offset_val k p = field_address (tarray tuchar n) [ArraySubsc k] p.
Proof. intros. rewrite arr_field_address by auto. simpl. f_equal. lia. Qed.

(* buf += c *)
Lemma add_ptr_n {cs: compspecs} p k c: isptr p -> 0 <= c <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k p) (Vint (Int.repr c))) =
  offset_val (k + c) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. normalize.
  all: try (rewrite Int.signed_repr by rep_lia; f_equal; lia).
Qed.

(* buf + i with a 64-bit index (buf[i] of the harness loops). *)
Lemma add_ptr_long {cs: compspecs} p n k i:
  field_compatible (tarray tuchar n) [] p -> 0 <= k + i < n -> 0 <= i <= Int64.max_unsigned ->
  force_val (sem_add_ptr_long tuchar (offset_val k p) (Vlong (Int64.repr i))) =
  field_address (tarray tuchar n) [ArraySubsc (k + i)] p.
Proof.
  intros FC Hk Hi. rewrite arr_field_address by auto.
  destruct p; try (destruct FC; contradiction). simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, ptrofs_add_repr. f_equal. lia.
Qed.

(* Slices of a whole byte object as the checksum specifications take them. *)
Lemma cbuf_ok_slice sh p data lo len:
  readable_share sh -> isptr p -> is_bytes data -> 0 <= lo -> 0 <= len -> lo + len <= Zlength data ->
  cbuf_ok false (offset_val lo p) sh p lo (Zlength data) len (bytes_rep data) (sublist lo (lo + len) data).
Proof.
  intros. unfold cbuf_ok. split; auto. split; auto. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist; lia | ]. split; [apply is_bytes_sublist; auto | ].
  apply sublist_bytes_rep.
Qed.

Lemma cbuf_ok_prefix sh p data len:
  readable_share sh -> isptr p -> is_bytes data -> 0 <= len -> len <= Zlength data ->
  cbuf_ok false p sh p 0 (Zlength data) len (bytes_rep data) (sublist 0 len data).
Proof.
  intros. pose proof (cbuf_ok_slice sh p data 0 len H H0 H1 ltac:(lia) H2 ltac:(lia)) as C.
  destruct p; try contradiction. simpl in C. rewrite ptrofs_add_repr_0_r in C.
  rewrite Z.add_0_l in C. unfold cbuf_ok. simpl. rewrite ptrofs_add_repr_0_r. exact C.
Qed.

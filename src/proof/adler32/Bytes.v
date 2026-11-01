(* Byte buffers as the checksum specifications take them (shared by adler32 and crc32).

   A byte is a Z in 0..255, represented in memory as nondet_bytes leaves it: Vint (Int.repr b).
   The buffer argument of adler32/adler32_z/crc32/crc32_z is either Z_NULL (isnull = true) or the slice
   [lo, lo + len) of an object p of n bytes whose contents (any values outside the slice) hold the bytes
   data inside it (cbuf_ok).  The specifications keep the whole object in their SEP, so a caller that holds
   a larger buffer passes it as it is (no splitting); a caller that holds exactly the bytes passes
   lo = 0, n = len, contents = bytes_rep data.

   The functions compare buf with Z_NULL, which needs buf to be weakly valid (a pointer into or one past an
   object).  The object gives that when n > 0; for an empty object (n = 0: malloc(0)) the caller also
   passes the object's malloc token (tok = true: malloc_token vsh (tarray tuchar n) p, valid by VST's
   malloc_token_valid_pointer).  cbuf_valid: tok = true, or n > 0, or Z_NULL.  Callers with n > 0 or with
   Z_NULL pass tok = false (cbuf_valid_pos, cbuf_valid_null); callers with a malloc'd object may always
   pass its token (cbuf_valid_tok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Definition bytes_rep (l: list Z) : list val := map (fun b => Vint (Int.repr b)) l.
Definition is_bytes (l: list Z) : Prop := Forall (fun b => 0 <= b <= Byte.max_unsigned) l.

Definition cbuf_ok (isnull: bool) (buf: val) (sh: share) (p: val) (lo n len: Z) (contents: list val)
  (data: list Z) : Prop :=
  if isnull then buf = nullval
  else buf = offset_val lo p /\ readable_share sh /\ 0 <= lo /\ lo + len <= n /\ Zlength data = len /\
       is_bytes data /\ sublist lo (lo + len) contents = bytes_rep data.

Definition cbuf_valid (isnull tok: bool) (n: Z) : Prop := isnull = false -> tok = false -> 0 < n.

Lemma cbuf_valid_pos isnull tok n: 0 < n -> cbuf_valid isnull tok n.
Proof. intros H _ _. lia. Qed.

Lemma cbuf_valid_null tok n: cbuf_valid true tok n.
Proof. intros E. discriminate. Qed.

Lemma cbuf_valid_tok isnull n: cbuf_valid isnull true n.
Proof. intros _ E. discriminate. Qed.

Lemma Zlength_bytes_rep l: Zlength (bytes_rep l) = Zlength l.
Proof. unfold bytes_rep. apply Zlength_map. Qed.

Lemma bytes_rep_app l1 l2: bytes_rep (l1 ++ l2) = bytes_rep l1 ++ bytes_rep l2.
Proof. unfold bytes_rep. apply map_app. Qed.

Lemma sublist_bytes_rep lo hi l: sublist lo hi (bytes_rep l) = bytes_rep (sublist lo hi l).
Proof. unfold bytes_rep. apply sublist_map. Qed.

Lemma Znth_bytes_rep i l: 0 <= i < Zlength l -> Znth i (bytes_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold bytes_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma is_bytes_Znth l i: is_bytes l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Byte.max_unsigned.
Proof. intros H Hi. unfold is_bytes in H. rewrite Forall_forall in H. apply H. apply Znth_In. auto. Qed.

Lemma is_bytes_sublist l lo hi: is_bytes l -> is_bytes (sublist lo hi l).
Proof. unfold is_bytes. intros. apply Forall_sublist. auto. Qed.

Lemma is_bytes_app l1 l2: is_bytes l1 -> is_bytes l2 -> is_bytes (l1 ++ l2).
Proof. unfold is_bytes. intros. apply Forall_app. auto. Qed.

(* The whole object as a caller holding exactly the bytes passes it. *)
Lemma cbuf_ok_whole sh p data:
  readable_share sh -> is_bytes data -> isptr p ->
  cbuf_ok false p sh p 0 (Zlength data) (Zlength data) (bytes_rep data) data.
Proof.
  intros R B P. destruct p; try contradiction. simpl.
  rewrite Ptrofs.add_zero. split3; auto. split3; [lia | lia | ]. split3; auto.
  rewrite sublist_same; auto. rewrite Zlength_bytes_rep. lia.
Qed.

(* The comparison buf == Z_NULL inside the checksum functions is defined: buf is weakly valid. *)
Lemma cbuf_weak_valid {cs: compspecs} tok vsh sh p lo n contents:
  readable_share sh -> 0 <= lo <= n -> (tok = true \/ 0 < n) -> isptr p ->
  (if tok then malloc_token vsh (tarray tuchar n) p else emp) * data_at sh (tarray tuchar n) contents p
  |-- weak_valid_pointer (offset_val lo p).
Proof.
  intros Hsh Hlo Htok Hp.
  destruct (zlt 0 n).
  - apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply data_at_memory_block | ].
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
  - destruct Htok as [-> | ?]; [ | lia]. assert (n = 0) by lia. subst n. assert (lo = 0) by lia. subst lo.
    apply sepcon_weak_valid_pointer1.
    eapply derives_trans; [apply andp_right; [apply malloc_token_valid_pointer; simpl; lia | apply derives_refl] | ].
    apply derives_trans with (valid_pointer p); [apply andp_left1, derives_refl | ].
    eapply derives_trans; [apply valid_pointer_weak | ].
    destruct p; try contradiction. simpl. rewrite ptrofs_add_repr_0_r. auto.
Qed.

Local Transparent denote_tc_test_eq.

Lemma cbuf_test_eq {cs: compspecs} tok vsh sh p lo n contents:
  readable_share sh -> 0 <= lo <= n -> (tok = true \/ 0 < n) -> isptr p ->
  (if tok then malloc_token vsh (tarray tuchar n) p else emp) * data_at sh (tarray tuchar n) contents p
  |-- denote_tc_test_eq (offset_val lo p) (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Hlo Htok Hp. destruct p; try contradiction.
  unfold denote_tc_test_eq, offset_val. cbv [Archi.ptr64].
  apply andp_right; [apply prop_right; reflexivity | ].
  apply (cbuf_weak_valid tok vsh sh (Vptr b i) lo n contents); auto.
Qed.

Lemma cbuf_test_eq_frame {cs: compspecs} R tok vsh sh p lo n contents:
  readable_share sh -> 0 <= lo <= n -> (tok = true \/ 0 < n) -> isptr p ->
  R * ((if tok then malloc_token vsh (tarray tuchar n) p else emp) * data_at sh (tarray tuchar n) contents p)
  |-- denote_tc_test_eq (offset_val lo p) (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Hlo Htok Hp. destruct p; try contradiction.
  unfold denote_tc_test_eq, offset_val. cbv [Archi.ptr64].
  apply andp_right; [apply prop_right; reflexivity | ].
  apply sepcon_weak_valid_pointer2.
  apply (cbuf_weak_valid tok vsh sh (Vptr b i) lo n contents); auto.
Qed.

(* The byte i of the slice. *)
Lemma Znth_cbuf lo len contents data i:
  sublist lo (lo + len) contents = bytes_rep data -> Zlength data = len ->
  0 <= lo -> lo + len <= Zlength contents -> 0 <= i < len ->
  Znth (lo + i) contents = Vint (Int.repr (Znth i data)).
Proof.
  intros Hsub Hlen Hlo Hn Hi.
  rewrite <- Znth_bytes_rep by lia. rewrite <- Hsub.
  rewrite Znth_sublist by lia. f_equal. lia.
Qed.

(* buf = buf + 1 on a byte pointer. *)
Lemma add_ptr_1 {cs: compspecs} p k: isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val k p) (Vint (Int.repr 1))) =
  offset_val (k + 1) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. normalize.
Qed.

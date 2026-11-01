(* The bit writer of harness/rj_bad_block.c and harness/rj_far_back.c (put_bits, put_literal), as a function on
   the stream's bytes: RFC 1951 3.1.1 packing.  Bit q of a byte list is bit q mod 8 of byte q / 8 (Format.bytes_bits
   reads the bits in this order); put_bits(stream, &bit, value, count, huffman) writes the count low bits of value
   at bits [bit, bit + count): the least significant first (a data element: Format.bits_le), or with huffman <> 0
   the most significant first (a Huffman code: Format.bits_msb); put_literal writes a literal's fixed code
   (RFC 1951 3.2.6), i.e. Format.send_sym fixed_ll.

   The lemmas at the end are what the laws use: the bits of the written bytes, and the fold of put_literal over
   the literals (the main loops). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.zlist.list_solver.
Require Import Zlib.proof.rfc1951.Format.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* stream[q / 8] = (stream[q / 8] & ~mask) | (one ? mask : 0), mask = 1 << (q % 8) *)
Definition set_bit (bytes: list Z) (q: Z) (b: bool) : list Z :=
  let k := q / 8 in
  let mask := 2 ^ (q mod 8) in
  upd_Znth k bytes (Z.lor (Z.land (Znth k bytes) (Z.lnot mask)) (if b then mask else 0)).

(* the bits bs written from bit position q on *)
Fixpoint write_bits (bytes: list Z) (q: Z) (bs: list bool) : list Z :=
  match bs with
  | [] => bytes
  | b :: r => write_bits (set_bit bytes q b) (q + 1) r
  end.

(* the bits put_bits writes: bit i is (value >> shift) & 1, shift = huffman ? count - 1 - i : i *)
Definition pb_bits (value count huffman: Z) : list bool :=
  if huffman =? 0 then bits_le value count else bits_msb value count.

(* put_bits(stream, &bit, value, count, huffman): the new bytes (bit becomes bit + count) *)
Definition put_bits_m (bytes: list Z) (bit value count huffman: Z) : list Z :=
  write_bits bytes bit (pb_bits value count huffman).

(* put_literal(stream, &bit, literal): the new bytes; bit grows by lit_len literal *)
Definition put_literal_m (bytes: list Z) (bit lit: Z) : list Z :=
  if lit <? 144 then put_bits_m bytes bit (48 + lit) 8 1 else put_bits_m bytes bit (400 + lit - 144) 9 1.
Definition lit_len (lit: Z) : Z := if lit <? 144 then 8 else 9.

(* the loop `for (i = 0; i < literals; i++) put_literal(stream, &bit, literal[i]);` from bit position q *)
Fixpoint put_lits (bytes: list Z) (q: Z) (lits: list Z) : list Z :=
  match lits with
  | [] => bytes
  | l :: r => put_lits (put_literal_m bytes q l) (q + lit_len l) r
  end.
Fixpoint lits_len (lits: list Z) : Z :=
  match lits with [] => 0 | l :: r => lit_len l + lits_len r end.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts                                                                                          *)

(* membership in 0 .. n - 1, for the checks by computation below *)
Lemma bw_in_seq : forall x n, 0 <= x < Z.of_nat n -> In x (map Z.of_nat (seq 0 n)).
Proof. intros. replace x with (Z.of_nat (Z.to_nat x)) by lia. apply in_map, in_seq. lia. Qed.

(* the byte set_bit writes into the byte x for bit k = q mod 8 *)
Definition set_byte (x k: Z) (b: bool) : Z := Z.lor (Z.land x (Z.lnot (2 ^ k))) (if b then 2 ^ k else 0).

(* all 256 * 8 * 2 cases, by computation *)
Lemma set_byte_check :
  forallb (fun x => forallb (fun k => forallb (fun b =>
    (0 <=? set_byte x k b) && (set_byte x k b <=? 255) &&
    (if list_eq_dec bool_dec (bits_le (set_byte x k b) 8) (upd_Znth k (bits_le x 8) b) then true else false))
    [true; false]) (map Z.of_nat (seq 0 8))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

(* the new byte is a byte, and its bits are the old ones with bit k replaced by b *)
Lemma set_byte_ok : forall x k b, 0 <= x <= 255 -> 0 <= k < 8 ->
  0 <= set_byte x k b <= 255 /\ bits_le (set_byte x k b) 8 = upd_Znth k (bits_le x 8) b.
Proof.
  intros x k b Hx Hk. pose proof set_byte_check as H.
  rewrite forallb_forall in H. specialize (H x (bw_in_seq x 256 ltac:(lia))).
  rewrite forallb_forall in H. specialize (H k (bw_in_seq k 8 ltac:(lia))).
  rewrite forallb_forall in H. specialize (H b ltac:(destruct b; simpl; auto)).
  destruct (list_eq_dec bool_dec _ _) as [E|E].
  - rewrite andb_true_r, andb_true_iff, !Z.leb_le in H. split; [lia|exact E].
  - rewrite andb_false_r in H. discriminate H.
Qed.

(* setting one bit: the bits of the bytes with bit q replaced by b *)
Lemma set_bit_ok : forall bytes q b,
  is_bytes bytes -> 0 <= q < 8 * Zlength bytes ->
  Zlength (set_bit bytes q b) = Zlength bytes /\ is_bytes (set_bit bytes q b) /\
  bytes_bits (set_bit bytes q b) =
    sublist 0 q (bytes_bits bytes) ++ b :: sublist (q + 1) (8 * Zlength bytes) (bytes_bits bytes).
Proof.
  intros bytes q b Hb Hq.
  set (n := Zlength bytes) in *. set (j := q / 8). set (k := q mod 8).
  assert (Hj: 0 <= j < n) by (unfold j; split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  assert (Hk: 0 <= k < 8) by (unfold k; apply Z.mod_pos_bound; lia).
  assert (Hqjk: q = 8 * j + k) by (unfold j, k; apply Z.div_mod; lia).
  set (x := Znth j bytes).
  assert (Hx: 0 <= x <= 255) by (apply (is_bytes_Znth bytes j Hb); lia).
  destruct (set_byte_ok x k b Hx Hk) as [Hy HY].
  assert (E: set_bit bytes q b = upd_Znth j bytes (set_byte x k b)) by reflexivity.
  rewrite E. clear E.
  split; [rewrite upd_Znth_Zlength; lia|]. split.
  { unfold is_bytes in *. apply Forall_upd_Znth; auto; lia. }
  assert (Hsplit: bytes = sublist 0 j bytes ++ [x] ++ sublist (j + 1) n bytes).
  { unfold x, n. rewrite <- upd_Znth_unfold by lia. rewrite upd_Znth_triv; auto; lia. }
  assert (HBB: bytes_bits bytes =
    bytes_bits (sublist 0 j bytes) ++ bits_le x 8 ++ bytes_bits (sublist (j + 1) n bytes)).
  { rewrite Hsplit at 1. rewrite !dkit_bytes_bits_app. change (bytes_bits [x]) with (bits_le x 8 ++ []). rewrite app_nil_r. reflexivity. }
  rewrite upd_Znth_unfold by lia. fold n. rewrite HBB, !dkit_bytes_bits_app.
  change (bytes_bits [set_byte x k b]) with (bits_le (set_byte x k b) 8 ++ []).
  rewrite app_nil_r, HY.
  assert (HA: Zlength (bytes_bits (sublist 0 j bytes)) = 8 * j)
    by (rewrite dkit_bytes_bits_len, Zlength_sublist; lia).
  assert (HC: Zlength (bytes_bits (sublist (j + 1) n bytes)) = 8 * (n - j - 1))
    by (rewrite dkit_bytes_bits_len, Zlength_sublist; lia).
  assert (HX: Zlength (bits_le x 8) = 8) by (apply dkit_bits_le_len; lia).
  rewrite Hqjk. clear HY Hsplit Hqjk HBB.
  remember (bytes_bits (sublist 0 j bytes)) as A. remember (bytes_bits (sublist (j + 1) n bytes)) as C.
  remember (bits_le x 8) as X.
  list_solve.
Qed.

(* writing bits keeps the length and the byte range, and replaces exactly the bits [q, q + |bs|) *)
Lemma write_bits_ok : forall bs bytes q,
  is_bytes bytes -> 0 <= q -> q + Zlength bs <= 8 * Zlength bytes ->
  Zlength (write_bits bytes q bs) = Zlength bytes /\ is_bytes (write_bits bytes q bs) /\
  bytes_bits (write_bits bytes q bs) =
    sublist 0 q (bytes_bits bytes) ++ bs ++ sublist (q + Zlength bs) (8 * Zlength bytes) (bytes_bits bytes).
Proof.
  induction bs as [|b r IH]; intros bytes q Hb Hq Hl; simpl write_bits.
  - pose proof (dkit_bytes_bits_len bytes). split; [reflexivity|]. split; [exact Hb|].
    rewrite Zlength_nil in *. generalize dependent (bytes_bits bytes). intros. list_solve.
  - rewrite Zlength_cons in Hl. pose proof (Zlength_nonneg r).
    destruct (set_bit_ok bytes q b Hb ltac:(lia)) as (H1 & H2 & H3).
    destruct (IH (set_bit bytes q b) (q + 1) H2 ltac:(lia) ltac:(lia)) as (H4 & H5 & H6).
    rewrite H1 in *. split; [exact H4|]. split; [exact H5|].
    rewrite H6, H3. pose proof (dkit_bytes_bits_len bytes).
    generalize dependent (bytes_bits bytes). intros. list_solve.
Qed.

Lemma pb_bits_len : forall value count huffman, 0 <= count -> Zlength (pb_bits value count huffman) = count.
Proof.
  intros. unfold pb_bits. destruct (huffman =? 0).
  - apply dkit_bits_le_len; auto.
  - unfold bits_msb. rewrite Zlength_rev. apply dkit_bits_le_len; auto.
Qed.

(* writing a concatenation is writing its two parts one after the other *)
Lemma write_bits_app : forall a b bytes q,
  write_bits bytes q (a ++ b) = write_bits (write_bits bytes q a) (q + Zlength a) b.
Proof.
  induction a as [|x r IH]; intros b bytes q; simpl.
  - rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - rewrite IH, Zlength_cons. f_equal. lia.
Qed.

(* the fixed literal codes: 00110000 + lit in 8 bits below 144, 110010000 + (lit - 144) in 9 bits from 144 on
   (RFC 1951 3.2.6); all 256 literals checked by computation against Format's canonical code *)
Lemma lit_code_check :
  forallb (fun l =>
    (if list_eq_dec bool_dec (pb_bits (if l <? 144 then 48 + l else 400 + l - 144) (lit_len l) 1)
                             (send_sym fixed_ll l) then true else false) &&
    (lit_len l =? Znth l fixed_ll)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

(* a literal's bits are its fixed code *)
Lemma put_literal_send : forall bytes q lit, 0 <= lit < 256 ->
  put_literal_m bytes q lit = write_bits bytes q (send_sym fixed_ll lit) /\
  lit_len lit = Zlength (send_sym fixed_ll lit) /\ lit_len lit = Znth lit fixed_ll.
Proof.
  intros bytes q lit Hl. pose proof lit_code_check as H.
  rewrite forallb_forall in H. specialize (H lit (bw_in_seq lit 256 ltac:(lia))).
  destruct (list_eq_dec bool_dec _ _) as [E|E]; [|discriminate H].
  rewrite andb_true_l, Z.eqb_eq in H.
  assert (P: put_literal_m bytes q lit =
             write_bits bytes q (pb_bits (if lit <? 144 then 48 + lit else 400 + lit - 144) (lit_len lit) 1))
    by (unfold put_literal_m, lit_len, put_bits_m; destruct (lit <? 144); reflexivity).
  split; [rewrite P, E; reflexivity|]. split; [|exact H].
  rewrite <- E, pb_bits_len; [reflexivity|]. unfold lit_len. destruct (lit <? 144); lia.
Qed.

Lemma put_lits_send : forall lits bytes q, Forall (fun l => 0 <= l < 256) lits ->
  put_lits bytes q lits = write_bits bytes q (concat (map (send_sym fixed_ll) lits)) /\
  lits_len lits = Zlength (concat (map (send_sym fixed_ll) lits)).
Proof.
  induction lits as [|l r IH]; intros bytes q H; simpl.
  - split; reflexivity.
  - inversion H as [|? ? Hl Hr]; subst.
    destruct (put_literal_send bytes q l Hl) as (E1 & E2 & _).
    destruct (IH (put_literal_m bytes q l) (q + lit_len l) Hr) as (E3 & E4).
    rewrite E3, E1, E2, write_bits_app. split; [reflexivity|]. rewrite Zlength_app. lia.
Qed.

(* the main loop's step: one more literal *)
Lemma put_lits_snoc : forall lits l bytes q,
  put_lits bytes q (lits ++ [l]) = put_literal_m (put_lits bytes q lits) (q + lits_len lits) l /\
  lits_len (lits ++ [l]) = lits_len lits + lit_len l.
Proof.
  induction lits as [|a r IH]; intros l bytes q; simpl.
  - rewrite Z.add_0_r. split; [reflexivity|lia].
  - destruct (IH l (put_literal_m bytes q a) (q + lit_len a)) as [E1 E2].
    rewrite E1, E2. split; [f_equal; lia|lia].
Qed.

Lemma lits_len_bounds : forall lits, 8 * Zlength lits <= lits_len lits <= 9 * Zlength lits.
Proof.
  induction lits as [|a r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. unfold lit_len. destruct (a <? 144); lia.
Qed.

(* the length and the byte range of the written bytes (the main loops' invariants) *)
Lemma put_bits_m_ok : forall bytes bit value count huffman,
  is_bytes bytes -> 0 <= bit -> 0 <= count -> bit + count <= 8 * Zlength bytes ->
  Zlength (put_bits_m bytes bit value count huffman) = Zlength bytes /\
  is_bytes (put_bits_m bytes bit value count huffman).
Proof.
  intros bytes bit value count huffman Hb Hbit Hc Hl. unfold put_bits_m.
  destruct (write_bits_ok (pb_bits value count huffman) bytes bit Hb Hbit ltac:(rewrite pb_bits_len; lia))
    as (A & B & _).
  split; assumption.
Qed.

Lemma put_lits_ok : forall lits bytes q,
  is_bytes bytes -> 0 <= q -> q + lits_len lits <= 8 * Zlength bytes ->
  Zlength (put_lits bytes q lits) = Zlength bytes /\ is_bytes (put_lits bytes q lits).
Proof.
  induction lits as [|a r IH]; intros bytes q Hb Hq Hl; simpl in *.
  - split; [reflexivity|exact Hb].
  - assert (E: put_literal_m bytes q a =
               put_bits_m bytes q (if a <? 144 then 48 + a else 400 + a - 144) (lit_len a) 1)
      by (unfold put_literal_m, lit_len; destruct (a <? 144); reflexivity).
    pose proof (lits_len_bounds r). pose proof (Zlength_nonneg r).
    assert (0 < lit_len a) by (unfold lit_len; destruct (a <? 144); lia).
    destruct (put_bits_m_ok bytes q (if a <? 144 then 48 + a else 400 + a - 144) (lit_len a) 1 Hb Hq
      ltac:(lia) ltac:(lia)) as [L1 B1].
    rewrite <- E in L1, B1.
    destruct (IH (put_literal_m bytes q a) (q + lit_len a) B1 ltac:(lia) ltac:(lia)) as [L2 B2].
    rewrite L2, L1. split; [reflexivity|exact B2].
Qed.

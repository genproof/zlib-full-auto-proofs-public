(** * Cost lemma (ii) for the tight deflateBound / compressBound: arithmetic core

    Block accounting: if every block ends at most [8 * (B + 5)] bits after the point where it started
    (counting from a byte-aligned budget [A = sum of (B_j + 5)] over earlier blocks), the stream fits in
    [n + n>>12 + n>>14 + n>>25 + 7] bytes, because every block except the last holds at least 16383 bytes.

    Stored blocks and Huffman blocks that could have been stored ([buf <> NULL]) meet the per-block bound by the
    _tr_flush_block decision alone.  A block with [buf = NULL] has [B >= 32507] and at most 16383 symbols; for it
    the bound follows from a fixed reference code R1 (literals 9 bits, END 7, length code 257 2 bits, other length
    codes 7 bits, distance codes 5 bits; Kraft sum < 1), Huffman optimality ([HuffAbs.huff_opt]) against R1, a
    crude header bound, and a bound on the overhead of the length-limit repair in gen_bitlen. *)

From Coq Require Import ZArith List Lia.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model.
Require Import Zlib.proof.huffman.HuffAbs.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Block accounting *)

(** A stored block: 3 header bits, padding to the next byte, LEN/NLEN, then the bytes. *)
Lemma acct_stored : forall p A B, 0 <= p <= 8 * A -> 0 <= B ->
  8 * ((p + 3 + 7) / 8) + 32 + 8 * B <= 8 * (A + B + 5).
Proof. intros. assert ((p + 3 + 7) / 8 < A + 2) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

(** A Huffman block (cost [L] after the 3 header bits) that _tr_flush_block did not store although
    [buf <> NULL]: then [stored_len + 4 > opt_lenb = (L + 3 + 7) >> 3]. *)
Lemma acct_not_stored : forall p A B L, p <= 8 * A -> 0 <= L ->
  (L + 3 + 7) / 8 < B + 4 -> p + 3 + L <= 8 * (A + B + 5).
Proof.
  intros p A B L Hp HL Hd.
  assert (L + 3 + 7 < 8 * (B + 4)).
  { destruct (Z_lt_le_dec (L + 3 + 7) (8 * (B + 4))) as [?|Hc]; [lia|].
    assert (B + 4 <= (L + 3 + 7) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  lia.
Qed.

(** A Huffman block with [buf = NULL]: the per-block bound is exactly [L + 3 <= 8 * B + 40]. *)
Lemma acct_null : forall p A B L, p <= 8 * A -> L + 3 <= 8 * B + 40 -> p + 3 + L <= 8 * (A + B + 5).
Proof. intros. lia. Qed.

(** The final byte count: [N] non-last blocks of at least 16383 bytes each. *)
Lemma acct_total : forall n N, 0 <= n -> 0 <= N -> 16383 * N <= n ->
  n + 5 * (N + 1) <= n + n / 4096 + n / 16384 + n / 33554432 + 7.
Proof.
  intros n N Hn HN HNn.
  assert (Ha := Z.mul_div_le n 4096 ltac:(lia)). assert (Ha' := Z.mul_succ_div_gt n 4096 ltac:(lia)).
  assert (Hb := Z.mul_div_le n 16384 ltac:(lia)). assert (Hb' := Z.mul_succ_div_gt n 16384 ltac:(lia)).
  assert (Hc := Z.mul_div_le n 33554432 ltac:(lia)).
  assert (Hc' := Z.mul_succ_div_gt n 33554432 ltac:(lia)).
  lia.
Qed.

Fixpoint sumZl (l : list Z) : Z := match l with [] => 0 | x :: r => x + sumZl r end.

(** Blocks [bs ++ [last]] whose non-last blocks hold at least 16383 bytes each: the budget
    [sum (B_i + 5)] is within the tight bound of the total input [n]. *)
Theorem acct_blocks : forall bs last,
  Forall (fun b => 16383 <= b) bs -> 0 <= last ->
  let n := sumZl bs + last in
  sumZl (map (fun b => b + 5) (bs ++ [last])) <= n + n / 4096 + n / 16384 + n / 33554432 + 7.
Proof.
  intros bs last Hbs Hl n.
  assert (E : forall l, sumZl (map (fun b => b + 5) l) = sumZl l + 5 * Zlength l).
  { induction l; [reflexivity|]. rewrite Zlength_cons. cbn [map sumZl]. lia. }
  assert (G : forall l, Forall (fun b => 16383 <= b) l -> 16383 * Zlength l <= sumZl l).
  { induction l; intros H; [simpl; lia|]. inversion H; subst. rewrite Zlength_cons. cbn [sumZl].
    specialize (IHl H3). lia. }
  assert (P : forall l, Forall (fun b => 16383 <= b) l -> 0 <= sumZl l).
  { intros l H. specialize (G l H). pose proof (Zlength_nonneg l). lia. }
  rewrite E. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  assert (Hs : sumZl (bs ++ [last]) = sumZl bs + last).
  { clear. induction bs; simpl; lia. }
  rewrite Hs. specialize (G bs Hbs). specialize (P bs Hbs). pose proof (Zlength_nonneg bs).
  pose proof (acct_total n (Zlength bs) ltac:(unfold n; lia) ltac:(lia) ltac:(unfold n; lia)).
  unfold n in *. lia.
Qed.

(** ** The reference code R1 *)

Definition r1_ll : list Z := repeat 9 256 ++ [7; 2] ++ repeat 7 28.   (* literal/length alphabet, 286 codes *)
Definition r1_dl : list Z := repeat 5 30.                             (* distance alphabet, 30 codes *)

Definition kraft15 (lens : list Z) : Z := sumZl (map (fun l => 2 ^ (15 - l)) lens).

Lemma r1_ll_length : Zlength r1_ll = 286.
Proof. reflexivity. Qed.
Lemma r1_dl_length : Zlength r1_dl = 30.
Proof. reflexivity. Qed.

(** Kraft sums scaled by 2^15: 0.9765625 and 0.9375. *)
Lemma r1_ll_kraft : kraft15 r1_ll = 32000.
Proof. vm_compute. reflexivity. Qed.
Lemma r1_dl_kraft : kraft15 r1_dl = 30720.
Proof. vm_compute. reflexivity. Qed.

Lemma r1_ll_range : Forall (fun l => 1 <= l <= 15) r1_ll.
Proof. repeat constructor; lia. Qed.
Lemma r1_dl_range : Forall (fun l => 1 <= l <= 15) r1_dl.
Proof. repeat constructor; lia. Qed.

(** ** Per-symbol cost of a code (the bits send_symbol emits) *)

(** [dist = 0]: literal [lc]; otherwise a match of length [lc + 3] at distance [dist]. *)
Definition sym_bits (llens dlens : list Z) (dist lc : Z) : Z :=
  if dist =? 0 then Znth lc llens
  else
    let code := Znth lc length_code_tab in
    let dc := d_code (dist - 1) in
    Znth (code + LITERALS + 1) llens + Znth code extra_lbits + Znth dc dlens + Znth dc extra_dbits.

Definition sym_bytes (dist lc : Z) : Z := if dist =? 0 then 1 else lc + 3.

Lemma Znth_le_bound : forall (l : list Z) i m, 0 <= m -> Forall (fun x => x <= m) l -> Znth i l <= m.
Proof.
  intros l i m Hm H.
  destruct (Z_lt_le_dec i 0); [assert (Znth i l = 0) by (apply Znth_underflow; lia); lia|].
  destruct (Z_lt_le_dec i (Zlength l)); [apply (Forall_Znth (fun x => x <= m)); auto; lia|].
  assert (Znth i l = 0) by (apply Znth_overflow; lia). lia.
Qed.

Definition sym_check (lc : Z) : bool :=
  (2 * (Znth lc r1_ll - 8) <=? 7 - 5) &&
  (let code := Znth lc length_code_tab in
   2 * (Znth (code + LITERALS + 1) r1_ll + Znth code extra_lbits + 5 + 13 - 8 * (lc + 3)) <=? 7 - 5 * (lc + 3)).

Lemma sym_check_all : forallb sym_check (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

(** The key per-symbol inequality: under R1, [2 * (bits - 8 * bytes) <= 7 - 5 * bytes]. *)
Lemma r1_sym : forall dist lc, 0 <= lc < 256 ->
  2 * (sym_bits r1_ll r1_dl dist lc - 8 * sym_bytes dist lc) <= 7 - 5 * sym_bytes dist lc.
Proof.
  intros dist lc Hlc.
  assert (Hc : sym_check lc = true).
  { pose proof sym_check_all as H. rewrite forallb_forall in H. apply H.
    apply in_map_iff. exists (Z.to_nat lc). split; [lia|]. apply in_seq. lia. }
  unfold sym_check in Hc. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1, H2.
  unfold sym_bits, sym_bytes. destruct (dist =? 0); [lia|].
  assert (Hd1 : Znth (d_code (dist - 1)) r1_dl <= 5)
    by (apply Znth_le_bound; [lia|]; repeat constructor; lia).
  assert (Hd2 : Znth (d_code (dist - 1)) extra_dbits <= 13)
    by (apply Znth_le_bound; [lia|]; repeat constructor; lia).
  cbv zeta in *. lia.
Qed.

(** A block's symbols: (dist, lc) pairs as read from sym_buf. *)
Definition blk_bits (llens dlens : list Z) (syms : list (Z * Z)) : Z :=
  sumZl (map (fun s => sym_bits llens dlens (fst s) (snd s)) syms).
Definition blk_bytes (syms : list (Z * Z)) : Z := sumZl (map (fun s => sym_bytes (fst s) (snd s)) syms).

Lemma r1_blk : forall syms, Forall (fun s => 0 <= snd s < 256) syms ->
  2 * (blk_bits r1_ll r1_dl syms - 8 * blk_bytes syms) <= 7 * Zlength syms - 5 * blk_bytes syms.
Proof.
  induction syms as [|[d lc] r IH]; intros H; [reflexivity|].
  inversion H; subst. specialize (IH H3). simpl in H2. pose proof (r1_sym d lc H2).
  unfold blk_bits, blk_bytes in *. rewrite Zlength_cons. cbn [map sumZl fst snd]. lia.
Qed.

(** The composition bound for a block that cannot be stored ([buf = NULL]): at most 16383 symbols carrying
    at least 32507 bytes.  Including END (7 bits under R1), R1 is at least 23920 bits below [8 * B]. *)
Theorem r1_null_block : forall syms, Forall (fun s => 0 <= snd s < 256) syms ->
  Zlength syms <= 16383 -> 32507 <= blk_bytes syms ->
  blk_bits r1_ll r1_dl syms + Znth END_BLOCK r1_ll - 8 * blk_bytes syms <= -23920.
Proof.
  intros syms H Hn Hb. pose proof (r1_blk syms H). assert (Znth END_BLOCK r1_ll = 7) by reflexivity. lia.
Qed.

(** ** Huffman cost against a reference code *)

(** [HuffAbs.huff_opt] specialised to a reference length per initial item. *)
Corollary huff_le_ref : forall P R D (r : item -> Z), huff P R ->
  (forall I, In I P -> 0 <= weight I) -> (forall I, In I P -> 0 <= r I <= D) ->
  sumZ (map (fun I => 2 ^ (D - r I)) P) <= 2 ^ D ->
  cost R <= sumZ (map (fun I => cost I + weight I * r I) P).
Proof.
  intros P R D r H Hw Hr Hk.
  pose proof (huff_opt P R H D (map (fun I => (I, r I)) P)) as Ho.
  unfold cq, kq in Ho. rewrite !map_map in Ho. cbn [fst snd] in Ho. apply Ho.
  - apply map_id.
  - intros p Hp. apply in_map_iff in Hp as [I [<- HI]]. apply Hr; auto.
  - exact Hk.
  - exact Hw.
Qed.

(** The Kraft sum over a duplicate-free subset of an alphabet is at most the sum over the alphabet. *)
Lemma sumZ_nodup_incl : forall (f : Z -> Z) (l full : list Z), (forall x, 0 <= f x) ->
  NoDup l -> incl l full -> sumZ (map f l) <= sumZ (map f full).
Proof.
  intros f l. induction l as [|x l IH]; intros full Hf Hnd Hi.
  - simpl. apply sumZ_nonneg. intros; apply Hf.
  - inversion Hnd; subst.
    assert (Hx : In x full) by (apply Hi; left; auto).
    apply in_split in Hx as [f1 [f2 ->]].
    assert (Hi' : incl l (f1 ++ f2)).
    { intros y Hy. assert (In y (f1 ++ x :: f2)) by (apply Hi; right; auto).
      apply in_app_or in H. apply in_or_app. destruct H as [H|[H|H]]; auto. subst; contradiction. }
    specialize (IH (f1 ++ f2) Hf H2 Hi').
    rewrite map_app, sumZ_app in IH. rewrite map_app, sumZ_app. simpl. pose proof (Hf x). lia.
Qed.

(** ** The [buf = NULL] block, assembled *)

(** Hypotheses, all about one block with [buf = NULL]:
    - [B = blk_bytes syms >= 32507], at most 16383 symbols (one deflate block);
    - [Lr1] = R1 cost of the data including END;
    - [Ldyn = Hd + Ddyn] is opt_len: tree header [Hd <= 71 + 7 * (286 + 30)] plus data cost [Ddyn];
    - [Ddyn <= Lr1 + 4 + Delta]: Huffman optimality against R1 (the 4 covers a forced distance node), plus the
      length-limit repair overhead [Delta];
    - the chosen tree costs [L <= Ldyn + 7] (static chosen only when [static_lenb <= opt_lenb]).
    Then the block meets the accounting bound as soon as [Delta <= 21600]. *)
Theorem null_block_bound : forall syms Hd Ddyn Delta L,
  Forall (fun s => 0 <= snd s < 256) syms -> Zlength syms <= 16383 -> 32507 <= blk_bytes syms ->
  Hd <= 71 + 7 * (286 + 30) ->
  Ddyn <= blk_bits r1_ll r1_dl syms + Znth END_BLOCK r1_ll + 4 + Delta ->
  L <= Hd + Ddyn + 7 -> Delta <= 21600 ->
  L + 3 <= 8 * blk_bytes syms + 40.
Proof. intros. pose proof (r1_null_block syms H H0 H1). lia. Qed.

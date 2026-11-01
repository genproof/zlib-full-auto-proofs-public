(* Law rfc_level0_blocks (data of any length), main (harness/rfc_level0_blocks.c): the definitions and the pure
   facts of the check of the stored blocks, from `at = head_len` (after `if (code != Z_STREAM_END) return 0;`)
   to main's end, under DCS.CS (the compspecs of main's proof, L0B2MainStmt.v).  The proof is L0B2Loop.v
   (the loop) and L0B2Block.v (one block after its header byte), split for the compile time.

   [l0_seg24] is main's chain of statements (L0B2Kit.v) from its 24th, `at = head_len`, on.  The state there
   ([A_loop]): the output object holds what deflate wrote, the wrapper header H, the stored blocks of the data
   and the trailer (Level0Calls.lf_call at Z_STREAM_END), then bytes deflate did not touch; the copy of the
   data that main made with copy_of before the deflate() calls (expected, at ep) holds the data, and the blocks
   are compared with it; the stream's total_out is at least the end of the blocks.  [part_loop] proves the rest of
   main from it: at block i (0 <= i < blocks) at = |H| + 65540 i and done = 65535 i, and the bytes there are
   [stored_block last d] with d the next min(n - done, 65535) bytes of the data, last = 1 iff i + 1 = blocks
   ([block_at]).  The loop invariant writes at and done for every i <= blocks as |H| + 5 i + min(n, 65535 i)
   and min(n, 65535 i).  The data has at most PTRDIFF_MAX bytes, so every offset stays below
   l0_size < 2^64 (L0Kit2.l0_size_range): no size_t arithmetic of the loop wraps. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.Level0Defs.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2MainStmt.
Require Import Zlib.proof.harness.rfc_level0_blocks.L0B2Kit.
Require Import Zlib.proof.harness.rfc_level0_size.L0Kit2.
Require Zlib.contracts.rfc_level0_blocks.
Require Import Zlib.harness.rfc_level0_blocks.code.
#[local] Existing Instance DCS.CS.

(** ** The stored blocks, block by block *)

(* the blocks after the first i *)
Lemma l0_blocks_sub_nat (n : Z) (k : nat) :
  65535 * Z.of_nat k < n -> l0_blocks n = l0_blocks (n - 65535 * Z.of_nat k) + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros Hn.
  - rewrite Z.mul_0_r, Z.sub_0_r. lia.
  - rewrite Nat2Z.inj_succ in *. rewrite IH by lia.
    rewrite (l0_blocks_step (n - 65535 * Z.of_nat k)) by lia.
    replace (n - 65535 * Z.of_nat k - 65535) with (n - 65535 * Z.succ (Z.of_nat k)) by lia. lia.
Qed.

Lemma l0_blocks_sub (n i : Z) :
  0 <= i -> 65535 * i < n -> l0_blocks n = l0_blocks (n - 65535 * i) + i.
Proof.
  intros Hi Hn. rewrite <- (Z2Nat.id i Hi) in *. apply l0_blocks_sub_nat. exact Hn.
Qed.

(* before the last block, the data is not used up *)
Lemma l0_blocks_lt (n i : Z) :
  0 <= n -> 0 <= i < l0_blocks n -> 65535 * i < n \/ i = 0.
Proof.
  intros Hn Hi. unfold l0_blocks in Hi. destruct (Z.eqb_spec n 0) as [->|Hn0]; [lia|].
  left. assert (i + 1 <= (n + 65534) / 65535) by lia.
  assert (65535 * (i + 1) <= n + 65534); [| lia].
  apply Z.le_trans with (65535 * ((n + 65534) / 65535)); [nia | apply Z.mul_div_le; lia].
Qed.

(* the data is used up after the last block *)
Lemma l0_blocks_cover (n : Z) : 0 <= n -> n <= 65535 * l0_blocks n.
Proof.
  intros Hn. unfold l0_blocks. destruct (Z.eqb_spec n 0) as [->|]; [lia|].
  pose proof (Z.mod_pos_bound (n + 65534) 65535 ltac:(lia)).
  pose proof (Z.div_mod (n + 65534) 65535 ltac:(lia)). lia.
Qed.

(* the first i blocks, then the blocks of the rest of the data *)
Lemma stored_blocks_split_nat (d : list Z) (k : nat) :
  65535 * Z.of_nat k < Zlength d \/ k = O ->
  exists X, Zlength X = 65540 * Z.of_nat k /\
            stored_blocks d = X ++ stored_blocks (sublist (65535 * Z.of_nat k) (Zlength d) d).
Proof.
  induction k as [|k IH]; intros Hk.
  - exists []. split; [reflexivity|]. rewrite Z.mul_0_r, sublist_same by lia. reflexivity.
  - destruct Hk as [Hk|Hk]; [|discriminate]. rewrite Nat2Z.inj_succ in *.
    destruct IH as (X & HX & E); [left; lia|].
    set (r := sublist (65535 * Z.of_nat k) (Zlength d) d) in E.
    assert (Hr : Zlength r = Zlength d - 65535 * Z.of_nat k) by (subst r; rewrite Zlength_sublist; lia).
    rewrite (stored_blocks_eq r) in E. unfold MAX_STORED_LEN in E.
    destruct (Z.leb_spec (Zlength r) 65535) as [|_]; [lia|].
    exists (X ++ stored_block 0 (sublist 0 65535 r)). split.
    + rewrite Zlength_app, Zlength_stored_block, Zlength_sublist by lia. lia.
    + rewrite E, app_assoc. f_equal. f_equal. subst r. rewrite Hr, sublist_sublist by lia. f_equal; lia.
Qed.

(* block i: [stored_block last d] at offset 65540 i of the blocks, d the next min(n - 65535 i, 65535) bytes *)
Definition blen (n i : Z) : Z := Z.min (n - 65535 * i) 65535.
Definition blast (n i : Z) : Z := if i + 1 =? l0_blocks n then 1 else 0.

Lemma block_at (d : list Z) (i : Z) :
  0 <= i < l0_blocks (Zlength d) ->
  exists X Y, Zlength X = 65540 * i /\
    stored_blocks d = X ++ stored_block (blast (Zlength d) i)
                             (sublist (65535 * i) (65535 * i + blen (Zlength d) i) d) ++ Y.
Proof.
  intros Hi. pose proof (Zlength_nonneg d) as Hn.
  pose proof (l0_blocks_lt (Zlength d) i Hn Hi) as Hlt.
  destruct (stored_blocks_split_nat d (Z.to_nat i)) as (X & HX & E).
  { rewrite Z2Nat.id by lia. destruct Hlt as [| ->]; [left; lia | right; reflexivity]. }
  rewrite Z2Nat.id in HX, E by lia.
  set (r := sublist (65535 * i) (Zlength d) d) in E.
  assert (Hr : Zlength r = Zlength d - 65535 * i)
    by (subst r; rewrite Zlength_sublist; [lia | destruct Hlt as [| ->]; lia | lia]).
  rewrite (stored_blocks_eq r) in E. unfold MAX_STORED_LEN in E.
  assert (Hb : l0_blocks (Zlength d) = l0_blocks (Zlength r) + i).
  { destruct Hlt as [Hlt | ->].
    - rewrite Hr. apply l0_blocks_sub; lia.
    - rewrite Hr, Z.mul_0_r, Z.sub_0_r. lia. }
  unfold blast, blen. exists X.
  destruct (Z.leb_spec (Zlength r) 65535) as [Hle|Hgt].
  - exists []. split; [exact HX|].
    rewrite (l0_blocks_one (Zlength r)) in Hb by (pose proof (Zlength_nonneg r); lia).
    rewrite (proj2 (Z.eqb_eq (i + 1) (l0_blocks (Zlength d)))) by lia.
    rewrite Z.min_l by lia. rewrite app_nil_r, E. subst r. f_equal. f_equal. f_equal. lia.
  - exists (stored_blocks (sublist 65535 (Zlength r) r)). split; [exact HX|].
    rewrite (l0_blocks_step (Zlength r)) in Hb by lia.
    pose proof (l0_blocks_pos (Zlength r - 65535) ltac:(lia)).
    rewrite (proj2 (Z.eqb_neq (i + 1) (l0_blocks (Zlength d)))) by lia.
    rewrite Z.min_r by lia. rewrite E. f_equal. f_equal. f_equal.
    subst r. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the output object's bytes at a block [Bk] after [P] *)
Lemma znth_mid (P Bk Q : list Z) (junk : list val) (k : Z) :
  0 <= k < Zlength Bk -> Znth (Zlength P + k) (map vi (P ++ Bk ++ Q) ++ junk) = vi (Znth k Bk).
Proof.
  intros Hk. rewrite Znth_app1 by (rewrite Zlength_map, !Zlength_app; list_solve).
  rewrite Znth_map by (rewrite !Zlength_app; list_solve).
  rewrite Znth_app2 by lia. rewrite Znth_app1 by lia. f_equal. f_equal. lia.
Qed.

Lemma sublist_mid (P Bk Q : list Z) (junk : list val) (lo hi : Z) :
  0 <= lo <= hi -> hi <= Zlength Bk ->
  sublist (Zlength P + lo) (Zlength P + hi) (map vi (P ++ Bk ++ Q) ++ junk) = map vi (sublist lo hi Bk).
Proof.
  intros Hl Hh. rewrite sublist_app1 by (rewrite ?Zlength_map, ?Zlength_app; list_solve).
  rewrite sublist_map. f_equal. list_solve.
Qed.

(* a byte value loaded as an unsigned char *)
Lemma is_int_vi_byte (x : Z) : 0 <= x < 256 -> is_int I8 Unsigned (vi x).
Proof. intros Hx. unfold vi; simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. Qed.

(** ** The suffix of main's body from `at = head_len` (statement 24, L0B2Kit.v) *)

Definition l0_seg24 : statement := ltac:(l0_get_seg 24%nat).

(** ** The state after deflate returned Z_STREAM_END ([l0_seg24], `at = head_len`)

    [out] is what deflate wrote (the wrapper header H, the stored blocks of the data [inb], the trailer T), [junk]
    the rest of the output object of [room] bytes; [tot] the stream's total_out; [Fr] the rest of main's
    resources, which with the total_out field give the local z_stream back at the return ([HC] in
    [part_loop]). *)
Definition A_loop (gv : globals) (vs ep cp : val) (n hl room tot : Z) (inb : list Z) (H T : list Z)
    (junk : list val) (Fr : mpred) : environ -> mpred :=
  PROP ((0 <= n <= 9223372036854775807)%Z; Zlength inb = n; bytes inb; Zlength H = hl; (0 <= hl <= 10)%Z;
        (hl + Zlength (stored_blocks inb) <= tot <= Int64.max_unsigned)%Z;
        (Zlength (H ++ stored_blocks inb ++ T) + Zlength junk = room)%Z; (room <= Int64.max_unsigned)%Z;
        isptr ep; isptr cp)
  LOCAL (temp _data_len (vl n); temp _blocks (vl (l0_blocks n)); temp _head_len (vl hl);
         temp _expected ep; temp _compressed cp; lvar _strm t_strm vs; gvars gv)
  SEP (data_at Ews (tarray tuchar room) (map vi (H ++ stored_blocks inb ++ T) ++ junk) cp;
       data_at Ews (tarray tuchar n) (map vi inb) ep;
       field_at Ews t_strm (DOT _total_out) (vl tot) vs; Fr).

(** ** One block after the check of its header byte (L0B2Block.v)

    [blk_rest] is the rest of the loop body after the first gp_assert of block i: the checks of LEN and NLEN,
    bytes_eq on the block's data, `at += 5 + len; done += len`.  [blk_P] is the state there: at =
    |H| + 65540 i, done = 65535 i, len the block's length; [C] the contents of the output object, [Dv] of the
    copy of the data. *)
Definition blk_rest : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [f_main fn_body] in (fn_body f_main) in
        match x with context [Ssequence (Ssequence (Ssequence (Sset _t'21 _) _) _) ?r] => exact r end).

Definition blk_P (gv : globals) (vs ep cp : val) (n hl room tot B i len : Z) (C Dv : list val) (Fr : mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _len (vl len); temp _i (Vlong (Int64.repr i)); temp _at (vl (hl + 5 * i + 65535 * i));
         temp _done (vl (65535 * i)); temp _data_len (vl n); temp _blocks (vl B); temp _head_len (vl hl);
         temp _expected ep; temp _compressed cp; lvar _strm t_strm vs; gvars gv)
  SEP (data_at Ews (tarray tuchar room) C cp; data_at Ews (tarray tuchar n) Dv ep;
       field_at Ews t_strm (DOT _total_out) (vl tot) vs; Fr).

Definition blk_Q (gv : globals) (vs ep cp : val) (n hl room tot B i len : Z) (C Dv : list val) (Fr : mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _i (Vlong (Int64.repr i)); temp _at (vl (hl + 5 * i + 65535 * i + 5 + len));
         temp _done (vl (65535 * i + len)); temp _data_len (vl n); temp _blocks (vl B); temp _head_len (vl hl);
         temp _expected ep; temp _compressed cp; lvar _strm t_strm vs; gvars gv)
  SEP (data_at Ews (tarray tuchar room) C cp; data_at Ews (tarray tuchar n) Dv ep;
       field_at Ews t_strm (DOT _total_out) (vl tot) vs; Fr).

(* what block i's bytes are: LEN, NLEN (least significant byte first) after the header byte at offset a, then
   the len bytes d, which are also the data's bytes at done = 65535 i *)
Definition blk_ok (n hl room B i len : Z) (C Dv : list val) (d : list Z) : Prop :=
  let a := hl + 5 * i + 65535 * i in
  0 <= n <= 9223372036854775807 /\ 0 <= hl <= 10 /\ 0 <= i < B /\ B <= 140739635871745 /\
  0 <= len <= 65535 /\ 65535 * i + len <= n /\ a + 5 + len <= room /\ room <= Int64.max_unsigned /\
  Znth (a + 1) C = vi (len mod 256) /\ Znth (a + 2) C = vi (len / 256) /\
  Znth (a + 3) C = vi ((65535 - len) mod 256) /\ Znth (a + 4) C = vi ((65535 - len) / 256) /\
  sublist (a + 5) (a + 5 + len) C = map vi d /\ Zlength d = len /\ is_bytes d /\
  sublist (65535 * i) (65535 * i + len) Dv = map vi d.


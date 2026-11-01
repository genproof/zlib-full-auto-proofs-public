(** * Lemma (i), the overlay of sym_buf on pending_buf (CVE-2018-25032): the statement

    With LIT_MEM off, sym_buf = pending_buf + lit_bufsize (L = 2^(memLevel+6)), 3 bytes per symbol, at most
    L - 1 symbols per block; compress_block reads symbol k (bytes L + 3k .. L + 3k + 2) and then writes its code
    bits at pending_buf[pending].  [overlay_statement] says: at the compress_block call of _tr_flush_block (static
    or dynamic trees, as _tr_flush_block decides), after the block header and with the bits left over from the
    previous block, the bit position after k symbols never exceeds 8 * (L + 3k), for every k up to the number of
    symbols; so the writes never reach a symbol byte that is still to be read (zlib's assertion
    [pending < lit_bufsize + sx], see [Bits.pending_from_bits]), the symbols are still intact when compress_block
    starts, and compress_block over the overlaid buffer computes what it computes over a separate symbol list
    ([overlay_compress] below). *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The block at _tr_flush_block *)

(** The literal/length code _tr_tally counts for a symbol (dist, lc): the literal [lc] when [dist = 0], else the
    length code of the match length [lc + 3]. *)
Definition lcode_of (s : Z * Z) : Z :=
  if fst s =? 0 then snd s else Znth (snd s) length_code_tab + LITERALS + 1.

(** The frequencies _tr_tally accumulates for a symbol list (END_BLOCK counted once, by init_block). *)
Definition lfreq (syms : list (Z * Z)) (c : Z) : Z :=
  Zlength (filter (fun s => lcode_of s =? c) syms) + (if c =? END_BLOCK then 1 else 0).
Definition dfreq (syms : list (Z * Z)) (c : Z) : Z :=
  Zlength (filter (fun s => negb (fst s =? 0) && (d_code (fst s - 1) =? c)) syms).

(** The state at the call of _tr_flush_block for a block of symbols [syms] (each a pair (dist, lc) as
    _tr_tally stores it: dist 0 and the literal lc, or the distance 1..32768 and the match length minus 3). *)
Record flush_pre (s : tstate) (syms : list (Z * Z)) : Prop := {
  fp_L : exists ml, 1 <= ml <= 9 /\ tr_lit_bufsize s = 2 ^ (ml + 6);
  fp_out : bits_ok (tr_out s) /\ o_pending (tr_out s) = 0 /\ o_bi_valid (tr_out s) <= 7 /\
           Zlength (o_buf (tr_out s)) = 4 * tr_lit_bufsize s;
  fp_syms : tr_sym_next s = 3 * Zlength syms /\ Zlength syms <= tr_lit_bufsize s - 1 /\
            (forall x, In x syms -> valid_sym (fst x) (snd x)) /\
            (forall i, 0 <= i < 3 * Zlength syms ->
               Znth (tr_lit_bufsize s + i) (o_buf (tr_out s)) = Znth i (sym_bytes syms));
  fp_ltree : Zlength (fc (tr_ltree s)) = HEAP_SIZE /\ Zlength (dl (tr_ltree s)) = HEAP_SIZE /\
             (forall n, 0 <= n < HEAP_SIZE -> 0 <= Znth n (fc (tr_ltree s)) < 65536) /\
             forall c, 0 <= c < L_CODES -> Znth c (fc (tr_ltree s)) = lfreq syms c;
  fp_dtree : Zlength (fc (tr_dtree s)) = 2 * D_CODES + 1 /\ Zlength (dl (tr_dtree s)) = 2 * D_CODES + 1 /\
             (forall n, 0 <= n < 2 * D_CODES + 1 -> 0 <= Znth n (fc (tr_dtree s)) < 65536) /\
             forall c, 0 <= c < D_CODES -> Znth c (fc (tr_dtree s)) = dfreq syms c;
  fp_bltree : Zlength (fc (tr_bltree s)) = 2 * BL_CODES + 1 /\ Zlength (dl (tr_bltree s)) = 2 * BL_CODES + 1 /\
              (forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc (tr_bltree s)) < 65536) /\
              forall c, 0 <= c < BL_CODES -> Znth c (fc (tr_bltree s)) = 0;
  fp_work : Zlength (w_heap (tr_wk s)) = HEAP_SIZE /\ Zlength (w_depth (tr_wk s)) = HEAP_SIZE /\
            Zlength (w_bl_count (tr_wk s)) = MAX_BITS + 1 /\
            w_opt_len (tr_wk s) = 0 /\ w_static_len (tr_wk s) = 0
}.

(** ** The compress_block call of _tr_flush_block *)

(** The first part of _tr_flush_block: the trees, opt_lenb, static_lenb, max_blindex. *)
Definition flush_prep (s : tstate) (stored_len : Z) : tstate * Z * Z * Z :=
  if tr_level s >? 0 then
    let s := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s in
    let '(lt, lmax, w) := build_tree static_l_desc (tr_ltree s) (tr_wk s) in
    let s := set_wk (set_lmax (set_ltree s lt) lmax) w in
    let '(dt, dmax, w) := build_tree static_d_desc (tr_dtree s) (tr_wk s) in
    let s := set_wk (set_dmax (set_dtree s dt) dmax) w in
    let '(s, max_blindex) := build_bl_tree s in
    let opt_lenb := Z.shiftr (u64 (w_opt_len (tr_wk s) + 3 + 7)) 3 in
    let static_lenb := Z.shiftr (u64 (w_static_len (tr_wk s) + 3 + 7)) 3 in
    let opt_lenb := if (static_lenb <=? opt_lenb) || (tr_strategy s =? Z_FIXED) then static_lenb else opt_lenb in
    (s, opt_lenb, static_lenb, max_blindex)
  else (s, u64 (stored_len + 5), u64 (stored_len + 5), 0).

(** The arguments of compress_block (start of the output after the block header; literal/length codes and
    lengths; distance codes and lengths) when _tr_flush_block emits a static or dynamic block; [None] for a
    stored block. *)
Definition flush_call (s : tstate) (buf : option (list Z)) (stored_len last : Z)
    : option (outbuf * list Z * list Z * list Z * list Z) :=
  let '(s, opt_lenb, static_lenb, max_blindex) := flush_prep s stored_len in
  let stat := Some (send_bits (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3,
                    static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len) in
  let dyn := Some (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
                     (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1),
                   fc (tr_ltree s), dl (tr_ltree s), fc (tr_dtree s), dl (tr_dtree s)) in
  match buf with
  | Some _ => if u64 (stored_len + 4) <=? opt_lenb then None else if static_lenb =? opt_lenb then stat else dyn
  | None => if static_lenb =? opt_lenb then stat else dyn
  end.

(** _tr_flush_block in terms of [flush_prep] (definitional). *)
Lemma tr_flush_block_prep : forall s buf stored_len last,
  tr_flush_block s buf stored_len last =
  let '(s, opt_lenb, static_lenb, max_blindex) := flush_prep s stored_len in
  let '(o, kind) :=
    match buf with
    | Some b =>
      if u64 (stored_len + 4) <=? opt_lenb then (tr_stored_block (tr_out s) b stored_len last, BK_stored)
      else if static_lenb =? opt_lenb then
        (compress_block (send_bits (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3) (tr_lit_bufsize s)
           (tr_sym_next s) static_ltree_code static_ltree_len static_dtree_code static_dtree_len, BK_static)
      else
        (compress_block
           (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
              (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1))
           (tr_lit_bufsize s) (tr_sym_next s)
           (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)), BK_dynamic)
    | None =>
      if static_lenb =? opt_lenb then
        (compress_block (send_bits (tr_out s) (Z.shiftl STATIC_TREES 1 + last) 3) (tr_lit_bufsize s)
           (tr_sym_next s) static_ltree_code static_ltree_len static_dtree_code static_dtree_len, BK_static)
      else
        (compress_block
           (send_all_trees (send_bits (tr_out s) (Z.shiftl DYN_TREES 1 + last) 3)
              (tr_ltree s) (tr_dtree s) (tr_bltree s) (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1))
           (tr_lit_bufsize s) (tr_sym_next s)
           (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)), BK_dynamic)
    end in
  let s := init_block (set_out s o) in
  let s := if negb (last =? 0) then set_out s (bi_windup (tr_out s)) else s in
  (s, kind).
Proof. reflexivity. Qed.

(** ** The property at the call *)

(** At a compress_block call [(o, codes)] for the symbols [syms] with the symbol area at offset [L]: the output
    state is sane, the symbols are intact, every code compress_block sends is a proper code, and the bit
    position after the first k symbols is at most 8 * (L + 3k). *)
Definition overlay_ok (L : Z) (syms : list (Z * Z)) (c : outbuf * list Z * list Z * list Z * list Z) : Prop :=
  let '(o, lcodes, llens, dcodes, dlens) := c in
  bits_ok o /\ Zlength (o_buf o) = 4 * L /\
  (forall i, 0 <= i < 3 * Zlength syms -> Znth (L + i) (o_buf o) = Znth i (sym_bytes syms)) /\
  (forall x, In x syms -> sym_codes_ok lcodes llens dcodes dlens (fst x) (snd x)) /\
  code_ok lcodes llens END_BLOCK /\
  forall k, (k <= length syms)%nat ->
    bitpos (compress_sep o lcodes llens dcodes dlens (firstn k syms)) <= 8 * (L + 3 * Z.of_nat k).

(** Lemma (i). *)
Definition overlay_statement : Prop :=
  forall s syms buf stored_len last,
    flush_pre s syms -> 0 <= last <= 1 ->
    forall c, flush_call s buf stored_len last = Some c -> overlay_ok (tr_lit_bufsize s) syms c.

(** ** Consequences at the call *)

(** compress_block over the overlaid buffer = the run over the separate symbol list, and zlib's assertion
    [pending < lit_bufsize + sx] holds after every symbol. *)
Theorem overlay_compress : forall L syms o lcodes llens dcodes dlens,
  (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  overlay_ok L syms (o, lcodes, llens, dcodes, dlens) ->
  compress_block o L (3 * Zlength syms) lcodes llens dcodes dlens =
    send_code (compress_sep o lcodes llens dcodes dlens syms) END_BLOCK lcodes llens /\
  forall m, (1 <= m <= length syms)%nat ->
    o_pending (compress_sep o lcodes llens dcodes dlens (firstn m syms)) < L + 3 * Z.of_nat m.
Proof.
  intros L syms o lcodes llens dcodes dlens Hv [Hok [Hlen [Hsy [Hcodes [Hend Hbits]]]]].
  assert (Hp : forall m, (1 <= m <= length syms)%nat ->
            o_pending (compress_sep o lcodes llens dcodes dlens (firstn m syms)) < L + 3 * Z.of_nat m).
  { intros m Hm. apply pending_from_bits; [exact Hok|intros x Hx; split; auto|lia|apply Hbits; lia|lia]. }
  split; [|exact Hp].
  destruct syms as [|s0 r].
  - rewrite Zlength_nil. apply compress_block_empty.
  - apply compress_block_sep.
    + discriminate.
    + intros x Hx. destruct (Hv x Hx) as [_ H]. lia.
    + exact Hsy.
    + intros m Hm. assert (H := Hp m ltac:(lia)). lia.
Qed.

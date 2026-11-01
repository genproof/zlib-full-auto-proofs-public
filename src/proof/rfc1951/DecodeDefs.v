(* What inflate's state means while it decodes a well-formed stream (Format.v): THE definitions of the decode
   theory.

   The context G: the wrapper, the window bits wb, the history, the blocks, the inflateInit2 windowBits iw, and
   the input src = the stream bytes followed by anything.  The decoder is at a bit position q of src's bits
   (bytes_bits src): c bytes consumed (pos + m_nx), `bits` of them still in the bit buffer, q = 8 c - bits, and
   hold = the value of the bits [q, 8 c) (`hold_ok`).  `at_mode` says, mode by mode, where q is in the stream
   (the block k, the symbol j, the token t, ...), what the state's fields hold (length, offset, extra, lens,
   the tables `tdec` decoding the block's codes, last) and what the output so far is (out: the history
   followed by the bytes produced).  Bounds on bits: below 8, or below what the current read needs (a read
   that ran out of input stops with fewer bits than the element it reads).

   `Kd` is the invariant at every loop head of one inflate() call (Model2.loop2 from Spec5.m_init), relative to
   the call's start (pos: bytes consumed before the call, inp: the bytes offered, ob: the output before the
   call); `dinv` is the invariant between calls.  `group_ok P` (one pass of the switch, Model2.stepf2, from a
   loop head whose mode satisfies P) is what the parts prove, group by group; `leave_why` is why a pass left
   the loop (progress). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Format.
Require Export Zlib.proof.inflate.Model2.
Require Export Zlib.proof.inflate.Inv3.
Require Export Zlib.proof.inflate_api.ApiModel.
Require Zlib.proof.inftrees.ref.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The context                                                                                    *)

Record dctx := DCtx {
  dc_w : wrapper;       (* the wrapper *)
  dc_wb : Z;            (* window bits of the stream (zlib: its header's) *)
  dc_hist : list Z;     (* the history (preset dictionary) *)
  dc_bs : list block;   (* the blocks *)
  dc_iw : Z;            (* inflateInit2's windowBits *)
  dc_src : list Z }.    (* the input: the stream, then anything *)

Definition hdr_bytes (w: wrapper) : list Z :=
  match w with
  | WRaw => []
  | WZlib wb flevel did =>
      zlib_hdr wb flevel (match did with Some _ => true | None => false end) ++
      match did with Some i => be_bytes i 4 | None => [] end
  | WGzip h => gz_bytes h
  end.

Definition wrapped (G: dctx) : bool := match dc_w G with WRaw => false | _ => true end.

(* the gzip headers covered: no extra field, name, comment or header CRC *)
Definition gz_simple (h: gzhdr) : Prop :=
  gz_extra h = None /\ gz_name h = None /\ gz_comment h = None /\ gz_hcrc h = false.

(* inflateInit2's windowBits accepts the stream *)
Definition accepts (G: dctx) : Prop :=
  match dc_w G with
  | WRaw => dc_iw G = - dc_wb G
  | WZlib _ _ _ => dc_iw G = dc_wb G \/ dc_iw G = 0 \/ dc_iw G = 32 + dc_wb G
  | WGzip _ => dc_iw G = 16 + dc_wb G \/ dc_iw G = 32 + dc_wb G
  end.

Definition full (G: dctx) : list Z := expand (dc_hist G) (dc_bs G).
(* the trailer's length in bytes *)
Definition trl_len (w: wrapper) : Z := match w with WRaw => 0 | WZlib _ _ _ => 4 | WGzip _ => 8 end.
Definition slen (G: dctx) : Z := Zlength (stream_bytes (dc_w G) (dc_hist G) (dc_bs G)).

Definition dctx_ok (G: dctx) : Prop :=
  stream_ok (dc_w G) (dc_wb G) (dc_hist G) (dc_bs G) /\ accepts G /\
  (forall h, dc_w G = WGzip h -> gz_simple h) /\
  (forall wb fl did, dc_w G = WZlib wb fl did ->
     did = None \/ did = Some (Zlib.proof.adler32.Model.ref_adler32 1 (dc_hist G))) /\
  slen G <= Zlength (dc_src G) /\ Zlength (dc_src G) <= 2 ^ 31 - 1 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) (dc_hist G) (dc_bs G).

(* ---------------------------------------------------------------------------------------------- *)
(* Positions (absolute bit positions in bytes_bits src)                                           *)

Definition sbits (G: dctx) : list bool := bytes_bits (dc_src G).
Definition D0 (G: dctx) : Z := 8 * Zlength (hdr_bytes (dc_w G)).
Definition nblk (G: dctx) : Z := Zlength (dc_bs G).
Definition blk (G: dctx) (k: Z) : block := nth (Z.to_nat k) (dc_bs G) (Stored []).

(* the position (from the start of the deflate stream at p) of block k *)
Fixpoint epos (p: Z) (bs: list block) (k: nat) : Z :=
  match k, bs with
  | S k', b :: r => epos (p + Zlength (enc_block p false b)) r k'
  | _, _ => p
  end.
Definition bpos (G: dctx) (k: Z) : Z := D0 G + epos 0 (dc_bs G) (Z.to_nat k).
(* the end of the deflate stream (byte-aligned) *)
Definition endpos (G: dctx) : Z := D0 G + Zlength (deflate_bits (dc_bs G)).

(* the output after k blocks; the last flag of block k *)
Definition outk (G: dctx) (k: Z) : list Z := expand (dc_hist G) (firstn (Z.to_nat k) (dc_bs G)).
Definition lastflag (G: dctx) (k: Z) : Z := if k =? nblk G - 1 then 1 else 0.

(* a Huffman block: its codes, symbols, header length (BFINAL, BTYPE and the dynamic header) *)
Definition hb_codes (b: block) : list Z * list Z :=
  match b with
  | Fixed _ => (fixed_ll, fixed_dl)
  | Dynamic nlen ndist _ toks _ => (dyn_ll nlen toks, dyn_dl nlen ndist toks)
  | Stored _ => ([], [])
  end.
Definition hb_syms (b: block) : list sym :=
  match b with Fixed s => s | Dynamic _ _ _ _ s => s | Stored _ => [] end.
Definition hb_hdr (b: block) : Z :=
  match b with
  | Fixed _ => 3
  | Dynamic _ _ clsent toks _ => 17 + 3 * Zlength clsent + Zlength (flat_map (send_tok (cl_lens clsent)) toks)
  | Stored _ => 0
  end.

Definition sym_at (syms: list sym) (j: Z) : sym := nth (Z.to_nat j) syms (Lit 0).
(* the bits of the first j symbols *)
Definition sym_off (ll dl: list Z) (syms: list sym) (j: Z) : Z :=
  Zlength (flat_map (send_one ll dl) (firstn (Z.to_nat j) syms)).
(* the length of the first code of symbol j (the end-of-block code when j = |syms|) *)
Definition sym_first_len (ll: list Z) (syms: list sym) (j: Z) : Z :=
  if j <? Zlength syms then
    match sym_at syms j with Lit b => Znth b ll | Ref len _ => Znth (257 + len_code len) ll end
  else Znth 256 ll.

(* the bits of the first t code length tokens *)
Definition tok_off (cl: list Z) (toks: list cltok) (t: Z) : Z :=
  Zlength (flat_map (send_tok cl) (firstn (Z.to_nat t) toks)).
Definition tok_at (toks: list cltok) (t: Z) : cltok := nth (Z.to_nat t) toks (CLen 0).
Definition toks_upto (toks: list cltok) (t: Z) : list Z := tok_expand [] (firstn (Z.to_nat t) toks).

(* the bit buffer: the bits [8c - bits, 8c) of the input *)
Definition hold_ok (G: dctx) (c hold bits: Z) : Prop :=
  0 <= bits <= 8 * c /\ c <= Zlength (dc_src G) /\
  hold = bval (sublist (8 * c - bits) (8 * c) (sbits G)).

(* ---------------------------------------------------------------------------------------------- *)
(* Tables                                                                                         *)

(* inflate's table walk (Model.lookup1 / lookup2, inflate_fast's): the root entry of the low root bits, a
   link to a second-level entry; (op, val, number of bits) *)
Definition twalk (s: istate) (t: tref) (root pat: Z) : option (Z * Z * Z) :=
  let e := tab_entry lenfix_list distfix_list s t (pat mod 2 ^ root) in
  if ref.is_link (e_op e) then
    let e2 := tab_entry lenfix_list distfix_list s t (e_val e + Z.shiftr pat (e_bits e) mod 2 ^ e_op e) in
    if ref.is_link (e_op e2) then None else Some (e_op e2, e_val e2, e_bits e + e_bits e2)
  else Some (e_op e, e_val e, e_bits e).

(* the table (t, root) of the state decodes the code `lens` of kind `type` (inftrees CODES / LENS / DISTS):
   the bits of every code (the code reversed: sent most significant bit first, read least significant first),
   followed by ANY bits, walk to the entry of its symbol, of its length *)
Definition tdec (s: istate) (t: tref) (root type: Z) (lens: list Z) : Prop :=
  1 <= root <= 15 /\
  (forall sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> forall x, 0 <= x ->
   exists op val,
     twalk s t root (Z.lor (ref.reverse_bits (code lens sy) (Znth sy lens)) (Z.shiftl x (Znth sy lens)))
       = Some (op, val, Znth sy lens) /\
     ref.means_symbol type sy op val = true) /\
  (* a partial read: a pattern that agrees with a code on b < its length bits (the rest anything, e.g. the
     zero bits above `bits` in hold) reaches an entry that needs more than b bits (root entry, or a link and
     its second-level entry) *)
  (forall sy, 0 <= sy < Zlength lens -> Znth sy lens <> 0 -> forall b pat, 0 <= b < Znth sy lens -> 0 <= pat ->
   pat mod 2 ^ b = ref.reverse_bits (code lens sy) (Znth sy lens) mod 2 ^ b ->
   let e := tab_entry lenfix_list distfix_list s t (pat mod 2 ^ root) in
   b < e_bits e \/
   (ref.is_link (e_op e) = true /\
    b < e_bits e + e_bits (tab_entry lenfix_list distfix_list s t (e_val e + Z.shiftr pat (e_bits e) mod 2 ^ e_op e)))) /\
  (* the code length code's table has no links (CODELENS uses lookup1 only) *)
  (type = CODES -> forall i, 0 <= i < 2 ^ root ->
   ref.is_link (e_op (tab_entry lenfix_list distfix_list s t i)) = false).

(* ---------------------------------------------------------------------------------------------- *)
(* Where the decoder is, mode by mode                                                             *)

Section At.
Variables (G: dctx) (s: istate) (q bits: Z) (out: list Z).

(* inside block k *)
Definition in_blk (k: Z) : Prop := 0 <= k < nblk G /\ i_last s = lastflag G k.

(* HEAD: nothing read but the first bytes of the header (raw: nothing); nothing produced (total 0) *)
Definition at_head : Prop :=
  out = dc_hist G /\ q = 0 /\ bits < 16 /\ i_last s = 0 /\ i_total s = 0 /\ (wrapped G = false -> bits < 8) /\
  (* FDICT streams enter the theory after the dictionary (law inflate_dict) *)
  (forall wb fl i, dc_w G = WZlib wb fl (Some i) -> False).

(* gzip header (gz_simple): FLAGS after the 2 magic bytes, TIME after FLG, OS after MTIME *)
Definition at_gzhdr (md: Z) : Prop :=
  exists h, dc_w G = WGzip h /\ out = dc_hist G /\ i_last s = 0 /\ i_total s = 0 /\
  ((md = FLAGS /\ q = 16 /\ bits < 16) \/
   (md = TIME /\ q = 32 /\ bits < 32 /\ i_flags s = 8 + 256 * gz_flg h) \/
   (md = OS /\ q = 64 /\ bits < 16 /\ i_flags s = 8 + 256 * gz_flg h)).

(* TYPE / TYPEDO: at the start of block k (k = nblk: after the last block) *)
Definition at_type : Prop :=
  exists k, 0 <= k <= nblk G /\ q = bpos G k /\ out = outk G k /\ bits < 8 /\
  i_last s = (if k =? 0 then 0 else lastflag G (k - 1)).

(* STORED: after BFINAL and BTYPE of stored block k (or after the padding, with a partial LEN/NLEN) *)
Definition at_stored : Prop :=
  exists k bytes, in_blk k /\ blk G k = Stored bytes /\ out = outk G k /\
  let p := bpos G k + 3 in (q = p /\ bits < 8) \/ (q = p + pad8 p /\ bits mod 8 = 0 /\ bits < 32).

(* COPY_ / COPY: in stored block k, length = the bytes still to copy *)
Definition at_copy : Prop :=
  exists k bytes, in_blk k /\ blk G k = Stored bytes /\
  let p := bpos G k + 3 in let r := i_length s in
  0 <= r <= Zlength bytes /\ bits = 0 /\
  q = p + pad8 p + 32 + 8 * (Zlength bytes - r) /\ out = outk G k ++ sublist 0 (Zlength bytes - r) bytes.

(* TABLE: after BFINAL and BTYPE of dynamic block k *)
Definition at_table : Prop :=
  exists k nlen ndist clsent toks syms, in_blk k /\ blk G k = Dynamic nlen ndist clsent toks syms /\
  out = outk G k /\ q = bpos G k + 3 /\ bits < 14.

(* LENLENS: have code length code lengths read *)
Definition at_lenlens : Prop :=
  exists k nlen ndist clsent toks syms, in_blk k /\ blk G k = Dynamic nlen ndist clsent toks syms /\
  out = outk G k /\ i_nlen s = nlen /\ i_ndist s = ndist /\ i_ncode s = Zlength clsent /\
  0 <= i_have s <= Zlength clsent /\
  (forall i, 0 <= i < i_have s -> Znth (Znth i order) (i_lens s) = Znth i clsent) /\
  q = bpos G k + 17 + 3 * i_have s /\ bits < 8.

(* CODELENS: t tokens read (have = the lengths they give), the code length code's table *)
Definition at_codelens : Prop :=
  exists k nlen ndist clsent toks syms t, in_blk k /\ blk G k = Dynamic nlen ndist clsent toks syms /\
  out = outk G k /\ i_nlen s = nlen /\ i_ndist s = ndist /\ 0 <= t <= Zlength toks /\
  i_have s = Zlength (toks_upto toks t) /\ sublist 0 (i_have s) (i_lens s) = toks_upto toks t /\
  tdec s (i_lencode s) (i_lenbits s) CODES (cl_lens clsent) /\
  q = bpos G k + 17 + 3 * Zlength clsent + tok_off (cl_lens clsent) toks t /\
  (bits < 8 \/ (t < Zlength toks /\ bits < Zlength (send_tok (cl_lens clsent) (tok_at toks t)))).

(* in Huffman block k (fixed or dynamic) before symbol j, at bit p0, its tables in the state *)
Definition in_huff (k j: Z) (ll dl: list Z) (syms: list sym) (p0: Z) : Prop :=
  in_blk k /\
  ((blk G k = Fixed syms /\ ll = fixed_ll /\ dl = fixed_dl) \/
   (exists nlen ndist clsent toks, blk G k = Dynamic nlen ndist clsent toks syms /\
      ll = dyn_ll nlen toks /\ dl = dyn_dl nlen ndist toks)) /\
  0 <= j <= Zlength syms /\
  tdec s (i_lencode s) (i_lenbits s) LENS ll /\ tdec s (i_distcode s) (i_distbits s) DISTS dl /\
  p0 = bpos G k + hb_hdr (blk G k) + sym_off ll dl syms j.

Definition outj (k: Z) (syms: list sym) (j: Z) : list Z := syms_data (outk G k) (firstn (Z.to_nat j) syms).

(* LEN_ / LEN: before symbol j (j = |syms|: the end-of-block code) *)
Definition at_len : Prop :=
  exists k j ll dl syms p0, in_huff k j ll dl syms p0 /\ out = outj k syms j /\ q = p0 /\
  (bits < 8 \/ bits < sym_first_len ll syms j).

(* LENEXT: symbol j is a reference, its length code read *)
Definition at_lenext : Prop :=
  exists k j ll dl syms p0 len dist, in_huff k j ll dl syms p0 /\ j < Zlength syms /\
  sym_at syms j = Ref len dist /\ out = outj k syms j /\
  let i := len_code len in
  i_length s = Znth i len_base /\ i_extra s = Znth i len_extra /\
  q = p0 + Zlength (send_sym ll (257 + i)) /\ (bits < 8 \/ bits < Znth i len_extra).

(* DIST: the length and its extra bits read *)
Definition at_dist : Prop :=
  exists k j ll dl syms p0 len dist, in_huff k j ll dl syms p0 /\ j < Zlength syms /\
  sym_at syms j = Ref len dist /\ out = outj k syms j /\
  let i := len_code len in
  i_length s = len /\ q = p0 + Zlength (send_sym ll (257 + i)) + Znth i len_extra /\
  (bits < 8 \/ bits < Znth (dist_code dist) dl).

(* DISTEXT: the distance code read *)
Definition at_distext : Prop :=
  exists k j ll dl syms p0 len dist, in_huff k j ll dl syms p0 /\ j < Zlength syms /\
  sym_at syms j = Ref len dist /\ out = outj k syms j /\
  let i := len_code len in let d := dist_code dist in
  i_length s = len /\ i_offset s = Znth d dist_base /\ i_extra s = Znth d dist_extra /\
  q = p0 + Zlength (send_sym ll (257 + i)) + Znth i len_extra + Znth d dl /\
  (bits < 8 \/ bits < Znth d dist_extra).

(* MATCH: the reference read, length = the bytes still to copy *)
Definition at_match : Prop :=
  exists k j ll dl syms p0 len dist, in_huff k j ll dl syms p0 /\ j < Zlength syms /\
  sym_at syms j = Ref len dist /\
  i_offset s = dist /\ 1 <= i_length s <= len /\
  out = lz_copy (Z.to_nat (len - i_length s)) dist (outj k syms j) /\
  q = p0 + Zlength (send_one ll dl (Ref len dist)) /\ bits < 8.

(* LIT: the literal read, not yet written *)
Definition at_lit : Prop :=
  exists k j ll dl syms p0 b, in_huff k j ll dl syms p0 /\ j < Zlength syms /\
  sym_at syms j = Lit b /\ i_length s = b /\ out = outj k syms j /\
  q = p0 + Zlength (send_sym ll b) /\ bits < 8.

(* CHECK: after the last block (byte-aligned), a partial trailer in the bit buffer *)
Definition at_check : Prop :=
  out = full G /\ i_last s = 1 /\ q = endpos G /\ bits mod 8 = 0 /\ bits < 32 /\ (wrapped G = false -> bits = 0).
(* LENGTH (gzip): after the CRC-32 *)
Definition at_length : Prop :=
  out = full G /\ i_last s = 1 /\ q = endpos G + 32 /\ bits mod 8 = 0 /\ bits < 32 /\
  (exists h, dc_w G = WGzip h).
(* DONE: exactly the stream consumed *)
Definition at_done : Prop :=
  out = full G /\ i_last s = 1 /\ q = 8 * slen G /\ bits = 0.

End At.

Definition at_mode (G: dctx) (s: istate) (c hold bits: Z) (out: list Z) : Prop :=
  let md := i_mode s in let q := 8 * c - bits in
  hold_ok G c hold bits /\
  ((md = HEAD /\ at_head G s q bits out) \/
   ((md = FLAGS \/ md = TIME \/ md = OS) /\ at_gzhdr G s q bits out md) \/
   ((md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO) /\ at_type G s q bits out) \/
   (md = STORED /\ at_stored G s q bits out) \/
   ((md = COPY_ \/ md = COPY) /\ at_copy G s q bits out) \/
   (md = TABLE /\ at_table G s q bits out) \/
   (md = LENLENS /\ at_lenlens G s q bits out) \/
   (md = CODELENS /\ at_codelens G s q bits out) \/
   ((md = LEN_ \/ md = LEN) /\ at_len G s q bits out) \/
   (md = LENEXT /\ at_lenext G s q bits out) \/
   (md = DIST /\ at_dist G s q bits out) \/
   (md = DISTEXT /\ at_distext G s q bits out) \/
   (md = MATCH /\ at_match G s q bits out) \/
   (md = LIT /\ at_lit G s q bits out) \/
   (md = CHECK /\ at_check G s q bits out) \/
   (md = LENGTH /\ at_length G s q bits out) \/
   (md = DONE /\ at_done G s q bits out)).

(* ---------------------------------------------------------------------------------------------- *)
(* The state beyond the position: wrapper, window, check value                                    *)

(* the window byte at distance d back (MATCH / inflate_fast) *)
Definition win_at (s: istate) (d: Z) : Z :=
  if d <=? i_wnext s then Znth (i_wnext s - d) (i_wdata s) else Znth (i_wsize s - (d - i_wnext s)) (i_wdata s).

(* the window holds the last min(|ob|, wsize) bytes of ob (the output before the call, history included),
   wsize = 2^wbits >= 2^wb; or it is not allocated yet and there is no output (nor history) *)
Definition win_ok (G: dctx) (s: istate) (ob: list Z) : Prop :=
  (i_wsize s = 0 /\ ob = []) \/
  (i_wsize s = 2 ^ i_wbits s /\ i_whave s = Z.min (Zlength ob) (i_wsize s) /\
   forall d, 1 <= d <= i_whave s -> win_at s d = Znth (Zlength ob - d) ob).

(* the wrapper's check of the data d *)
Definition chkv (G: dctx) (d: list Z) : Z :=
  match dc_w G with
  | WZlib _ _ _ => Zlib.proof.adler32.Model.ref_adler32 1 d
  | WGzip _ => Zlib.proof.crc32.Model.ref_crc32 0 d
  | WRaw => 0
  end.
(* the data part of the output *)
Definition produced (G: dctx) (out: list Z) : list Z := sublist (Zlength (dc_hist G)) (Zlength out) out.

(* the wrap and wbits inflateInit2 stores for its windowBits iw: those of reset2_wb, with bit 3 of wrap set when
   the window size comes from the header (wbits 0; inflateReset2 of patch F8, ApiModel.reset2_wrap) *)
Definition init_wrap_wb (iw: Z) : option (Z * Z) :=
  match reset2_wb iw with Some (wrap, wb) => Some (reset2_wrap wrap wb, wb) | None => None end.

Lemma init_wrap_wb_of iw wrap wb : reset2_wb iw = Some (wrap, wb) -> init_wrap_wb iw = Some (reset2_wrap wrap wb, wb).
Proof. intros E. unfold init_wrap_wb. rewrite E. reflexivity. Qed.

Lemma init_wrap_wb_inv iw w wb : init_wrap_wb iw = Some (w, wb) ->
  exists wrap, reset2_wb iw = Some (wrap, wb) /\ w = reset2_wrap wrap wb.
Proof.
  unfold init_wrap_wb. destruct (reset2_wb iw) as [[wrap b]|]; intros E; [|discriminate].
  inversion E. eauto.
Qed.

(* bit 3 aside, the stored wrap is reset2_wb's: the same bits 0..2 (bit 2: check the trailer), 0 for raw only *)
Lemma init_wrap_wb_bits iw w wb : init_wrap_wb iw = Some (w, wb) ->
  exists wrap, reset2_wb iw = Some (wrap, wb) /\ w = reset2_wrap wrap wb /\
    Z.land w 7 = wrap /\ Z.land w 4 = Z.land wrap 4 /\ (w = 0 <-> wrap = 0).
Proof.
  intros E. destruct (init_wrap_wb_inv _ _ _ E) as (wrap & R & ->). exists wrap.
  split; [exact R|]. split; [reflexivity|]. unfold reset2_wrap.
  destruct (reset2_wb_cases _ _ _ R) as [(-> & B)|(A & B)].
  - replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv. tauto.
  - assert (C: wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
    destruct (wb =? 0); destruct C as [-> | [-> | ->]]; cbv; (split; [reflexivity|split; [reflexivity|]]);
      split; intros X; discriminate X.
Qed.

(* the fixed fields: wrap, no gz_header, wbits (before the header: as inflateInit2 set it; after: >= wb) *)
Definition glob_ok (G: dctx) (s: istate) : Prop :=
  (exists wb0, init_wrap_wb (dc_iw G) = Some (i_wrap s, wb0) /\
     (i_mode s = HEAD -> i_wbits s = wb0)) /\
  i_head s = false /\
  (i_mode s <> HEAD -> dc_wb G <= i_wbits s <= 15) /\
  (wrapped G = true -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
     i_flags s = match dc_w G with WGzip h => 8 + 256 * gz_flg h | _ => 0 end).

(* the check value and total: of the data produced before the call (ob), up to CHECK; of all the data
   afterwards (CHECK computes it over ob ++ ow) *)
Definition chk_ok (G: dctx) (s: istate) (ob ow: list Z) : Prop :=
  wrapped G = true -> i_mode s <> HEAD -> i_mode s <> FLAGS -> i_mode s <> TIME -> i_mode s <> OS ->
  let d := if (i_mode s =? LENGTH) || (i_mode s =? DONE) then produced G (ob ++ ow) else produced G ob in
  i_check s = chkv G d /\ i_total s = Zlength d mod 2 ^ 64 /\
  (* v4: the output starts with the history (a preset dictionary: zlib FDICT) *)
  (exists d', ob = dc_hist G ++ d').

(* ---------------------------------------------------------------------------------------------- *)
(* The invariants                                                                                 *)

Definition after_check (G: dctx) (md: Z) : bool := wrapped G && ((md =? LENGTH) || (md =? DONE)).

(* at a loop head of a call (and at its exit): pos bytes consumed before the call, inp offered, ob the output
   before the call *)
Record Kd (G: dctx) (pos: Z) (inp ob: list Z) (m: mst) : Prop := {
  kd_inp : m_inp m = inp;
  kd_at : at_mode G (m_s m) (pos + m_nx m) (m_hold m) (m_bits m) (ob ++ m_ow m);
  kd_glob : glob_ok G (m_s m);
  kd_win : m_mode m < CHECK -> win_ok G (m_s m) ob;
  kd_chk : chk_ok G (m_s m) ob (m_ow m);
  (* tout: the data before the call; after CHECK, with the call's output (CHECK counted it, out = left) *)
  kd_tout : m_tout m = Zlength (produced G (if after_check G (m_mode m) then ob ++ m_ow m else ob)) mod 2 ^ 64;
  kd_out : if after_check G (m_mode m) then m_out m = m_left m else m_out m = m_aout m;
  kd_ret : m_ret m = (if (m_mode m =? DONE) && (m_leave m =? 1) then Z_STREAM_END else Z_OK) }.

(* between calls: the state s, total_out tout, pos bytes consumed, out the output (history included) *)
Definition dinv (G: dctx) (pos: Z) (out: list Z) (s: istate) (tout: Z) : Prop :=
  at_mode G s pos (i_hold s) (i_bits s) out /\ glob_ok G s /\
  (i_mode s < CHECK -> win_ok G s out) /\ chk_ok G s out [] /\
  tout = Zlength (produced G out) mod 2 ^ 64.

(* why a pass left the loop: out of input (and the stream not finished), out of output space (and data left),
   Z_BLOCK / Z_TREES at a block boundary or after a header, or the end *)
Definition leave_why (G: dctx) (pos: Z) (inp ob: list Z) (flush: Z) (m: mst) : Prop :=
  m_mode m = DONE \/
  (m_nx m = Zlength inp /\ pos + Zlength inp < slen G) \/
  (m_left m = 0 /\ Zlength (ob ++ m_ow m) < Zlength (full G)) \/
  (flush = Z_BLOCK \/ flush = Z_TREES).

(* what one pass of the switch gives from a loop head: no return (no Z_NEED_DICT, Z_MEM_ERROR, error), the
   invariant, the output only grows, and the reason when it leaves *)
Definition dstep_post (G: dctx) (pos: Z) (inp ob: list Z) (flush: Z) (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kd G pos inp ob m' /\ (exists d, m_ow m' = m_ow m ++ d) /\
               (m_leave m' = 1 -> leave_why G pos inp ob flush m')
  | IRet _ _ => False
  end.

Definition group_ok (P: Z -> Prop) : Prop :=
  forall G pos inp ob flush m,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> P (m_mode m) ->
    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).

(* the groups of modes *)
Definition md_hdr (md: Z) : Prop := md = HEAD \/ md = FLAGS \/ md = TIME \/ md = OS.
Definition md_type (md: Z) : Prop :=
  md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO \/ md = STORED \/ md = COPY_ \/ md = COPY.
Definition md_tab (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS.
Definition md_dec (md: Z) : Prop :=
  md = LEN_ \/ md = LEN \/ md = LENEXT \/ md = DIST \/ md = DISTEXT \/ md = MATCH \/ md = LIT.
Definition md_trl (md: Z) : Prop := md = CHECK \/ md = LENGTH \/ md = DONE.

(* LEN's fast path (inflate_fast from a loop head at LEN with >= 6 input bytes, >= 258 output bytes, bits < 8)
   and `if (state->mode == TYPE) state->back = -1;` *)
Definition dfast_stmt : Prop :=
  forall G pos inp ob m,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    let m' := fast lenfix_list distfix_list (restore m) in
    let m' := if m_mode m' =? Zlib.proof.inflate.Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m' in
    Kd G pos inp ob m' /\ m_leave m' = 0 /\ (exists d, m_ow m' = m_ow m ++ d) /\
    (m_mode m' = LEN \/ m_mode m' = Zlib.proof.inflate.Model.TYPE).

(* ---------------------------------------------------------------------------------------------- *)
(* The kit: facts about the bit buffer and the layout of the stream, shared by the parts            *)

Record dkit_stmt : Prop := {
  (* PULLBYTE *)
  dk_pull : forall G c hold bits, hold_ok G c hold bits -> c < Zlength (dc_src G) -> bits + 8 <= 64 ->
    bytes_ok (dc_src G) ->
    hold_ok G (c + 1) ((hold + Znth c (dc_src G) * 2 ^ bits) mod 2 ^ 64) (bits + 8);
  (* BITS(n) *)
  dk_bitsn : forall G c hold bits n, hold_ok G c hold bits -> 0 <= n <= bits ->
    hold mod 2 ^ n = bval (sublist (8 * c - bits) (8 * c - bits + n) (sbits G));
  (* DROPBITS(n) *)
  dk_drop : forall G c hold bits n, hold_ok G c hold bits -> 0 <= n <= bits ->
    hold_ok G c (Z.shiftr hold n) (bits - n);
  (* the hold is below 2^bits *)
  dk_hold_lt : forall G c hold bits, hold_ok G c hold bits -> bytes_ok (dc_src G) -> 0 <= hold < 2 ^ bits;
  (* the layout of the input *)
  dk_hdr : forall G, dctx_ok G -> sublist 0 (D0 G) (sbits G) = bytes_bits (hdr_bytes (dc_w G));
  dk_deflate : forall G, dctx_ok G -> sublist (D0 G) (endpos G) (sbits G) = deflate_bits (dc_bs G);
  dk_blk : forall G k, dctx_ok G -> 0 <= k < nblk G ->
    bpos G (k + 1) = bpos G k + Zlength (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) /\
    sublist (bpos G k) (bpos G (k + 1)) (sbits G) = enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k);
  dk_bpos0 : forall G, bpos G 0 = D0 G;
  dk_end : forall G, dctx_ok G -> endpos G = bpos G (nblk G) + pad8 (bpos G (nblk G)) /\
    sublist (bpos G (nblk G)) (endpos G) (sbits G) = zeros (pad8 (bpos G (nblk G)));
  dk_D0 : forall G, D0 G mod 8 = 0;
  dk_slen : forall G, dctx_ok G -> endpos G + 8 * trl_len (dc_w G) = 8 * slen G;
  (* the trailer: zlib the big-endian Adler-32 of the data, gzip the CRC-32 and the length; the end *)
  dk_trailer : forall G, dctx_ok G ->
    endpos G mod 8 = 0 /\
    sublist (endpos G / 8) (slen G) (dc_src G) =
      match dc_w G with
      | WRaw => []
      | WZlib _ _ _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 (produced G (full G))) 4
      | WGzip _ => le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (produced G (full G))) 4 ++
                   le_bytes (Zlength (produced G (full G)) mod 2 ^ 32) 4
      end;
  (* the output block by block *)
  dk_outk : forall G k, 0 <= k < nblk G -> outk G (k + 1) = block_data (outk G k) (blk G k);
  dk_outk0 : forall G, outk G 0 = dc_hist G;
  dk_full : forall G, outk G (nblk G) = full G;
  dk_full_len : forall G k, 0 <= k <= nblk G -> Zlength (outk G k) <= Zlength (full G) /\
    exists rest, full G = outk G k ++ rest;
  dk_produced : forall G d, produced G (dc_hist G ++ d) = d
}.

(* ---------------------------------------------------------------------------------------------- *)
(* The tables inflate builds decode the codes (the bridge to inftrees' fact_decode)                 *)

Record tabdec_stmt : Prop := {
  (* the fixed tables *)
  td_fixed : forall s, tdec s TLenfix 9 LENS fixed_ll /\ tdec s TDistfix 5 DISTS fixed_dl;
  (* LENLENS: the code length code (19 lengths at lens[0..19), next = 0) *)
  td_cl : forall s,
    i_next s = 0 -> Zlength (i_lens s) = 320 -> Zlength (i_codes s) = ENOUGH_CODES ->
    Forall entry_ok (i_codes s) -> cl_code_ok (sublist 0 19 (i_lens s)) ->
    let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
    r = 0 /\ forall s', i_codes s' = codes -> tdec s' (TCodes 0) lb CODES (sublist 0 19 (i_lens s));
  (* CODELENS: the literal/length table at 0, then the distance table after it *)
  td_lld : forall s nlen ndist,
    257 <= nlen <= 286 -> 1 <= ndist <= 30 ->
    i_next s = 0 -> Zlength (i_lens s) = 320 -> Zlength (i_codes s) = ENOUGH_CODES ->
    Forall entry_ok (i_codes s) ->
    ll_code_ok (sublist 0 nlen (i_lens s)) -> dl_code_ok (sublist nlen (nlen + ndist) (i_lens s)) ->
    let '(r1, codes1, nxt1, lb) := call_table LENS 0 nlen 9 s in
    r1 = 0 /\
    let s1 := set_i_next (set_i_codes s codes1) nxt1 in
    let '(r2, codes2, nxt2, db) := call_table DISTS nlen ndist 6 s1 in
    r2 = 0 /\ forall s', i_codes s' = codes2 ->
      tdec s' (TCodes 0) lb LENS (sublist 0 nlen (i_lens s)) /\
      tdec s' (TCodes nxt1) db DISTS (sublist nlen (nlen + ndist) (i_lens s))
}.

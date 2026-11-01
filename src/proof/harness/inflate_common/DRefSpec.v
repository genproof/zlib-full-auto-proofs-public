(* harness/deflate_ref.h (the reference DEFLATE encoder of the inflate laws) and inflate_decode.c's dyn_header:
   THE specifications, against the abstract format src/proof/rfc1951/Format.v.

   - the bit writer `struct bw` holds the bits B written so far: buf[0 .. |pack B|) = pack B (the last byte, when
     |B| is not a multiple of 8, holds the pending bits, zero above them), len = |B| / 8, nb = |B| mod 8; the
     buffer is the object at buf (cap bytes; the bytes from |pack B| on are anything) (`bw_bytes_ok`);
   - every writer appends to B: bw_bit (1 bit), bw_bits (Format.bits_le), bw_code (Format.bits_msb), bw_byte
     (8 bits at a byte boundary), bw_align (Format.zeros (pad8 |B|)), bw_fixed (Format.send_sym fixed_ll),
     bw_fixed_match (Format.send_one fixed_ll fixed_dl (Ref len dist));
   - len_code / dist_code return Format.len_code / dist_code (they read the static tables ref_lbase / ref_dbase,
     whose Clight identifiers carry the harness's name: the specs take them as parameters `ti`);
   - canonical: Format.code mod 2^16 (0 for an unused symbol); kraft: Format.kraft_sum and nused; code_ok:
     `code_okb`;
   - dyn_header (inflate_decode.c): either it blocks (a gp_assume fails) or it wrote the header of a dynamic
     block (`dyn_hdr_bits`) for some well-formed (`dyn_hdr_ok`) code length code and tokens, the lengths in ll and
     the canonical codes in lcodes / dcodes.

   The specifications are at the compspecs of inflate_decode's harness unit (struct bw); move them to a law's
   compspecs with change_composite_env (as HarnessLib.v).  The functions bw_* / canonical / kraft / code_ok have
   the same Clight in every harness that includes deflate_ref.h; len_code, dist_code and bw_fixed_match read the
   tables through the harness's identifiers (`dref_tabs`). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Export Zlib.proof.rfc1951.Format.
Require Zlib.harness.x_inflate_decode.code.
Require Zlib.contracts.x_inflate_decode.
Module HD := Zlib.harness.x_inflate_decode.code.

#[local] Existing Instance Zlib.contracts.x_inflate_decode.Harness.CS.

Definition t_bw : type := Tstruct HD._bw noattr.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure values                                                                                    *)

(* the bytes of the buffer: pack B, then anything *)
Definition bw_bytes_ok (B: list bool) (cap: Z) (contents: list val) : Prop :=
  Zlength contents = cap /\ Zlength (pack B) <= cap /\ sublist 0 (Zlength (pack B)) contents = bytes_rep (pack B).

(* the struct: buf, len = |B| / 8, nb = |B| mod 8 *)
Definition bw_rep (sh: share) (B: list bool) (buf: val) (w: val) : mpred :=
  data_at sh t_bw (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w.

(* the bit writer with its buffer object *)
Definition bw_at (sh bsh: share) (B: list bool) (cap: Z) (buf: val) (w: val) : mpred :=
  EX contents: list val, !! bw_bytes_ok B cap contents &&
  (bw_rep sh B buf w * data_at bsh (tarray tuchar cap) contents buf).

(* room for k more bits (and the struct's counters in range) *)
Definition bw_room (B: list bool) (cap k: Z) : Prop :=
  0 <= k /\ (Zlength B + k + 7) / 8 <= cap /\ cap <= Int.max_unsigned.

(* canonical: the code of symbol i, 16 bits, 0 when unused *)
Definition canon_val (lens: list Z) (i: Z) : Z := if Znth i lens =? 0 then 0 else code lens i mod 65536.
Definition canon_vals (lens: list Z) : list Z := map (fun i => canon_val lens (Z.of_nat i)) (seq 0 (length lens)).

(* code_ok(lens, n, type) *)
Definition code_okb (type: Z) (lens: list Z) : bool :=
  (kraft_sum lens =? 32768) ||
  (negb (type =? 0) && (nused lens =? 1) && (kraft_sum lens =? 16384)) ||
  ((type =? 2) && (nused lens =? 0)).

(* the header of a dynamic block after BFINAL and BTYPE, as dyn_header writes it *)
Definition dyn_hdr_bits (nlen ndist: Z) (clsent: list Z) (toks: list cltok) : list bool :=
  bits_le (nlen - 257) 5 ++ bits_le (ndist - 1) 5 ++ bits_le (Zlength clsent - 4) 4 ++
  flat_map (fun c => bits_le c 3) clsent ++ flat_map (send_tok (cl_lens clsent)) toks.

(* what dyn_header guarantees: all 19 code length code lengths sent, Format.block_ok's conditions on the codes *)
Definition dyn_hdr_ok (nlen ndist: Z) (clsent: list Z) (toks: list cltok) : Prop :=
  Zlength clsent = 19 /\ Forall (fun c => 0 <= c <= 7) clsent /\ cl_code_ok (cl_lens clsent) /\
  toks_ok (cl_lens clsent) [] toks /\ Zlength (dyn_lens toks) = nlen + ndist /\
  ll_code_ok (dyn_ll nlen toks) /\ dl_code_ok (dyn_dl nlen ndist toks).

(* ---------------------------------------------------------------------------------------------- *)
(* The static tables of deflate_ref.h (identifiers of the harness: ti = (lbase, lext, dbase, dext))   *)

Definition zvals (l: list Z) : list val := map (fun x => Vint (Int.repr x)) l.

Definition dref_tabs (gv: globals) (sh: share) (ti: ident * ident * ident * ident) : mpred :=
  let '(ilb, ile, idb, ide) := ti in
  (data_at sh (tarray tushort 29) (zvals len_base) (gv ilb) *
   data_at sh (tarray tuchar 29) (zvals len_extra) (gv ile) *
   data_at sh (tarray tushort 30) (zvals dist_base) (gv idb) *
   data_at sh (tarray tuchar 30) (zvals dist_extra) (gv ide))%logic.

(* inflate_decode's identifiers *)
Definition id_tabs : ident * ident * ident * ident :=
  (HD._x_inflate_decode__ref_lbase, HD._x_inflate_decode__ref_lext, HD._x_inflate_decode__ref_dbase,
   HD._x_inflate_decode__ref_dext).

(* ---------------------------------------------------------------------------------------------- *)
(* The bit writer                                                                                 *)

Definition bw_bit_spec :=
  DECLARE HD._bw_bit
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, b: Z
  PRE [ tptr t_bw, tuint ]
    PROP (writable_share sh; writable_share bsh; bw_room B cap 1; 0 <= b <= Int.max_unsigned)
    PARAMS (w; Vint (Int.repr b))
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ [Z.odd b]) cap buf w).

Definition bw_bits_spec :=
  DECLARE HD._bw_bits
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, v: Z, n: Z
  PRE [ tptr t_bw, tuint, tuint ]
    PROP (writable_share sh; writable_share bsh; 0 <= n <= 32; bw_room B cap n; 0 <= v <= Int.max_unsigned)
    PARAMS (w; Vint (Int.repr v); Vint (Int.repr n))
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ bits_le v n) cap buf w).

Definition bw_code_spec :=
  DECLARE HD._bw_code
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, c: Z, n: Z
  PRE [ tptr t_bw, tuint, tuint ]
    PROP (writable_share sh; writable_share bsh; 0 <= n <= 32; bw_room B cap n; 0 <= c <= Int.max_unsigned)
    PARAMS (w; Vint (Int.repr c); Vint (Int.repr n))
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ bits_msb c n) cap buf w).

Definition bw_byte_spec :=
  DECLARE HD._bw_byte
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, b: Z
  PRE [ tptr t_bw, tuchar ]
    PROP (writable_share sh; writable_share bsh; Zlength B mod 8 = 0; bw_room B cap 8; 0 <= b <= 255)
    PARAMS (w; Vint (Int.repr b))
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ bits_le b 8) cap buf w).

Definition bw_align_spec :=
  DECLARE HD._bw_align
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val
  PRE [ tptr t_bw ]
    PROP (writable_share sh; writable_share bsh; bw_room B cap 0)
    PARAMS (w)
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ zeros (pad8 (Zlength B))) cap buf w).

(* the fixed literal/length code of v < 288 *)
Definition bw_fixed_spec :=
  DECLARE HD._bw_fixed
  WITH sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, v: Z
  PRE [ tptr t_bw, tuint ]
    PROP (writable_share sh; writable_share bsh; 0 <= v < 288; bw_room B cap 9)
    PARAMS (w; Vint (Int.repr v))
    SEP (bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN () SEP (bw_at sh bsh (B ++ send_sym fixed_ll v) cap buf w).

Definition len_code_spec (ti: ident * ident * ident * ident) :=
  DECLARE HD._len_code
  WITH gv: globals, tsh: share, len: Z
  PRE [ tuint ]
    PROP (readable_share tsh; 3 <= len <= 258)
    PARAMS (Vint (Int.repr len)) GLOBALS (gv)
    SEP (dref_tabs gv tsh ti)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (len_code len))) SEP (dref_tabs gv tsh ti).

Definition dist_code_spec (ti: ident * ident * ident * ident) :=
  DECLARE HD._dist_code
  WITH gv: globals, tsh: share, dist: Z
  PRE [ tuint ]
    PROP (readable_share tsh; 1 <= dist <= 32768)
    PARAMS (Vint (Int.repr dist)) GLOBALS (gv)
    SEP (dref_tabs gv tsh ti)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (dist_code dist))) SEP (dref_tabs gv tsh ti).

(* a back-reference with the fixed codes (at most 8 + 5 + 5 + 13 = 31 bits) *)
Definition bw_fixed_match_spec (ti: ident * ident * ident * ident) :=
  DECLARE HD._bw_fixed_match
  WITH gv: globals, tsh: share, sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, len: Z, dist: Z
  PRE [ tptr t_bw, tuint, tuint ]
    PROP (readable_share tsh; writable_share sh; writable_share bsh; 3 <= len <= 258; 1 <= dist <= 32768;
          bw_room B cap 31)
    PARAMS (w; Vint (Int.repr len); Vint (Int.repr dist)) GLOBALS (gv)
    SEP (dref_tabs gv tsh ti; bw_at sh bsh B cap buf w)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (dref_tabs gv tsh ti; bw_at sh bsh (B ++ send_one fixed_ll fixed_dl (Ref len dist)) cap buf w).

(* ---------------------------------------------------------------------------------------------- *)
(* Codes                                                                                          *)

(* canonical(lens, n, codes): lens = the slice [lo, lo + n) of an object (Bytes.cbuf_ok), lengths <= 15; codes
   = an object of K >= n unsigned shorts; codes[0 .. n) := canon_vals lens *)
Definition canonical_spec :=
  DECLARE HD._canonical
  WITH lbuf: val, lsh: share, lp: val, lo: Z, ln: Z, lcont: list val, n: Z, lens: list Z,
       csh: share, cp: val, K: Z, ccont: list val
  PRE [ tptr tuchar, tuint, tptr tushort ]
    PROP (readable_share lsh; writable_share csh; 0 <= n <= 316; n <= K; Zlength ccont = K;
          cbuf_ok false lbuf lsh lp lo ln n lcont lens; Forall (fun l => 0 <= l <= 15) lens)
    PARAMS (lbuf; Vint (Int.repr n); cp)
    SEP (data_at lsh (tarray tuchar ln) lcont lp; data_at csh (tarray tushort K) ccont cp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at lsh (tarray tuchar ln) lcont lp;
         data_at csh (tarray tushort K) (zvals (canon_vals lens) ++ sublist n K ccont) cp).

(* kraft(lens, n, &used) *)
Definition kraft_spec :=
  DECLARE HD._kraft
  WITH lbuf: val, lsh: share, lp: val, lo: Z, ln: Z, lcont: list val, n: Z, lens: list Z, ush: share, up: val
  PRE [ tptr tuchar, tuint, tptr tuint ]
    PROP (readable_share lsh; writable_share ush; 0 <= n <= 316;
          cbuf_ok false lbuf lsh lp lo ln n lcont lens; Forall (fun l => 0 <= l <= 15) lens)
    PARAMS (lbuf; Vint (Int.repr n); up)
    SEP (data_at lsh (tarray tuchar ln) lcont lp; data_at_ ush tuint up)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (kraft_sum lens)))
    SEP (data_at lsh (tarray tuchar ln) lcont lp; data_at ush tuint (Vint (Int.repr (nused lens))) up).

(* code_ok(lens, n, type), type 0 (code length code), 1 (literal/length), 2 (distance) *)
Definition code_ok_spec :=
  DECLARE HD._code_ok
  WITH lbuf: val, lsh: share, lp: val, lo: Z, ln: Z, lcont: list val, n: Z, lens: list Z, type: Z
  PRE [ tptr tuchar, tuint, tint ]
    PROP (readable_share lsh; 0 <= n <= 316; 0 <= type <= 2;
          cbuf_ok false lbuf lsh lp lo ln n lcont lens; Forall (fun l => 0 <= l <= 15) lens)
    PARAMS (lbuf; Vint (Int.repr n); Vint (Int.repr type))
    SEP (data_at lsh (tarray tuchar ln) lcont lp)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if code_okb type lens then 1 else 0)))
    SEP (data_at lsh (tarray tuchar ln) lcont lp).

(* ---------------------------------------------------------------------------------------------- *)
(* dyn_header (inflate_decode.c)                                                                  *)

(* dyn_header(w, nlen, ndist, ll, lcodes, dcodes): ll an object of 316 bytes, lcodes of 286 and dcodes of 30
   unsigned shorts (any contents); room for 15 + 2 (nlen + ndist) more bytes.  Afterwards (when no gp_assume
   blocked): the header bits for some well-formed clsent / toks, ll[0 .. nlen + ndist) = the code lengths,
   lcodes[0 .. nlen) and dcodes[0 .. ndist) = their canonical codes. *)
Definition dyn_header_spec :=
  DECLARE HD._dyn_header
  WITH gv: globals, sh: share, bsh: share, B: list bool, cap: Z, buf: val, w: val, nlen: Z, ndist: Z,
       llsh: share, llp: val, llc: list val, lcp: val, lcc: list val, dcp: val, dcc: list val
  PRE [ tptr t_bw, tuint, tuint, tptr tuchar, tptr tushort, tptr tushort ]
    PROP (writable_share sh; writable_share bsh; writable_share llsh;
          257 <= nlen <= 286; 1 <= ndist <= 30;
          Zlength B / 8 + 15 + 2 * (nlen + ndist) <= cap; cap <= Int.max_unsigned;
          Zlength llc = 316; Zlength lcc = 286; Zlength dcc = 30)
    PARAMS (w; Vint (Int.repr nlen); Vint (Int.repr ndist); llp; lcp; dcp) GLOBALS (gv)
    SEP (data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
         bw_at sh bsh B cap buf w;
         data_at llsh (tarray tuchar 316) llc llp;
         data_at llsh (tarray tushort 286) lcc lcp;
         data_at llsh (tarray tushort 30) dcc dcp)
  POST [ tvoid ]
    EX clsent: list Z, EX toks: list cltok,
    PROP (dyn_hdr_ok nlen ndist clsent toks)
    RETURN ()
    SEP (data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
         bw_at sh bsh (B ++ dyn_hdr_bits nlen ndist clsent toks) cap buf w;
         data_at llsh (tarray tuchar 316) (zvals (dyn_lens toks) ++ sublist (nlen + ndist) 316 llc) llp;
         data_at llsh (tarray tushort 286) (zvals (canon_vals (dyn_ll nlen toks)) ++ sublist nlen 286 lcc) lcp;
         data_at llsh (tarray tushort 30) (zvals (canon_vals (dyn_dl nlen ndist toks)) ++ sublist ndist 30 dcc) dcp).

(* ---------------------------------------------------------------------------------------------- *)
(* The contexts of the bodies (callees only)                                                      *)

(* no global: Vprog_dref; the tables of a harness: Vprog_tabs ti; dyn_header: Vprog_dyn (entry_shared needs
   every entry of a body's varspecs in the law's program) *)
Definition Vprog_dref : varspecs := [].
Definition Vprog_tabs (ti: ident * ident * ident * ident) : varspecs :=
  let '(ilb, ile, idb, ide) := ti in
  [(ilb, tarray tushort 29); (ile, tarray tuchar 29); (idb, tarray tushort 30); (ide, tarray tuchar 30)].
Definition Vprog_dyn : varspecs := [(HD._cl_order, tarray tuchar 19)].
Definition Gprog_bw_bit : funspecs := [].
Definition Gprog_bw_bits : funspecs := [bw_bit_spec].
Definition Gprog_bw_code : funspecs := [bw_bit_spec].
Definition Gprog_bw_byte : funspecs := [].
Definition Gprog_bw_align : funspecs := [].
Definition Gprog_bw_fixed : funspecs := [bw_code_spec].
Definition Gprog_len_code : funspecs := [].
Definition Gprog_dist_code : funspecs := [].
Definition Gprog_bw_fixed_match (ti: ident * ident * ident * ident) : funspecs :=
  [len_code_spec ti; dist_code_spec ti; bw_fixed_spec; bw_bits_spec; bw_code_spec].
Definition Gprog_canonical : funspecs := [].
Definition Gprog_kraft : funspecs := [].
Definition Gprog_code_ok : funspecs := [kraft_spec].
Definition Gprog_dyn_header : funspecs :=
  [nondet_bytes_spec; gp_assume_spec; code_ok_spec; canonical_spec; bw_bits_spec; bw_code_spec].

(* the bodies (proved in DRefBw.v, DRefCodes.v, DRefCanon.v, DRefDyn.v) *)
Definition dref_bw_bodies : Prop :=
  semax_body Vprog_dref Gprog_bw_bit HD.f_bw_bit bw_bit_spec /\
  semax_body Vprog_dref Gprog_bw_bits HD.f_bw_bits bw_bits_spec /\
  semax_body Vprog_dref Gprog_bw_code HD.f_bw_code bw_code_spec /\
  semax_body Vprog_dref Gprog_bw_byte HD.f_bw_byte bw_byte_spec /\
  semax_body Vprog_dref Gprog_bw_align HD.f_bw_align bw_align_spec.
Definition dref_code_bodies : Prop :=
  semax_body Vprog_dref Gprog_bw_fixed HD.f_bw_fixed bw_fixed_spec /\
  semax_body (Vprog_tabs id_tabs) Gprog_len_code HD.f_len_code (len_code_spec id_tabs) /\
  semax_body (Vprog_tabs id_tabs) Gprog_dist_code HD.f_dist_code (dist_code_spec id_tabs) /\
  semax_body (Vprog_tabs id_tabs) (Gprog_bw_fixed_match id_tabs) HD.f_bw_fixed_match (bw_fixed_match_spec id_tabs).
Definition dref_canon_bodies : Prop :=
  semax_body Vprog_dref Gprog_canonical HD.f_canonical canonical_spec /\
  semax_body Vprog_dref Gprog_kraft HD.f_kraft kraft_spec /\
  semax_body Vprog_dref Gprog_code_ok HD.f_code_ok code_ok_spec.
Definition dref_dyn_body : Prop :=
  semax_body Vprog_dyn Gprog_dyn_header HD.f_dyn_header dyn_header_spec.

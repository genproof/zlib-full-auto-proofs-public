(* The parts of DecDec.group_dec: the statements, proved in their own files DecDec*.v and
   assembled in DecDec.v.

   - canon_stmt (DecDecCanon.v): canonical codes (Format.code) of a complete code or a single code are
     prefix-free, and cover every 15-bit pattern (complete) or the all-zeros pattern (single);
   - walk_stmt (DecDecWalk.v, from canon_stmt): the table walk `twalk` on the VALID bits V of the bit buffer
     (hold = bval V; higher bits zero), when V and the code of the symbol sy sent next are compatible (one
     is a prefix of the other), finds an entry of L bits with L <= |V| exactly when the code is complete in
     V, and then it is the entry of sy;
   - dcode_stmt (DecDecLook.v, from walk_stmt): LEN's / DIST's decoding of a code (lookup1, lookup2 for a
     link, the DROPBITS) = `dcode`: either the entry of sy and exactly its code consumed (bits < 8 after),
     or the input runs out with fewer bits than the code (and the stream is longer than the input);
   - need_stmt (DecDecNeed.v): NEEDBITS(n) for n extra bits (bits_le v n) at the bit position;
   - lay_stmt (DecDecLay.v, from dkit_stmt): the layout of a Huffman block: the codes are good, the symbol
     j is at p0 (and valid: sym_ok), the end-of-block code ends at bpos (k+1), the output is a prefix of
     the data;
   - copy_stmt (DecDecCopy.v): MATCH's copy (window or output) appends lz_copy;
   - tabs_stmt (DecDecTabs.v): len_code / dist_code and means_symbol facts;
   - the passes, mode by mode (pass_ok: from a state satisfying Kd at mode X, the switch case gives
     dstep_post): LIT, MATCH (DecDecMatch.v), DISTEXT, DIST (DecDecDist.v), LENEXT (DecDecLenext.v),
     LEN (DecDecLen.v); a pass that falls through to the next case uses the next mode's pass_ok.
   Helpers (Kd transfer, at_mode introduction / elimination): DecDecKd.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

Definition used (lens: list Z) (s: Z) : Prop := 0 <= s < Zlength lens /\ Znth s lens <> 0.

(* ---------------------------------------------------------------------------------------------- *)
(* Canonical codes                                                                                *)

Definition canon_stmt : Prop :=
  forall lens, lens_ok lens -> (complete lens \/ single lens) ->
    (forall s s' R, used lens s -> used lens s' -> send_sym lens s' ++ R = send_sym lens s -> s' = s) /\
    (forall W, Zlength W = MAXLEN -> (complete lens \/ W = zeros MAXLEN) ->
       exists s R, used lens s /\ W = send_sym lens s ++ R).

(* ---------------------------------------------------------------------------------------------- *)
(* The table walk on the valid bits                                                               *)

Definition walk_stmt : Prop :=
  forall s t root type lens sy V R,
    tdec s t root type lens -> lens_ok lens -> (complete lens \/ single lens) -> used lens sy ->
    (V ++ R = send_sym lens sy \/ V = send_sym lens sy ++ R) ->
    exists op val L,
      twalk s t root (bval V) = Some (op, val, L) /\
      (L <= Zlength V <-> Znth sy lens <= Zlength V) /\
      (L <= Zlength V -> L = Znth sy lens /\ ref.means_symbol type sy op val = true).

(* ---------------------------------------------------------------------------------------------- *)
(* Decoding one code (c_LEN, c_DIST)                                                              *)

(* the lookups and the DROPBITS of c_LEN (lk = islink LENS) and c_DIST (lk = islink DISTS) *)
Definition dcode (lk: Z -> bool) (t: tref) (rb: Z) (m: mst) : entry * mst * bool :=
  let '(here, m, ok) := lookup1 lenfix_list distfix_list t rb m in
  if negb ok then (here, m, false) else
  let '(here, m, ok) :=
    if lk (e_op here) then
      let '(h2, m, ok) := lookup2 lenfix_list distfix_list t here m in
      if negb ok then (h2, m, false) else
      (h2, dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))), true)
    else (here, m, true) in
  if negb ok then (here, m, false) else
  (here, dropbits (e_bits here) (upd_s m (fun s => set_i_back s (i_back s + e_bits here))), true).

(* the input of a call: pos bytes consumed before it, inp offered *)
Definition in_ctx (G: dctx) (pos: Z) (inp: list Z) : Prop :=
  dctx_ok G /\ 0 <= pos /\ pos + Zlength inp <= Zlength (dc_src G) /\
  inp = sublist pos (pos + Zlength inp) (dc_src G).

(* the bit buffer of m at its place in the input *)
Definition m_buf (G: dctx) (pos: Z) (inp: list Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= m_nx m <= Zlength inp /\ hold_ok G (pos + m_nx m) (m_hold m) (m_bits m).

Definition dcode_stmt : Prop :=
  forall G pos inp m kind t rb lens sy q,
    in_ctx G pos inp -> m_buf G pos inp m -> q = 8 * (pos + m_nx m) - m_bits m ->
    (kind = LENS \/ kind = DISTS) ->
    tvalid kind lenfix_list distfix_list (m_s m) t rb -> tdec (m_s m) t rb kind lens ->
    lens_ok lens -> (complete lens \/ single lens) -> used lens sy ->
    sublist q (q + Znth sy lens) (sbits G) = send_sym lens sy -> q + Znth sy lens <= 8 * slen G ->
    (m_bits m < 8 \/ m_bits m < Znth sy lens) ->
    let '(here, m', ok) := dcode (islink kind) t rb m in
    exists nx h b bk lv,
      m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx (upd_s m (fun s => set_i_back s bk)) nx) h) b) lv /\
      m_nx m <= nx <= Zlength inp /\ hold_ok G (pos + nx) h b /\
      (ok = true -> lv = m_leave m /\ ref.means_symbol kind sy (e_op here) (e_val here) = true /\
                    8 * (pos + nx) - b = q + Znth sy lens /\ 0 <= b < 8) /\
      (ok = false -> lv = 1 /\ nx = Zlength inp /\ 8 * (pos + nx) - b = q /\ b < Znth sy lens /\
                     pos + Zlength inp < slen G).

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(n) of n extra bits (c_LENEXT, c_DISTEXT)                                              *)

Definition need_stmt : Prop :=
  forall G pos inp m n v q,
    in_ctx G pos inp -> m_buf G pos inp m -> q = 8 * (pos + m_nx m) - m_bits m -> m_leave m = 0 ->
    1 <= n <= 15 -> 0 <= v < 2 ^ n ->
    sublist q (q + n) (sbits G) = bits_le v n -> q + n <= 8 * slen G ->
    (m_bits m < 8 \/ m_bits m < n) ->
    exists nx h b,
      needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) (m_leave (needbits n m)) /\
      m_nx m <= nx <= Zlength inp /\ hold_ok G (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
      ((m_leave (needbits n m) = 1 /\ nx = Zlength inp /\ b < n /\ pos + Zlength inp < slen G) \/
       (m_leave (needbits n m) = 0 /\ n <= b < n + 8 /\ h mod 2 ^ n = v)).

(* ---------------------------------------------------------------------------------------------- *)
(* The layout of a Huffman block                                                                  *)

Definition lay_stmt : Prop :=
  forall G s k j ll dl syms p0,
    dctx_ok G -> in_huff G s k j ll dl syms p0 ->
    lens_ok ll /\ (complete ll \/ single ll) /\ used ll 256 /\
    lens_ok dl /\ (complete dl \/ single dl \/ empty_code dl) /\
    (exists rest, full G = outj G k syms j ++ rest) /\
    (j < Zlength syms ->
       let sy := sym_at syms j in
       sym_ok (2 ^ dc_wb G) ll dl (outj G k syms j) sy /\
       sublist p0 (p0 + Zlength (send_one ll dl sy)) (sbits G) = send_one ll dl sy /\
       p0 + Zlength (send_one ll dl sy) <= 8 * slen G /\
       outj G k syms (j + 1) = sym_data (outj G k syms j) sy /\
       in_huff G s k (j + 1) ll dl syms (p0 + Zlength (send_one ll dl sy))) /\
    (j = Zlength syms ->
       sublist p0 (p0 + Zlength (send_sym ll 256)) (sbits G) = send_sym ll 256 /\
       p0 + Zlength (send_sym ll 256) = bpos G (k + 1) /\ bpos G (k + 1) <= 8 * slen G /\
       outj G k syms j = outk G (k + 1)).

(* ---------------------------------------------------------------------------------------------- *)
(* MATCH's copy                                                                                   *)

Definition copy_stmt : Prop :=
  forall G m ob dist,
    win_ok G (m_s m) ob -> 0 <= i_wbits (m_s m) -> 0 <= i_wnext (m_s m) ->
    m_out m = m_aout m -> Zlength (m_ow m) <= m_aout m <= 2 ^ 31 - 1 -> 0 < m_left m ->
    i_offset (m_s m) = dist -> 1 <= dist <= Zlength (ob ++ m_ow m) -> dist <= 2 ^ i_wbits (m_s m) ->
    1 <= i_length (m_s m) ->
    exists c ow',
      1 <= c <= Z.min (i_length (m_s m)) (m_left m) /\
      ob ++ ow' = lz_copy (Z.to_nat c) dist (ob ++ m_ow m) /\ (exists d, ow' = m_ow m ++ d) /\
      c_MATCH m = IBrk (let m1 := upd_s (set_m_ow m ow') (fun s => set_i_length s (i_length (m_s m) - c)) in
                        if i_length (m_s m) - c =? 0 then set_mode m1 LEN else m1).

(* ---------------------------------------------------------------------------------------------- *)
(* Lengths, distances and the meaning of the table entries                                        *)

Definition tabs_stmt : Prop :=
  (forall len, 3 <= len <= 258 -> let i := len_code len in
     0 <= i <= 28 /\ 0 <= Znth i len_extra <= 5 /\
     Znth i len_base <= len < Znth i len_base + 2 ^ Znth i len_extra) /\
  (forall dist, 1 <= dist <= 32768 -> let d := dist_code dist in
     0 <= d <= 29 /\ 0 <= Znth d dist_extra <= 13 /\
     Znth d dist_base <= dist < Znth d dist_base + 2 ^ Znth d dist_extra) /\
  (forall sy op val, 0 <= sy < 256 -> ref.means_symbol LENS sy op val = true -> op = 0 /\ val = sy) /\
  (forall op val, ref.means_symbol LENS 256 op val = true -> op = 96) /\
  (forall i op val, 0 <= i <= 28 -> ref.means_symbol LENS (257 + i) op val = true ->
     op = 16 + Znth i len_extra /\ val = Znth i len_base) /\
  (forall d op val, 0 <= d <= 29 -> ref.means_symbol DISTS d op val = true ->
     op = 16 + Znth d dist_extra /\ val = Znth d dist_base).

(* ---------------------------------------------------------------------------------------------- *)
(* The passes                                                                                     *)

(* what the passes need of mwf3, kept by every pass of this group *)
Definition dw (m: mst) : Prop :=
  tvalid LENS lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) /\
  tvalid DISTS lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) (i_distbits (m_s m)) /\
  0 <= m_nx m <= Zlength (m_inp m) /\ Zlength (m_ow m) <= m_aout m <= 2 ^ 31 - 1 /\
  0 <= i_wnext (m_s m).

Definition pass_ok (X: Z) (c: mst -> iout) : Prop :=
  forall G pos inp ob flush m,
    in_ctx G pos inp -> Kd G pos inp ob m -> dw m -> m_leave m = 0 -> m_mode m = X ->
    dstep_post G pos inp ob flush m (c m).

(* LEN (its fast path needs mwf3) *)
Definition pass_len_ok : Prop :=
  forall G pos inp ob flush m,
    in_ctx G pos inp -> Kd G pos inp ob m -> mwf3 m -> dw m -> m_leave m = 0 -> m_mode m = LEN ->
    dstep_post G pos inp ob flush m (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m).

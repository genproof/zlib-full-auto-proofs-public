(* The theory of inflate() on a raw stream whose first block is fixed-Huffman literals followed by an invalid
   element (FRFacts.v): the definitions and the statements of its parts.

   - `fr_at C s c hold bits out`: where the decoder is, mode by mode, with c input bytes consumed, the bit buffer
     (hold, bits) and the output so far `out`: before the block header (HEAD, TYPEDO), before literal j (LEN_ /
     LEN, the tail when j = |lits|), after literal j's code (LIT), inside the tail (LENEXT, DIST, DISTEXT, MATCH),
     or after the error (BAD).  The bit position is q = 8 c - bits, and hold holds the bits [q, 8 c) of the input
     (DecodeDefs.hold_ok over the context `fr_g C`, whose only meaningful field is the input).
   - `fr_inv`: the invariant between calls (the `I` of FRFacts.fr_facts).
   - `fr_K`: the invariant at the loop heads of one call (Model2.loop2 from Spec5.m_init); `fr_E`: the machine
     when the loop is left (the error, or a reason FRFacts.fr_stop); `fr_res`: what one pass of the switch gives.
   - The parts: the layout of the input (`fr_layout_stmt`), reading bits and fixed codes (`fr_bits_stmt`), the
     passes of the switch mode by mode (`fr_pass`), inflate_fast (`fr_fast_stmt`), the exit (`fr_leave_stmt`)
     and one call (`fr_call_stmt`). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.bit_writer.FRFacts.
Require Export Zlib.proof.rfc1951.DecodeDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Positions in the input                                                                         *)

Definition fr_n (C: frc) : Z := Zlength (fr_lits C).

(* the decode context of the input (hold_ok and DecodeDefs.dkit_stmt only use dc_src) *)
Definition fr_g (C: frc) : dctx := DCtx WRaw 0 [] [] 0 (fr_src C).

(* the bit position of literal j (j = |lits|: the tail) *)
Definition fr_lpos (C: frc) (j: Z) : Z :=
  3 + Zlength (concat (map (send_sym fixed_ll) (firstn (Z.to_nat j) (fr_lits C)))).
Definition fr_tpos (C: frc) : Z := fr_lpos C (fr_n C).

(* the output after j literals *)
Definition fr_lit (C: frc) (j: Z) : list Z := firstn (Z.to_nat j) (fr_lits C).

(* the fixed tables in the state (TYPEDO sets them for BTYPE 01) *)
Definition fr_fixed (s: istate) : Prop :=
  i_lencode s = TLenfix /\ i_lenbits s = 9 /\ i_distcode s = TDistfix /\ i_distbits s = 5.

(* ---------------------------------------------------------------------------------------------- *)
(* Where the decoder is                                                                           *)

Definition fr_at (C: frc) (s: istate) (c hold bits: Z) (out: list Z) : Prop :=
  let md := i_mode s in let q := 8 * c - bits in let t := fr_tpos C in
  (* after the error: nothing more than the literals written *)
  (md = BAD /\ Zlength out <= fr_n C) \/
  (hold_ok (fr_g C) c hold bits /\
   (* nothing read (raw: HEAD goes to TYPEDO) *)
   ((md = HEAD /\ c = 0 /\ bits = 0 /\ out = [] /\ i_last s = 0 /\ i_wrap s = 0) \/
    (md = TYPEDO /\ c = 0 /\ bits = 0 /\ out = [] /\ i_last s = 0) \/
    (fr_fixed s /\
     (* before literal j (j = |lits|: before the tail) *)
     (((md = LEN_ \/ md = LEN) /\ bits <= 8 /\
       exists j, 0 <= j <= fr_n C /\ q = fr_lpos C j /\ out = fr_lit C j) \/
      (* literal j read, not yet written *)
      (md = LIT /\ bits < 8 /\
       exists j, 0 <= j < fr_n C /\ q = fr_lpos C (j + 1) /\ out = fr_lit C j /\
                 i_length s = Znth j (fr_lits C)) \/
      (* the tail's length code read (TDCode: 257, no extra bits) *)
      (md = LENEXT /\ bits < 8 /\ out = fr_lits C /\
       ((exists w, fr_tail C = TDCode w /\ q = t + Znth 257 fixed_ll /\ i_extra s = 0) \/
        (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ q = t + Znth lc fixed_ll /\
           i_extra s = Znth (lc - 257) len_extra))) \/
      (* the length and its extra bits read *)
      (md = DIST /\ bits < 8 /\ out = fr_lits C /\
       ((exists w, fr_tail C = TDCode w /\ q = t + Znth 257 fixed_ll) \/
        (exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\
           q = t + Znth lc fixed_ll + Znth (lc - 257) len_extra))) \/
      (* TFar: the distance code read *)
      (* (NEEDBITS of up to 13 extra bits may stop with 8 <= bits < extra) *)
      (md = DISTEXT /\ (bits < 8 \/ bits < i_extra s) /\ out = fr_lits C /\
       exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\
         q = t + Znth lc fixed_ll + Znth (lc - 257) len_extra + Znth dc fixed_dl /\
         i_offset s = Znth dc dist_base /\ i_extra s = Znth dc dist_extra) \/
      (* TFar: the distance read (larger than the output) *)
      (md = MATCH /\ out = fr_lits C /\
       exists lc lx dc dx, fr_tail C = TFar lc lx dc dx /\ i_offset s = Znth dc dist_base + dx))))).

(* between calls: pos bytes consumed, ob the output so far; the window never holds more than the output *)
Definition fr_inv (C: frc) (pos: Z) (ob: list Z) (s: istate) : Prop :=
  fr_at C s pos (i_hold s) (i_bits s) ob /\ i_whave s <= Zlength ob.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

(* the hypotheses of FRFacts.fr_call *)
Definition fr_ctx (C: frc) (pos: Z) (inp: list Z) (L: live) (z: zfields) : Prop :=
  fr_ok C /\ 0 <= pos /\ pos + Zlength inp <= Zlength (fr_src C) /\
  inp = sublist pos (pos + Zlength inp) (fr_src C) /\ Zlength inp <= Int.max_unsigned /\
  live_ok L /\ zf_ok z.

(* the window fields (and sane) are never written by the loop *)
Definition fr_wsame (s s': istate) : Prop :=
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\ i_win s' = i_win s /\
  i_wdata s' = i_wdata s /\ i_wbits s' = i_wbits s /\ i_sane s' = i_sane s.

(* the machine of the call offered inp from pos, ob the output before the call, L the state at its start *)
Record fr_M (C: frc) (pos: Z) (inp ob: list Z) (L: live) (z: zfields) (m: mst) : Prop := {
  frm_inp : m_inp m = inp;
  frm_in : m_in m = Zlength inp;
  frm_aout : m_aout m = zf_ao z;
  frm_out : m_out m = zf_ao z;
  frm_nx : 0 <= m_nx m <= Zlength inp;
  frm_ow : Zlength (m_ow m) <= zf_ao z;
  frm_win : fr_wsame (l_s L) (m_s m);
  frm_whave : i_whave (l_s L) <= Zlength ob;
  frm_at : fr_at C (m_s m) (pos + m_nx m) (m_hold m) (m_bits m) (ob ++ m_ow m) }.

(* at a loop head *)
Record fr_K (C: frc) (pos: Z) (inp ob: list Z) (L: live) (z: zfields) (m: mst) : Prop := {
  frk_m : fr_M C pos inp ob L z m;
  frk_leave : m_leave m = 0;
  frk_ret : m_ret m = Z_OK }.

(* when the loop is left: the error (BAD, after c_BAD), or no error and a reason to stop *)
Record fr_E (C: frc) (pos: Z) (inp ob: list Z) (L: live) (z: zfields) (flush: Z) (m: mst) : Prop := {
  fre_m : fr_M C pos inp ob L z m;
  fre_leave : m_leave m = 1;
  fre_why : (m_mode m = BAD /\ m_ret m = Z_DATA_ERROR) \/
            (m_mode m <> BAD /\ m_ret m = Z_OK /\
             fr_stop C pos (m_nx m) (Zlength inp) (Zlength ob) (Zlength (m_ow m)) (zf_ao z) flush) }.

(* one pass of the switch: the next loop head, or the exit; never a return *)
Definition fr_res (C: frc) (pos: Z) (inp ob: list Z) (L: live) (z: zfields) (flush: Z) (o: iout) : Prop :=
  match o with
  | IBrk m' => fr_K C pos inp ob L z m' \/ fr_E C pos inp ob L z flush m'
  | IRet _ _ => False
  end.

(* a case of the switch (f flush m) from a loop head whose mode satisfies P *)
Definition fr_pass (P: Z -> Prop) (f: Z -> mst -> iout) : Prop :=
  forall C pos inp ob L z flush m,
    fr_ctx C pos inp L z -> fr_K C pos inp ob L z m -> P (m_mode m) ->
    fr_res C pos inp ob L z flush (f flush m).

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                      *)

(* the layout of the input (from fr_ok) and the lengths of the fixed codes *)
Definition fr_layout_stmt : Prop :=
  forall C, fr_ok C ->
  let sb := bytes_bits (fr_src C) in
  (forall j, 0 <= j < fr_n C ->
     0 <= Znth j (fr_lits C) < 256 /\
     fr_lpos C (j + 1) = fr_lpos C j + Znth (Znth j (fr_lits C)) fixed_ll /\
     sublist (fr_lpos C j) (fr_lpos C (j + 1)) sb = send_sym fixed_ll (Znth j (fr_lits C)) /\
     fr_lit C (j + 1) = fr_lit C j ++ [Znth j (fr_lits C)]) /\
  fr_lpos C 0 = 3 /\
  (forall j, 0 <= j <= fr_n C -> 3 <= fr_lpos C j <= fr_tpos C) /\
  (forall j, 0 <= j <= fr_n C -> Zlength (fr_lit C j) = j) /\
  fr_lit C (fr_n C) = fr_lits C /\
  fr_tpos C < fr_end C <= 8 * Zlength (fr_src C) /\
  (let t := fr_tpos C in
   match fr_tail C with
   | TLL w => fr_end C = t + Znth (286 + w) fixed_ll /\ sublist t (fr_end C) sb = send_sym fixed_ll (286 + w)
   | TDCode w =>
       fr_end C = t + Znth 257 fixed_ll + Znth (30 + w) fixed_dl /\
       sublist t (t + Znth 257 fixed_ll) sb = send_sym fixed_ll 257 /\
       sublist (t + Znth 257 fixed_ll) (fr_end C) sb = send_sym fixed_dl (30 + w)
   | TFar lc lx dc dx =>
       let p1 := t + Znth lc fixed_ll in
       let p2 := p1 + Znth (lc - 257) len_extra in
       let p3 := p2 + Znth dc fixed_dl in
       fr_end C = p3 + Znth dc dist_extra /\
       sublist t p1 sb = send_sym fixed_ll lc /\
       sublist p1 p2 sb = bits_le lx (Znth (lc - 257) len_extra) /\
       sublist p2 p3 sb = send_sym fixed_dl dc /\
       sublist p3 (fr_end C) sb = bits_le dx (Znth dc dist_extra)
   end) /\
  Zlength fixed_ll = 288 /\ Zlength fixed_dl = 32 /\
  (forall sy, 0 <= sy < 288 -> 7 <= Znth sy fixed_ll <= 9) /\
  (forall sy, 0 <= sy < 32 -> Znth sy fixed_dl = 5) /\
  (forall i, 0 <= i <= 28 -> 0 <= Znth i len_extra <= 5 /\ 3 <= Znth i len_base <= 258) /\
  (forall d, 0 <= d <= 29 -> 0 <= Znth d dist_extra <= 13 /\ 1 <= Znth d dist_base <= 24577).

(* the input of a call: pos bytes consumed before it, inp offered *)
Definition fr_in (C: frc) (pos: Z) (inp: list Z) : Prop :=
  bytes_ok (fr_src C) /\ 0 <= pos /\ pos + Zlength inp <= Zlength (fr_src C) /\
  inp = sublist pos (pos + Zlength inp) (fr_src C).

(* the bit buffer of m at its place in the input *)
Definition fr_buf (C: frc) (pos: Z) (inp: list Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= m_nx m <= Zlength inp /\ hold_ok (fr_g C) (pos + m_nx m) (m_hold m) (m_bits m).

(* reading the input: one fixed code (the slow path's lookup1, the fixed tables have no links), extra bits
   (NEEDBITS), and the meaning of the fixed tables' entries *)
Record fr_bits_stmt : Prop := {
  fb_lookup : forall C pos inp m t rb kind lens sy,
    fr_in C pos inp -> fr_buf C pos inp m ->
    ((t = TLenfix /\ rb = 9 /\ kind = LENS /\ lens = fixed_ll) \/
     (t = TDistfix /\ rb = 5 /\ kind = DISTS /\ lens = fixed_dl)) ->
    0 <= sy < Zlength lens -> m_bits m <= 8 ->
    let q := 8 * (pos + m_nx m) - m_bits m in
    q + Znth sy lens <= 8 * Zlength (fr_src C) ->
    sublist q (q + Znth sy lens) (bytes_bits (fr_src C)) = send_sym lens sy ->
    let '(here, m', ok) := lookup1 lenfix_list distfix_list t rb m in
    exists nx h b lv,
      m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
      m_nx m <= nx <= Zlength inp /\ hold_ok (fr_g C) (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
      (ok = true -> lv = m_leave m /\ e_bits here = Znth sy lens /\ Znth sy lens <= b < Znth sy lens + 8 /\
                    ref.means_symbol kind sy (e_op here) (e_val here) = true) /\
      (ok = false -> lv = 1 /\ nx = Zlength inp /\ b < Znth sy lens);
  fb_need : forall C pos inp m n v,
    fr_in C pos inp -> fr_buf C pos inp m -> m_leave m = 0 -> 1 <= n <= 15 -> 0 <= v < 2 ^ n ->
    (m_bits m < 8 \/ m_bits m < n) ->
    let q := 8 * (pos + m_nx m) - m_bits m in
    q + n <= 8 * Zlength (fr_src C) -> sublist q (q + n) (bytes_bits (fr_src C)) = bits_le v n ->
    exists nx h b,
      needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) (m_leave (needbits n m)) /\
      m_nx m <= nx <= Zlength inp /\ hold_ok (fr_g C) (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
      ((m_leave (needbits n m) = 1 /\ nx = Zlength inp /\ b < n) \/
       (m_leave (needbits n m) = 0 /\ n <= b < n + 8 /\ h mod 2 ^ n = v));
  fb_ms_lit : forall sy op val, 0 <= sy < 256 -> ref.means_symbol LENS sy op val = true -> op = 0 /\ val = sy;
  fb_ms_len : forall i op val, 0 <= i <= 28 -> ref.means_symbol LENS (257 + i) op val = true ->
    op = 16 + Znth i len_extra /\ val = Znth i len_base;
  fb_ms_dist : forall d op val, 0 <= d <= 29 -> ref.means_symbol DISTS d op val = true ->
    op = 16 + Znth d dist_extra /\ val = Znth d dist_base;
  fb_ms_bad : forall type sy op val,
    ((type = LENS /\ (sy = 286 \/ sy = 287)) \/ (type = DISTS /\ (sy = 30 \/ sy = 31))) ->
    ref.means_symbol type sy op val = true -> Z.land op 112 = 64 }.

(* the header: HEAD (raw: to TYPEDO) and TYPEDO (BFINAL, BTYPE 01: LEN_, Z_TREES stops there) *)
Definition fr_head_stmt : Prop :=
  fr_pass (fun md => md = HEAD) (fun _ m => c_HEAD2 m) /\
  fr_pass (fun md => md = TYPEDO) (fun flush m => c_TYPEDO flush m).

(* LEN's fast path: inflate_fast (6 input bytes, 258 output bytes, bits < 8) and the test of TYPE after it *)
Definition fr_fast_stmt : Prop :=
  forall C pos inp ob L z m,
    fr_ctx C pos inp L z -> fr_K C pos inp ob L z m -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    let m1 := fast lenfix_list distfix_list (restore m) in
    fr_K C pos inp ob L z
      (if m_mode m1 =? Zlib.proof.inflate.Model.TYPE then upd_s m1 (fun s => set_i_back s (-1)) else m1).

(* the tail's modes (LENEXT falls through into DIST, DIST into DISTEXT, DISTEXT into MATCH) and BAD *)
Definition fr_tail_stmt : Prop :=
  fr_pass (fun md => md = LENEXT) (fun _ m => c_LENEXT lenfix_list distfix_list m) /\
  fr_pass (fun md => md = DIST) (fun _ m => c_DIST lenfix_list distfix_list m) /\
  fr_pass (fun md => md = DISTEXT) (fun _ m => c_DISTEXT m) /\
  fr_pass (fun md => md = MATCH) (fun _ m => c_MATCH m) /\
  fr_pass (fun md => md = BAD) (fun _ m => c_BAD m).

(* LEN (the fast path, or one code: a literal to LIT, the tail into LENEXT or BAD) and LIT *)
Definition fr_len_stmt : Prop :=
  fr_pass (fun md => md = LEN) (fun _ m => c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m) /\
  fr_pass (fun md => md = LIT) (fun _ m => c_LIT m).

(* all the passes *)
Definition fr_passes : Prop := fr_head_stmt /\ fr_len_stmt /\ fr_tail_stmt.

(* the exit of the loop, then inf_leave *)
Definition fr_leave_stmt : Prop :=
  forall C pos inp ob L z flush m res,
    fr_ctx C pos inp L z -> fr_E C pos inp ob L z flush m -> inf_leave flush m res ->
    fr_post fr_inv C pos ob L z inp flush res.

(* one call (FRFacts.fr_call with I = fr_inv) *)
Definition fr_call_stmt : Prop :=
  forall C pos ob L z inp flush res,
    fr_ok C -> fr_inv C pos ob (l_s L) -> live_ok L -> zf_ok z ->
    0 <= pos -> pos + Zlength inp <= Zlength (fr_src C) -> inp = sublist pos (pos + Zlength inp) (fr_src C) ->
    Zlength inp <= Int.max_unsigned -> Int.min_signed <= flush <= Int.max_signed ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    fr_post fr_inv C pos ob L z inp flush res.

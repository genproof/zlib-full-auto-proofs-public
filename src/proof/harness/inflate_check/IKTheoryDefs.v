(* Law inflate_check, the theory: THE definitions shared by IKTheory*.v.

   The theory reuses law inflate_codes' intra-call invariant Kc (inflate_codes/TheoryDefs.v: wrap fixed,
   bits <= 31 outside BAD/MEM, the header bytes in HEAD/DICTID/DICT, ...; its per-group step lemmas are Qed
   in inflate_codes/Theory*.v) and adds Kx, the facts this law needs, at every loop head of one inflate()
   call (Model2.loop2 from Spec5.m_init) and at its exit:
   - the bit buffer: hold holds exactly the input bits not yet consumed: with P = pos + m_nx m (the bytes of
     src pulled so far), hold = (le_val src[0..P)) >> (8 P - bits) (ik_bitbuf);
   - bits = 0 in the modes that take whole bytes from the input without the bit buffer (EXTRA, NAME, COMMENT,
     COPY_, COPY; EXLEN without FEXTRA);
   - raw stream (wrap = 0): strm->adler (m_adler) stays a0 (its value on entry), no header mode;
   - wrapped stream, before the header is complete: nothing produced (ik_pre), the header bytes read so far
     are valid (gzip: ik_gzhdr_ok, zlib with FDICT: ik_zh_ok);
   - wrapped stream, after the header: the header is valid, gzip iff flags <> 0, and the check value is the
     reference check of out ++ (the bytes of this call counted so far: the first aout - out bytes of m_ow;
     CHECK's `out = left` counts them all), and strm->adler (m_adler) is it (ik_post);
   - state->total and strm->total_out: the length of all output counted so far, mod 2^64;
   - the trailer: in CHECK bits is a multiple of 8; in LENGTH / DONE the trailer bytes before the consumed
     position are the check value (and for gzip the length) (ik_trail).
   `out`: all the bytes produced by the previous calls; `pos`: the bytes of src consumed by them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_check.IKFacts.
Require Export Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer                                                                                 *)

(* P bytes of src pulled, hold = the bits of them not yet consumed (bits of them) *)
Definition ik_bitbuf (src: list Z) (P hold bits: Z) : Prop :=
  0 <= bits <= 8 * P /\ hold = Z.shiftr (le_val (sublist 0 P src)) (8 * P - bits).

(* ---------------------------------------------------------------------------------------------- *)
(* Modes                                                                                          *)

Definition ik_gzhdr_mode (md: Z) : Prop :=
  md = FLAGS \/ md = TIME \/ md = OS \/ md = EXLEN \/ md = EXTRA \/ md = NAME \/ md = COMMENT \/ md = HCRC.
Definition ik_pre_mode (md: Z) : Prop :=
  md = HEAD \/ ik_gzhdr_mode md \/ md = DICTID \/ md = DICT.
Definition ik_post_mode (md: Z) : Prop :=
  md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO \/ md = STORED \/ md = COPY_ \/ md = COPY \/
  md = TABLE \/ md = LENLENS \/ md = CODELENS \/ decode_mode md \/ md = CHECK \/ md = LENGTH \/ md = DONE.

(* ---------------------------------------------------------------------------------------------- *)
(* The wrapper                                                                                    *)

(* gzip by the wrapper bits of wrap (6: gzip only; 7: detected from the first two bytes; bit 3, the window size
   from the header, does not matter); for an accepted w >= 0, ik_gzw (wrap_of w) src = ik_gz w src *)
Definition ik_gzw (wrap: Z) (src: list Z) : bool :=
  (Z.land wrap 7 =? 6) ||
  ((Z.land wrap 7 =? 7) && (2 <=? Zlength src) && (Znth 0 src =? 31) && (Znth 1 src =? 139)).

(* before the header is complete: nothing produced *)
Definition ik_pre (out: list Z) (m: mst) : Prop :=
  out = [] /\ m_ow m = [] /\ m_out m = m_aout m.

(* the gzip header modes: 1f 8b read (8 P - bits: the consumed bits); from TIME on also 08 FLG checked *)
Definition ik_gzhdr_ok (wrap: Z) (src: list Z) (P bits md flags: Z) : Prop :=
  Z.land wrap 2 <> 0 /\ ik_gzw wrap src = true /\
  2 <= Zlength src /\ Znth 0 src = 31 /\ Znth 1 src = 139 /\
  (md = FLAGS -> 8 * P - bits = 16) /\
  (md <> FLAGS -> ik_ghdr src /\ Z.land flags 255 = 8 /\ 32 <= 8 * P - bits) /\
  (md = OS -> 64 <= 8 * P - bits) /\
  (md = EXLEN \/ md = EXTRA \/ md = NAME \/ md = COMMENT \/ md = HCRC -> 80 <= 8 * P - bits).

(* DICTID / DICT: a valid zlib header was read *)
Definition ik_zh_ok (wrap: Z) (src: list Z) (P bits flags: Z) : Prop :=
  Z.land wrap 1 <> 0 /\ ik_gzw wrap src = false /\ ik_zhdr src /\ flags = 0 /\ 16 <= 8 * P - bits.

(* after the header *)
Definition ik_post (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (m: mst) : Prop :=
  let P := pos + m_nx m in
  let s := m_s m in
  ((i_flags s = 0 /\ ik_zhdr src /\ ik_gzw wrap src = false /\ 16 <= 8 * P - m_bits m) \/
   (Z.land (i_flags s) 255 = 8 /\ ik_ghdr src /\ ik_gzw wrap src = true /\ 80 <= 8 * P - m_bits m)) /\
  i_check s = ik_chk (negb (i_flags s =? 0)) (out ++ sublist 0 (m_aout m - m_out m) (m_ow m)) /\
  m_adler m = i_check s.

(* the trailer (wrapped stream) *)
Definition ik_trail (src: list Z) (pos: Z) (m: mst) : Prop :=
  let P := pos + m_nx m in
  let s := m_s m in
  let Q := P - m_bits m / 8 in
  (m_mode m = CHECK -> m_bits m mod 8 = 0) /\
  (m_mode m = LENGTH ->
     m_out m = m_left m /\ m_bits m mod 8 = 0 /\
     (i_flags s = 0 -> m_bits m = 0 /\ 6 <= Q /\ be32 (sublist (Q - 4) Q src) = i_check s) /\
     (i_flags s <> 0 -> 14 <= Q /\ le32 (sublist (Q - 4) Q src) = i_check s)) /\
  (m_mode m = DONE ->
     m_out m = m_left m /\ m_bits m = 0 /\
     (i_flags s = 0 -> 6 <= P /\ be32 (sublist (P - 4) P src) = i_check s) /\
     (i_flags s <> 0 -> 18 <= P /\ le32 (sublist (P - 8) (P - 4) src) = i_check s /\
                        le32 (sublist (P - 4) P src) = i_total s mod 2 ^ 32)).

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant                                                                                  *)

Record Kx (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a0: Z) (m: mst) : Prop := {
  kx_wrap : wrap = 0 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7 \/ wrap = 13 \/ wrap = 14 \/ wrap = 15;
  kx_buf : ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m);
  kx_bits0 : (m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/ m_mode m = COPY_ \/
              m_mode m = COPY -> m_bits m = 0) /\
             (m_mode m = EXLEN -> Z.land (i_flags (m_s m)) 1024 = 0 -> m_bits m = 0);
  kx_out : m_out m = m_aout m \/ m_out m = m_left m;
  kx_total : i_total (m_s m) = (Zlength out + (m_aout m - m_out m)) mod 2 ^ 64;
  kx_tout : m_tout m = (Zlength out + (m_aout m - m_out m)) mod 2 ^ 64;
  kx_raw : wrap = 0 ->
    m_adler m = a0 /\ ~ ik_gzhdr_mode (m_mode m) /\ m_mode m <> DICTID /\ m_mode m <> DICT;
  kx_pre : wrap <> 0 -> ik_pre_mode (m_mode m) -> ik_pre out m;
  kx_gzh : wrap <> 0 -> ik_gzhdr_mode (m_mode m) ->
    ik_gzhdr_ok wrap src (pos + m_nx m) (m_bits m) (m_mode m) (i_flags (m_s m));
  kx_zh : wrap <> 0 -> (m_mode m = DICTID \/ m_mode m = DICT) ->
    ik_zh_ok wrap src (pos + m_nx m) (m_bits m) (i_flags (m_s m));
  kx_post : wrap <> 0 -> ik_post_mode (m_mode m) -> ik_post wrap src pos out m;
  kx_bad : wrap <> 0 -> (m_mode m = BAD \/ m_mode m = MEM) -> ik_pre out m \/ ik_post wrap src pos out m;
  kx_trail : wrap <> 0 -> ik_trail src pos m }.

(* what one pass of the switch gives from a loop head *)
Definition stepx_post (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a0: Z) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kx wrap src pos out a0 m'
  | IRet _ m' => Kx wrap src pos out a0 m'
  end.

(* stepx_post for every loop head (with Kc and mwf3, as inflate_codes' group_ok) whose mode satisfies P *)
Definition groupx_ok (P: Z -> Prop) : Prop :=
  forall wrap src pos out a0 inp aout flush m,
    ctx_ok src pos inp -> Kc wrap src pos inp aout m -> Kx wrap src pos out a0 m -> mwf3 m ->
    m_leave m = 0 -> P (m_mode m) ->
    stepx_post wrap src pos out a0 (stepf2 flush lenfix_list distfix_list m).

(* groupx_ok with the previous output bytes (CHECK's CRC-32 continuation needs bytes_ok out) *)
Definition groupx_okb (P: Z -> Prop) : Prop :=
  forall wrap src pos out a0 inp aout flush m,
    ctx_ok src pos inp -> Kc wrap src pos inp aout m -> Kx wrap src pos out a0 m -> mwf3 m ->
    m_leave m = 0 -> P (m_mode m) -> bytes_ok out ->
    stepx_post wrap src pos out a0 (stepf2 flush lenfix_list distfix_list m).

(* ---------------------------------------------------------------------------------------------- *)
(* The kit: the bit buffer under the machine's primitives (IKBits.v proves ik_kit)                *)

(* m' differs from m at most in the input position, the bit buffer and leave *)
Definition ik_same_but_buf (m m': mst) : Prop :=
  m_s m' = m_s m /\ m_h m' = m_h m /\ m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_ow m' = m_ow m /\
  m_in m' = m_in m /\ m_out m' = m_out m /\ m_ret m' = m_ret m /\ m_adler m' = m_adler m /\
  m_msg m' = m_msg m /\ m_tin m' = m_tin m /\ m_tout m' = m_tout m /\ m_snx m' = m_snx m /\
  m_sow m' = m_sow m.

Record ik_kit : Prop := {
  (* little-endian values *)
  kk_le_app : forall l1 l2, le_val (l1 ++ l2) = le_val l1 + 2 ^ (8 * Zlength l1) * le_val l2;
  kk_le_range : forall l, bytes_ok l -> 0 <= le_val l < 2 ^ (8 * Zlength l);
  kk_le32 : forall l, Zlength l = 4 -> le_val l = le32 l;
  kk_swap32 : forall l, bytes_ok l -> Zlength l = 4 -> swap32 (le_val l) = be32 l;
  (* the bit buffer as values *)
  kk_bb_range : forall src P hold bits, bytes_ok src -> 0 <= P <= Zlength src ->
    ik_bitbuf src P hold bits -> 0 <= hold < 2 ^ bits;
  kk_bb_init : forall src P, bytes_ok src -> 0 <= P <= Zlength src -> ik_bitbuf src P 0 0;
  kk_bb_pull : forall src P hold bits, bytes_ok src -> 0 <= P < Zlength src -> bits <= 56 ->
    ik_bitbuf src P hold bits ->
    ik_bitbuf src (P + 1) (u64 (hold + Znth P src * 2 ^ bits)) (u32 (bits + 8)) /\
    u64 (hold + Znth P src * 2 ^ bits) = hold + Znth P src * 2 ^ bits /\ u32 (bits + 8) = bits + 8;
  kk_bb_drop : forall src P hold bits n, 0 <= n <= bits ->
    ik_bitbuf src P hold bits -> ik_bitbuf src P (Z.shiftr hold n) (bits - n);
  kk_bb_bytebits : forall src P hold bits, ik_bitbuf src P hold bits ->
    ik_bitbuf src P (Z.shiftr hold (bits mod 8)) (bits - bits mod 8);
  kk_bb_giveback : forall src P hold bits k, bytes_ok src -> 0 <= P <= Zlength src -> 0 <= k -> 8 * k <= bits ->
    ik_bitbuf src P hold bits -> ik_bitbuf src (P - k) (hold mod 2 ^ (bits - 8 * k)) (bits - 8 * k);
  (* hold of k whole bytes: the last k bytes pulled *)
  kk_bb_bytes : forall src P hold k, bytes_ok src -> 0 <= P <= Zlength src -> 0 <= k ->
    ik_bitbuf src P hold (8 * k) -> hold = le_val (sublist (P - k) P src);
  (* the machine's primitives (the call's context: the bytes offered are src[pos .. pos + |inp|)) *)
  kk_pull : forall src pos inp m, ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m < Zlength inp ->
    m_bits m <= 56 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    ik_bitbuf src (pos + m_nx (pull m)) (m_hold (pull m)) (m_bits (pull m)) /\
    m_nx (pull m) = m_nx m + 1 /\ m_bits (pull m) = m_bits m + 8 /\ m_leave (pull m) = m_leave m /\
    ik_same_but_buf m (pull m);
  kk_needbits : forall src pos inp n m, ctx_ok src pos inp -> m_inp m = inp -> 0 <= m_nx m <= Zlength inp ->
    0 <= n <= 32 -> 0 <= m_bits m <= 32 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    let m' := needbits n m in
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (m_bits m < n -> m_bits m' < n + 8) /\ (n <= m_bits m -> m' = m) /\
    ((m_leave m' = 1 /\ m_nx m' = Zlength inp /\ m_bits m' < n) \/ (m_leave m' = m_leave m /\ n <= m_bits m'));
  kk_lookup1 : forall src pos inp fx dx t nb m here m' ok, ctx_ok src pos inp -> m_inp m = inp ->
    0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 40 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    lookup1 fx dx t nb m = (here, m', ok) ->
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (ok = true -> m_leave m' = m_leave m) /\ (ok = false -> m_leave m' = 1);
  kk_lookup2 : forall src pos inp fx dx t last m here m' ok, ctx_ok src pos inp -> m_inp m = inp ->
    0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 40 -> ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) ->
    lookup2 fx dx t last m = (here, m', ok) ->
    ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') /\ ik_same_but_buf m m' /\
    m_nx m <= m_nx m' <= Zlength inp /\ m_bits m' - m_bits m = 8 * (m_nx m' - m_nx m) /\
    (ok = true -> m_leave m' = m_leave m) /\ (ok = false -> m_leave m' = 1);
  (* the reference checks *)
  kk_adler_upd : forall l d, bytes_ok l -> bytes_ok d ->
    adler32_z_val (ref_adler32 1 l) d = ref_adler32 1 (l ++ d);
  kk_crc_upd : forall l d, bytes_ok l -> bytes_ok d -> ref_crc32 (ref_crc32 0 l) d = ref_crc32 0 (l ++ d);
  kk_adler_nil : ref_adler32 1 [] = 1;
  kk_crc_nil : ref_crc32 0 [] = 0
}.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                      *)

(* LEN's fast path: inflate_fast and `if (state->mode == TYPE) state->back = -1;` keep Kx *)
Definition fastx_stmt : Prop :=
  forall wrap src pos out a0 inp aout m,
    ctx_ok src pos inp -> Kc wrap src pos inp aout m -> Kx wrap src pos out a0 m -> mwf3 m ->
    m_leave m = 0 -> m_mode m = LEN -> m_out m = m_aout m ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    let m' := fast lenfix_list distfix_list (restore m) in
    let m' := if m_mode m' =? Zlib.proof.inflate.Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m' in
    Kx wrap src pos out a0 m'.

Definition headx_stmt : Prop := ik_kit -> groupx_ok md_head.
Definition hdrx_stmt : Prop := ik_kit -> groupx_ok md_hdr.
Definition dictx_stmt : Prop := ik_kit -> groupx_ok md_dict.
Definition blockx_stmt : Prop := ik_kit -> groupx_okb md_block.
Definition fastx_part_stmt : Prop := ik_kit -> fastx_stmt.
Definition decx_stmt : Prop := ik_kit -> fastx_stmt -> groupx_ok decode_mode.
(* TABLE -> LENLENS -> CODELENS fall into LEN_ (dec), as in inflate_codes' tab_stmt *)
Definition tabx_stmt : Prop := ik_kit -> stepf2_mwf3_stmt -> groupx_ok decode_mode -> groupx_ok md_tab.

(* the call level (IKTheoryCall.v): the invariant I of the harness's loop and the facts of IKFacts.v, from the
   pass lemma of every mode *)
Definition callx_stmt : Prop := ik_kit -> groupx_ok (fun _ => True) -> ik_theory_stmt.
Definition callxb_stmt : Prop := ik_kit -> groupx_okb (fun _ => True) -> ik_theory_stmt.

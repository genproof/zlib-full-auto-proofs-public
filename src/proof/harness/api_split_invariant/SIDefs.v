(* The theory of the law api_split_invariant: the relation between the concrete model of an inflate()
   call (Model2.run2) and the abstract decoder (SIAbs.astep), and the statements of its parts.

   A concrete call starts at byte P0 of the whole input src (it is offered src[P0 .. P0 + |m_inp|)) with
   the output O0 already written by the earlier calls; it writes m_ow after O0.  At a loop head of the
   call, the machine m is related to an abstract state a (`rel src P0 O0 m a`):
   - the bit position: a_q a = 8 (P0 + m_nx m) - m_bits m, and the bit buffer holds the input's bits
     from there (`bitbuf`); a call may stop in the middle of a NEEDBITS or of a table lookup with more
     bits pulled than used, which does not move the bit position;
   - the output: a_O a = O0 ++ m_ow m;
   - the istate: equal in every field both use (`seq`), the length/offset/extra only in the modes that
     read them (inflate_fast leaves them stale, the slow path sets them); hold/bits as above;
   - check and total: the concrete ones are those of O0 (inf_leave updates them at the end of each call,
     CHECK in the call), the abstract check is the header's value;
   - the window: the last min(|O0|, 32768) bytes of O0 (`swin_ok`), while a match may still read it.
   Between calls, `brel src P O s a` relates the stream's istate s after P bytes read and O written.

   The proof (each a part, in its own file):
   - abstract invariant `awf` (ranges, valid tables with `trep`, wbits 15, no dictionary), kept by astep;
   - `sim_ok P`: one concrete pass of the switch (stepf2) from a related loop head in a mode of P moves
     the abstract state along steps within the call's limits, and if the call stops there, it is for a
     reason the abstract trace sees (`stop_ok`): the stream ended (DONE/BAD), or the next abstract step
     needs input or output space beyond the call's, or the flush is Z_BLOCK/Z_TREES;
   - the call (`call_stmt`): run2 from a boundary state; then the facts of SIFacts.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.api_split_invariant.SIAbs.
Require Export Zlib.proof.inflate.Inv3.
Require Export Zlib.proof.inflate_api.Spec5.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Modes                                                                                          *)

Definition hdr_mode (md: Z) : Prop :=
  md = HEAD \/ md = FLAGS \/ md = TIME \/ md = OS \/ md = EXLEN \/ md = EXTRA \/ md = NAME \/
  md = COMMENT \/ md = HCRC \/ md = DICTID \/ md = DICT.
Definition data_mode (md: Z) : Prop :=
  md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO \/ md = STORED \/ md = COPY_ \/ md = COPY \/
  md = TABLE \/ md = LENLENS \/ md = CODELENS \/ decode_mode md \/ md = CHECK.
Definition post_mode (md: Z) : Prop := md = LENGTH \/ md = DONE.
(* the modes in which a match may still read the window *)
Definition win_mode (md: Z) : Prop := hdr_mode md \/ (data_mode md /\ md <> CHECK).

(* the modes that read state->length, ->offset, ->extra *)
Definition len_live (md: Z) : Prop :=
  md = LENEXT \/ md = DIST \/ md = DISTEXT \/ md = MATCH \/ md = LIT \/ md = COPY_ \/ md = COPY \/ md = EXTRA.
Definition off_live (md: Z) : Prop := md = DISTEXT \/ md = MATCH.
Definition ext_live (md: Z) : Prop := md = LENEXT \/ md = DISTEXT.

(* the groups of the simulation *)
Definition md_hdr (md: Z) : Prop := hdr_mode md.
Definition md_block (md: Z) : Prop :=
  md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO \/ md = STORED \/ md = COPY_ \/ md = COPY \/
  md = CHECK \/ md = LENGTH \/ md = DONE \/ md = BAD.
Definition md_tab (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS.
(* decode modes: Inv.decode_mode (LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT) *)

(* ---------------------------------------------------------------------------------------------- *)
(* Tables: an entry's code bits decide it (inflate_table replicates every entry over the indices    *)
(* that agree with it on its bits, in the root table and in each sub-table)                       *)

Definition trep (get: Z -> entry) (rb: Z) (lk: Z -> bool) : Prop :=
  (forall i j, 0 <= i < 2 ^ rb -> 0 <= j < 2 ^ rb -> lk (e_op (get i)) = false ->
     i mod 2 ^ e_bits (get i) = j mod 2 ^ e_bits (get i) -> get j = get i) /\
  (forall i, 0 <= i < 2 ^ rb -> lk (e_op (get i)) = true ->
     forall j k, 0 <= j < 2 ^ e_op (get i) -> 0 <= k < 2 ^ e_op (get i) ->
       j mod 2 ^ e_bits (get (e_val (get i) + j)) = k mod 2 ^ e_bits (get (e_val (get i) + j)) ->
       get (e_val (get i) + k) = get (e_val (get i) + j)).

(* the tables of the state in use: LENS/DISTS in the decode modes, the code length code in CODELENS *)
Definition tpre_ok (s: istate) : Prop :=
  (decode_mode (i_mode s) ->
     trep (tab_entry lenfix_list distfix_list s (i_lencode s)) (i_lenbits s) len_islink /\
     trep (tab_entry lenfix_list distfix_list s (i_distcode s)) (i_distbits s) dist_islink) /\
  (i_mode s = CODELENS -> trep (tab_entry lenfix_list distfix_list s (i_lencode s)) (i_lenbits s) no_link).

(* a distance entry's largest distance is at most 32768 (the 32 KiB window) *)
Definition dist_ok (e: entry) : Prop := Z.land (e_op e) 16 <> 0 -> e_val e + 2 ^ Z.land (e_op e) 15 - 1 <= 32768.

(* inflate_table's tables have the property, and so have the fixed tables; the distance tables'
   entries have distances up to 32768 (a part) *)
Definition tabrep_stmt : Prop :=
  (forall type lens req old root used t,
     inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
     cap_ok type lens req (Zlength old) -> Forall entry_ok old ->
     inflate_table_model type lens req old = ROk root used t ->
     trep (fun i => Znth i t) root
       (if type =? CODES then no_link else if type =? LENS then len_islink else dist_islink)) /\
  trep (fun i => Znth i lenfix_list) 9 len_islink /\ trep (fun i => Znth i distfix_list) 5 dist_islink /\
  (forall lens req old root used t,
     inputs_ok DISTS lens req -> cap_ok DISTS lens req (Zlength old) -> Forall entry_ok old ->
     inflate_table_model DISTS lens req old = ROk root used t ->
     forall i, 0 <= i < used -> dist_ok (Znth i t)) /\
  Forall dist_ok distfix_list.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract invariant                                                                         *)

Record awf (src: list Z) (a: ast) : Prop := {
  aw_src : bytes_ok src;
  aw_swf : swf (a_s a);
  aw_md : modewf (a_s a);
  aw_s3 : swf3 (a_s a);
  aw_tp : tpre_ok (a_s a);
  aw_wbits : i_wbits (a_s a) = 15;
  aw_wrap : i_wrap (a_s a) = 0 \/ i_wrap (a_s a) = 5 \/ i_wrap (a_s a) = 6 \/ i_wrap (a_s a) = 7;
  aw_dict : i_havedict (a_s a) = 0;
  aw_head : i_head (a_s a) = false;
  aw_mode : HEAD <= a_mode a <= BAD;
  aw_offset : a_mode a = MATCH -> i_offset (a_s a) <= 32768;
  aw_distext : a_mode a = DISTEXT -> i_offset (a_s a) + 2 ^ i_extra (a_s a) - 1 <= 32768;
  aw_dtab : decode_mode (a_mode a) -> forall src' q,
    dist_ok (fst (adecode lenfix_list distfix_list src' (a_s a) (i_distcode (a_s a)) (i_distbits (a_s a))
                          dist_islink q));
  aw_q : 0 <= a_q a;
  aw_O : bytes_ok (a_O a);
  aw_hdrO : hdr_mode (a_mode a) -> a_O a = [];
  (* the header's check value in the data phase: 1 (zlib's adler32) or 0 (gzip's crc32) *)
  aw_chk : data_mode (a_mode a) -> i_wrap (a_s a) <> 0 ->
           (i_flags (a_s a) = 0 /\ i_check (a_s a) = 1) \/ (i_flags (a_s a) <> 0 /\ i_check (a_s a) = 0);
  (* the abstract steps never write state->back (inflateMark's): it keeps a value modewf accepts *)
  aw_back : i_back (a_s a) <= 15;
  (* the gzip header modes after FLAGS: the flags are the header's (8 + 256 FLG), not 0 *)
  aw_gzf : TIME <= a_mode a <= HCRC -> i_flags (a_s a) <> 0 }.

(* the shape of a step: the bit position only grows; the output only grows, by the byte written *)
Definition astep_shape (src: list Z) (a: ast) : Prop :=
  match astep lenfix_list distfix_list src a with
  | AGo n w a' => a_q a <= n /\ a_q a' = n /\
      (a_O a' = a_O a \/ (w = true /\ exists b, a_O a' = a_O a ++ [b]))
  | AEnd _ => True
  end.

(* the initial state after inflateInit2 with windowBits w *)
Definition a0 (w: Z) : ast := AS (l_s (init_live nullval w)) 0 [].

Definition si_window (w: Z) : Prop := w = -15 \/ w = 15 \/ w = 31 \/ w = 47.

(* a part: the invariant at the start, kept by every step, and the shape of the steps *)
Definition awf_stmt : Prop :=
  (forall w src, si_window w -> bytes_ok src -> awf src (a0 w)) /\
  (forall src a n w a', awf src a -> astep lenfix_list distfix_list src a = AGo n w a' -> awf src a') /\
  (forall src a, awf src a -> astep_shape src a).

(* ---------------------------------------------------------------------------------------------- *)
(* The concrete machine's bit buffer                                                              *)

(* the bit position of the machine of a call that started at input byte P0 *)
Definition mq (P0: Z) (m: mst) : Z := 8 * (P0 + m_nx m) - m_bits m.

Record bitbuf (src: list Z) (P0: Z) (m: mst) : Prop := {
  bb_src : bytes_ok src;
  bb_P0 : 0 <= P0;
  bb_inp : P0 + Zlength (m_inp m) <= Zlength src /\ m_inp m = sublist P0 (P0 + Zlength (m_inp m)) src;
  bb_nx : 0 <= m_nx m <= Zlength (m_inp m);
  bb_bits : 0 <= m_bits m <= 39 /\ m_bits m <= 8 * (P0 + m_nx m);
  bb_hold : m_hold m = sbits src (mq P0 m) (m_bits m) }.

(* ---------------------------------------------------------------------------------------------- *)
(* The window                                                                                     *)

(* the byte d back from the end of the window (as MATCH and inflate_fast index it) *)
Definition swin_at (s: istate) (d: Z) : Z :=
  if d <=? i_wnext s then Znth (i_wnext s - d) (i_wdata s) else Znth (i_wsize s - (d - i_wnext s)) (i_wdata s).

(* the window holds the last min(|O|, 32768) bytes of O, or it is not allocated and O is empty *)
Definition swin_ok (s: istate) (O: list Z) : Prop :=
  (i_wsize s = 0 /\ i_whave s = 0 /\ O = []) \/
  (i_wsize s = 32768 /\ i_win s = true /\ i_whave s = Z.min (Zlength O) 32768 /\
   0 <= i_wnext s < 32768 /\ (i_whave s < 32768 -> i_wnext s = i_whave s) /\
   Zlength (i_wdata s) = i_whave s /\
   forall d, 1 <= d <= i_whave s -> swin_at s d = Znth (Zlength O - d) O).

(* ---------------------------------------------------------------------------------------------- *)
(* The relation                                                                                   *)

(* the bit buffer in the modes that read whole bytes: a header field is read by NEEDBITS(n) then INITBITS (all
   the buffer is consumed, so it holds whole bytes, fewer than n bits); the strings, the extra field and a
   stored block's bytes are read from next_in directly (the buffer is empty: also in EXLEN without FEXTRA,
   which goes on into NAME); the trailer by NEEDBITS(32) after
   BYTEBITS / INITBITS *)
Definition bits_ok (s: istate) (bits: Z) : Prop :=
  let md := i_mode s in
  (hdr_mode md -> bits mod 8 = 0 /\ bits < (if orb (md =? TIME) (md =? DICTID) then 32 else 16) /\
                  (md = EXTRA \/ md = NAME \/ md = COMMENT \/ (md = EXLEN /\ Z.land (i_flags s) 1024 = 0) ->
                   bits = 0)) /\
  (md = COPY_ \/ md = COPY -> bits = 0) /\
  (md = CHECK \/ md = LENGTH -> bits mod 8 = 0).

(* the istate fields both machines keep equal *)
Record seq (s t: istate) : Prop := {
  se_last : i_last s = i_last t;
  se_wrap : i_wrap s = i_wrap t;
  se_havedict : i_havedict s = i_havedict t;
  se_flags : i_flags s = i_flags t;
  se_dmax : i_dmax s = i_dmax t;
  se_head : i_head s = i_head t;
  se_wbits : i_wbits s = i_wbits t;
  se_lencode : i_lencode s = i_lencode t;
  se_distcode : i_distcode s = i_distcode t;
  se_lenbits : i_lenbits s = i_lenbits t;
  se_distbits : i_distbits s = i_distbits t;
  se_ncode : i_ncode s = i_ncode t;
  se_nlen : i_nlen s = i_nlen t;
  se_ndist : i_ndist s = i_ndist t;
  se_have : i_have s = i_have t;
  se_next : i_next s = i_next t;
  se_lens : i_lens s = i_lens t;
  se_codes : i_codes s = i_codes t;
  se_sane : i_sane s = i_sane t;
  se_length : len_live (i_mode t) -> i_length s = i_length t;
  se_offset : off_live (i_mode t) -> i_offset s = i_offset t;
  se_extra : ext_live (i_mode t) -> i_extra s = i_extra t }.

(* a loop head of a call that started at input byte P0 with O0 written before *)
Record rel (src: list Z) (P0: Z) (O0: list Z) (m: mst) (a: ast) : Prop := {
  rl_bb : bitbuf src P0 m;
  rl_mode : m_mode m = a_mode a;
  rl_q : m_mode m <> BAD -> a_q a = mq P0 m;
  rl_bits : bits_ok (m_s m) (m_bits m);
  rl_O : a_O a = O0 ++ m_ow m;
  rl_aout : Zlength (m_ow m) <= m_aout m <= Int.max_unsigned;
  rl_in : m_in m = Zlength (m_inp m);
  (* CHECK of a wrapped stream sets out = left; a raw stream's CHECK and LENGTH change nothing *)
  rl_out : m_left m <= m_out m <= m_aout m /\
           (post_mode (m_mode m) -> i_wrap (m_s m) <> 0 -> m_out m = m_left m) /\
           (hdr_mode (m_mode m) \/ data_mode (m_mode m) \/ (post_mode (m_mode m) /\ i_wrap (m_s m) = 0) ->
              m_out m = m_aout m);
  rl_ret : m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK;
  rl_s : m_mode m <> BAD -> seq (m_s m) (a_s a);
  rl_chk : (hdr_mode (m_mode m) -> i_check (m_s m) = i_check (a_s a)) /\
           (data_mode (m_mode m) -> i_wrap (m_s m) <> 0 ->
              i_check (m_s m) = update_check (i_flags (a_s a)) (i_check (a_s a)) O0);
  rl_tot : (hdr_mode (m_mode m) \/ data_mode (m_mode m) \/ (post_mode (m_mode m) /\ i_wrap (m_s m) = 0) ->
              i_total (m_s m) = u64 (Zlength O0)) /\
           (post_mode (m_mode m) -> i_wrap (m_s m) <> 0 -> i_total (m_s m) = u64 (Zlength (a_O a)));
  rl_tout : m_tout m = u64 (Zlength O0 + Zlength (m_ow m) - (m_out m - m_left m));
  rl_win : win_mode (m_mode m) -> swin_ok (m_s m) O0;
  rl_head : i_head (m_s m) = false }.

(* between calls: the stream's istate after P bytes of input were read and O written *)
Record brel (src: list Z) (P: Z) (O: list Z) (s: istate) (a: ast) : Prop := {
  br_P : 0 <= P <= Zlength src;
  br_bits : 0 <= i_bits s <= 39 /\ i_bits s <= 8 * P;
  br_mode : i_mode s = a_mode a;
  br_q : i_mode s <> BAD -> a_q a = 8 * P - i_bits s;
  br_bits_ok : bits_ok s (i_bits s);
  br_hold : i_hold s = sbits src (8 * P - i_bits s) (i_bits s);
  br_O : a_O a = O;
  br_s : i_mode s <> BAD -> seq s (a_s a);
  br_chk : (hdr_mode (i_mode s) -> i_check s = i_check (a_s a)) /\
           (data_mode (i_mode s) -> i_wrap s <> 0 -> i_check s = update_check (i_flags (a_s a)) (i_check (a_s a)) O);
  br_tot : i_mode s <> BAD -> i_total s = u64 (Zlength O);
  br_win : win_mode (i_mode s) -> swin_ok s O;
  br_head : i_head s = false }.

(* why a call may stop at m (related to a): the stream ended, or the next abstract step needs more than
   the call's input (I bytes from the start of src) or output space (R bytes in all), or the flush asks
   inflate() to stop at block boundaries *)
Definition stop_ok (flush: Z) (src: list Z) (I R: Z) (m: mst) (a: ast) : Prop :=
  match astep lenfix_list distfix_list src a with
  | AEnd r => m_ret m = r /\ (m_mode m = DONE \/ m_mode m = BAD)
  | o => m_ret m = Z_OK /\ (flush = Z_BLOCK \/ flush = Z_TREES \/ ablocked src I R a o)
  end.

(* the simulation of one pass of the switch from a loop head in a mode of P *)
Definition sim_ok (P: Z -> Prop) : Prop :=
  forall flush src P0 O0 m a,
    rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> P (m_mode m) ->
    match stepf2 flush lenfix_list distfix_list m with
    | IBrk m' => exists a', areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' /\
                   rel src P0 O0 m' a' /\ (m_leave m' = 1 -> stop_ok flush src (P0 + Zlength (m_inp m))
                                                                  (Zlength O0 + m_aout m) m' a')
    | IRet r m' => r = Z_NEED_DICT /\
                   exists a', areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' /\
                   rel src P0 O0 m' a' /\ astep lenfix_list distfix_list src a' = AEnd Z_NEED_DICT
    end.

(* LEN's fast path: inflate_fast moves along the abstract trace and does not stop the loop *)
Definition fast_sim_stmt : Prop :=
  forall src P0 O0 m a,
    rel src P0 O0 m a -> awf src a -> m_leave m = 0 -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    let m1 := fast lenfix_list distfix_list (restore m) in
    let m2 := if m_mode m1 =? Zlib.proof.inflate.Model.TYPE then upd_s m1 (fun s => set_i_back s (-1)) else m1 in
    exists a', areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' /\ rel src P0 O0 m2 a' /\
               m_leave m2 = 0.

(* ---------------------------------------------------------------------------------------------- *)
(* The kit: the bit buffer operations and the table lookups on the input's bits (a part)          *)

Definition kit_bits_stmt : Prop :=
  (* PULLBYTE *)
  (forall src P0 m, bitbuf src P0 m -> 0 < m_have m -> m_bits m <= 31 ->
     bitbuf src P0 (pull m) /\ mq P0 (pull m) = mq P0 m) /\
  (* NEEDBITS(n): the bits pulled are the input's; when it does not leave, the low n bits of hold are
     the n bits at the bit position; when it leaves, the input of the call ends before them *)
  (forall src P0 m n, bitbuf src P0 m -> m_leave m = 0 -> 0 <= n <= 32 ->
     let m' := needbits n m in
     bitbuf src P0 m' /\ mq P0 m' = mq P0 m /\
     m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
     (m_leave m' = 0 -> n <= m_bits m' /\ m_bits m' <= Z.max (m_bits m) (n + 7) /\
                        m_hold m' mod 2 ^ n = sbits src (mq P0 m) n) /\
     (m_leave m' <> 0 -> m_leave m' = 1 /\ m_have m' = 0 /\ m_bits m' < n /\
                         8 * (P0 + Zlength (m_inp m)) < mq P0 m + n)) /\
  (* DROPBITS(k) and BITS(k) *)
  (forall src P0 m k, bitbuf src P0 m -> 0 <= k <= m_bits m ->
     bitbuf src P0 (dropbits k m) /\ mq P0 (dropbits k m) = mq P0 m + k /\
     bitsn m k = sbits src (mq P0 m) k) /\
  (* INITBITS: all the bits are consumed *)
  (forall src P0 m, bitbuf src P0 m -> bitbuf src P0 (initbits m) /\ mq P0 (initbits m) = mq P0 m + m_bits m) /\
  (* BYTEBITS *)
  (forall src P0 m, bitbuf src P0 m ->
     bitbuf src P0 (bytebits m) /\ mq P0 (bytebits m) = align8 (mq P0 m)) /\
  (* the bits of the input *)
  (forall src q n k, bytes_ok src -> 0 <= q -> 0 <= k <= n -> sbits src q n mod 2 ^ k = sbits src q k) /\
  (forall src q n k, bytes_ok src -> 0 <= q -> 0 <= k <= n ->
     Z.shiftr (sbits src q n) k = sbits src (q + k) (n - k)) /\
  (forall src q n, bytes_ok src -> 0 <= n -> 0 <= sbits src q n < 2 ^ n) /\
  (forall src q, bytes_ok src -> 0 <= q -> q mod 8 = 0 -> sbits src q 8 = sbyte src q).

(* the slow path's lookups (lookup1, then lookup2 after a link) find the entry of adecode, or leave
   because the code is longer than the bits the call has *)
Definition kit_lookup_stmt : Prop :=
  forall src P0 m kind t nb lk,
    bitbuf src P0 m -> m_leave m = 0 ->
    tvalid kind lenfix_list distfix_list (m_s m) t nb ->
    trep (tab_entry lenfix_list distfix_list (m_s m) t) nb lk ->
    (forall op, lk op = true -> islink kind op = true) ->
    let q := mq P0 m in
    let root := tab_entry lenfix_list distfix_list (m_s m) t (sbits src q nb) in
    (let '(here, m', ok) := lookup1 lenfix_list distfix_list t nb m in
     m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
     bitbuf src P0 m' /\ mq P0 m' = q /\
     (ok = true -> m_leave m' = 0 /\ here = root /\ e_bits here <= m_bits m' /\
                   m_bits m' <= Z.max (m_bits m) (e_bits here + 7)) /\
     (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\ 8 * (P0 + Zlength (m_inp m)) < q + e_bits root)) /\
    (lk (e_op root) = true ->
     forall m1, bitbuf src P0 m1 -> m_leave m1 = 0 -> m_s m1 = m_s m -> m_inp m1 = m_inp m -> mq P0 m1 = q -> e_bits root <= m_bits m1 ->
     let h2 := tab_entry lenfix_list distfix_list (m_s m) t (e_val root + sbits src (q + e_bits root) (e_op root)) in
     let '(here, m', ok) := lookup2 lenfix_list distfix_list t root m1 in
     m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m1 (m_nx m')) (m_hold m')) (m_bits m')) (m_leave m') /\
     bitbuf src P0 m' /\ mq P0 m' = q /\
     (ok = true -> m_leave m' = 0 /\ here = h2 /\ e_bits root + e_bits here <= m_bits m' /\
                   m_bits m' <= Z.max (m_bits m1) (e_bits root + e_bits here + 7)) /\
     (ok = false -> m_leave m' = 1 /\ m_have m' = 0 /\
                    8 * (P0 + Zlength (m_inp m)) < q + e_bits root + e_bits h2)).

Definition kit_stmt : Prop := kit_bits_stmt /\ kit_lookup_stmt.

(* ---------------------------------------------------------------------------------------------- *)
(* The group statements (parts) and the call                                                      *)

Definition hdr_sim_stmt : Prop := kit_stmt -> awf_stmt -> sim_ok md_block -> sim_ok md_hdr.
Definition block_sim_stmt : Prop := kit_stmt -> awf_stmt -> sim_ok md_block.
Definition dec_sim_stmt : Prop := kit_stmt -> awf_stmt -> fast_sim_stmt -> sim_ok decode_mode.
Definition tab_sim_stmt : Prop := kit_stmt -> awf_stmt -> sim_ok decode_mode -> sim_ok md_tab.
Definition fast_part_stmt : Prop := kit_stmt -> awf_stmt -> fast_sim_stmt.

Definition final_code (r: Z) : bool := (r =? Z_STREAM_END) || (r =? Z_NEED_DICT) || (r =? Z_DATA_ERROR).

(* one call from a boundary state: the abstract state moves within the call's limits; the call's result
   is the abstract state's (the stream's end, or a stop the abstract trace sees) *)
Definition call_stmt : Prop :=
  forall src flush P O z L inp res a,
    awf src a -> brel src P O (l_s L) a -> live_ok L -> zf_ok z -> zf_tout z = u64 (Zlength O) ->
    0 <= P -> P + Zlength inp <= Zlength src -> inp = sublist P (P + Zlength inp) src ->
    Zlength inp <= Int.max_unsigned ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in let r := r_ret res in
    let I := P + Zlength inp in let R := Zlength O + zf_ao z in
    r = Z_MEM_ERROR \/
    (m_inp m = inp /\ m_aout m = zf_ao z /\ 0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\
     Zlength (m_ow m) <= zf_ao z /\ m_tout m = u64 (Zlength O + Zlength (m_ow m)) /\
     exists a', areach src I R a a' /\ awf src a' /\ brel src (P + m_snx m) (O ++ m_ow m) (m_s m) a' /\
       (final_code r = true -> astep lenfix_list distfix_list src a' = AEnd r) /\
       (final_code r = false -> (r = Z_OK \/ r = Z_BUF_ERROR) /\
          (flush = Z_BLOCK \/ flush = Z_TREES \/ ablocked src I R a' (astep lenfix_list distfix_list src a')))).

Definition call_part_stmt : Prop :=
  kit_stmt -> awf_stmt -> sim_ok md_hdr -> sim_ok md_block -> sim_ok md_tab -> sim_ok decode_mode -> call_stmt.

(* Law inflate_header, the theory: THE definitions shared by IHT*.v.

   The input is the fixed member src = ih_src g (IHFacts.v); every call is offered src[pos .. pos + |inp|).
   The state of inflate at a loop head (and at a call boundary) is described relative to the absolute
   position P = pos + m_nx (the bytes of src consumed so far) by `J`, one constructor per mode:
   HEAD (P <= 1 bytes in the bit buffer), FLAGS (bytes 2..3), TIME (4..7), OS (8..9), EXLEN (10..11), EXTRA
   (the extra field [ih_xs, ih_ne), i_length = what is left of it, the buffer partial), NAME [ih_ne, ih_nn),
   COMMENT [ih_nn, ih_nc), HCRC (the 2 stored bytes [ih_nc, ih_nh)), then TYPE/TYPEDO, STORED, COPY_/COPY,
   CHECK, LENGTH, DONE over the 13 bytes after the header (01 00 00 ff ff, 8 zero bytes); BAD only for a
   reserved FLG bit or a wrong header CRC, with head->done = 0.  The bit buffer (hold, bits) holds the bytes
   [a, P) of the current field (`bb`); the header CRC (when FHCRC) is the CRC-32 of src[0 .. k) (`ck`).
   `Jc`: what holds in every mode (wrap 6/7, or 14/15 with bit 3 when windowBits 16/32
   leaves the window size to the header (fix F8), i_head, no window, total 0, the header maxima).
   `Km`: the machine at a loop head of one call (or its exit): J plus the locals (no output, out = avail_out,
   total_out 0, the return code).
   Case lemmas: `case_ok X c`: from a loop head in mode X, c gives a machine satisfying Km (never IRet).
   The kit `ih_kit`: the facts about src and the model's helpers the cases use (proved in IHTKit*.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_header.IHFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* little-endian value of bytes (the bit buffer after pulling them from bits = 0) *)
Fixpoint ih_le (l: list Z) : Z :=
  match l with [] => 0 | b :: l' => b + 256 * ih_le l' end.

(* ---------------------------------------------------------------------------------------------- *)
(* Positions in src                                                                               *)

(* the end of the extra part (XLEN and the field) *)
Definition ih_ne (g: ihg) : Z := 10 + (if fl g 4 then 2 + Zlength (g_xf g) else 0).
(* the start of the extra field's data *)
Definition ih_xs (g: ihg) : Z := if fl g 4 then 12 else 10.
(* the end of the name (zero byte included) *)
Definition ih_nn (g: ihg) : Z := ih_ne g + (if fl g 8 then Zlength (g_nf g) + 1 else 0).
(* the end of the comment = the length of the header *)
Definition ih_nc (g: ihg) : Z := ih_nn g + (if fl g 16 then Zlength (g_cf g) + 1 else 0).
(* the end of the stored header CRC *)
Definition ih_nh (g: ihg) : Z := ih_nc g + (if fl g 2 then 2 else 0).

(* ---------------------------------------------------------------------------------------------- *)
(* The state                                                                                      *)

(* in every mode *)
Record Jc (h0: hstate) (s: istate) (h: hstate) : Prop := {
  jc_wrap : i_wrap s = 6 \/ i_wrap s = 7 \/ i_wrap s = 14 \/ i_wrap s = 15;
  jc_head : i_head s = true;
  jc_wsize : i_wsize s = 0;
  jc_total : i_total s = 0;
  jc_xmax : h_extra_max h = h_extra_max h0;
  jc_nmax : h_name_max h = h_name_max h0;
  jc_cmax : h_comm_max h = h_comm_max h0 }.

(* the bit buffer holds src[a .. P) *)
Definition bb (g: ihg) (a P hold bits: Z) : Prop :=
  bits = 8 * (P - a) /\ hold = ih_le (sublist a P (ih_src g)).

(* the header CRC so far (only computed with FHCRC) *)
Definition ck (g: ihg) (s: istate) (k: Z) : Prop :=
  fl g 2 = true -> i_check s = ref_crc32 0 (sublist 0 k (ih_src g)).

(* state->flags once FLAGS was read *)
Definition fg (g: ihg) (s: istate) : Prop := i_flags s = 8 + 256 * g_flg g.

(* the gz_header: fields not touched yet *)
Definition hx0 (h0 h: hstate) : Prop := h_xp h = h_xp h0 /\ h_xbuf h = h_xbuf h0.
Definition hn0 (h0 h: hstate) : Prop := h_np h = h_np h0 /\ h_nbuf h = h_nbuf h0.
Definition hc0 (h0 h: hstate) : Prop := h_cp h = h_cp h0 /\ h_cbuf h = h_cbuf h0.
(* fields stored *)
Definition hT (g: ihg) (h: hstate) : Prop := h_text h = Z.land (g_flg g) 1.
Definition hM (g: ihg) (h: hstate) : Prop := h_time h = g_mtime g.
Definition hO (g: ihg) (h: hstate) : Prop := h_xflags h = g_xfl g /\ h_os h = g_os g.
(* the extra field: k bytes stored (partial), all of it (final) *)
Definition hxk (g: ihg) (h0: hstate) (k: Z) (h: hstate) : Prop :=
  if fl g 4 then h_extra_len h = Zlength (g_xf g) /\ h_xp h = h_xp h0 /\
                 (h_xp h0 = true -> h_xbuf h = fbuf (h_xbuf h0) (sublist 0 k (g_xf g)))
  else h_xp h = false.
Definition hxf (g: ihg) (h0: hstate) (h: hstate) : Prop :=
  if fl g 4 then h_extra_len h = Zlength (g_xf g) /\ h_xp h = h_xp h0 /\
                 (h_xp h0 = true -> h_xbuf h = fbuf (h_xbuf h0) (g_xf g))
  else h_xp h = false.
(* the name: k bytes read (partial, also without FNAME at k = 0), all of it with the zero byte (final) *)
Definition hnk (g: ihg) (h0: hstate) (k: Z) (h: hstate) : Prop :=
  h_np h = h_np h0 /\ (h_np h0 = true -> h_nbuf h = fbuf (h_nbuf h0) (sublist 0 k (g_nf g ++ [0]))).
Definition hnf (g: ihg) (h0: hstate) (h: hstate) : Prop :=
  if fl g 8 then h_np h = h_np h0 /\ (h_np h0 = true -> h_nbuf h = fbuf (h_nbuf h0) (g_nf g ++ [0]))
  else h_np h = false.
Definition hck (g: ihg) (h0: hstate) (k: Z) (h: hstate) : Prop :=
  h_cp h = h_cp h0 /\ (h_cp h0 = true -> h_cbuf h = fbuf (h_cbuf h0) (sublist 0 k (g_cf g ++ [0]))).
Definition hcf (g: ihg) (h0: hstate) (h: hstate) : Prop :=
  if fl g 16 then h_cp h = h_cp h0 /\ (h_cp h0 = true -> h_cbuf h = fbuf (h_cbuf h0) (g_cf g ++ [0]))
  else h_cp h = false.

(* the state at absolute position P (s: the struct; h: the gz_header; hold, bits: the bit buffer) *)
Inductive J (g: ihg) (h0: hstate) (P: Z) (s: istate) (h: hstate) (hold bits: Z) : Prop :=
| J_HEAD : i_mode s = HEAD -> 0 <= P <= 1 -> bb g 0 P hold bits ->
    h_done h = 0 -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J g h0 P s h hold bits
| J_FLAGS : i_mode s = FLAGS -> 2 <= P <= 3 -> bb g 2 P hold bits ->
    i_check s = ref_crc32 0 (sublist 0 2 (ih_src g)) ->
    h_done h = 0 -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J g h0 P s h hold bits
| J_TIME : i_mode s = TIME -> 4 <= P <= 7 -> bb g 4 P hold bits ->
    fg g s -> ih_reserved g = false -> ck g s 4 ->
    h_done h = 0 -> hT g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J g h0 P s h hold bits
| J_OS : i_mode s = OS -> 8 <= P <= 9 -> bb g 8 P hold bits ->
    fg g s -> ih_reserved g = false -> ck g s 8 ->
    h_done h = 0 -> hT g h -> hM g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J g h0 P s h hold bits
| J_EXLEN : i_mode s = EXLEN -> 10 <= P <= 10 + (if fl g 4 then 1 else 0) -> bb g 10 P hold bits ->
    fg g s -> ih_reserved g = false -> ck g s 10 ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hx0 h0 h -> hn0 h0 h -> hc0 h0 h -> i_last s = 0 -> J g h0 P s h hold bits
| J_EXTRA : i_mode s = EXTRA -> ih_xs g <= P <= ih_ne g -> hold = 0 -> bits = 0 ->
    (fl g 4 = true -> i_length s = ih_ne g - P) ->
    fg g s -> ih_reserved g = false -> ck g s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxk g h0 (P - ih_xs g) h -> hn0 h0 h -> hc0 h0 h ->
    i_last s = 0 -> J g h0 P s h hold bits
| J_NAME : i_mode s = NAME -> ih_ne g <= P -> (P < ih_nn g \/ P = ih_ne g) -> hold = 0 -> bits = 0 ->
    i_length s = (if h_np h0 then Z.min (P - ih_ne g) (h_name_max h0) else 0) ->
    fg g s -> ih_reserved g = false -> ck g s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnk g h0 (P - ih_ne g) h -> hc0 h0 h ->
    i_last s = 0 -> J g h0 P s h hold bits
| J_COMMENT : i_mode s = COMMENT -> ih_nn g <= P -> (P < ih_nc g \/ P = ih_nn g) -> hold = 0 -> bits = 0 ->
    i_length s = (if h_cp h0 then Z.min (P - ih_nn g) (h_comm_max h0) else 0) ->
    fg g s -> ih_reserved g = false -> ck g s P ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hck g h0 (P - ih_nn g) h ->
    i_last s = 0 -> J g h0 P s h hold bits
| J_HCRC : i_mode s = HCRC -> ih_nc g <= P <= ih_nc g + (if fl g 2 then 1 else 0) ->
    bb g (ih_nc g) P hold bits -> fg g s -> ih_reserved g = false -> ck g s (ih_nc g) ->
    h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hcf g h0 h ->
    i_last s = 0 -> J g h0 P s h hold bits
| J_TYPE : (i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO) ->
    ((P = ih_nh g /\ i_last s = 0) \/ (P = ih_nh g + 5 /\ i_last s = 1)) -> hold = 0 -> bits = 0 ->
    i_check s = 0 -> fg g s -> ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_STORED : i_mode s = STORED -> i_last s = 1 -> ih_nh g + 1 <= P <= ih_nh g + 4 ->
    (bb g (ih_nh g + 1) P hold bits \/ (P = ih_nh g + 1 /\ hold = 0 /\ bits = 5)) ->
    i_check s = 0 -> fg g s -> ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_COPY : (i_mode s = COPY_ \/ i_mode s = COPY) -> P = ih_nh g + 5 -> hold = 0 -> bits = 0 ->
    i_length s = 0 -> i_last s = 1 ->
    i_check s = 0 -> fg g s -> ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_CHECK : i_mode s = CHECK -> ih_nh g + 5 <= P <= ih_nh g + 8 -> bb g (ih_nh g + 5) P hold bits ->
    i_check s = 0 -> fg g s -> ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_LENGTH : i_mode s = LENGTH -> ih_nh g + 9 <= P <= ih_nh g + 12 -> bb g (ih_nh g + 9) P hold bits ->
    fg g s -> ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_DONE : i_mode s = DONE -> P = ih_nh g + 13 ->
    ih_reserved g = false -> ih_badcrc g = false -> ih_done_ok g h0 h ->
    J g h0 P s h hold bits
| J_BAD : i_mode s = BAD -> h_done h = 0 -> orb (ih_reserved g) (ih_badcrc g) = true ->
    J g h0 P s h hold bits.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

(* the bytes offered are src[pos .. pos + |inp|) *)
Definition ih_ctx (g: ihg) (pos: Z) (inp: list Z) : Prop :=
  0 <= pos /\ pos + Zlength inp <= Zlength (ih_src g) /\ inp = sublist pos (pos + Zlength inp) (ih_src g).

(* the machine at a loop head (or the exit) of a call offered inp at pos *)
Record Km (g: ihg) (h0: hstate) (pos: Z) (inp: list Z) (m: mst) : Prop := {
  km_inp : m_inp m = inp;
  km_nx : 0 <= m_nx m <= Zlength inp;
  km_ow : m_ow m = [];
  km_out : m_out m = m_aout m;
  km_tout : m_tout m = 0;
  km_ret : m_ret m = Z_OK \/ (m_ret m = Z_STREAM_END /\ m_mode m = DONE) \/
           (m_ret m = Z_DATA_ERROR /\ m_mode m = BAD);
  km_lv : m_leave m = 0 \/ m_leave m = 1;
  km_jc : Jc h0 (m_s m) (m_h m);
  km_j : J g h0 (pos + m_nx m) (m_s m) (m_h m) (m_hold m) (m_bits m) }.

Definition ok_out (g: ihg) (h0: hstate) (pos: Z) (inp: list Z) (o: iout) : Prop :=
  match o with IBrk m' => Km g h0 pos inp m' | IRet _ _ => False end.

(* from a loop head in mode X, the case c keeps Km *)
Definition case_ok (X: Z) (c: mst -> iout) : Prop :=
  forall g h0 pos inp m,
    ih_ok g -> hwf h0 -> ih_ctx g pos inp -> Km g h0 pos inp m -> m_leave m = 0 -> m_mode m = X ->
    ok_out g h0 pos inp (c m).

(* ---------------------------------------------------------------------------------------------- *)
(* The kit                                                                                        *)

(* the layout of src *)
Record ih_lay (g: ihg) : Prop := {
  ly_bytes : is_bytes (ih_src g);
  ly_len : Zlength (ih_src g) = ih_nh g + 13;
  ly_ord : ih_xs g <= ih_ne g /\ ih_ne g <= ih_nn g /\ ih_nn g <= ih_nc g /\ ih_nc g <= ih_nh g;
  ly_hdr : sublist 0 (ih_nc g) (ih_src g) = ih_hdr g;
  ly_id : ih_le (sublist 0 2 (ih_src g)) = 35615 /\ hbytes2 35615 = sublist 0 2 (ih_src g);
  ly_fl : ih_le (sublist 2 4 (ih_src g)) = 8 + 256 * g_flg g /\
          hbytes2 (8 + 256 * g_flg g) = sublist 2 4 (ih_src g);
  ly_mt : ih_le (sublist 4 8 (ih_src g)) = g_mtime g /\ hbytes4 (g_mtime g) = sublist 4 8 (ih_src g);
  ly_os : ih_le (sublist 8 10 (ih_src g)) = g_xfl g + 256 * g_os g /\
          hbytes2 (g_xfl g + 256 * g_os g) = sublist 8 10 (ih_src g);
  ly_xl : fl g 4 = true -> ih_le (sublist 10 12 (ih_src g)) = Zlength (g_xf g) /\
          hbytes2 (Zlength (g_xf g)) = sublist 10 12 (ih_src g);
  ly_xf : fl g 4 = true -> sublist 12 (ih_ne g) (ih_src g) = g_xf g;
  ly_nf : fl g 8 = true -> sublist (ih_ne g) (ih_nn g) (ih_src g) = g_nf g ++ [0];
  ly_cf : fl g 16 = true -> sublist (ih_nn g) (ih_nc g) (ih_src g) = g_cf g ++ [0];
  ly_hc : fl g 2 = true ->
          (ih_le (sublist (ih_nc g) (ih_nc g + 2) (ih_src g)) =?
           Z.land (ref_crc32 0 (sublist 0 (ih_nc g) (ih_src g))) 65535) = negb (ih_badcrc g);
  ly_blk : sublist (ih_nh g) (ih_nh g + 5) (ih_src g) = [1; 0; 0; 255; 255];
  ly_tr : sublist (ih_nh g + 5) (ih_nh g + 13) (ih_src g) = Zrepeat 0 8 }.

(* FLG in state->flags (= CM + 256 * FLG), XFL/OS in hold *)
Definition ih_bits_stmt : Prop :=
  (forall F, 0 <= F <= 255 ->
    s32 (8 + 256 * F) = 8 + 256 * F /\ Z.land (8 + 256 * F) 255 = 8 /\
    (Z.land (8 + 256 * F) 57344 =? 0) = (Z.land F 224 =? 0) /\
    (Z.land (8 + 256 * F) 512 =? 0) = (Z.land F 2 =? 0) /\
    (Z.land (8 + 256 * F) 1024 =? 0) = (Z.land F 4 =? 0) /\
    (Z.land (8 + 256 * F) 2048 =? 0) = (Z.land F 8 =? 0) /\
    (Z.land (8 + 256 * F) 4096 =? 0) = (Z.land F 16 =? 0) /\
    Z.land (Z.shiftr (8 + 256 * F) 8) 1 = Z.land F 1 /\
    Z.land (Z.shiftr (8 + 256 * F) 9) 1 = Z.land (Z.shiftr F 1) 1) /\
  (forall a b, 0 <= a <= 255 -> 0 <= b <= 255 ->
    Z.land (a + 256 * b) 255 = a /\ s32 (Z.shiftr (a + 256 * b) 8) = b).

(* NEEDBITS(n) when the bit buffer holds src[a .. P) (whole bytes) *)
Definition ih_nb_stmt : Prop :=
  forall (src inp: list Z) (pos a n: Z) (m: mst),
    is_bytes src -> 0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
    m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 < n <= 32 -> 0 <= a ->
    a <= pos + m_nx m <= a + (n + 7) / 8 ->
    m_bits m = 8 * (pos + m_nx m - a) -> m_hold m = ih_le (sublist a (pos + m_nx m) src) ->
    exists nx' lv',
      needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') (ih_le (sublist a (pos + nx') src)))
                                   (8 * (pos + nx' - a))) lv' /\
      m_nx m <= nx' <= Zlength inp /\
      ((lv' = 1 /\ nx' = Zlength inp /\ pos + nx' < a + (n + 7) / 8) \/
       (lv' = m_leave m /\ pos + nx' = a + (n + 7) / 8)).

(* the do-while of NAME / COMMENT on the field f (nonzero bytes, then 0), j bytes of it read before *)
Definition ih_zstr_stmt : Prop :=
  forall (f bytes buf b0: list Z) (j have: Z) (wr: bool) (k: nat),
    0 < Zlength f -> Znth (Zlength f - 1) f = 0 -> (forall i, 0 <= i < Zlength f - 1 -> Znth i f <> 0) ->
    0 <= j < Zlength f -> 0 < have -> (Z.to_nat have <= k)%nat ->
    (forall i, 0 <= i < Z.min have (Zlength f - j) -> Znth i bytes = Znth (j + i) f) ->
    (wr = true -> buf = fbuf b0 (sublist 0 j f)) ->
    zstr_f k bytes have (if wr then Z.min j (Zlength b0) else 0) (Zlength b0) wr buf 0 =
    (Z.min have (Zlength f - j), Znth (j + Z.min have (Zlength f - j) - 1) f,
     (if wr then Z.min (j + Z.min have (Zlength f - j)) (Zlength b0) else 0),
     (if wr then fbuf b0 (sublist 0 (j + Z.min have (Zlength f - j)) f) else buf)).

(* EXTRA's zmemcpy into head->extra: j bytes of the field xf stored before, c more read *)
Definition ih_put_stmt : Prop :=
  forall (b0 xf: list Z) (j c: Z),
    0 <= j -> 0 < c -> j + c <= Zlength xf -> Zlength xf <= 65535 ->
    (j < Zlength b0 ->
       put_bytes (fbuf b0 (sublist 0 j xf)) j
         (sublist j (j + (if Zlength b0 <? u32 (j + c) then Zlength b0 - j else c)) xf) =
       fbuf b0 (sublist 0 (j + c) xf)) /\
    (Zlength b0 <= j -> fbuf b0 (sublist 0 j xf) = fbuf b0 (sublist 0 (j + c) xf)).

(* the CRC of a prefix, continued *)
Definition ih_crc_stmt : Prop :=
  forall (src: list Z) (a b: Z), is_bytes src -> 0 <= a <= b -> b <= Zlength src ->
    ref_crc32 (ref_crc32 0 (sublist 0 a src)) (sublist a b src) = ref_crc32 0 (sublist 0 b src).

(* the input offered, in src *)
Definition ih_in_stmt : Prop :=
  forall (src inp: list Z) (pos nx n: Z),
    0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
    0 <= nx -> 0 <= n -> nx + n <= Zlength inp ->
    sublist nx (nx + n) inp = sublist (pos + nx) (pos + nx + n) src /\
    (n > 0 -> Znth nx inp = Znth (pos + nx) src).

Record ih_kit : Prop := {
  k_lay : forall g, ih_ok g -> ih_lay g;
  k_bits : ih_bits_stmt;
  k_nb : ih_nb_stmt;
  k_zstr : ih_zstr_stmt;
  k_put : ih_put_stmt;
  k_crc : ih_crc_stmt;
  k_in : ih_in_stmt }.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases (each falls through into the next one: its statement assumes the next)              *)

Definition ihc_head_stmt : Prop := ih_kit -> case_ok HEAD c_HEAD2.
Definition ihc_flags_stmt : Prop := ih_kit -> case_ok TIME c_TIME2 -> case_ok FLAGS c_FLAGS2.
Definition ihc_time_stmt : Prop := ih_kit -> case_ok OS c_OS2 -> case_ok TIME c_TIME2.
Definition ihc_os_stmt : Prop := ih_kit -> case_ok EXLEN c_EXLEN2 -> case_ok OS c_OS2.
Definition ihc_exlen_stmt : Prop := ih_kit -> case_ok EXTRA c_EXTRA2 -> case_ok EXLEN c_EXLEN2.
Definition ihc_extra_stmt : Prop := ih_kit -> case_ok NAME c_NAME2 -> case_ok EXTRA c_EXTRA2.
Definition ihc_name_stmt : Prop := ih_kit -> case_ok COMMENT c_COMMENT2 -> case_ok NAME c_NAME2.
Definition ihc_comment_stmt : Prop := ih_kit -> case_ok HCRC c_HCRC -> case_ok COMMENT c_COMMENT2.
Definition ihc_hcrc_stmt : Prop := ih_kit -> case_ok HCRC c_HCRC.
Definition ihc_block_stmt : Prop := ih_kit ->
  (forall flush, case_ok Zlib.proof.inflate.Model.TYPE (c_TYPE flush)) /\
  (forall flush, case_ok TYPEDO (c_TYPEDO flush)) /\
  (forall flush, case_ok STORED (c_STORED flush)) /\
  case_ok COPY_ c_COPY_ /\ case_ok COPY c_COPY /\ case_ok CHECK c_CHECK /\ case_ok LENGTH c_LENGTH /\
  case_ok DONE c_DONE /\ case_ok BAD c_BAD.

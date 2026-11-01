(* Version 5 (= version 4 over the corrected model Model2.v (run2), the case layer v5 (Callees5's Vprog),
   live_ok: wbits 0 -> wrapped and no window (patch F6 of patch/PATCH.md makes it an invariant), the header
   pointer facts; head_mem with the zero-size header buffers' tokens).  Version 4 (= version 3 + fixes: live_ok's
   wbits-0 conjunct (it also gives wbits <> 0 in DICT), the wbits range of a reset's input, the uInt bound of a
   dictionary, syncsearch's got/len ranges, inflate()'s buffers only on a live stream, inflateInit2_ on a stream
   with undefined fields (rawf, istream_raw)).  Version 3 of the external specifications (the first version + the fixes:
   the invariant swf3 of Inv3.v, a writable gz_header share, the padding of struct inflate_state, malloc tokens for possibly
   empty buffers, reset functions that accept any values in the fields they only write).

   THE external specifications of inflate.c's API functions (one per function, for every client: the
   inflate harnesses, uncompr.c, the round-trip laws), at the compspecs of the inflate unit.

   A stream after inflateInit2_ is `istream gv shs strmp z st`: the struct z_stream at strmp with the
   fields z (zfields, ApiModel), zalloc/zfree = zcalloc/zcfree, opaque = NULL, and
   - st = Some L (live): strm->state = l_sp L, the malloc'ed struct inflate_state holding l_s L (an
     istate satisfying swf and modewf), the window (allocated or not), the gz_header record l_h L;
   - st = None (ended or never started): strm->state = NULL.
   The application's gz_header (inflateGetHeader) is NOT part of istream: when i_head (l_s L), inflate()
   takes `head_mem L` too (head_rep of Rep.v) and gives it back.

   Every function's result is given by the model (src/proof/inflate/Model.v `run` for inflate(),
   src/proof/inflate_api/Model.v for the others). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Callees5.
Require Export Zlib.proof.inflate.CaseHyps5.
Require Export Zlib.proof.inflate_api.ApiModel.
Require Zlib.proof.zutil.Spec.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The live part of a stream                                                                     *)

Record live := Live {
  l_sp : val;       (* strm->state *)
  l_winp : val;     (* the window when allocated (i_win) *)
  l_s : istate;
  l_h : hstate;     (* the application's gz_header, meaningful when i_head *)
  l_headp : val; l_hsh : share; l_xb : val; l_nb : val; l_cb : val }.

Definition set_l_s (L: live) (s: istate) : live :=
  Live (l_sp L) (l_winp L) s (l_h L) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L).
Definition set_l_winp (L: live) (w: val) : live :=
  Live (l_sp L) w (l_s L) (l_h L) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L).
Definition set_l_head (L: live) (h: hstate) (headp: val) (hsh: share) (xb nb cb: val) : live :=
  Live (l_sp L) (l_winp L) (l_s L) h headp hsh xb nb cb.

Definition live_ok (L: live) : Prop :=
  isptr (l_sp L) /\ swf (l_s L) /\ modewf (l_s L) /\ hwf (l_h L) /\ swf3 (l_s L) /\ writable_share (l_hsh L) /\
  (* wbits 0 (window size from the header): a zlib or gzip wrapped stream (wrap & 3, so that inflateValidate,
     which toggles bit 4, keeps it) without a window (patch F6) *)
  (i_wbits (l_s L) = 0 -> Z.land (i_wrap (l_s L)) 3 <> 0 /\ i_win (l_s L) = false) /\
  (* a header field marked present has a buffer *)
  (i_head (l_s L) = true ->
     (h_xp (l_h L) = true -> l_xb L <> nullval) /\ (h_np (l_h L) = true -> l_nb L <> nullval) /\
     (h_cp (l_h L) = true -> l_cb L <> nullval)) /\
  (* wbits 0 with a wrapper: before the header (HEAD) or a final mode *)
  (i_wbits (l_s L) = 0 -> i_wrap (l_s L) <> 0 ->
     i_flags (l_s L) = -1 /\ (i_mode (l_s L) = HEAD \/ i_mode (l_s L) = BAD \/ i_mode (l_s L) = SYNC \/
                              i_mode (l_s L) = MEM)).

Lemma land3_wrap: forall w, Z.land w 3 <> 0 -> w <> 0.
Proof. intros w H E. subst w. apply H. reflexivity. Qed.

Definition zf_ok (z: zfields) : Prop :=
  0 <= zf_ai z <= Int.max_unsigned /\ 0 <= zf_ao z <= Int.max_unsigned /\
  0 <= zf_tin z <= Int64.max_unsigned /\ 0 <= zf_tout z <= Int64.max_unsigned /\
  Int.min_signed <= zf_dt z <= Int.max_signed /\ 0 <= zf_adler z <= Int64.max_unsigned.

Definition st_ptr (st: option live) : val := match st with None => nullval | Some L => l_sp L end.

(* struct z_stream with the fields z and strm->state = st *)
Definition zstrm_at (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: val) : mpred :=
  strm_rep gv shs strmp (zf_ni z) (Vint (Int.repr (zf_ai z))) (zf_tin z) (zf_no z)
    (Vint (Int.repr (zf_ao z))) (zf_tout z) (msg_val gv (zf_msg z)) st (zf_dt z) (zf_adler z) (zf_res z).

(* the 4 bytes of padding after the last member of struct inflate_state (sizeof 7160, `was` ends at 7156) *)
Definition state_pad (sp: val) : mpred := memory_block Ews 4 (offset_val 7156 sp).

(* the memory behind strm->state *)
Definition state_mem (gv: globals) (strmp: val) (L: live) : mpred :=
  malloc_token Ews t_state (l_sp L) * state_rep gv (l_sp L) strmp (l_headp L) (l_winp L) (l_s L) *
  win_rep (l_winp L) (l_s L) * state_pad (l_sp L).

(* the application's gz_header while inflate holds it *)
Definition head_mem (L: live) : mpred :=
  if i_head (l_s L) then
    head_rep (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L) *
    btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L))
  else emp.
Definition head_opt (st: option live) : mpred :=
  match st with None => emp | Some L => head_mem L end.

Definition istream (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) : mpred :=
  !! (zf_ok z /\ writable_share shs) &&
  match st with
  | None => zstrm_at gv shs strmp z nullval
  | Some L => !! live_ok L && (zstrm_at gv shs strmp z (l_sp L) * state_mem gv strmp L)
  end.

(* a stream argument that may be Z_NULL *)
Definition istream_opt (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) : mpred :=
  if eq_dec strmp nullval then emp else istream gv shs strmp z st.

(* inflateStateCheck(strm) = 0 *)
Definition is_live (strmp: val) (st: option live) : option live :=
  if eq_dec strmp nullval then None else st.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate()                                                                                      *)

Definition out_opt (ob: option outbuf) (ow: list Z) : mpred :=
  match ob with None => emp | Some o => out_rep o ow end.

(* the malloc tokens of the input/output objects when they may be empty (a pointer to a 0-byte object is
   compared with NULL: VST needs the token for its validity) *)
Definition in_tok (tok: bool) (ib: inbuf) : mpred :=
  match ib with InBuf _ p _ n _ => if tok then malloc_token Ews (tarray tuchar n) p else emp | InNull => emp end.
Definition out_tok (tok: bool) (ob: option outbuf) : mpred :=
  match ob with Some (OutBuf _ p _ n _) => if tok then malloc_token Ews (tarray tuchar n) p else emp | None => emp end.
(* the input and output objects with their tokens; only for a live stream (on a Z_NULL or ended stream
   inflate() returns at once and touches neither: the caller may pass one object as both) *)
Definition bufs_opt (st: option live) (ib: inbuf) (ob: option outbuf) (ow: list Z) (itok otok: bool) : mpred :=
  match st with
  | Some _ => in_rep ib * out_opt ob ow * in_tok itok ib * out_tok otok ob
  | None => emp
  end.

Definition in_tok_ok (tok: bool) (ib: inbuf) : Prop :=
  match ib with InBuf _ _ _ n _ => tok = false -> 0 < n | InNull => True end.
Definition out_tok_ok (tok: bool) (ob: option outbuf) : Prop :=
  match ob with Some (OutBuf _ _ _ n _) => tok = false -> 0 < n | None => True end.

(* the machine at the loop head after the prologue (TYPE -> TYPEDO, LOAD, in/out/ret) *)
Definition m_init (z: zfields) (L: live) (inp: list Z) : mst :=
  let s := l_s L in
  let s := if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s in
  MS s (l_h L) inp (zf_ao z) 0 [] (i_hold s) (i_bits s) (Zlength inp) (zf_ao z) Z_OK 0
     (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0.

(* the stream fields after the call *)
Definition z_after (z: zfields) (ib: inbuf) (o: outbuf) (res: result) : zfields :=
  let m := r_m res in
  ZF (in_ptr ib (m_snx m)) (Zlength (m_inp m) - m_snx m) (m_tin m) (out_ptr o (m_sow m))
     (m_aout m - m_sow m) (m_tout m) (m_msg m)
     (match r_dtype res with Some d => d | None => zf_dt z end) (m_adler m) (zf_res z).

(* the stream error of the prologue: Z_NULL or ended stream, next_out Z_NULL, or next_in Z_NULL with
   avail_in > 0 *)
Definition inflate_bad (strmp: val) (z: zfields) (st: option live) (ib: inbuf) (ob: option outbuf) : Prop :=
  is_live strmp st = None \/ ob = None \/ (ib = InNull /\ zf_ai z <> 0).

(* the outcome of inflate(strm, flush): return value, the stream's fields and live part, the bytes
   written into the output space *)
Definition inflate_rel (flush: Z) (strmp: val) (z: zfields) (st: option live) (ib: inbuf) (inp: list Z)
    (ob: option outbuf) (r: Z) (z': zfields) (st': option live) (ow: list Z) : Prop :=
  (inflate_bad strmp z st ib ob /\ r = Z_STREAM_ERROR /\ z' = z /\ st' = st /\ ow = []) \/
  (~ inflate_bad strmp z st ib ob /\
   exists L o res winp,
     st = Some L /\ ob = Some o /\
     Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res /\
     0 <= m_snx (r_m res) <= Zlength inp /\
     r = r_ret res /\ ow = m_ow (r_m res) /\ z' = z_after z ib o res /\
     (i_win (l_s L) = true -> winp = l_winp L) /\
     st' = Some (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L)
                      (l_nb L) (l_cb L))).

Definition inflate_spec :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          zf_ai z <= Int.max_signed; zf_ao z <= Int.max_signed)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateInit2_ / inflateInit_                                                                   *)

(* struct z_stream before inflateInit2_: the fields inflateInit2_ neither reads nor needs are any values
   (uncompress2_z's z_stream is a local with most fields undefined); zalloc, zfree = za, zf;
   msg, state, opaque anything *)
Record rawf := RF { rf_ni: val; rf_ai: val; rf_tin: val; rf_no: val; rf_ao: val; rf_tout: val; rf_dt: val;
                    rf_adler: val; rf_res: val }.

Definition raw_strm (gv: globals) (shs: share) (strmp: val) (r: rawf) (msgv stv za zf opq: val) : mpred :=
  data_at shs t_strm
    (rf_ni r, (rf_ai r, (rf_tin r, (rf_no r, (rf_ao r, (rf_tout r, (msgv, (stv, (za, (zf, (opq,
     (rf_dt r, (rf_adler r, rf_res r))))))))))))) strmp.

(* the stream fields a successful inflateInit2_ writes (inflateResetKeep): totals 0, msg NULL, data_type 0,
   adler = wrap & 1 when wrap <> 0 *)
Definition raw_after_init (r: rawf) (s: istate) : rawf :=
  RF (rf_ni r) (rf_ai r) (Vlong (Int64.repr 0)) (rf_no r) (rf_ao r) (Vlong (Int64.repr 0)) (Vint (Int.repr 0))
     (if i_wrap s =? 0 then rf_adler r else Vlong (Int64.repr (Z.land (i_wrap s) 1))) (rf_res r).

(* a live stream whose application fields are values (rawf): an istream once they are defined *)
Definition istream_raw (gv: globals) (shs: share) (strmp: val) (r: rawf) (L: live) : mpred :=
  !! (writable_share shs /\ live_ok L) &&
  (raw_strm gv shs strmp r nullval (l_sp L) (gv _zcalloc) (gv _zcfree) nullval * state_mem gv strmp L).

Lemma istream_raw_istream: forall gv shs strmp z L,
  zf_ok z -> zf_msg z = None ->
  istream_raw gv shs strmp
    (RF (zf_ni z) (Vint (Int.repr (zf_ai z))) (Vlong (Int64.repr (zf_tin z))) (zf_no z)
        (Vint (Int.repr (zf_ao z))) (Vlong (Int64.repr (zf_tout z))) (Vint (Int.repr (zf_dt z)))
        (Vlong (Int64.repr (zf_adler z))) (zf_res z)) L
  = istream gv shs strmp z (Some L).
Proof.
  intros gv shs strmp z L Hz Hm. unfold istream_raw, istream, zstrm_at, strm_rep, raw_strm. rewrite Hm.
  simpl msg_val. apply pred_ext; entailer!.
Qed.

(* inflate.c's ZLIB_VERSION literal "1.3.2" *)
Definition version_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6) (map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0])
    (gv ___stringlit_inflate_1).

Definition sizeof_z_stream : Z := 112.

(* the outcome of inflateInit2_: the return value and the stream afterwards (memory: init_mem) *)
Definition init_ret (strmp: val) (c ssize w: Z) (alloc_ok: bool) : Z :=
  if orb (negb (c =? 49)) (negb (ssize =? sizeof_z_stream)) then Z_VERSION_ERROR
  else if eq_dec strmp nullval then Z_STREAM_ERROR
  else if negb alloc_ok then Z_MEM_ERROR
  else if wbits_ok w then Z_OK else Z_STREAM_ERROR.

Definition init_live (sp: val) (w: Z) : live :=
  let s := match reset2_wb w with Some (wrap, wb) => init_s wrap wb | None => zero_s end in
  Live sp nullval s (HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0) nullval Ews nullval nullval nullval.

Definition init_mem (gv: globals) (shs: share) (strmp: val) (r: rawf) (msgv stv opq: val) (ret: Z)
    (sp: val) (w: Z) : mpred :=
  if eq_dec strmp nullval then emp else
  if ret =? Z_VERSION_ERROR then raw_strm gv shs strmp r msgv stv nullval nullval opq
  else if ret =? Z_MEM_ERROR then raw_strm gv shs strmp r nullval stv (gv _zcalloc) (gv _zcfree) nullval
  else if ret =? Z_OK then
    let L := init_live sp w in istream_raw gv shs strmp (raw_after_init r (l_s L)) L
  else raw_strm gv shs strmp r nullval nullval (gv _zcalloc) (gv _zcfree) nullval.

Definition inflateInit2__spec :=
  DECLARE _inflateInit2_
  WITH gv: globals, shs: share, strmp: val, r: rawf, msgv: val, stv: val, opq: val, w: Z,
       ver: val, vsh: share, vc: list val, c: Z, ssize: Z
  PRE [ tptr t_strm, tint, tptr tschar, tint ]
    PROP (readable_share vsh; isptr ver; 1 <= Zlength vc <= Ptrofs.max_unsigned; Znth 0 vc = Vint (Int.repr c);
          -128 <= c <= 127;
          Int.min_signed <= w <= Int.max_signed; Int.min_signed <= ssize <= Int.max_signed;
          strmp <> nullval -> writable_share shs)
    PARAMS (strmp; Vint (Int.repr w); ver; Vint (Int.repr ssize)) GLOBALS (gv)
    SEP (if eq_dec strmp nullval then emp else raw_strm gv shs strmp r msgv stv nullval nullval opq;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX sp: val,
    PROP (alloc_ok = true -> isptr sp)
    RETURN (Vint (Int.repr (init_ret strmp c ssize w alloc_ok)))
    SEP (init_mem gv shs strmp r msgv stv opq (init_ret strmp c ssize w alloc_ok) sp w;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv).

Definition inflateInit__spec :=
  DECLARE _inflateInit_
  WITH gv: globals, shs: share, strmp: val, r: rawf, msgv: val, stv: val, opq: val,
       ver: val, vsh: share, vc: list val, c: Z, ssize: Z
  PRE [ tptr t_strm, tptr tschar, tint ]
    PROP (readable_share vsh; isptr ver; 1 <= Zlength vc <= Ptrofs.max_unsigned; Znth 0 vc = Vint (Int.repr c);
          -128 <= c <= 127; Int.min_signed <= ssize <= Int.max_signed;
          strmp <> nullval -> writable_share shs)
    PARAMS (strmp; ver; Vint (Int.repr ssize)) GLOBALS (gv)
    SEP (if eq_dec strmp nullval then emp else raw_strm gv shs strmp r msgv stv nullval nullval opq;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX sp: val,
    PROP (alloc_ok = true -> isptr sp)
    RETURN (Vint (Int.repr (init_ret strmp c ssize 15 alloc_ok)))
    SEP (init_mem gv shs strmp r msgv stv opq (init_ret strmp c ssize 15 alloc_ok) sp 15;
         data_at vsh (tarray tschar (Zlength vc)) vc ver; version_lit gv; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateEnd                                                                                     *)

Definition inflateEnd_spec :=
  DECLARE _inflateEnd
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live
  PRE [ tptr t_strm ]
    PROP () PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with Some _ => Z_OK | None => Z_STREAM_ERROR end)))
    SEP (istream_opt gv shs strmp z None; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateResetKeep, inflateReset, inflateReset2                                                  *)

(* a function of the live state: Z_STREAM_ERROR and no change on a Z_NULL or ended stream *)
Definition on_live (strmp: val) (z: zfields) (st: option live)
    (f: zfields -> live -> Z * zfields * live) : Z * zfields * option live :=
  match is_live strmp st with
  | None => (Z_STREAM_ERROR, z, st)
  | Some L => let '(r, z', L') := f z L in (r, z', Some L')
  end.

Definition reset_keep_f (z: zfields) (L: live) : Z * zfields * live :=
  let s := reset_keep_s (l_s L) in (Z_OK, reset_keep_z z s, set_l_s L s).
Definition reset_f (z: zfields) (L: live) : Z * zfields * live :=
  let s := reset_full_s (l_s L) in (Z_OK, reset_keep_z z s, set_l_s L s).
Definition reset2_f (w: Z) (z: zfields) (L: live) : Z * zfields * live :=
  match reset2_wb w with
  | None => (Z_STREAM_ERROR, z, L)
  | Some (wrap, wb) => let s := reset2_s wrap wb (l_s L) in (Z_OK, reset_keep_z z s, set_l_s L s)
  end.

Definition fst3 {A B C} (x: A * B * C) : A := fst (fst x).
Definition snd3 {A B C} (x: A * B * C) : B := snd (fst x).
Definition thd3 {A B C} (x: A * B * C) : C := snd x.

(* The reset functions only WRITE state->lencode, distcode, next and sane (inflateInit2_ calls
   inflateReset2 on the zeroed state, where they are NULL / 0): their precondition takes any values there
   (state_rep_v), and only requires that the RESULT of the reset is a live state (live_ok). *)
Definition state_rep_v (gv: globals) (sp strmp headp winp: val) (s: istate) (vl vd vn vs: val) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) vl sp *
  field_at Ews t_state (DOT _distcode) vd sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) vn sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) vs sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma state_rep_v_eq: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  state_rep_v gv sp strmp headp winp s (tref_val gv sp (i_lencode s)) (tref_val gv sp (i_distcode s))
    (codes_at sp (i_next s)) (zv (i_sane s)).
Proof. reflexivity. Qed.

(* a stream as the reset functions take it: RLive L vl vd vn vs (the state of L with the 4 written fields
   holding vl vd vn vs), or an ended stream; RRaw L r vl vd vn vs: the same with the application's stream
   fields any values r (inflateInit2_ calls inflateReset2 on a stream whose fields may be undefined, e.g.
   uncompress2_z's local z_stream; the reset functions only write them) and msg NULL *)
Inductive rst := RNone | RLive (L: live) (vl vd vn vs: val) | RRaw (L: live) (r: rawf) (vl vd vn vs: val).

Definition rstream (gv: globals) (shs: share) (strmp: val) (z: zfields) (r: rst) : mpred :=
  match r with
  | RNone => istream gv shs strmp z None
  | RLive L vl vd vn vs =>
      !! (zf_ok z /\ writable_share shs /\ isptr (l_sp L) /\ HEAD <= i_mode (l_s L) <= SYNC /\
          0 <= i_wbits (l_s L) <= 23) &&
      (zstrm_at gv shs strmp z (l_sp L) * malloc_token Ews t_state (l_sp L) *
       state_rep_v gv (l_sp L) strmp (l_headp L) (l_winp L) (l_s L) vl vd vn vs *
       win_rep (l_winp L) (l_s L) * state_pad (l_sp L))
  | RRaw L r vl vd vn vs =>
      !! (writable_share shs /\ isptr (l_sp L) /\ HEAD <= i_mode (l_s L) <= SYNC /\
          0 <= i_wbits (l_s L) <= 23) &&
      (raw_strm gv shs strmp r nullval (l_sp L) (gv _zcalloc) (gv _zcfree) nullval *
       malloc_token Ews t_state (l_sp L) *
       state_rep_v gv (l_sp L) strmp (l_headp L) (l_winp L) (l_s L) vl vd vn vs *
       win_rep (l_winp L) (l_s L) * state_pad (l_sp L))
  end.

Definition rstream_opt (gv: globals) (shs: share) (strmp: val) (z: zfields) (r: rst) : mpred :=
  if eq_dec strmp nullval then emp else rstream gv shs strmp z r.

(* a live stream as an rst *)
Definition rst_of (gv: globals) (st: option live) : rst :=
  match st with
  | None => RNone
  | Some L => RLive L (tref_val gv (l_sp L) (i_lencode (l_s L))) (tref_val gv (l_sp L) (i_distcode (l_s L)))
                    (codes_at (l_sp L) (i_next (l_s L))) (zv (i_sane (l_s L)))
  end.

(* the outcome of a reset: the return value, the stream fields, the live part when it succeeds *)
Definition rs_live (strmp: val) (r: rst) : option live :=
  if eq_dec strmp nullval then None else
  match r with RNone => None | RLive L _ _ _ _ => Some L | RRaw L _ _ _ _ _ => Some L end.

(* the precondition of a reset: the reset state is live *)
Definition reset_pre (strmp: val) (r: rst) (f: zfields -> live -> Z * zfields * live) (z: zfields) : Prop :=
  match rs_live strmp r with
  | None => True
  | Some L => fst3 (f z L) = Z_OK -> live_ok (thd3 (f z L))
  end.

(* the memory after a reset: on Z_OK the live stream (for RRaw: with the fields the reset wrote,
   raw_after_init), otherwise the stream unchanged *)
Definition reset_post (gv: globals) (shs: share) (strmp: val) (z: zfields) (r: rst)
    (f: zfields -> live -> Z * zfields * live) : mpred :=
  match rs_live strmp r with
  | Some L => if fst3 (f z L) =? Z_OK then
                match r with
                | RRaw _ rf _ _ _ _ => istream_raw gv shs strmp (raw_after_init rf (l_s (thd3 (f z L)))) (thd3 (f z L))
                | _ => istream gv shs strmp (snd3 (f z L)) (Some (thd3 (f z L)))
                end
              else rstream_opt gv shs strmp z r
  | None => rstream_opt gv shs strmp z r
  end.

Definition reset_ret (strmp: val) (r: rst) (f: zfields -> live -> Z * zfields * live) (z: zfields) : Z :=
  match rs_live strmp r with Some L => fst3 (f z L) | None => Z_STREAM_ERROR end.

Definition inflateResetKeep_spec :=
  DECLARE _inflateResetKeep
  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst
  PRE [ tptr t_strm ]
    PROP (reset_pre strmp r reset_keep_f z) PARAMS (strmp) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r reset_keep_f z)))
    SEP (reset_post gv shs strmp z r reset_keep_f; zfuncs gv).

Definition inflateReset_spec :=
  DECLARE _inflateReset
  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst
  PRE [ tptr t_strm ]
    PROP (reset_pre strmp r reset_f z) PARAMS (strmp) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r reset_f z)))
    SEP (reset_post gv shs strmp z r reset_f; mem_mgr gv; zfuncs gv).

Definition inflateReset2_spec :=
  DECLARE _inflateReset2
  WITH gv: globals, shs: share, strmp: val, z: zfields, r: rst, w: Z
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= w <= Int.max_signed; reset_pre strmp r (reset2_f w) z)
    PARAMS (strmp; Vint (Int.repr w)) GLOBALS (gv)
    SEP (rstream_opt gv shs strmp z r; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (reset_ret strmp r (reset2_f w) z)))
    SEP (reset_post gv shs strmp z r (reset2_f w); mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflatePrime, inflateValidate, inflateSyncPoint, inflateMark, inflateCodesUsed                 *)

Definition prime_f (bits value: Z) (z: zfields) (L: live) : Z * zfields * live :=
  match prime_s bits value (l_s L) with
  | None => (Z_STREAM_ERROR, z, L)
  | Some s => (Z_OK, z, set_l_s L s)
  end.

Definition inflatePrime_spec :=
  DECLARE _inflatePrime
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, bits: Z, value: Z
  PRE [ tptr t_strm, tint, tint ]
    PROP (Int.min_signed <= bits <= Int.max_signed; Int.min_signed <= value <= Int.max_signed)
    PARAMS (strmp; Vint (Int.repr bits); Vint (Int.repr value)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (fst3 (on_live strmp z st (prime_f bits value)))))
    SEP (istream_opt gv shs strmp (snd3 (on_live strmp z st (prime_f bits value)))
           (thd3 (on_live strmp z st (prime_f bits value))); zfuncs gv).

Definition validate_f (check: Z) (z: zfields) (L: live) : Z * zfields * live :=
  (Z_OK, z, set_l_s L (validate_s check (l_s L))).

Definition inflateValidate_spec :=
  DECLARE _inflateValidate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, check: Z
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= check <= Int.max_signed)
    PARAMS (strmp; Vint (Int.repr check)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (fst3 (on_live strmp z st (validate_f check)))))
    SEP (istream_opt gv shs strmp (snd3 (on_live strmp z st (validate_f check)))
           (thd3 (on_live strmp z st (validate_f check))); zfuncs gv).

Definition inflateSyncPoint_spec :=
  DECLARE _inflateSyncPoint
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live
  PRE [ tptr t_strm ]
    PROP () PARAMS (strmp) GLOBALS (gv) SEP (istream_opt gv shs strmp z st; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with Some L => syncpoint_val (l_s L) | None => Z_STREAM_ERROR end)))
    SEP (istream_opt gv shs strmp z st; zfuncs gv).

Definition inflateMark_spec :=
  DECLARE _inflateMark
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live
  PRE [ tptr t_strm ]
    PROP () PARAMS (strmp) GLOBALS (gv) SEP (istream_opt gv shs strmp z st; zfuncs gv)
  POST [ tlong ]
    PROP ()
    RETURN (Vlong (Int64.repr (match is_live strmp st with Some L => mark_val (l_s L) | None => -65536 end)))
    SEP (istream_opt gv shs strmp z st; zfuncs gv).

Definition inflateCodesUsed_spec :=
  DECLARE _inflateCodesUsed
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live
  PRE [ tptr t_strm ]
    PROP () PARAMS (strmp) GLOBALS (gv) SEP (istream_opt gv shs strmp z st; zfuncs gv)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (match is_live strmp st with Some L => i_next (l_s L) | None => -1 end)))
    SEP (istream_opt gv shs strmp z st; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetDictionary(strm, dictionary, dictLength): dictionary = NULL or an object with room for
   the window (whave bytes) at offset lo; dictLength = NULL or a uInt object                         *)

Inductive dictbuf := DNull | DBuf (sh: share) (p: val) (lo n: Z) (cont: list val).

Definition dict_ptr (d: dictbuf) : val := match d with DNull => nullval | DBuf _ p lo _ _ => offset_val lo p end.

Definition dict_rep (d: dictbuf) (data: option (list Z)) : mpred :=
  match d with
  | DNull => emp
  | DBuf sh p lo n c =>
      match data with
      | None => data_at sh (tarray tuchar n) c p
      | Some b => data_at sh (tarray tuchar n) (sublist 0 lo c ++ byte_vals b ++ sublist (lo + Zlength b) n c) p
      end
  end.

Definition dict_ok (d: dictbuf) (room: Z) : Prop :=
  match d with
  | DNull => True
  | DBuf sh p lo n c => writable_share sh /\ isptr p /\ 0 <= lo /\ lo + room <= n /\ Zlength c = n /\
                        n <= Ptrofs.max_unsigned
  end.

Definition len_rep (lp: val) (v: option Z) : mpred :=
  if eq_dec lp nullval then emp else
  match v with None => data_at_ Tsh tuint lp | Some x => data_at Tsh tuint (Vint (Int.repr x)) lp end.

Definition inflateGetDictionary_spec :=
  DECLARE _inflateGetDictionary
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, d: dictbuf, lp: val
  PRE [ tptr t_strm, tptr tuchar, tptr tuint ]
    PROP (match is_live strmp st with Some L => dict_ok d (i_whave (l_s L)) | None => True end)
    PARAMS (strmp; dict_ptr d; lp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; dict_rep d None; len_rep lp None; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with Some _ => Z_OK | None => Z_STREAM_ERROR end)))
    SEP (istream_opt gv shs strmp z st;
         dict_rep d (match is_live strmp st with Some L => Some (dict_bytes (l_s L)) | None => None end);
         len_rep lp (match is_live strmp st with Some L => Some (i_whave (l_s L)) | None => None end);
         zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSetDictionary(strm, dictionary, dictLength): the dictionary = the slice [lo, lo + |dict|)
   of an object                                                                                    *)

(* return value and live part after the call (alloc_ok: the window allocation, when attempted,
   succeeds; winp: the new window) *)
Definition setdict_f (dict: list Z) (alloc_ok: bool) (winp: val) (z: zfields) (L: live) : Z * zfields * live :=
  match setdict_check (l_s L) dict with
  | SDStream => (Z_STREAM_ERROR, z, L)
  | SDData => (Z_DATA_ERROR, z, L)
  | SDUpdate =>
      if i_win (l_s L) then (Z_OK, z, set_l_s L (setdict_s (l_s L) dict))
      else if alloc_ok then (Z_OK, z, set_l_winp (set_l_s L (setdict_s (l_s L) dict)) winp)
      else (Z_MEM_ERROR, z, set_l_s L (set_i_mode (l_s L) MEM))
  end.

Definition inflateSetDictionary_spec :=
  DECLARE _inflateSetDictionary
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live,
       dsh: share, p: val, lo: Z, n: Z, c: list val, dict: list Z, tok: bool
  PRE [ tptr t_strm, tptr tuchar, tuint ]
    PROP (readable_share dsh; isptr p; 0 <= lo; lo + Zlength dict <= n; Zlength c = n; n = 0 -> tok = true; Zlength dict <= Int.max_unsigned;
          n <= Ptrofs.max_unsigned; sublist lo (lo + Zlength dict) c = byte_vals dict; bytes_ok dict)
    PARAMS (strmp; offset_val lo p; Vint (Int.repr (Zlength dict))) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; data_at dsh (tarray tuchar n) c p;
         if tok then malloc_token Ews (tarray tuchar n) p else emp; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX winp: val,
    PROP ()
    RETURN (Vint (Int.repr (fst3 (on_live strmp z st (setdict_f dict alloc_ok winp)))))
    SEP (istream_opt gv shs strmp (snd3 (on_live strmp z st (setdict_f dict alloc_ok winp)))
           (thd3 (on_live strmp z st (setdict_f dict alloc_ok winp)));
         data_at dsh (tarray tuchar n) c p; if tok then malloc_token Ews (tarray tuchar n) p else emp;
         mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetHeader(strm, head): the application gives its gz_header (head_rep, h) to the stream   *)

(* the tokens of the zero-size header buffers *)
Definition hdr_btoks (xb nb cb: val) (h: hstate) : mpred :=
  btok xb (h_extra_max h) * btok nb (h_name_max h) * btok cb (h_comm_max h).

Definition inflateGetHeader_spec :=
  DECLARE _inflateGetHeader
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live,
       headp: val, hsh: share, xb: val, nb: val, cb: val, h: hstate
  PRE [ tptr t_strm, tptr t_head ]
    PROP (writable_share hsh; hwf h;
          h_xp h = true -> xb <> nullval; h_np h = true -> nb <> nullval; h_cp h = true -> cb <> nullval)
    PARAMS (strmp; headp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_rep hsh headp xb nb cb h; hdr_btoks xb nb cb h; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with
                            | Some L => if Z.land (i_wrap (l_s L)) 2 =? 0 then Z_STREAM_ERROR else Z_OK
                            | None => Z_STREAM_ERROR end)))
    SEP (match is_live strmp st with
         | Some L =>
             if Z.land (i_wrap (l_s L)) 2 =? 0 then
               istream_opt gv shs strmp z st * head_rep hsh headp xb nb cb h * hdr_btoks xb nb cb h
             else
               let L' := set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb in
               istream_opt gv shs strmp z (Some L') * head_mem L'
         | None => istream_opt gv shs strmp z st * head_rep hsh headp xb nb cb h * hdr_btoks xb nb cb h
         end;
         zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSync(strm): next_in a real object (InBuf) holding the avail_in bytes inp                *)

Definition sync_f (ib: inbuf) (inp: list Z) (z: zfields) (L: live) : Z * zfields * live :=
  match sync_s (l_s L) inp with
  | SyncBuf => (Z_BUF_ERROR, z, L)
  | SyncData s len => (Z_DATA_ERROR, set_zf_in z (in_ptr ib len) (Zlength inp - len) (u64 (zf_tin z + len)), set_l_s L s)
  | SyncOk s len =>
      let z1 := set_zf_in z (in_ptr ib len) (Zlength inp - len) (u64 (zf_tin z + len)) in
      (* inflateReset sees wrap with bit 3 cleared (patch F8) *)
      let z2 := reset_keep_z z1 (set_i_wrap s (Z.land (i_wrap s) (Z.lnot 8))) in
      (Z_OK, set_zf_counters z2 (zf_tin z1) (zf_tout z1), set_l_s L s)
  end.

Definition inflateSync_spec :=
  DECLARE _inflateSync
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z
  PRE [ tptr t_strm ]
    PROP (ib <> InNull; in_ok ib inp; zf_ni z = in_ptr ib 0; zf_ai z = Zlength inp)
    PARAMS (strmp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; in_rep ib; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (fst3 (on_live strmp z st (sync_f ib inp)))))
    SEP (istream_opt gv shs strmp (snd3 (on_live strmp z st (sync_f ib inp))) (thd3 (on_live strmp z st (sync_f ib inp)));
         in_rep ib; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* syncsearch(have, buf, len) (local to inflate.c): *have = got; buf = the slice [lo, lo + |data|)  *)

Definition syncsearch_spec :=
  DECLARE _syncsearch
  WITH hsh: share, hp: val, got: Z, bsh: share, p: val, lo: Z, n: Z, c: list val, data: list Z
  PRE [ tptr tuint, tptr tuchar, tuint ]
    PROP (writable_share hsh; readable_share bsh; 0 <= got <= Int.max_unsigned; Zlength data <= Int.max_unsigned;
          isptr p; 0 <= lo;
          lo + Zlength data <= n; Zlength c = n; n <= Ptrofs.max_unsigned;
          sublist lo (lo + Zlength data) c = byte_vals data; bytes_ok data)
    PARAMS (hp; offset_val lo p; Vint (Int.repr (Zlength data)))
    SEP (data_at hsh tuint (Vint (Int.repr got)) hp; data_at bsh (tarray tuchar n) c p)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (snd (ssearch got data))))
    SEP (data_at hsh tuint (Vint (Int.repr (fst (ssearch got data)))) hp; data_at bsh (tarray tuchar n) c p).

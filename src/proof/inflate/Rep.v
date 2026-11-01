(* The memory representation of the inflate model (Model.v) in the compspecs of the inflate unit.

   - state_rep: struct inflate_state, one field_at per member (the work[] scratch area holds anything);
     lencode/distcode point to inftrees.c's lenfix/distfix or into codes[]; next into codes[].
   - win_rep: the window, allocated (zcalloc, 2^wbits bytes) or not: its first whave bytes are i_wdata.
   - head_rep: the application's gz_header and its three buffers (when inflateGetHeader gave one).
   - strm_rep: struct z_stream.
   - tables_rep: the read-only globals inflate reads: lenfix, distfix (inftrees.c), order (inflate.c), and
     inflate_table's (itables). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Zlib.inftrees.code Zlib.inffast.code.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Model.
Require Export Zlib.proof.inflate.Fixed.
Require Export Zlib.proof.zutil.Libc.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition t_strm := Tstruct _z_stream_s noattr.
Definition t_state := Tstruct _inflate_state noattr.
Definition t_code := Tstruct ___gp_code noattr.
Definition t_head := Tstruct _gz_header_s noattr.

Notation zv z := (Vint (Int.repr z)) (only parsing).
Notation lv z := (Vlong (Int64.repr z)) (only parsing).
Definition ent (e: entry) : val * (val * val) := (zv (e_op e), (zv (e_bits e), zv (e_val e))).

Definition g_lenfix : ident := Zlib.inftrees.code._lenfix.
Definition g_distfix : ident := Zlib.inftrees.code._distfix.

(* &state->codes[k] *)
Definition codes_at (sp: val) (k: Z) : val := field_address0 t_state [ArraySubsc k; StructField _codes] sp.

Definition tref_val (gv: globals) (sp: val) (t: tref) : val :=
  match t with
  | TLenfix => gv g_lenfix
  | TDistfix => gv g_distfix
  | TCodes k => codes_at sp k
  end.

Definition msg_ident (m: msgid) : ident :=
  match m with
  | M_hdr_check => ___stringlit_inflate_18 | M_method => ___stringlit_inflate_16
  | M_wsize => ___stringlit_inflate_19 | M_hflags => ___stringlit_inflate_17
  | M_hcrc => ___stringlit_inflate_15 | M_btype => ___stringlit_inflate_14
  | M_stored => ___stringlit_inflate_13 | M_toomany => ___stringlit_inflate_12
  | M_cl_set => ___stringlit_inflate_11 | M_repeat => ___stringlit_inflate_7
  | M_eob => ___stringlit_inflate_8 | M_ll_set => ___stringlit_inflate_9
  | M_d_set => ___stringlit_inflate_10 | M_ll_code => ___stringlit_inflate_6
  | M_d_code => ___stringlit_inflate_5 | M_far => ___stringlit_inflate_4
  | M_dcheck => ___stringlit_inflate_3 | M_lcheck => ___stringlit_inflate_2
  | F_far => Zlib.inffast.code.___stringlit_inffast_3
  | F_d_code => Zlib.inffast.code.___stringlit_inffast_2
  | F_ll_code => Zlib.inffast.code.___stringlit_inffast_1
  end.

Definition msg_val (gv: globals) (m: option msgid) : val :=
  match m with None => nullval | Some i => gv (msg_ident i) end.

(* ---------------------------------------------------------------------------------------------- *)
(* struct inflate_state                                                                           *)

Definition state_rep (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
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
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* the window: 2^wbits bytes, the first whave of them the model's i_wdata *)
Definition win_rep (winp: val) (s: istate) : mpred :=
  if i_win s then
    malloc_token Ews (tarray tuchar (2 ^ i_wbits s)%Z) winp *
    data_at Ews (tarray tuchar (2 ^ i_wbits s)%Z)
      (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))%Z) winp
  else emp.

(* ---------------------------------------------------------------------------------------------- *)
(* the gz_header (when i_head): xb/nb/cb are the buffers the application gave (or null)            *)

Definition hbuf_rep (b: val) (max: Z) (cont: list Z) : mpred :=
  if eq_dec b nullval then emp else data_at Ews (tarray tuchar max) (byte_vals cont) b.

Definition head_rep (hsh: share) (headp xb nb cb: val) (h: hstate) : mpred :=
  data_at hsh t_head
    (zv (h_text h), (lv (h_time h), (zv (h_xflags h), (zv (h_os h),
     ((if h_xp h then xb else nullval), (zv (h_extra_len h), (zv (h_extra_max h),
     ((if h_np h then nb else nullval), (zv (h_name_max h),
     ((if h_cp h then cb else nullval), (zv (h_comm_max h), (zv (h_hcrc h), zv (h_done h)))))))))))))
    headp *
  hbuf_rep xb (h_extra_max h) (h_xbuf h) *
  hbuf_rep nb (h_name_max h) (h_nbuf h) *
  hbuf_rep cb (h_comm_max h) (h_cbuf h).

(* ---------------------------------------------------------------------------------------------- *)
(* struct z_stream                                                                                *)

Definition strm_rep (gv: globals) (shs: share) (strmp: val) (ni ai: val) (tin: Z) (no ao: val) (tout: Z)
    (msg: val) (sp: val) (dt adler: Z) (vres: val) : mpred :=
  data_at shs t_strm
    (ni, (ai, (lv tin, (no, (ao, (lv tout, (msg, (sp, (gv _zcalloc, (gv _zcfree,
     (nullval, (zv dt, (lv adler, vres))))))))))))) strmp.

(* the read-only tables inflate reads, and those of inflate_table (inftrees.c: lbase, lext, dbase, dext) *)
Definition tables_rep (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order) *
  Zlib.proof.inftrees.spec.itables gsh gv.

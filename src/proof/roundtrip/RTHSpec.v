(* Round-trip laws, part RT-H: inflate()'s and inflateGetHeader's specifications for an
   application gz_header whose scalar fields and buffer bytes are undefined until inflate writes them
   (harness/deflate_roundtrip.c's local `gz_header ih`, buffers from malloc).

   Spec5's head_rep has DEFINED fields; it sits inside Loop.mem_rep of every switch case, kit lemma and of the
   callee spec inflate_fast_spec3, so a partly undefined header can only be carried by the header cases.  Hence:
   - in the header modes HEAD .. HCRC the header is `head_rep6`: a field is the model's value once inflate wrote it
     (by the mode: TIME text; OS + time; EXLEN + xflags, os; EXTRA .. HCRC + extra_len when FEXTRA), anything
     before; each buffer's first `c` bytes are the model's (c: the bytes inflate wrote so far), the rest anything;
   - in every other mode the header is Spec5's head_rep (defined);
   - so an inflate() call that starts in a header mode with a header attached must pass the whole header
     (`hd6_ok`: no leave, no error, and at its end every field and buffer byte written: `hfull`).
   inflateGetHeader_spec6 takes a header struct with any field values and buffer bytes (`hraw6`) on a stream in
   mode HEAD or FLAGS.  Without a header attached (i_head false) both specs are Spec5's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* ---------------------------------------------------------------------------------------------- *)
(* what inflate has written into the header, as a function of the model state                    *)

(* the index of the first zero byte (the length when there is none) *)
Fixpoint fz (l: list Z) : Z :=
  match l with nil => 0 | x :: t => if x =? 0 then 0 else 1 + fz t end.

Definition hdr_mode (md: Z) : bool := andb (IM.HEAD <=? md) (md <=? IM.HCRC).

(* FEXTRA *)
Definition fextra (s: istate) : bool := negb (Z.land (i_flags s) 1024 =? 0).

(* the scalar fields written: 1 text, 2 + time, 3 + xflags/os, 4 + extra_len (with FEXTRA), 5 + hcrc *)
Definition hph (s: istate) : Z :=
  let md := i_mode s in
  if md =? IM.TIME then 1 else if md =? IM.OS then 2 else if md =? IM.EXLEN then 3
  else if andb (IM.EXTRA <=? md) (md <=? IM.HCRC) then 4 else 0.

(* the bytes written at the start of each buffer *)
Definition cx6 (s: istate) (h: hstate) : Z :=
  let md := i_mode s in
  if md =? IM.EXTRA then (if h_xp h then Z.min (h_extra_len h - i_length s) (h_extra_max h) else 0)
  else if andb (IM.NAME <=? md) (md <=? IM.HCRC) then (if h_xp h then Z.min (h_extra_len h) (h_extra_max h) else 0)
  else 0.

Definition cn6 (s: istate) (h: hstate) : Z :=
  let md := i_mode s in
  if md =? IM.NAME then i_length s
  else if andb (IM.COMMENT <=? md) (md <=? IM.HCRC) then
    (if h_np h then Z.min (fz (h_nbuf h) + 1) (h_name_max h) else 0)
  else 0.

Definition cc6 (s: istate) (h: hstate) : Z :=
  let md := i_mode s in
  if md =? IM.COMMENT then i_length s
  else if md =? IM.HCRC then (if h_cp h then Z.min (fz (h_cbuf h) + 1) (h_comm_max h) else 0)
  else 0.

(* the facts the counts rest on; done is 0 (inflateGetHeader wrote it) until HCRC leaves the header modes *)
Definition hinv6 (s: istate) (h: hstate) : Prop :=
  let md := i_mode s in
  h_done h = 0 /\
  (andb (IM.EXTRA <=? md) (md <=? IM.HCRC) = true -> h_xp h = true -> fextra s = true) /\
  (md = IM.EXTRA -> h_xp h = true -> 0 <= i_length s <= h_extra_len h) /\
  (md = IM.NAME -> 0 <= i_length s <= h_name_max h /\ (h_np h = false -> i_length s = 0) /\
                   Forall (fun x => x <> 0) (sublist 0 (i_length s) (h_nbuf h))) /\
  (md = IM.COMMENT -> 0 <= i_length s <= h_comm_max h /\ (h_cp h = false -> i_length s = 0) /\
                      Forall (fun x => x <> 0) (sublist 0 (i_length s) (h_cbuf h))).

(* ---------------------------------------------------------------------------------------------- *)
(* the header with possibly undefined parts                                                      *)

Definition hbuf6 (b: val) (max: Z) (l: list val) : mpred :=
  if eq_dec b nullval then emp else data_at Ews (tarray tuchar max) l b.

(* l holds max bytes, the first c of them the model's cont *)
Definition bufok6 (l: list val) (max c: Z) (cont: list Z) : Prop :=
  Zlength l = max /\ 0 <= c <= max /\ sublist 0 c l = byte_vals (sublist 0 c cont).

(* phase p of the scalar fields (hph), fx = FEXTRA, cx/cn/cc bytes written *)
Definition head_rep6p (hsh: share) (headp xb nb cb: val) (p: Z) (fx: bool) (cx cn cc: Z) (h: hstate) : mpred :=
  EX vt: val, EX vtm: val, EX vxf: val, EX vos: val, EX vxl: val, EX vhc: val,
  EX lx: list val, EX ln: list val, EX lc: list val,
  !! ((1 <= p -> vt = zv (h_text h)) /\ (2 <= p -> vtm = lv (h_time h)) /\
      (3 <= p -> vxf = zv (h_xflags h) /\ vos = zv (h_os h)) /\
      (4 <= p -> fx = true -> vxl = zv (h_extra_len h)) /\ (5 <= p -> vhc = zv (h_hcrc h)) /\
      bufok6 lx (h_extra_max h) cx (h_xbuf h) /\ bufok6 ln (h_name_max h) cn (h_nbuf h) /\
      bufok6 lc (h_comm_max h) cc (h_cbuf h)) &&
  (data_at hsh t_head
     (vt, (vtm, (vxf, (vos,
      ((if h_xp h then xb else nullval), (vxl, (zv (h_extra_max h),
      ((if h_np h then nb else nullval), (zv (h_name_max h),
      ((if h_cp h then cb else nullval), (zv (h_comm_max h), (vhc, zv (h_done h)))))))))))))
     headp *
   hbuf6 xb (h_extra_max h) lx * hbuf6 nb (h_name_max h) ln * hbuf6 cb (h_comm_max h) lc).

Definition head_rep6 (hsh: share) (headp xb nb cb: val) (s: istate) (h: hstate) : mpred :=
  !! hinv6 s h && head_rep6p hsh headp xb nb cb (hph s) (fextra s) (cx6 s h) (cn6 s h) (cc6 s h) h.

(* the header before inflateGetHeader: the pointer and size fields set, everything else anything *)
Definition hraw6 (hsh: share) (headp xb nb cb: val) (h: hstate) : mpred :=
  EX vt: val, EX vtm: val, EX vxf: val, EX vos: val, EX vxl: val, EX vhc: val, EX vd: val,
  EX lx: list val, EX ln: list val, EX lc: list val,
  !! (Zlength lx = h_extra_max h /\ Zlength ln = h_name_max h /\ Zlength lc = h_comm_max h) &&
  (data_at hsh t_head
     (vt, (vtm, (vxf, (vos,
      ((if h_xp h then xb else nullval), (vxl, (zv (h_extra_max h),
      ((if h_np h then nb else nullval), (zv (h_name_max h),
      ((if h_cp h then cb else nullval), (zv (h_comm_max h), (vhc, vd))))))))))))
     headp *
   hbuf6 xb (h_extra_max h) lx * hbuf6 nb (h_name_max h) ln * hbuf6 cb (h_comm_max h) lc).

(* the application's gz_header while inflate holds it: defined (Spec5's head_rep), or, in a header mode,
   partial *)
Definition head_mem6 (L: live) : mpred :=
  if i_head (l_s L) then
    (head_rep (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L) ||
     !! (hdr_mode (i_mode (l_s L)) = true) &&
     head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)) *
    btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L))
  else emp.
Definition head_opt6 (st: option live) : mpred :=
  match st with None => emp | Some L => head_mem6 L end.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate(): a call starting in a header mode with a header attached passes the whole header     *)

(* after the header: done, extra_len (FEXTRA) and every byte of the three buffers written *)
Definition hfull (s: istate) (h: hstate) : Prop :=
  h_done h = 1 /\ fextra s = true /\ h_xp h = true /\ h_np h = true /\ h_cp h = true /\
  h_extra_max h <= h_extra_len h /\ h_name_max h <= fz (h_nbuf h) + 1 /\ h_comm_max h <= fz (h_cbuf h) + 1.

(* from m, the passes of the switch through the header modes neither leave nor fail, and reach a non-header
   mode with the header complete *)
Fixpoint hpass (flush: Z) (n: nat) (m: mst) : Prop :=
  match n with
  | O => False
  | S n =>
      if hdr_mode (m_mode m) then
        match stepf2 flush lenfix_list distfix_list m with
        | IBrk m' => m_leave m' = 0 /\ hpass flush n m'
        | IRet _ _ => False
        end
      else hfull (m_s m) (m_h m)
  end.

Definition hd6_ok (flush: Z) (strmp: val) (z: zfields) (st: option live) (inp: list Z) : Prop :=
  match is_live strmp st with
  | Some L => i_head (l_s L) = true -> hdr_mode (i_mode (l_s L)) = true ->
              exists n, hpass flush n (m_init z L inp)
  | None => True
  end.

Definition inflate_spec6 :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          zf_ai z <= Int.max_signed; zf_ao z <= Int.max_signed;
          hd6_ok flush strmp z st inp)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt6 (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt6 (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetHeader(strm, head) on a header struct with any field values and buffer bytes          *)

(* a header may be attached with undefined fields only before inflate has read any of it *)
Definition hattach_ok (strmp: val) (st: option live) : Prop :=
  match is_live strmp st with
  | Some L => Z.land (i_wrap (l_s L)) 2 <> 0 -> i_mode (l_s L) = IM.HEAD \/ i_mode (l_s L) = IM.FLAGS
  | None => True
  end.

Definition inflateGetHeader_spec6 :=
  DECLARE _inflateGetHeader
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live,
       headp: val, hsh: share, xb: val, nb: val, cb: val, h: hstate
  PRE [ tptr t_strm, tptr t_head ]
    PROP (writable_share hsh; hwf h; hattach_ok strmp st;
          h_xp h = true -> xb <> nullval; h_np h = true -> nb <> nullval; h_cp h = true -> cb <> nullval)
    PARAMS (strmp; headp) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; hraw6 hsh headp xb nb cb h; hdr_btoks xb nb cb h; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with
                            | Some L => if Z.land (i_wrap (l_s L)) 2 =? 0 then Z_STREAM_ERROR else Z_OK
                            | None => Z_STREAM_ERROR end)))
    SEP (match is_live strmp st with
         | Some L =>
             if Z.land (i_wrap (l_s L)) 2 =? 0 then
               istream_opt gv shs strmp z st * hraw6 hsh headp xb nb cb h * hdr_btoks xb nb cb h
             else
               let L' := set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb in
               istream_opt gv shs strmp z (Some L') * head_mem6 L'
         | None => istream_opt gv shs strmp z st * hraw6 hsh headp xb nb cb h * hdr_btoks xb nb cb h
         end;
         zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* the body obligations (Vprog/Gprog as LibStmt5: inflate's callees keep their Spec5 specs)        *)

Definition rt_head6_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec6 /\
  semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec6.

(* Spec5's head_mem is a head_mem6; outside the header modes head_mem6 is Spec5's head_mem *)
Lemma head_mem_6: forall L, head_mem L |-- head_mem6 L.
Proof.
  intros L. unfold head_mem, head_mem6.
  destruct (i_head (l_s L)); [ | apply derives_refl].
  cancel. apply orp_right1. apply derives_refl.
Qed.

Lemma head_mem6_spec5: forall L, hdr_mode (i_mode (l_s L)) = false -> head_mem6 L |-- head_mem L.
Proof.
  intros L H. unfold head_mem, head_mem6.
  destruct (i_head (l_s L)); [ | apply derives_refl].
  cancel. apply orp_left; [apply derives_refl | ].
  apply derives_extract_prop. intros E. congruence.
Qed.

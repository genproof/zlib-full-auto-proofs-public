(* The model of inflate(), corrected: Model.v's c_COMMENT sets state->length = 0 at the end of the comment,
   which the C code does not do.  c_COMMENT2 omits it; c_NAME2 .. c_FLAGS2 are Model.v's
   cases that fall through into it; step2 / stepf2 / loop2 / run2 are Model.v's step / stepf / loop / run over
   them (every other case is Model.v's).  c_HEAD2: contract fix F7 tests the window size of a zlib
   header BEFORE storing it in state->wbits (Model.v's c_HEAD stores it first, as the unpatched code). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* case HEAD with patch F7: the window size is checked, then stored when wbits is 0 *)
Definition c_HEAD2 (m: mst) : iout :=
  if i_wrap (m_s m) =? 0 then IBrk (set_mode m TYPEDO) else
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let s := m_s m in
  if negb (Z.land (i_wrap s) 2 =? 0) && (m_hold m =? 35615) then
    let m := upd_s m (fun s => set_i_check (set_i_wbits s (if i_wbits s =? 0 then 15 else i_wbits s))
                                           (ref_crc32 0 (hbytes2 (m_hold m)))) in
    IBrk (set_mode (initbits m) FLAGS)
  else
  let m := if i_head s then upd_h m (fun h => set_h_done h (-1)) else m in
  if (Z.land (i_wrap s) 1 =? 0) ||
     negb (((m_hold m mod 256) * 256 + Z.shiftr (m_hold m) 8) mod 31 =? 0)
  then IBrk (set_bad m M_hdr_check) else
  if negb (m_hold m mod 16 =? 8) then IBrk (set_bad m M_method) else
  let m := dropbits 4 m in
  let len := m_hold m mod 16 + 8 in
  if (15 <? len) || (negb (i_wbits (m_s m) =? 0) && (i_wbits (m_s m) <? len)) then IBrk (set_bad m M_wsize) else
  let m := upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s)) in
  let mode := if Z.land (m_hold m) 512 =? 0 then TYPE else DICTID in
  let m := upd_s m (fun s => set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1) in
  IBrk (set_mode (initbits (set_m_adler m 1)) mode).

Section Cases2.
Variables (flush: Z) (lenfix distfix: list entry).
Variable fast : mst -> mst.

Definition c_COMMENT2 (m: mst) : iout :=
  (* the C code does NOT reset state->length here (Model.v's c_COMMENT does) *)
  let fin m := c_HCRC (set_mode m HCRC) in
  if negb (Z.land (i_flags (m_s m)) 4096 =? 0) then
    if m_have m =? 0 then IBrk (set_leave m) else
    let h := m_h m in
    let wr := i_head (m_s m) && h_cp h in
    let '(copy, b, ln, buf) := zstr_f (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                                 (m_have m) (i_length (m_s m)) (h_comm_max h) wr (h_cbuf h) 0 in
    let m := crc_if m (inbytes m copy) in
    let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_cbuf h buf) in
    let m := set_m_nx m (m_nx m + copy) in
    if negb (b =? 0) then IBrk (set_leave m) else fin m
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_cp h false) else m).

Definition c_NAME2 (m: mst) : iout :=
  let fin m := c_COMMENT2 (set_mode (upd_s m (fun s => set_i_length s 0)) COMMENT) in
  if negb (Z.land (i_flags (m_s m)) 2048 =? 0) then
    if m_have m =? 0 then IBrk (set_leave m) else
    let h := m_h m in
    let wr := i_head (m_s m) && h_np h in
    let '(copy, b, ln, buf) := zstr_f (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                                 (m_have m) (i_length (m_s m)) (h_name_max h) wr (h_nbuf h) 0 in
    let m := crc_if m (inbytes m copy) in
    let m := upd_h (upd_s m (fun s => set_i_length s ln)) (fun h => set_h_nbuf h buf) in
    let m := set_m_nx m (m_nx m + copy) in
    if negb (b =? 0) then IBrk (set_leave m) else fin m
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_np h false) else m).

Definition c_EXTRA2 (m: mst) : iout :=
  let fin m := c_NAME2 (set_mode (upd_s m (fun s => set_i_length s 0)) NAME) in
  let s := m_s m in
  if negb (Z.land (i_flags s) 1024 =? 0) then
    let copy := Z.min (i_length s) (m_have m) in
    let m := if negb (copy =? 0) then
        let h := m_h m in
        let len := u32 (h_extra_len h - i_length s) in
        let m := if i_head s && h_xp h && (len <? h_extra_max h) then
                   let n := if h_extra_max h <? u32 (len + copy) then h_extra_max h - len else copy in
                   upd_h m (fun h => set_h_xbuf h (put_bytes (h_xbuf h) len (inbytes m n)))
                 else m in
        let m := crc_if m (inbytes m copy) in
        set_m_nx (upd_s m (fun s => set_i_length s (i_length s - copy))) (m_nx m + copy)
      else m in
    if negb (i_length (m_s m) =? 0) then IBrk (set_leave m) else fin m
  else fin m.

Definition c_EXLEN2 (m: mst) : iout :=
  let fin m := c_EXTRA2 (set_mode m EXTRA) in
  if negb (Z.land (i_flags (m_s m)) 1024 =? 0) then
    let m := needbits 16 m in
    if m_leave m =? 1 then IBrk m else
    let v := u32 (m_hold m) in
    let m := upd_s m (fun s => set_i_length s v) in
    let m := if i_head (m_s m) then upd_h m (fun h => set_h_extra_len h v) else m in
    fin (initbits (crc_if m (hbytes2 (m_hold m))))
  else fin (if i_head (m_s m) then upd_h m (fun h => set_h_xp h false) else m).

Definition c_OS2 (m: mst) : iout :=
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let m := if i_head (m_s m) then
             upd_h m (fun h => set_h_os (set_h_xflags h (Z.land (m_hold m) 255)) (s32 (Z.shiftr (m_hold m) 8)))
           else m in
  c_EXLEN2 (set_mode (initbits (crc_if m (hbytes2 (m_hold m)))) EXLEN).

Definition c_TIME2 (m: mst) : iout :=
  let m := needbits 32 m in
  if m_leave m =? 1 then IBrk m else
  let m := if i_head (m_s m) then upd_h m (fun h => set_h_time h (m_hold m)) else m in
  c_OS2 (set_mode (initbits (crc_if m (hbytes4 (m_hold m)))) OS).

Definition c_FLAGS2 (m: mst) : iout :=
  let m := needbits 16 m in
  if m_leave m =? 1 then IBrk m else
  let fl := s32 (m_hold m) in
  let m := upd_s m (fun s => set_i_flags s fl) in
  if negb (Z.land fl 255 =? 8) then IBrk (set_bad m M_method) else
  if negb (Z.land fl 57344 =? 0) then IBrk (set_bad m M_hflags) else
  let m := if i_head (m_s m) then upd_h m (fun h => set_h_text h (Z.land (Z.shiftr (m_hold m) 8) 1)) else m in
  c_TIME2 (set_mode (initbits (crc_if m (hbytes2 (m_hold m)))) TIME).

Definition step2 (m: mst) : iout :=
  let md := m_mode m in
  if md =? HEAD then c_HEAD2 m
  else if md =? FLAGS then c_FLAGS2 m
  else if md =? TIME then c_TIME2 m
  else if md =? OS then c_OS2 m
  else if md =? EXLEN then c_EXLEN2 m
  else if md =? EXTRA then c_EXTRA2 m
  else if md =? NAME then c_NAME2 m
  else if md =? COMMENT then c_COMMENT2 m
  else if md =? HCRC then c_HCRC m
  else if md =? DICTID then c_DICTID flush m
  else if md =? DICT then c_DICT flush m
  else if md =? TYPE then c_TYPE flush m
  else if md =? TYPEDO then c_TYPEDO flush m
  else if md =? STORED then c_STORED flush m
  else if md =? COPY_ then c_COPY_ m
  else if md =? COPY then c_COPY m
  else if md =? TABLE then c_TABLE flush lenfix distfix fast m
  else if md =? LENLENS then c_LENLENS flush lenfix distfix fast m
  else if md =? CODELENS then c_CODELENS flush lenfix distfix fast m
  else if md =? LEN_ then c_LEN_ lenfix distfix fast m
  else if md =? LEN then c_LEN lenfix distfix fast m
  else if md =? LENEXT then c_LENEXT lenfix distfix m
  else if md =? DIST then c_DIST lenfix distfix m
  else if md =? DISTEXT then c_DISTEXT m
  else if md =? MATCH then c_MATCH m
  else if md =? LIT then c_LIT m
  else if md =? CHECK then c_CHECK m
  else if md =? LENGTH then c_LENGTH m
  else if md =? DONE then c_DONE m
  else if md =? BAD then c_BAD m
  else if md =? MEM then IRet Z_MEM_ERROR m
  else IRet Z_STREAM_ERROR m.

End Cases2.

Section Call2.
Variables (flush: Z) (lenfix distfix: list entry).

Definition stepf2 (m: mst) : iout := step2 flush lenfix distfix (fast lenfix distfix) m.

Inductive loop2 : mst -> iout -> Prop :=
| loop2_ret: forall m r m', stepf2 m = IRet r m' -> loop2 m (IRet r m')
| loop2_leave: forall m m', stepf2 m = IBrk m' -> m_leave m' = 1 -> loop2 m (IBrk m')
| loop2_next: forall m m' o, stepf2 m = IBrk m' -> m_leave m' <> 1 -> loop2 m' o -> loop2 m o.

End Call2.

Definition run2 (flush: Z) (fx dx: list entry) (m0: mst) (res: result) : Prop :=
  exists o, loop2 flush fx dx m0 o /\
  match o with
  | IRet r m => res = Res r m None
  | IBrk m => inf_leave flush m res
  end.

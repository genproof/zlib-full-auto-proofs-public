(* The specifications of inflate()'s callees, in the compspecs of the inflate unit (the bodies of
   inflate_fixed (inftrees.c) and inflate_fast (inffast.c) are proved in it too: their units have the
   same composites), and the instances that let inflate's proofs call the specifications stated in
   other units' compspecs (inflate_table: Inftrees.CS; crc32: Crc32.CS; adler32: Adler32.CS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate Zlib.units.Inftrees Zlib.units.Crc32 Zlib.units.Adler32.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.Loop.
Require Export Zlib.proof.inflate.Inv.
Require Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec Zlib.proof.inftrees.spec.
Require Zlib.proof.zutil.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

#[export] Instance CCE_inftrees : change_composite_env Zlib.units.Inftrees.CS Zlib.units.Inflate.CS.
Proof. make_cs_preserve Zlib.units.Inftrees.CS Zlib.units.Inflate.CS. Defined.
#[export] Instance CCE_crc32 : change_composite_env Zlib.units.Crc32.CS Zlib.units.Inflate.CS.
Proof. make_cs_preserve Zlib.units.Crc32.CS Zlib.units.Inflate.CS. Defined.
#[export] Instance CCE_adler32 : change_composite_env Zlib.units.Adler32.CS Zlib.units.Inflate.CS.
Proof. make_cs_preserve Zlib.units.Adler32.CS Zlib.units.Inflate.CS. Defined.

(* the allocator as the stream's zalloc/zfree: the function pointers *)
Definition zfuncs (gv: globals) : mpred :=
  func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc) *
  func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) (gv _zcfree).

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fixed(state): the fixed tables of inffixed.h                                          *)

Definition inflate_fixed_spec :=
  DECLARE _inflate_fixed
  WITH sp: val, gv: globals, v1: val, v2: val, v3: val, v4: val
  PRE [ tptr t_state ]
    PROP () PARAMS (sp) GLOBALS (gv)
    SEP (field_at Ews t_state (DOT _lencode) v1 sp; field_at Ews t_state (DOT _lenbits) v2 sp;
         field_at Ews t_state (DOT _distcode) v3 sp; field_at Ews t_state (DOT _distbits) v4 sp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_state (DOT _lencode) (gv g_lenfix) sp;
         field_at Ews t_state (DOT _lenbits) (Vint (Int.repr 9)) sp;
         field_at Ews t_state (DOT _distcode) (gv g_distfix) sp;
         field_at Ews t_state (DOT _distbits) (Vint (Int.repr 5)) sp).

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast(strm, start): the model's fast; called from LEN with RESTORE() done               *)

Definition inflate_fast_spec :=
  DECLARE _inflate_fast
  WITH F: frame, m: mst
  PRE [ tptr t_strm, tuint ]
    PROP (mwf m; m_mode m = LEN; m_snx m = m_nx m; m_sow m = Zlength (m_ow m);
          i_hold (m_s m) = m_hold m; i_bits (m_s m) = m_bits m;
          6 <= m_have m; 258 <= m_left m; m_bits m < 8; m_out m = m_aout m;
          in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m))
    PARAMS (f_strmp F; Vint (Int.repr (m_out m))) GLOBALS (f_gv F)
    SEP (mem_rep F m)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_rep F (fast lenfix_list distfix_list m)).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateStateCheck(strm): 1 for a Z_NULL stream, a stream without state (ended) or an invalid one;
   0 for a live stream (mode HEAD..SYNC).  The stream's zalloc/zfree are zcalloc/zcfree.            *)

Definition stream_ok_val (gv: globals) (sv: reptype t_strm) (st: val) : Prop :=
  let '(_, (_, (_, (_, (_, (_, (_, (st', (za, (zf, _)))))))))) := sv in
  st' = st /\ za = gv _zcalloc /\ zf = gv _zcfree.

Definition inflateStateCheck_spec :=
  DECLARE _inflateStateCheck
  WITH strmp: val, shs: share, sv: reptype t_strm, sp: val, md: Z, live: bool, gv: globals
  PRE [ tptr t_strm ]
    PROP (strmp = nullval \/ (readable_share shs /\ stream_ok_val gv sv (if live then sp else nullval));
          live = true -> isptr sp; Int.min_signed <= md <= Int.max_signed)
    PARAMS (strmp) GLOBALS (gv)
    SEP (if eq_dec strmp nullval then emp else
           (data_at shs t_strm sv strmp *
            if live then field_at Ews t_state (DOT _strm) strmp sp * field_at Ews t_state (DOT _mode) (Vint (Int.repr md)) sp
            else emp);
         zfuncs gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if eq_dec strmp nullval then 1 else if live then
                                      (if andb (HEAD <=? md) (md <=? SYNC) then 0 else 1) else 1)))
    SEP (if eq_dec strmp nullval then emp else
           (data_at shs t_strm sv strmp *
            if live then field_at Ews t_state (DOT _strm) strmp sp * field_at Ews t_state (DOT _mode) (Vint (Int.repr md)) sp
            else emp);
         zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* updatewindow(strm, end, copy): the window gets the copy bytes before end (the model's
   updatewindow); allocates the window when there is none (zcalloc: may fail, then returns 1 and
   nothing changes).  The source is the slice [e - copy, e) of an object.                          *)

Definition updatewindow_spec :=
  DECLARE _updatewindow
  WITH gv: globals, shs: share, strmp: val, sv: reptype t_strm, sp: val, headp: val, winp: val,
       s: istate, ssh: share, p: val, n: Z, c: list val, e: Z, data: list Z
  PRE [ tptr t_strm, tptr tuchar, tuint ]
    PROP (readable_share shs; stream_ok_val gv sv sp; swf s; readable_share ssh;
          0 <= Zlength data <= e; e <= n; Zlength c = n; n <= Ptrofs.max_unsigned;
          sublist (e - Zlength data) e c = byte_vals data; bytes_ok data;
          i_win s = false -> winp = nullval)
    PARAMS (strmp; offset_val e p; Vint (Int.repr (Zlength data))) GLOBALS (gv)
    SEP (data_at shs t_strm sv strmp; state_rep gv sp strmp headp winp s; win_rep winp s;
         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX winp': val,
    PROP ((r = 0 /\ (i_win s = true -> winp' = winp)) \/ (r = 1 /\ i_win s = false /\ winp' = nullval))
    RETURN (Vint (Int.repr r))
    SEP (data_at shs t_strm sv strmp;
         state_rep gv sp strmp headp winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
         win_rep winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* The context of inflate()'s body                                                               *)

Definition Gprog_inflate : funspecs :=
  [Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.crc32.Spec.crc32_spec; inflateStateCheck_spec;
   inflate_fast_spec; inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS)); updatewindow_spec].

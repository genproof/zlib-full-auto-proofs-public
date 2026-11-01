From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "inftrees.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___gp_code : ident := $"__gp_code".
Definition _adler : ident := $"adler".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _back : ident := $"back".
Definition _base : ident := $"base".
Definition _bits : ident := $"bits".
Definition _check : ident := $"check".
Definition _codes : ident := $"codes".
Definition _comm_max : ident := $"comm_max".
Definition _comment : ident := $"comment".
Definition _count : ident := $"count".
Definition _curr : ident := $"curr".
Definition _data_type : ident := $"data_type".
Definition _dbase : ident := $"dbase".
Definition _dext : ident := $"dext".
Definition _distbits : ident := $"distbits".
Definition _distcode : ident := $"distcode".
Definition _distfix : ident := $"distfix".
Definition _dmax : ident := $"dmax".
Definition _done : ident := $"done".
Definition _drop : ident := $"drop".
Definition _extra : ident := $"extra".
Definition _extra_len : ident := $"extra_len".
Definition _extra_max : ident := $"extra_max".
Definition _fill : ident := $"fill".
Definition _flags : ident := $"flags".
Definition _gz_header_s : ident := $"gz_header_s".
Definition _have : ident := $"have".
Definition _havedict : ident := $"havedict".
Definition _hcrc : ident := $"hcrc".
Definition _head : ident := $"head".
Definition _here : ident := $"here".
Definition _hold : ident := $"hold".
Definition _huff : ident := $"huff".
Definition _incr : ident := $"incr".
Definition _inflate_copyright : ident := $"inflate_copyright".
Definition _inflate_fixed : ident := $"inflate_fixed".
Definition _inflate_state : ident := $"inflate_state".
Definition _inflate_table : ident := $"inflate_table".
Definition _internal_state : ident := $"internal_state".
Definition _last : ident := $"last".
Definition _lbase : ident := $"lbase".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _lenbits : ident := $"lenbits".
Definition _lencode : ident := $"lencode".
Definition _lenfix : ident := $"lenfix".
Definition _length : ident := $"length".
Definition _lens : ident := $"lens".
Definition _lext : ident := $"lext".
Definition _low : ident := $"low".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _match : ident := $"match".
Definition _max : ident := $"max".
Definition _min : ident := $"min".
Definition _mode : ident := $"mode".
Definition _msg : ident := $"msg".
Definition _name : ident := $"name".
Definition _name_max : ident := $"name_max".
Definition _ncode : ident := $"ncode".
Definition _ndist : ident := $"ndist".
Definition _next : ident := $"next".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nlen : ident := $"nlen".
Definition _offs : ident := $"offs".
Definition _offset : ident := $"offset".
Definition _op : ident := $"op".
Definition _opaque : ident := $"opaque".
Definition _os : ident := $"os".
Definition _reserved : ident := $"reserved".
Definition _root : ident := $"root".
Definition _sane : ident := $"sane".
Definition _state : ident := $"state".
Definition _strm : ident := $"strm".
Definition _sym : ident := $"sym".
Definition _table : ident := $"table".
Definition _text : ident := $"text".
Definition _time : ident := $"time".
Definition _total : ident := $"total".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _type : ident := $"type".
Definition _used : ident := $"used".
Definition _val : ident := $"val".
Definition _was : ident := $"was".
Definition _wbits : ident := $"wbits".
Definition _whave : ident := $"whave".
Definition _window : ident := $"window".
Definition _wnext : ident := $"wnext".
Definition _work : ident := $"work".
Definition _wrap : ident := $"wrap".
Definition _wsize : ident := $"wsize".
Definition _xflags : ident := $"xflags".
Definition _z_stream_s : ident := $"z_stream_s".
Definition _zalloc : ident := $"zalloc".
Definition _zfree : ident := $"zfree".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_inflate_copyright := {|
  gvar_info := (tarray tschar 47);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 57) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 54) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_lbase := {|
  gvar_info := (tarray tushort 31);
  gvar_init := (Init_int16 (Int.repr 3) :: Init_int16 (Int.repr 4) ::
                Init_int16 (Int.repr 5) :: Init_int16 (Int.repr 6) ::
                Init_int16 (Int.repr 7) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 9) :: Init_int16 (Int.repr 10) ::
                Init_int16 (Int.repr 11) :: Init_int16 (Int.repr 13) ::
                Init_int16 (Int.repr 15) :: Init_int16 (Int.repr 17) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 23) ::
                Init_int16 (Int.repr 27) :: Init_int16 (Int.repr 31) ::
                Init_int16 (Int.repr 35) :: Init_int16 (Int.repr 43) ::
                Init_int16 (Int.repr 51) :: Init_int16 (Int.repr 59) ::
                Init_int16 (Int.repr 67) :: Init_int16 (Int.repr 83) ::
                Init_int16 (Int.repr 99) :: Init_int16 (Int.repr 115) ::
                Init_int16 (Int.repr 131) :: Init_int16 (Int.repr 163) ::
                Init_int16 (Int.repr 195) :: Init_int16 (Int.repr 227) ::
                Init_int16 (Int.repr 258) :: Init_int16 (Int.repr 0) ::
                Init_int16 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_lext := {|
  gvar_info := (tarray tushort 31);
  gvar_init := (Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 17) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 17) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 18) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 18) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 19) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 19) ::
                Init_int16 (Int.repr 20) :: Init_int16 (Int.repr 20) ::
                Init_int16 (Int.repr 20) :: Init_int16 (Int.repr 20) ::
                Init_int16 (Int.repr 21) :: Init_int16 (Int.repr 21) ::
                Init_int16 (Int.repr 21) :: Init_int16 (Int.repr 21) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 199) ::
                Init_int16 (Int.repr 75) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_dbase := {|
  gvar_info := (tarray tushort 32);
  gvar_init := (Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 3) :: Init_int16 (Int.repr 4) ::
                Init_int16 (Int.repr 5) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int16 (Int.repr 13) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 25) ::
                Init_int16 (Int.repr 33) :: Init_int16 (Int.repr 49) ::
                Init_int16 (Int.repr 65) :: Init_int16 (Int.repr 97) ::
                Init_int16 (Int.repr 129) :: Init_int16 (Int.repr 193) ::
                Init_int16 (Int.repr 257) :: Init_int16 (Int.repr 385) ::
                Init_int16 (Int.repr 513) :: Init_int16 (Int.repr 769) ::
                Init_int16 (Int.repr 1025) :: Init_int16 (Int.repr 1537) ::
                Init_int16 (Int.repr 2049) :: Init_int16 (Int.repr 3073) ::
                Init_int16 (Int.repr 4097) :: Init_int16 (Int.repr 6145) ::
                Init_int16 (Int.repr 8193) :: Init_int16 (Int.repr 12289) ::
                Init_int16 (Int.repr 16385) :: Init_int16 (Int.repr 24577) ::
                Init_int16 (Int.repr 0) :: Init_int16 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_dext := {|
  gvar_info := (tarray tushort 32);
  gvar_init := (Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 16) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 17) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 18) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 19) ::
                Init_int16 (Int.repr 20) :: Init_int16 (Int.repr 20) ::
                Init_int16 (Int.repr 21) :: Init_int16 (Int.repr 21) ::
                Init_int16 (Int.repr 22) :: Init_int16 (Int.repr 22) ::
                Init_int16 (Int.repr 23) :: Init_int16 (Int.repr 23) ::
                Init_int16 (Int.repr 24) :: Init_int16 (Int.repr 24) ::
                Init_int16 (Int.repr 25) :: Init_int16 (Int.repr 25) ::
                Init_int16 (Int.repr 26) :: Init_int16 (Int.repr 26) ::
                Init_int16 (Int.repr 27) :: Init_int16 (Int.repr 27) ::
                Init_int16 (Int.repr 28) :: Init_int16 (Int.repr 28) ::
                Init_int16 (Int.repr 29) :: Init_int16 (Int.repr 29) ::
                Init_int16 (Int.repr 64) :: Init_int16 (Int.repr 64) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_inflate_table := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_type, tint) :: (_lens, (tptr tushort)) ::
                (_codes, tuint) ::
                (_table, (tptr (tptr (Tstruct ___gp_code noattr)))) ::
                (_bits, (tptr tuint)) :: (_work, (tptr tushort)) :: nil);
  fn_vars := ((_here, (Tstruct ___gp_code noattr)) ::
              (_count, (tarray tushort 16)) ::
              (_offs, (tarray tushort 16)) :: nil);
  fn_temps := ((_len, tuint) :: (_sym, tuint) :: (_min, tuint) ::
               (_max, tuint) :: (_root, tuint) :: (_curr, tuint) ::
               (_drop, tuint) :: (_left, tint) :: (_used, tuint) ::
               (_huff, tuint) :: (_incr, tuint) :: (_fill, tuint) ::
               (_low, tuint) :: (_mask, tuint) ::
               (_next, (tptr (Tstruct ___gp_code noattr))) ::
               (_base, (tptr tushort)) :: (_extra, (tptr tushort)) ::
               (_match, tuint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tushort) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tushort) :: (_t'1, tint) ::
               (_t'54, tushort) :: (_t'53, tushort) :: (_t'52, tushort) ::
               (_t'51, tushort) :: (_t'50, tuchar) ::
               (_t'49, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'48, tuchar) ::
               (_t'47, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'46, tushort) ::
               (_t'45, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'44, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'43, tuchar) ::
               (_t'42, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'41, tuchar) ::
               (_t'40, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'39, tushort) ::
               (_t'38, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'37, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'36, tushort) :: (_t'35, tushort) :: (_t'34, tushort) ::
               (_t'33, tushort) :: (_t'32, tushort) :: (_t'31, tushort) ::
               (_t'30, tushort) :: (_t'29, tushort) :: (_t'28, tushort) ::
               (_t'27, tushort) :: (_t'26, tushort) :: (_t'25, tushort) ::
               (_t'24, tushort) :: (_t'23, tushort) :: (_t'22, tuchar) ::
               (_t'21, tuchar) :: (_t'20, tushort) :: (_t'19, tushort) ::
               (_t'18, tushort) :: (_t'17, tushort) ::
               (_t'16, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'15, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'14, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'13, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'12, tuchar) :: (_t'11, tuchar) :: (_t'10, tushort) ::
               (_t'9, (tptr (Tstruct ___gp_code noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _base (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _extra (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sset _match (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _len (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _len tuint)
                             (Econst_int (Int.repr 15) tint) tint)
                Sskip
                Sbreak)
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _count (tarray tushort 16))
                    (Etempvar _len tuint) (tptr tushort)) tushort)
                (Econst_int (Int.repr 0) tint)))
            (Sset _len
              (Ebinop Oadd (Etempvar _len tuint)
                (Econst_int (Int.repr 1) tint) tuint))))
        (Ssequence
          (Ssequence
            (Sset _sym (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _sym tuint)
                               (Etempvar _codes tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'52
                    (Ederef
                      (Ebinop Oadd (Etempvar _lens (tptr tushort))
                        (Etempvar _sym tuint) (tptr tushort)) tushort))
                  (Ssequence
                    (Sset _t'53
                      (Ederef
                        (Ebinop Oadd (Etempvar _lens (tptr tushort))
                          (Etempvar _sym tuint) (tptr tushort)) tushort))
                    (Ssequence
                      (Sset _t'54
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _t'53 tushort) (tptr tushort)) tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _t'52 tushort) (tptr tushort)) tushort)
                        (Ebinop Oadd (Etempvar _t'54 tushort)
                          (Econst_int (Int.repr 1) tint) tint))))))
              (Sset _sym
                (Ebinop Oadd (Etempvar _sym tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Sset _root (Ederef (Etempvar _bits (tptr tuint)) tuint))
            (Ssequence
              (Ssequence
                (Sset _max (Econst_int (Int.repr 15) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _max tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'51
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _max tuint) (tptr tushort)) tushort))
                      (Sifthenelse (Ebinop One (Etempvar _t'51 tushort)
                                     (Econst_int (Int.repr 0) tint) tint)
                        Sbreak
                        Sskip)))
                  (Sset _max
                    (Ebinop Osub (Etempvar _max tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _root tuint)
                               (Etempvar _max tuint) tint)
                  (Sset _root (Etempvar _max tuint))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _max tuint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield (Evar _here (Tstruct ___gp_code noattr)) _op
                          tuchar)
                        (Ecast (Econst_int (Int.repr 64) tint) tuchar))
                      (Ssequence
                        (Sassign
                          (Efield (Evar _here (Tstruct ___gp_code noattr))
                            _bits tuchar)
                          (Ecast (Econst_int (Int.repr 1) tint) tuchar))
                        (Ssequence
                          (Sassign
                            (Efield (Evar _here (Tstruct ___gp_code noattr))
                              _val tushort)
                            (Ecast (Econst_int (Int.repr 0) tint) tushort))
                          (Ssequence
                            (Ssequence
                              (Sset _t'49
                                (Ederef
                                  (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                  (tptr (Tstruct ___gp_code noattr))))
                              (Ssequence
                                (Sset _t'50
                                  (Efield
                                    (Evar _here (Tstruct ___gp_code noattr))
                                    _op tuchar))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'49 (tptr (Tstruct ___gp_code noattr)))
                                      (Tstruct ___gp_code noattr)) _op
                                    tuchar) (Etempvar _t'50 tuchar))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'47
                                  (Ederef
                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                    (tptr (Tstruct ___gp_code noattr))))
                                (Ssequence
                                  (Sset _t'48
                                    (Efield
                                      (Evar _here (Tstruct ___gp_code noattr))
                                      _bits tuchar))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'47 (tptr (Tstruct ___gp_code noattr)))
                                        (Tstruct ___gp_code noattr)) _bits
                                      tuchar) (Etempvar _t'48 tuchar))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'45
                                    (Ederef
                                      (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                      (tptr (Tstruct ___gp_code noattr))))
                                  (Ssequence
                                    (Sset _t'46
                                      (Efield
                                        (Evar _here (Tstruct ___gp_code noattr))
                                        _val tushort))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'45 (tptr (Tstruct ___gp_code noattr)))
                                          (Tstruct ___gp_code noattr)) _val
                                        tushort) (Etempvar _t'46 tushort))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'44
                                      (Ederef
                                        (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                        (tptr (Tstruct ___gp_code noattr))))
                                    (Sassign
                                      (Ederef
                                        (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                        (tptr (Tstruct ___gp_code noattr)))
                                      (Ebinop Oadd
                                        (Etempvar _t'44 (tptr (Tstruct ___gp_code noattr)))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (Tstruct ___gp_code noattr)))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'42
                                        (Ederef
                                          (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                          (tptr (Tstruct ___gp_code noattr))))
                                      (Ssequence
                                        (Sset _t'43
                                          (Efield
                                            (Evar _here (Tstruct ___gp_code noattr))
                                            _op tuchar))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'42 (tptr (Tstruct ___gp_code noattr)))
                                              (Tstruct ___gp_code noattr))
                                            _op tuchar)
                                          (Etempvar _t'43 tuchar))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'40
                                          (Ederef
                                            (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                            (tptr (Tstruct ___gp_code noattr))))
                                        (Ssequence
                                          (Sset _t'41
                                            (Efield
                                              (Evar _here (Tstruct ___gp_code noattr))
                                              _bits tuchar))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'40 (tptr (Tstruct ___gp_code noattr)))
                                                (Tstruct ___gp_code noattr))
                                              _bits tuchar)
                                            (Etempvar _t'41 tuchar))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'38
                                            (Ederef
                                              (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                              (tptr (Tstruct ___gp_code noattr))))
                                          (Ssequence
                                            (Sset _t'39
                                              (Efield
                                                (Evar _here (Tstruct ___gp_code noattr))
                                                _val tushort))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'38 (tptr (Tstruct ___gp_code noattr)))
                                                  (Tstruct ___gp_code noattr))
                                                _val tushort)
                                              (Etempvar _t'39 tushort))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'37
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr))))
                                            (Sassign
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr)))
                                              (Ebinop Oadd
                                                (Etempvar _t'37 (tptr (Tstruct ___gp_code noattr)))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr (Tstruct ___gp_code noattr)))))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Etempvar _bits (tptr tuint))
                                                tuint)
                                              (Econst_int (Int.repr 1) tint))
                                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Sset _min (Econst_int (Int.repr 1) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _min tuint)
                                         (Etempvar _max tuint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _t'36
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _count (tarray tushort 16))
                                  (Etempvar _min tuint) (tptr tushort))
                                tushort))
                            (Sifthenelse (Ebinop One (Etempvar _t'36 tushort)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              Sbreak
                              Sskip)))
                        (Sset _min
                          (Ebinop Oadd (Etempvar _min tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _root tuint)
                                     (Etempvar _min tuint) tint)
                        (Sset _root (Etempvar _min tuint))
                        Sskip)
                      (Ssequence
                        (Sset _left (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _len (Econst_int (Int.repr 1) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Ole
                                               (Etempvar _len tuint)
                                               (Econst_int (Int.repr 15) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _left
                                    (Ebinop Oshl (Etempvar _left tint)
                                      (Econst_int (Int.repr 1) tint) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'35
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _count (tarray tushort 16))
                                            (Etempvar _len tuint)
                                            (tptr tushort)) tushort))
                                      (Sset _left
                                        (Ebinop Osub (Etempvar _left tint)
                                          (Etempvar _t'35 tushort) tint)))
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _left tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sreturn (Some (Eunop Oneg
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)))
                                      Sskip))))
                              (Sset _len
                                (Ebinop Oadd (Etempvar _len tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Ogt (Etempvar _left tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _type tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Sset _t'1
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Sset _t'1
                                      (Ecast
                                        (Ebinop One (Etempvar _max tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tbool))
                                    (Sset _t'1
                                      (Ecast (Etempvar _t'1 tint) tbool))))
                                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'1 tint)
                                (Sreturn (Some (Eunop Oneg
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)))
                                Sskip))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _offs (tarray tushort 16))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tushort)) tushort)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Ssequence
                                  (Sset _len (Econst_int (Int.repr 1) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _len tuint)
                                                     (Econst_int (Int.repr 15) tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _t'33
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _offs (tarray tushort 16))
                                              (Etempvar _len tuint)
                                              (tptr tushort)) tushort))
                                        (Ssequence
                                          (Sset _t'34
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _count (tarray tushort 16))
                                                (Etempvar _len tuint)
                                                (tptr tushort)) tushort))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _offs (tarray tushort 16))
                                                (Ebinop Oadd
                                                  (Etempvar _len tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint) (tptr tushort))
                                              tushort)
                                            (Ebinop Oadd
                                              (Etempvar _t'33 tushort)
                                              (Etempvar _t'34 tushort) tint)))))
                                    (Sset _len
                                      (Ebinop Oadd (Etempvar _len tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _sym
                                      (Econst_int (Int.repr 0) tint))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _sym tuint)
                                                       (Etempvar _codes tuint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _t'30
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _lens (tptr tushort))
                                                (Etempvar _sym tuint)
                                                (tptr tushort)) tushort))
                                          (Sifthenelse (Ebinop One
                                                         (Etempvar _t'30 tushort)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'32
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _lens (tptr tushort))
                                                        (Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Sset _t'2
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _offs (tarray tushort 16))
                                                        (Etempvar _t'32 tushort)
                                                        (tptr tushort))
                                                      tushort)))
                                                (Ssequence
                                                  (Sset _t'31
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _lens (tptr tushort))
                                                        (Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _offs (tarray tushort 16))
                                                        (Etempvar _t'31 tushort)
                                                        (tptr tushort))
                                                      tushort)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'2 tushort)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint))))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _work (tptr tushort))
                                                    (Etempvar _t'2 tushort)
                                                    (tptr tushort)) tushort)
                                                (Ecast (Etempvar _sym tuint)
                                                  tushort)))
                                            Sskip)))
                                      (Sset _sym
                                        (Ebinop Oadd (Etempvar _sym tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint))))
                                  (Ssequence
                                    (Sswitch (Etempvar _type tint)
                                      (LScons (Some 0)
                                        (Ssequence
                                          (Sset _match
                                            (Econst_int (Int.repr 20) tint))
                                          Sbreak)
                                        (LScons (Some 1)
                                          (Ssequence
                                            (Sset _base
                                              (Evar _lbase (tarray tushort 31)))
                                            (Ssequence
                                              (Sset _extra
                                                (Evar _lext (tarray tushort 31)))
                                              (Ssequence
                                                (Sset _match
                                                  (Econst_int (Int.repr 257) tint))
                                                Sbreak)))
                                          (LScons (Some 2)
                                            (Ssequence
                                              (Sset _base
                                                (Evar _dbase (tarray tushort 32)))
                                              (Ssequence
                                                (Sset _extra
                                                  (Evar _dext (tarray tushort 32)))
                                                Sbreak))
                                            LSnil))))
                                    (Ssequence
                                      (Sset _huff
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sset _sym
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sset _len (Etempvar _min tuint))
                                          (Ssequence
                                            (Sset _next
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr))))
                                            (Ssequence
                                              (Sset _curr
                                                (Etempvar _root tuint))
                                              (Ssequence
                                                (Sset _drop
                                                  (Econst_int (Int.repr 0) tint))
                                                (Ssequence
                                                  (Sset _low
                                                    (Ecast
                                                      (Eunop Oneg
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint) tuint))
                                                  (Ssequence
                                                    (Sset _used
                                                      (Ebinop Oshl
                                                        (Econst_int (Int.repr 1) tuint)
                                                        (Etempvar _root tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _mask
                                                        (Ebinop Osub
                                                          (Etempvar _used tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _type tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 852) tint)
                                                                    tint)
                                                                  tbool))
                                                              (Sset _t'3
                                                                (Econst_int (Int.repr 0) tint)))
                                                            (Sifthenelse (Etempvar _t'3 tint)
                                                              (Sset _t'4
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _type tint)
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 592) tint)
                                                                    tint)
                                                                    tbool))
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Etempvar _t'4 tint)
                                                                    tbool)))
                                                                (Sset _t'4
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tbool)))))
                                                          (Sifthenelse (Etempvar _t'4 tint)
                                                            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                            Sskip))
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              Sskip
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                  (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'23
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'23 tushort)
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    tuint)
                                                                    (Etempvar _match tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'29 tushort))))
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _t'24 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _extra (tptr tushort))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'27 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _t'28 tushort)
                                                                    tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _base (tptr tushort))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'25 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'26 tushort)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Econst_int (Int.repr 0) tint)))))))
                                                                  (Ssequence
                                                                    (Sset _incr
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _fill
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _curr tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _min
                                                                    (Etempvar _fill tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _fill
                                                                    (Ebinop Osub
                                                                    (Etempvar _fill tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'22 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'21 tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'20 tushort))))))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _fill tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sset _incr
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint)
                                                                    (Sset _incr
                                                                    (Ebinop Oshr
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _huff
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _huff
                                                                    (Ebinop Oadd
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint)))
                                                                    (Sset _huff
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Ssequence
                                                                    (Sset _sym
                                                                    (Ebinop Oadd
                                                                    (Etempvar _sym tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _t'5
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'19 tushort)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tushort)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Etempvar _t'5 tushort)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'5 tushort)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _max tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _t'18
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _len
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _lens (tptr tushort))
                                                                    (Etempvar _t'18 tushort)
                                                                    (tptr tushort))
                                                                    tushort))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _root tuint)
                                                                    tint)
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _low tuint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'8
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'8 tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _drop tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _drop
                                                                    (Etempvar _root tuint))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _min tuint)
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _curr
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Etempvar _curr tuint)
                                                                    tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _max tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tint)
                                                                    (Etempvar _t'17 tushort)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _left tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _curr
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Sset _left
                                                                    (Ebinop Oshl
                                                                    (Etempvar _left tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))))
                                                                    (Ssequence
                                                                    (Sset _used
                                                                    (Ebinop Oadd
                                                                    (Etempvar _used tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _curr tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'6
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 852) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'6
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'6 tint)
                                                                    (Sset _t'7
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 592) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Etempvar _t'7 tint)
                                                                    tbool)))
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'7 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sset _low
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'16 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _curr tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'15 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _root tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'13 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _t'14 (tptr (Tstruct ___gp_code noattr)))
                                                                    tlong)
                                                                    tushort))))))))))))))
                                                                    Sskip))))))))))))))
                                                            Sskip)
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop One
                                                                (Etempvar _huff tuint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'12 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'11
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'11 tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'10
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'10 tushort))))))))
                                                              Sskip)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'9
                                                                  (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'9 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _used tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Ederef
                                                                    (Etempvar _bits (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _root tuint))
                                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))))
|}.

Definition v_lenfix := {|
  gvar_info := (tarray (Tstruct ___gp_code noattr) 512);
  gvar_init := (Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 80) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 16) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 115) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 112) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 48) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 192) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 96) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 160) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 128) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 64) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 224) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 88) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 24) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 144) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 120) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 56) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 208) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 104) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 40) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 176) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 136) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 72) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 240) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 84) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 20) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 227) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 52) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 200) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 36) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 168) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 132) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 68) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 232) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 92) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 28) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 152) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 83) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 124) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 60) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 216) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 108) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 44) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 184) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 12) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 140) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 76) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 248) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 82) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 18) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 163) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 50) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 196) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 98) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 34) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 164) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 2) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 130) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 66) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 228) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 90) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 26) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 148) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 122) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 58) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 212) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 106) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 42) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 180) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 138) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 74) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 244) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 86) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 22) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 0) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 118) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 54) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 204) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 102) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 38) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 172) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 134) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 70) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 236) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 94) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 30) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 156) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 99) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 126) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 62) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 220) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 46) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 188) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 14) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 142) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 78) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 252) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 81) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 131) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 113) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 49) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 194) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 97) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 33) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 162) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 129) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 65) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 226) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 89) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 25) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 146) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 57) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 210) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 105) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 41) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 178) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 137) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 73) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 242) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 85) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 21) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 258) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 117) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 53) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 202) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 37) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 170) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 133) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 69) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 234) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 93) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 29) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 154) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 83) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 125) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 61) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 218) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 109) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 45) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 186) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 141) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 77) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 250) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 83) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 195) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 198) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 166) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 131) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 230) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 91) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 150) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 123) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 214) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 182) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 139) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 75) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 246) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 87) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 0) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 119) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 55) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 206) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 39) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 174) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 135) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 71) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 238) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 95) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 158) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 99) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 127) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 63) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 222) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 111) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 47) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 190) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 143) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 79) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 254) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 80) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 16) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 115) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 112) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 48) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 193) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 96) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 32) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 161) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 128) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 64) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 225) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 88) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 24) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 145) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 120) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 56) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 209) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 104) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 40) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 177) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 136) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 72) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 241) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 84) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 20) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 227) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 52) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 201) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 36) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 169) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 132) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 68) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 233) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 92) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 28) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 153) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 83) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 124) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 60) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 217) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 108) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 44) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 185) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 12) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 140) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 76) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 249) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 82) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 18) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 163) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 50) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 197) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 98) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 34) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 165) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 2) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 130) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 66) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 229) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 90) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 26) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 149) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 122) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 58) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 213) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 106) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 42) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 181) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 138) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 74) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 245) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 86) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 22) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 0) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 118) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 54) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 205) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 102) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 38) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 173) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 134) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 70) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 237) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 94) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 30) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 157) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 99) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 126) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 62) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 221) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 46) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 189) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 14) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 142) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 78) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 253) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 81) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 131) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 113) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 49) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 195) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 10) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 97) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 33) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 163) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 1) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 129) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 65) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 227) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 6) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 89) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 25) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 147) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 121) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 57) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 211) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 105) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 41) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 179) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 137) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 73) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 243) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 85) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 21) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 258) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 117) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 53) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 203) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 37) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 171) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 133) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 69) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 235) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 8) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 93) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 29) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 155) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 83) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 125) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 61) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 219) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 109) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 45) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 187) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 141) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 77) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 251) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 83) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 195) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 199) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 35) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 167) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 131) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 231) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 91) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 151) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 67) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 123) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 59) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 215) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 19) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 43) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 183) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 11) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 139) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 75) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 247) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 87) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 23) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 0) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 51) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 119) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 55) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 207) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 39) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 175) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 135) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 71) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 239) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 95) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 31) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 159) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 99) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 127) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 63) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 223) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 7) ::
                Init_int16 (Int.repr 27) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 111) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 47) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 191) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 15) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int16 (Int.repr 143) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 8) ::
                Init_int16 (Int.repr 79) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 9) :: Init_int16 (Int.repr 255) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_distfix := {|
  gvar_info := (tarray (Tstruct ___gp_code noattr) 32);
  gvar_init := (Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 1) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 257) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 17) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 4097) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 5) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 1025) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 65) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 16385) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 3) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 513) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 33) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 8193) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 9) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 2049) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 129) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 0) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 2) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 385) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 25) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 6145) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 7) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 1537) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 97) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 24577) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 4) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 769) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 49) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 12289) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 13) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 3073) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 5) ::
                Init_int16 (Int.repr 193) :: Init_int8 (Int.repr 64) ::
                Init_int8 (Int.repr 5) :: Init_int16 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_inflate_fixed := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _inflate_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
        (Tstruct _inflate_state noattr)) _lencode
      (tptr (Tstruct ___gp_code noattr)))
    (Evar _lenfix (tarray (Tstruct ___gp_code noattr) 512)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
          (Tstruct _inflate_state noattr)) _lenbits tuint)
      (Econst_int (Int.repr 9) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
            (Tstruct _inflate_state noattr)) _distcode
          (tptr (Tstruct ___gp_code noattr)))
        (Evar _distfix (tarray (Tstruct ___gp_code noattr) 32)))
      (Sassign
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
            (Tstruct _inflate_state noattr)) _distbits tuint)
        (Econst_int (Int.repr 5) tint)))))
|}.

Definition composites : list composite_definition :=
(Composite _z_stream_s Struct
   (Member_plain _next_in (tptr tuchar) :: Member_plain _avail_in tuint ::
    Member_plain _total_in tulong :: Member_plain _next_out (tptr tuchar) ::
    Member_plain _avail_out tuint :: Member_plain _total_out tulong ::
    Member_plain _msg (tptr tschar) ::
    Member_plain _state (tptr (Tstruct _internal_state noattr)) ::
    Member_plain _zalloc
      (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil) (tptr tvoid)
              cc_default)) ::
    Member_plain _zfree
      (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
              cc_default)) :: Member_plain _opaque (tptr tvoid) ::
    Member_plain _data_type tint :: Member_plain _adler tulong ::
    Member_plain _reserved tulong :: nil)
   noattr ::
 Composite _gz_header_s Struct
   (Member_plain _text tint :: Member_plain _time tulong ::
    Member_plain _xflags tint :: Member_plain _os tint ::
    Member_plain _extra (tptr tuchar) :: Member_plain _extra_len tuint ::
    Member_plain _extra_max tuint :: Member_plain _name (tptr tuchar) ::
    Member_plain _name_max tuint :: Member_plain _comment (tptr tuchar) ::
    Member_plain _comm_max tuint :: Member_plain _hcrc tint ::
    Member_plain _done tint :: nil)
   noattr ::
 Composite ___gp_code Struct
   (Member_plain _op tuchar :: Member_plain _bits tuchar ::
    Member_plain _val tushort :: nil)
   noattr ::
 Composite _inflate_state Struct
   (Member_plain _strm (tptr (Tstruct _z_stream_s noattr)) ::
    Member_plain _mode tint :: Member_plain _last tint ::
    Member_plain _wrap tint :: Member_plain _havedict tint ::
    Member_plain _flags tint :: Member_plain _dmax tuint ::
    Member_plain _check tulong :: Member_plain _total tulong ::
    Member_plain _head (tptr (Tstruct _gz_header_s noattr)) ::
    Member_plain _wbits tuint :: Member_plain _wsize tuint ::
    Member_plain _whave tuint :: Member_plain _wnext tuint ::
    Member_plain _window (tptr tuchar) :: Member_plain _hold tulong ::
    Member_plain _bits tuint :: Member_plain _length tuint ::
    Member_plain _offset tuint :: Member_plain _extra tuint ::
    Member_plain _lencode (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _distcode (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _lenbits tuint :: Member_plain _distbits tuint ::
    Member_plain _ncode tuint :: Member_plain _nlen tuint ::
    Member_plain _ndist tuint :: Member_plain _have tuint ::
    Member_plain _next (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _lens (tarray tushort 320) ::
    Member_plain _work (tarray tushort 288) ::
    Member_plain _codes (tarray (Tstruct ___gp_code noattr) 1444) ::
    Member_plain _sane tint :: Member_plain _back tint ::
    Member_plain _was tuint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_inflate_copyright, Gvar v_inflate_copyright) :: (_lbase, Gvar v_lbase) ::
 (_lext, Gvar v_lext) :: (_dbase, Gvar v_dbase) :: (_dext, Gvar v_dext) ::
 (_inflate_table, Gfun(Internal f_inflate_table)) ::
 (_lenfix, Gvar v_lenfix) :: (_distfix, Gvar v_distfix) ::
 (_inflate_fixed, Gfun(Internal f_inflate_fixed)) :: nil).

Definition public_idents : list ident :=
(_inflate_fixed :: _inflate_table :: _inflate_copyright ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.



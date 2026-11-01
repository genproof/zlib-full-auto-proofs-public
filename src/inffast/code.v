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
  Definition source_file := "inffast.c".
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
Definition ___stringlit_inffast_1 : ident := $"__stringlit_inffast_1".
Definition ___stringlit_inffast_2 : ident := $"__stringlit_inffast_2".
Definition ___stringlit_inffast_3 : ident := $"__stringlit_inffast_3".
Definition _adler : ident := $"adler".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _back : ident := $"back".
Definition _beg : ident := $"beg".
Definition _bits : ident := $"bits".
Definition _check : ident := $"check".
Definition _codes : ident := $"codes".
Definition _comm_max : ident := $"comm_max".
Definition _comment : ident := $"comment".
Definition _data_type : ident := $"data_type".
Definition _dcode : ident := $"dcode".
Definition _dist : ident := $"dist".
Definition _distbits : ident := $"distbits".
Definition _distcode : ident := $"distcode".
Definition _dmask : ident := $"dmask".
Definition _dmax : ident := $"dmax".
Definition _done : ident := $"done".
Definition _end : ident := $"end".
Definition _extra : ident := $"extra".
Definition _extra_len : ident := $"extra_len".
Definition _extra_max : ident := $"extra_max".
Definition _flags : ident := $"flags".
Definition _from : ident := $"from".
Definition _gz_header_s : ident := $"gz_header_s".
Definition _have : ident := $"have".
Definition _havedict : ident := $"havedict".
Definition _hcrc : ident := $"hcrc".
Definition _head : ident := $"head".
Definition _here : ident := $"here".
Definition _hold : ident := $"hold".
Definition _in : ident := $"in".
Definition _inflate_fast : ident := $"inflate_fast".
Definition _inflate_state : ident := $"inflate_state".
Definition _internal_state : ident := $"internal_state".
Definition _last : ident := $"last".
Definition _lcode : ident := $"lcode".
Definition _len : ident := $"len".
Definition _lenbits : ident := $"lenbits".
Definition _lencode : ident := $"lencode".
Definition _length : ident := $"length".
Definition _lens : ident := $"lens".
Definition _lmask : ident := $"lmask".
Definition _main : ident := $"main".
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
Definition _offset : ident := $"offset".
Definition _op : ident := $"op".
Definition _opaque : ident := $"opaque".
Definition _os : ident := $"os".
Definition _out : ident := $"out".
Definition _reserved : ident := $"reserved".
Definition _sane : ident := $"sane".
Definition _start : ident := $"start".
Definition _state : ident := $"state".
Definition _strm : ident := $"strm".
Definition _text : ident := $"text".
Definition _time : ident := $"time".
Definition _total : ident := $"total".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
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
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
Definition _t'75 : ident := 202%positive.
Definition _t'76 : ident := 203%positive.
Definition _t'77 : ident := 204%positive.
Definition _t'78 : ident := 205%positive.
Definition _t'79 : ident := 206%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'80 : ident := 207%positive.
Definition _t'81 : ident := 208%positive.
Definition _t'82 : ident := 209%positive.
Definition _t'83 : ident := 210%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_inffast_2 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inffast_1 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inffast_3 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_inflate_fast := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_start, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_in, (tptr tuchar)) :: (_last, (tptr tuchar)) ::
               (_out, (tptr tuchar)) :: (_beg, (tptr tuchar)) ::
               (_end, (tptr tuchar)) :: (_wsize, tuint) :: (_whave, tuint) ::
               (_wnext, tuint) :: (_window, (tptr tuchar)) ::
               (_hold, tulong) :: (_bits, tuint) ::
               (_lcode, (tptr (Tstruct ___gp_code noattr))) ::
               (_dcode, (tptr (Tstruct ___gp_code noattr))) ::
               (_lmask, tuint) :: (_dmask, tuint) ::
               (_here, (tptr (Tstruct ___gp_code noattr))) :: (_op, tuint) ::
               (_len, tuint) :: (_dist, tuint) :: (_from, (tptr tuchar)) ::
               (_t'46, tlong) :: (_t'45, tlong) :: (_t'44, (tptr tuchar)) ::
               (_t'43, (tptr tuchar)) :: (_t'42, (tptr tuchar)) ::
               (_t'41, (tptr tuchar)) :: (_t'40, (tptr tuchar)) ::
               (_t'39, (tptr tuchar)) :: (_t'38, (tptr tuchar)) ::
               (_t'37, (tptr tuchar)) :: (_t'36, (tptr tuchar)) ::
               (_t'35, (tptr tuchar)) :: (_t'34, (tptr tuchar)) ::
               (_t'33, (tptr tuchar)) :: (_t'32, (tptr tuchar)) ::
               (_t'31, (tptr tuchar)) :: (_t'30, (tptr tuchar)) ::
               (_t'29, (tptr tuchar)) :: (_t'28, (tptr tuchar)) ::
               (_t'27, (tptr tuchar)) :: (_t'26, (tptr tuchar)) ::
               (_t'25, (tptr tuchar)) :: (_t'24, (tptr tuchar)) ::
               (_t'23, (tptr tuchar)) :: (_t'22, tuint) ::
               (_t'21, (tptr tuchar)) :: (_t'20, (tptr tuchar)) ::
               (_t'19, tuint) :: (_t'18, (tptr tuchar)) ::
               (_t'17, (tptr tuchar)) :: (_t'16, tuint) ::
               (_t'15, (tptr tuchar)) :: (_t'14, (tptr tuchar)) ::
               (_t'13, tuint) :: (_t'12, (tptr tuchar)) ::
               (_t'11, (tptr tuchar)) :: (_t'10, tint) ::
               (_t'9, (tptr tuchar)) :: (_t'8, (tptr tuchar)) ::
               (_t'7, (tptr tuchar)) :: (_t'6, (tptr tuchar)) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, (tptr tuchar)) ::
               (_t'2, (tptr tuchar)) :: (_t'1, tint) ::
               (_t'83, (tptr (Tstruct _internal_state noattr))) ::
               (_t'82, tuint) :: (_t'81, tuint) :: (_t'80, tuint) ::
               (_t'79, tuint) :: (_t'78, tuint) :: (_t'77, tuchar) ::
               (_t'76, tuchar) :: (_t'75, tuchar) :: (_t'74, tuchar) ::
               (_t'73, tushort) :: (_t'72, tushort) :: (_t'71, tushort) ::
               (_t'70, tuchar) :: (_t'69, tuchar) :: (_t'68, tuchar) ::
               (_t'67, tuchar) :: (_t'66, tuchar) :: (_t'65, tushort) ::
               (_t'64, tushort) :: (_t'63, tuchar) :: (_t'62, tuchar) ::
               (_t'61, tint) :: (_t'60, tuchar) :: (_t'59, tuchar) ::
               (_t'58, tuchar) :: (_t'57, tuchar) :: (_t'56, tuchar) ::
               (_t'55, tuchar) :: (_t'54, tuchar) :: (_t'53, tuchar) ::
               (_t'52, tuchar) :: (_t'51, tuchar) :: (_t'50, tuchar) ::
               (_t'49, tuchar) :: (_t'48, tuchar) :: (_t'47, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'83
      (Efield
        (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
          (Tstruct _z_stream_s noattr)) _state
        (tptr (Tstruct _internal_state noattr))))
    (Sset _state
      (Ecast (Etempvar _t'83 (tptr (Tstruct _internal_state noattr)))
        (tptr (Tstruct _inflate_state noattr)))))
  (Ssequence
    (Sset _in
      (Efield
        (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
          (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar)))
    (Ssequence
      (Ssequence
        (Sset _t'82
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _avail_in tuint))
        (Sset _last
          (Ebinop Oadd (Etempvar _in (tptr tuchar))
            (Ebinop Osub (Etempvar _t'82 tuint)
              (Econst_int (Int.repr 5) tint) tuint) (tptr tuchar))))
      (Ssequence
        (Sset _out
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _next_out (tptr tuchar)))
        (Ssequence
          (Ssequence
            (Sset _t'81
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _avail_out tuint))
            (Sset _beg
              (Ebinop Osub (Etempvar _out (tptr tuchar))
                (Ebinop Osub (Etempvar _start tuint) (Etempvar _t'81 tuint)
                  tuint) (tptr tuchar))))
          (Ssequence
            (Ssequence
              (Sset _t'80
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _avail_out tuint))
              (Sset _end
                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                  (Ebinop Osub (Etempvar _t'80 tuint)
                    (Econst_int (Int.repr 257) tint) tuint) (tptr tuchar))))
            (Ssequence
              (Sset _wsize
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wsize tuint))
              (Ssequence
                (Sset _whave
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _whave tuint))
                (Ssequence
                  (Sset _wnext
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wnext tuint))
                  (Ssequence
                    (Sset _window
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _window
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _hold
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _hold tulong))
                      (Ssequence
                        (Sset _bits
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _bits tuint))
                        (Ssequence
                          (Sset _lcode
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _lencode
                              (tptr (Tstruct ___gp_code noattr))))
                          (Ssequence
                            (Sset _dcode
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _distcode
                                (tptr (Tstruct ___gp_code noattr))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'79
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr))
                                    _lenbits tuint))
                                (Sset _lmask
                                  (Ebinop Osub
                                    (Ebinop Oshl
                                      (Econst_int (Int.repr 1) tuint)
                                      (Etempvar _t'79 tuint) tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'78
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _distbits tuint))
                                  (Sset _dmask
                                    (Ebinop Osub
                                      (Ebinop Oshl
                                        (Econst_int (Int.repr 1) tuint)
                                        (Etempvar _t'78 tuint) tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))
                                (Ssequence
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _bits tuint)
                                                     (Econst_int (Int.repr 15) tint)
                                                     tint)
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'2
                                                (Etempvar _in (tptr tuchar)))
                                              (Sset _in
                                                (Ebinop Oadd
                                                  (Etempvar _t'2 (tptr tuchar))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuchar))))
                                            (Ssequence
                                              (Sset _t'77
                                                (Ederef
                                                  (Etempvar _t'2 (tptr tuchar))
                                                  tuchar))
                                              (Sset _hold
                                                (Ebinop Oadd
                                                  (Etempvar _hold tulong)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _t'77 tuchar)
                                                      tulong)
                                                    (Etempvar _bits tuint)
                                                    tulong) tulong))))
                                          (Ssequence
                                            (Sset _bits
                                              (Ebinop Oadd
                                                (Etempvar _bits tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'3
                                                    (Etempvar _in (tptr tuchar)))
                                                  (Sset _in
                                                    (Ebinop Oadd
                                                      (Etempvar _t'3 (tptr tuchar))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'76
                                                    (Ederef
                                                      (Etempvar _t'3 (tptr tuchar))
                                                      tuchar))
                                                  (Sset _hold
                                                    (Ebinop Oadd
                                                      (Etempvar _hold tulong)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _t'76 tuchar)
                                                          tulong)
                                                        (Etempvar _bits tuint)
                                                        tulong) tulong))))
                                              (Sset _bits
                                                (Ebinop Oadd
                                                  (Etempvar _bits tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint)))))
                                        Sskip)
                                      (Ssequence
                                        (Sset _here
                                          (Ebinop Oadd
                                            (Etempvar _lcode (tptr (Tstruct ___gp_code noattr)))
                                            (Ebinop Oand
                                              (Etempvar _hold tulong)
                                              (Etempvar _lmask tuint) tulong)
                                            (tptr (Tstruct ___gp_code noattr))))
                                        (Ssequence
                                          (Sloop
                                            (Ssequence
                                              Sskip
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'75
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                        (Tstruct ___gp_code noattr))
                                                      _bits tuchar))
                                                  (Sset _op
                                                    (Ecast
                                                      (Etempvar _t'75 tuchar)
                                                      tuint)))
                                                (Ssequence
                                                  (Sset _hold
                                                    (Ebinop Oshr
                                                      (Etempvar _hold tulong)
                                                      (Etempvar _op tuint)
                                                      tulong))
                                                  (Ssequence
                                                    (Sset _bits
                                                      (Ebinop Osub
                                                        (Etempvar _bits tuint)
                                                        (Etempvar _op tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'74
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                              (Tstruct ___gp_code noattr))
                                                            _op tuchar))
                                                        (Sset _op
                                                          (Ecast
                                                            (Etempvar _t'74 tuchar)
                                                            tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _op tuint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Sset _t'4
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sset _t'4
                                                                (Ecast
                                                                  (Ebinop Oand
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                  tbool)))
                                                            (Sifthenelse (Etempvar _t'4 tint)
                                                              (Sset _t'5
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sset _t'5
                                                                (Ecast
                                                                  (Ebinop Oand
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tuint)
                                                                  tbool))))
                                                          (Sifthenelse (Etempvar _t'5 tint)
                                                            Sbreak
                                                            Sskip))
                                                        (Ssequence
                                                          (Sset _t'73
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                                (Tstruct ___gp_code noattr))
                                                              _val tushort))
                                                          (Sset _here
                                                            (Ebinop Oadd
                                                              (Ebinop Oadd
                                                                (Etempvar _lcode (tptr (Tstruct ___gp_code noattr)))
                                                                (Etempvar _t'73 tushort)
                                                                (tptr (Tstruct ___gp_code noattr)))
                                                              (Ebinop Oand
                                                                (Etempvar _hold tulong)
                                                                (Ebinop Osub
                                                                  (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)
                                                                tulong)
                                                              (tptr (Tstruct ___gp_code noattr)))))))))))
                                            Sskip)
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _op tuint)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'6
                                                  (Etempvar _out (tptr tuchar)))
                                                (Sset _out
                                                  (Ebinop Oadd
                                                    (Etempvar _t'6 (tptr tuchar))
                                                    (Econst_int (Int.repr 1) tint)
                                                    (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'72
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                      (Tstruct ___gp_code noattr))
                                                    _val tushort))
                                                (Sassign
                                                  (Ederef
                                                    (Etempvar _t'6 (tptr tuchar))
                                                    tuchar)
                                                  (Ecast
                                                    (Etempvar _t'72 tushort)
                                                    tuchar))))
                                            (Sifthenelse (Ebinop Oand
                                                           (Etempvar _op tuint)
                                                           (Econst_int (Int.repr 16) tint)
                                                           tuint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'71
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                        (Tstruct ___gp_code noattr))
                                                      _val tushort))
                                                  (Sset _len
                                                    (Ecast
                                                      (Etempvar _t'71 tushort)
                                                      tuint)))
                                                (Ssequence
                                                  (Sset _op
                                                    (Ebinop Oand
                                                      (Etempvar _op tuint)
                                                      (Econst_int (Int.repr 15) tint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sifthenelse (Etempvar _op tuint)
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _bits tuint)
                                                            (Etempvar _op tuint)
                                                            tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'7
                                                                  (Etempvar _in (tptr tuchar)))
                                                                (Sset _in
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'7 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                              (Ssequence
                                                                (Sset _t'70
                                                                  (Ederef
                                                                    (Etempvar _t'7 (tptr tuchar))
                                                                    tuchar))
                                                                (Sset _hold
                                                                  (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'70 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                            (Sset _bits
                                                              (Ebinop Oadd
                                                                (Etempvar _bits tuint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tuint)))
                                                          Sskip)
                                                        (Ssequence
                                                          (Sset _len
                                                            (Ebinop Oadd
                                                              (Etempvar _len tuint)
                                                              (Ebinop Oand
                                                                (Ecast
                                                                  (Etempvar _hold tulong)
                                                                  tuint)
                                                                (Ebinop Osub
                                                                  (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)
                                                                tuint) tuint))
                                                          (Ssequence
                                                            (Sset _hold
                                                              (Ebinop Oshr
                                                                (Etempvar _hold tulong)
                                                                (Etempvar _op tuint)
                                                                tulong))
                                                            (Sset _bits
                                                              (Ebinop Osub
                                                                (Etempvar _bits tuint)
                                                                (Etempvar _op tuint)
                                                                tuint)))))
                                                      Sskip)
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'8
                                                                (Etempvar _in (tptr tuchar)))
                                                              (Sset _in
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'8 (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'69
                                                                (Ederef
                                                                  (Etempvar _t'8 (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _hold
                                                                (Ebinop Oadd
                                                                  (Etempvar _hold tulong)
                                                                  (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'69 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                  tulong))))
                                                          (Ssequence
                                                            (Sset _bits
                                                              (Ebinop Oadd
                                                                (Etempvar _bits tuint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'9
                                                                    (Etempvar _in (tptr tuchar)))
                                                                  (Sset _in
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'9 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                (Ssequence
                                                                  (Sset _t'68
                                                                    (Ederef
                                                                    (Etempvar _t'9 (tptr tuchar))
                                                                    tuchar))
                                                                  (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'68 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                              (Sset _bits
                                                                (Ebinop Oadd
                                                                  (Etempvar _bits tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)))))
                                                        Sskip)
                                                      (Ssequence
                                                        (Sset _here
                                                          (Ebinop Oadd
                                                            (Etempvar _dcode (tptr (Tstruct ___gp_code noattr)))
                                                            (Ebinop Oand
                                                              (Etempvar _hold tulong)
                                                              (Etempvar _dmask tuint)
                                                              tulong)
                                                            (tptr (Tstruct ___gp_code noattr))))
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              Sskip
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'67
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                  (Sset _op
                                                                    (Ecast
                                                                    (Etempvar _t'67 tuchar)
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _op tuint)
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'66
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sset _op
                                                                    (Ecast
                                                                    (Etempvar _t'66 tuchar)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Sset _t'10
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'10
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tuint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'10 tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sset _t'65
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sset _here
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dcode (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _t'65 tushort)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tulong)
                                                                    (tptr (Tstruct ___gp_code noattr)))))))))))
                                                            Sskip)
                                                          (Sifthenelse 
                                                            (Ebinop Oand
                                                              (Etempvar _op tuint)
                                                              (Econst_int (Int.repr 16) tint)
                                                              tuint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'64
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _here (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                (Sset _dist
                                                                  (Ecast
                                                                    (Etempvar _t'64 tushort)
                                                                    tuint)))
                                                              (Ssequence
                                                                (Sset _op
                                                                  (Ebinop Oand
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Etempvar _op tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'11
                                                                    (Etempvar _in (tptr tuchar)))
                                                                    (Sset _in
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'11 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Ederef
                                                                    (Etempvar _t'11 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'63 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Etempvar _op tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Etempvar _in (tptr tuchar)))
                                                                    (Sset _in
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'12 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Ederef
                                                                    (Etempvar _t'12 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'62 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)))
                                                                    Sskip)))
                                                                    Sskip)
                                                                  (Ssequence
                                                                    (Sset _dist
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dist tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _op tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _op
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _beg (tptr tuchar))
                                                                    tlong)
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _dist tuint)
                                                                    (Etempvar _op tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _op
                                                                    (Ebinop Osub
                                                                    (Etempvar _dist tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _op tuint)
                                                                    (Etempvar _whave tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'61
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _sane
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'61 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inffast_3 (tarray tschar 30))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Etempvar _window (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _wnext tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _from (tptr tuchar))
                                                                    (Ebinop Osub
                                                                    (Etempvar _wsize tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                    (tptr tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuint)
                                                                    (Etempvar _len tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'14 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'15
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'15 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Ederef
                                                                    (Etempvar _t'15 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'14 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'60 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _op
                                                                    (Etempvar _t'13 tuint)))
                                                                    (Sifthenelse (Etempvar _t'13 tuint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Sset _from
                                                                    (Ebinop Osub
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _dist tuint)
                                                                    (tptr tuchar)))))
                                                                    Sskip))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _wnext tuint)
                                                                    (Etempvar _op tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _from (tptr tuchar))
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _wsize tuint)
                                                                    (Etempvar _wnext tuint)
                                                                    tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _op
                                                                    (Ebinop Osub
                                                                    (Etempvar _op tuint)
                                                                    (Etempvar _wnext tuint)
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuint)
                                                                    (Etempvar _len tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'17 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'18
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'18 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Ederef
                                                                    (Etempvar _t'18 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'17 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'59 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _op
                                                                    (Etempvar _t'16 tuint)))
                                                                    (Sifthenelse (Etempvar _t'16 tuint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Etempvar _window (tptr tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _wnext tuint)
                                                                    (Etempvar _len tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _op
                                                                    (Etempvar _wnext tuint))
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'20 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'21
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'21 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Ederef
                                                                    (Etempvar _t'21 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'20 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'58 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _op
                                                                    (Etempvar _t'19 tuint)))
                                                                    (Sifthenelse (Etempvar _t'19 tuint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Sset _from
                                                                    (Ebinop Osub
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _dist tuint)
                                                                    (tptr tuchar))))))
                                                                    Sskip))))
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _from (tptr tuchar))
                                                                    (Ebinop Osub
                                                                    (Etempvar _wnext tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint)
                                                                    (tptr tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuint)
                                                                    (Etempvar _len tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _op tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'23 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'24
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'24 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Ederef
                                                                    (Etempvar _t'24 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'23 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'57 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _op tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _op
                                                                    (Etempvar _t'22 tuint)))
                                                                    (Sifthenelse (Etempvar _t'22 tuint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Sset _from
                                                                    (Ebinop Osub
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _dist tuint)
                                                                    (tptr tuchar)))))
                                                                    Sskip))))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'25 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'26
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'26 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Ederef
                                                                    (Etempvar _t'26 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'25 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'56 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'27 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'28
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'28 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Ederef
                                                                    (Etempvar _t'28 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'27 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'55 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'29 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'30
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'30 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Ederef
                                                                    (Etempvar _t'30 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'29 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'54 tuchar))))
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint))))))
                                                                    (Sifthenelse (Etempvar _len tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'31 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'32
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'32 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Ederef
                                                                    (Etempvar _t'32 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'31 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'53 tuchar))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'33 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'34
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'34 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Ederef
                                                                    (Etempvar _t'34 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'33 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'52 tuchar))))
                                                                    Sskip))
                                                                    Sskip))))))
                                                                    (Ssequence
                                                                    (Sset _from
                                                                    (Ebinop Osub
                                                                    (Etempvar _out (tptr tuchar))
                                                                    (Etempvar _dist tuint)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'35 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'36
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'36 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Ederef
                                                                    (Etempvar _t'36 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'35 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'51 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'37 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'38
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'38 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Ederef
                                                                    (Etempvar _t'38 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'37 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'50 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'39 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'40
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Ederef
                                                                    (Etempvar _t'40 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'39 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'49 tuchar))))
                                                                    (Sset _len
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Sifthenelse (Etempvar _len tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'41 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'42
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'42 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Ederef
                                                                    (Etempvar _t'42 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'41 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'48 tuchar))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Etempvar _out (tptr tuchar)))
                                                                    (Sset _out
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'43 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'44
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Ederef
                                                                    (Etempvar _t'44 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'43 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'47 tuchar))))
                                                                    Sskip))
                                                                    Sskip)))))))))))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                  _msg
                                                                  (tptr tschar))
                                                                (Ecast
                                                                  (Evar ___stringlit_inffast_2 (tarray tschar 22))
                                                                  (tptr tschar)))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                  (Econst_int (Int.repr 16209) tint))
                                                                Sbreak)))))))))
                                              (Sifthenelse (Ebinop Oand
                                                             (Etempvar _op tuint)
                                                             (Econst_int (Int.repr 32) tint)
                                                             tuint)
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _mode tint)
                                                    (Econst_int (Int.repr 16191) tint))
                                                  Sbreak)
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                        (Tstruct _z_stream_s noattr))
                                                      _msg (tptr tschar))
                                                    (Ecast
                                                      (Evar ___stringlit_inffast_1 (tarray tschar 28))
                                                      (tptr tschar)))
                                                  (Ssequence
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _mode tint)
                                                      (Econst_int (Int.repr 16209) tint))
                                                    Sbreak))))))))
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _in (tptr tuchar))
                                                     (Etempvar _last (tptr tuchar))
                                                     tint)
                                        (Sset _t'1
                                          (Ecast
                                            (Ebinop Olt
                                              (Etempvar _out (tptr tuchar))
                                              (Etempvar _end (tptr tuchar))
                                              tint) tbool))
                                        (Sset _t'1
                                          (Econst_int (Int.repr 0) tint)))
                                      (Sifthenelse (Etempvar _t'1 tint)
                                        Sskip
                                        Sbreak)))
                                  (Ssequence
                                    (Sset _len
                                      (Ebinop Oshr (Etempvar _bits tuint)
                                        (Econst_int (Int.repr 3) tint) tuint))
                                    (Ssequence
                                      (Sset _in
                                        (Ebinop Osub
                                          (Etempvar _in (tptr tuchar))
                                          (Etempvar _len tuint)
                                          (tptr tuchar)))
                                      (Ssequence
                                        (Sset _bits
                                          (Ebinop Osub (Etempvar _bits tuint)
                                            (Ebinop Oshl
                                              (Etempvar _len tuint)
                                              (Econst_int (Int.repr 3) tint)
                                              tuint) tuint))
                                        (Ssequence
                                          (Sset _hold
                                            (Ebinop Oand
                                              (Etempvar _hold tulong)
                                              (Ebinop Osub
                                                (Ebinop Oshl
                                                  (Econst_int (Int.repr 1) tuint)
                                                  (Etempvar _bits tuint)
                                                  tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint) tulong))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                  (Tstruct _z_stream_s noattr))
                                                _next_in (tptr tuchar))
                                              (Etempvar _in (tptr tuchar)))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                    (Tstruct _z_stream_s noattr))
                                                  _next_out (tptr tuchar))
                                                (Etempvar _out (tptr tuchar)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Etempvar _in (tptr tuchar))
                                                                 (Etempvar _last (tptr tuchar))
                                                                 tint)
                                                    (Sset _t'45
                                                      (Ecast
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 5) tint)
                                                          (Ebinop Osub
                                                            (Etempvar _last (tptr tuchar))
                                                            (Etempvar _in (tptr tuchar))
                                                            tlong) tlong)
                                                        tlong))
                                                    (Sset _t'45
                                                      (Ecast
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 5) tint)
                                                          (Ebinop Osub
                                                            (Etempvar _in (tptr tuchar))
                                                            (Etempvar _last (tptr tuchar))
                                                            tlong) tlong)
                                                        tlong)))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                        (Tstruct _z_stream_s noattr))
                                                      _avail_in tuint)
                                                    (Ecast
                                                      (Etempvar _t'45 tlong)
                                                      tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _out (tptr tuchar))
                                                                   (Etempvar _end (tptr tuchar))
                                                                   tint)
                                                      (Sset _t'46
                                                        (Ecast
                                                          (Ebinop Oadd
                                                            (Econst_int (Int.repr 257) tint)
                                                            (Ebinop Osub
                                                              (Etempvar _end (tptr tuchar))
                                                              (Etempvar _out (tptr tuchar))
                                                              tlong) tlong)
                                                          tlong))
                                                      (Sset _t'46
                                                        (Ecast
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 257) tint)
                                                            (Ebinop Osub
                                                              (Etempvar _out (tptr tuchar))
                                                              (Etempvar _end (tptr tuchar))
                                                              tlong) tlong)
                                                          tlong)))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                          (Tstruct _z_stream_s noattr))
                                                        _avail_out tuint)
                                                      (Ecast
                                                        (Etempvar _t'46 tlong)
                                                        tuint)))
                                                  (Ssequence
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _hold tulong)
                                                      (Etempvar _hold tulong))
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _bits tuint)
                                                        (Etempvar _bits tuint))
                                                      (Sreturn None))))))))))))))))))))))))))))
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
     cc_default)) :: (___stringlit_inffast_2, Gvar v___stringlit_inffast_2) ::
 (___stringlit_inffast_1, Gvar v___stringlit_inffast_1) ::
 (___stringlit_inffast_3, Gvar v___stringlit_inffast_3) ::
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
 (_inflate_fast, Gfun(Internal f_inflate_fast)) :: nil).

Definition public_idents : list ident :=
(_inflate_fast :: ___builtin_debug :: ___builtin_write32_reversed ::
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



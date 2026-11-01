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
  Definition source_file := "harness/x_inflate_dict.c".
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
Definition ___stringlit_x_inflate_dict_1 : ident := $"__stringlit_x_inflate_dict_1".
Definition _a : ident := $"a".
Definition _adler : ident := $"adler".
Definition _ain : ident := $"ain".
Definition _aout : ident := $"aout".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _b : ident := $"b".
Definition _bad : ident := $"bad".
Definition _blen : ident := $"blen".
Definition _btype : ident := $"btype".
Definition _buf : ident := $"buf".
Definition _bw : ident := $"bw".
Definition _bw_align : ident := $"bw_align".
Definition _bw_bit : ident := $"bw_bit".
Definition _bw_bits : ident := $"bw_bits".
Definition _bw_byte : ident := $"bw_byte".
Definition _bw_code : ident := $"bw_code".
Definition _bw_fixed : ident := $"bw_fixed".
Definition _bw_fixed_match : ident := $"bw_fixed_match".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_same : ident := $"bytes_same".
Definition _c : ident := $"c".
Definition _cmf : ident := $"cmf".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _data_type : ident := $"data_type".
Definition _dict : ident := $"dict".
Definition _dict_set : ident := $"dict_set".
Definition _dictid : ident := $"dictid".
Definition _dist : ident := $"dist".
Definition _dist_code : ident := $"dist_code".
Definition _dl : ident := $"dl".
Definition _dlen : ident := $"dlen".
Definition _exact_copy : ident := $"exact_copy".
Definition _exact_space : ident := $"exact_space".
Definition _flevel : ident := $"flevel".
Definition _flg : ident := $"flg".
Definition _flg0 : ident := $"flg0".
Definition _flush : ident := $"flush".
Definition _gd : ident := $"gd".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _have : ident := $"have".
Definition _hist : ident := $"hist".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _ib : ident := $"ib".
Definition _inflate : ident := $"inflate".
Definition _inflateEnd : ident := $"inflateEnd".
Definition _inflateGetDictionary : ident := $"inflateGetDictionary".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _inflateSetDictionary : ident := $"inflateSetDictionary".
Definition _internal_state : ident := $"internal_state".
Definition _isel : ident := $"isel".
Definition _iw : ident := $"iw".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _kind : ident := $"kind".
Definition _last : ident := $"last".
Definition _len : ident := $"len".
Definition _len__1 : ident := $"len__1".
Definition _len_code : ident := $"len_code".
Definition _lim : ident := $"lim".
Definition _lit : ident := $"lit".
Definition _made : ident := $"made".
Definition _main : ident := $"main".
Definition _maxd : ident := $"maxd".
Definition _more : ident := $"more".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _nb : ident := $"nb".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _ob : ident := $"ob".
Definition _opaque : ident := $"opaque".
Definition _opos : ident := $"opos".
Definition _osnap : ident := $"osnap".
Definition _p : ident := $"p".
Definition _pos : ident := $"pos".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _ref_adler32 : ident := $"ref_adler32".
Definition _x_inflate_dict__ref_dbase : ident := $"x_inflate_dict__ref_dbase".
Definition _x_inflate_dict__ref_dext : ident := $"x_inflate_dict__ref_dext".
Definition _x_inflate_dict__ref_lbase : ident := $"x_inflate_dict__ref_lbase".
Definition _x_inflate_dict__ref_lext : ident := $"x_inflate_dict__ref_lext".
Definition _reserved : ident := $"reserved".
Definition _s : ident := $"s".
Definition _s1 : ident := $"s1".
Definition _s2 : ident := $"s2".
Definition _slen : ident := $"slen".
Definition _snap : ident := $"snap".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _step : ident := $"step".
Definition _stream_defaults : ident := $"stream_defaults".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _v : ident := $"v".
Definition _w : ident := $"w".
Definition _wb : ident := $"wb".
Definition _wrap : ident := $"wrap".
Definition _wsel : ident := $"wsel".
Definition _z_stream_s : ident := $"z_stream_s".
Definition _zalloc : ident := $"zalloc".
Definition _zfree : ident := $"zfree".
Definition _zlib : ident := $"zlib".
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
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_x_inflate_dict_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_ref_adler32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, tulong) :: (_buf, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_s1, tulong) :: (_s2, tulong) :: (_i, tulong) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _s1
    (Ebinop Oand (Etempvar _a tulong) (Econst_int (Int.repr 65535) tint)
      tulong))
  (Ssequence
    (Sset _s2
      (Ebinop Oand
        (Ebinop Oshr (Etempvar _a tulong) (Econst_int (Int.repr 16) tint)
          tulong) (Econst_int (Int.repr 65535) tint) tulong))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _n tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                      (Etempvar _i tulong) (tptr tuchar)) tuchar))
                (Sset _s1
                  (Ebinop Omod
                    (Ebinop Oadd (Etempvar _s1 tulong) (Etempvar _t'1 tuchar)
                      tulong) (Econst_long (Int64.repr 65521) tulong) tulong)))
              (Sset _s2
                (Ebinop Omod
                  (Ebinop Oadd (Etempvar _s2 tulong) (Etempvar _s1 tulong)
                    tulong) (Econst_long (Int64.repr 65521) tulong) tulong))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Sreturn (Some (Ebinop Oor
                       (Ebinop Oshl (Etempvar _s2 tulong)
                         (Econst_int (Int.repr 16) tint) tulong)
                       (Etempvar _s1 tulong) tulong))))))
|}.

Definition f_bytes_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
                  (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_bytes_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_s, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar) (Etempvar _t'1 tuchar))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_exact_copy := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr tuchar)) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _p (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Etempvar _p (tptr tuchar)) :: (Etempvar _src (tptr tuchar)) ::
         (Etempvar _n tuint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tuchar))))))
|}.

Definition f_exact_space := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: (_snap, (tptr (tptr tuchar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_q, (tptr tuchar)) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default)) ((Etempvar _n tuint) :: nil))
      (Sset _q (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tuchar))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sset _t'3 (Econst_int (Int.repr 1) tint))
          (Sset _t'3
            (Ecast
              (Ebinop Oeq (Etempvar _q (tptr tuchar))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              tbool)))
        (Sifthenelse (Etempvar _t'3 tint)
          (Ssequence
            (Scall None
              (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                       cc_default))
              ((Etempvar _p (tptr tuchar)) :: nil))
            (Ssequence
              (Scall None
                (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                         cc_default))
                ((Etempvar _q (tptr tuchar)) :: nil))
              (Ssequence
                (Sassign
                  (Ederef (Etempvar _snap (tptr (tptr tuchar)))
                    (tptr tuchar))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)))))))
          Sskip))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Etempvar _p (tptr tuchar)) :: (Etempvar _n tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Etempvar _q (tptr tuchar)) :: (Etempvar _p (tptr tuchar)) ::
             (Etempvar _n tuint) :: nil))
          (Ssequence
            (Sassign
              (Ederef (Etempvar _snap (tptr (tptr tuchar))) (tptr tuchar))
              (Etempvar _q (tptr tuchar)))
            (Sreturn (Some (Etempvar _p (tptr tuchar))))))))))
|}.

Definition f_stream_defaults := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
        (Tstruct _z_stream_s noattr)) _zalloc
      (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil) (tptr tvoid)
              cc_default))) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
          (Tstruct _z_stream_s noattr)) _zfree
        (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                cc_default))) (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar))
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _avail_in tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _next_out (tptr tuchar))
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _avail_out tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Scall None
                  (Evar _nondet_bytes (Tfunction
                                        ((tptr tuchar) :: tulong :: nil)
                                        tvoid cc_default))
                  ((Ecast
                     (Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                           (Tstruct _z_stream_s noattr)) _total_in tulong)
                       (tptr tulong)) (tptr tuchar)) ::
                   (Esizeof tulong tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _nondet_bytes (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                    ((Ecast
                       (Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                             (Tstruct _z_stream_s noattr)) _total_out tulong)
                         (tptr tulong)) (tptr tuchar)) ::
                     (Esizeof tulong tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _nondet_bytes (Tfunction
                                            ((tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                      ((Ecast
                         (Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                               (Tstruct _z_stream_s noattr)) _adler tulong)
                           (tptr tulong)) (tptr tuchar)) ::
                       (Esizeof tulong tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Ecast
                           (Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                 (Tstruct _z_stream_s noattr)) _data_type
                               tint) (tptr tint)) (tptr tuchar)) ::
                         (Esizeof tint tulong) :: nil))
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Ecast
                           (Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                 (Tstruct _z_stream_s noattr)) _reserved
                               tulong) (tptr tulong)) (tptr tuchar)) ::
                         (Esizeof tulong tulong) :: nil)))))))))))))
|}.

Definition f_bw_bit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_b, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'12, tuint) :: (_t'11, (tptr tuchar)) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuchar) :: (_t'7, tuint) ::
               (_t'6, (tptr tuchar)) :: (_t'5, tuint) ::
               (_t'4, (tptr tuchar)) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'10
      (Efield
        (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
          (Tstruct _bw noattr)) _nb tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _buf (tptr tuchar)))
        (Ssequence
          (Sset _t'12
            (Efield
              (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                (Tstruct _bw noattr)) _len tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'11 (tptr tuchar))
                (Etempvar _t'12 tuint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 0) tint))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
            (Tstruct _bw noattr)) _buf (tptr tuchar)))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _len tuint))
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                (Tstruct _bw noattr)) _buf (tptr tuchar)))
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                  (Tstruct _bw noattr)) _len tuint))
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd (Etempvar _t'6 (tptr tuchar))
                    (Etempvar _t'7 tuint) (tptr tuchar)) tuchar))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                      (Tstruct _bw noattr)) _nb tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'4 (tptr tuchar))
                      (Etempvar _t'5 tuint) (tptr tuchar)) tuchar)
                  (Ecast
                    (Ebinop Oor (Etempvar _t'8 tuchar)
                      (Ebinop Oshl
                        (Ebinop Oand (Etempvar _b tuint)
                          (Econst_int (Int.repr 1) tint) tuint)
                        (Etempvar _t'9 tuint) tuint) tuint) tuchar))))))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _nb tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _nb tuint)
          (Ebinop Oadd (Etempvar _t'3 tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _nb tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                       (Econst_int (Int.repr 8) tint) tint)
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                  (Tstruct _bw noattr)) _nb tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                    (Tstruct _bw noattr)) _len tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
                    (Tstruct _bw noattr)) _len tuint)
                (Ebinop Oadd (Etempvar _t'2 tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          Sskip)))))
|}.

Definition f_bw_bits := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_v, tuint) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint) tint)
        Sskip
        Sbreak)
      (Scall None
        (Evar _bw_bit (Tfunction
                        ((tptr (Tstruct _bw noattr)) :: tuint :: nil) tvoid
                        cc_default))
        ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
         (Ebinop Oshr (Etempvar _v tuint) (Etempvar _i tuint) tuint) :: nil)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_bw_code := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_c, tuint) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Etempvar _n tuint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _i tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Scall None
        (Evar _bw_bit (Tfunction
                        ((tptr (Tstruct _bw noattr)) :: tuint :: nil) tvoid
                        cc_default))
        ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
         (Ebinop Oshr (Etempvar _c tuint)
           (Ebinop Osub (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
             tuint) tuint) :: nil)))
    (Sset _i
      (Ebinop Osub (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_bw_byte := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_b, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, (tptr tuchar)) :: (_t'1, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
          (Tstruct _bw noattr)) _buf (tptr tuchar)))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
            (Tstruct _bw noattr)) _len tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _t'2 (tptr tuchar)) (Etempvar _t'3 tuint)
            (tptr tuchar)) tuchar) (Etempvar _b tuchar))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
          (Tstruct _bw noattr)) _len tuint))
    (Sassign
      (Efield
        (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
          (Tstruct _bw noattr)) _len tuint)
      (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
        tuint))))
|}.

Definition f_bw_align := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _w (tptr (Tstruct _bw noattr))) (Tstruct _bw noattr))
      _nb tuint))
  (Sifthenelse (Ebinop One (Etempvar _t'1 tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
            (Tstruct _bw noattr)) _nb tuint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _len tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _bw noattr)))
              (Tstruct _bw noattr)) _len tuint)
          (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    Sskip))
|}.

Definition f_bw_fixed := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Olt (Etempvar _v tuint) (Econst_int (Int.repr 144) tint)
               tint)
  (Scall None
    (Evar _bw_code (Tfunction
                     ((tptr (Tstruct _bw noattr)) :: tuint :: tuint :: nil)
                     tvoid cc_default))
    ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
     (Ebinop Oadd (Econst_int (Int.repr 48) tint) (Etempvar _v tuint) tuint) ::
     (Econst_int (Int.repr 8) tint) :: nil))
  (Sifthenelse (Ebinop Olt (Etempvar _v tuint)
                 (Econst_int (Int.repr 256) tint) tint)
    (Scall None
      (Evar _bw_code (Tfunction
                       ((tptr (Tstruct _bw noattr)) :: tuint :: tuint :: nil)
                       tvoid cc_default))
      ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
       (Ebinop Oadd (Econst_int (Int.repr 400) tint)
         (Ebinop Osub (Etempvar _v tuint) (Econst_int (Int.repr 144) tint)
           tuint) tuint) :: (Econst_int (Int.repr 9) tint) :: nil))
    (Sifthenelse (Ebinop Olt (Etempvar _v tuint)
                   (Econst_int (Int.repr 280) tint) tint)
      (Scall None
        (Evar _bw_code (Tfunction
                         ((tptr (Tstruct _bw noattr)) :: tuint :: tuint ::
                          nil) tvoid cc_default))
        ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
         (Ebinop Osub (Etempvar _v tuint) (Econst_int (Int.repr 256) tint)
           tuint) :: (Econst_int (Int.repr 7) tint) :: nil))
      (Scall None
        (Evar _bw_code (Tfunction
                         ((tptr (Tstruct _bw noattr)) :: tuint :: tuint ::
                          nil) tvoid cc_default))
        ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
         (Ebinop Oadd (Econst_int (Int.repr 192) tint)
           (Ebinop Osub (Etempvar _v tuint) (Econst_int (Int.repr 280) tint)
             tuint) tuint) :: (Econst_int (Int.repr 8) tint) :: nil)))))
|}.

Definition v_x_inflate_dict__ref_lbase := {|
  gvar_info := (tarray tushort 29);
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
                Init_int16 (Int.repr 258) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_inflate_dict__ref_lext := {|
  gvar_info := (tarray tuchar 29);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_inflate_dict__ref_dbase := {|
  gvar_info := (tarray tushort 30);
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
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_inflate_dict__ref_dext := {|
  gvar_info := (tarray tuchar 30);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 1) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_len_code := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, tint) :: (_t'2, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 28) tint))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _len tuint)
                   (Econst_int (Int.repr 258) tint) tint)
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt
                             (Ebinop Oadd (Etempvar _i tuint)
                               (Econst_int (Int.repr 1) tint) tuint)
                             (Econst_int (Int.repr 28) tint) tint)
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Evar _x_inflate_dict__ref_lbase (tarray tushort 29))
                        (Ebinop Oadd (Etempvar _i tuint)
                          (Econst_int (Int.repr 1) tint) tuint)
                        (tptr tushort)) tushort))
                  (Sset _t'1
                    (Ecast
                      (Ebinop Ole (Etempvar _t'2 tushort)
                        (Etempvar _len tuint) tint) tbool)))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint)))
          Sskip))
      Sskip)
    (Sreturn (Some (Etempvar _i tuint)))))
|}.

Definition f_dist_code := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_dist, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tuint) :: (_t'1, tint) :: (_t'2, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _j (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Olt
                         (Ebinop Oadd (Etempvar _j tuint)
                           (Econst_int (Int.repr 1) tint) tuint)
                         (Econst_int (Int.repr 30) tint) tint)
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _x_inflate_dict__ref_dbase (tarray tushort 30))
                    (Ebinop Oadd (Etempvar _j tuint)
                      (Econst_int (Int.repr 1) tint) tuint) (tptr tushort))
                  tushort))
              (Sset _t'1
                (Ecast
                  (Ebinop Ole (Etempvar _t'2 tushort) (Etempvar _dist tuint)
                    tint) tbool)))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      Sskip)
    (Sreturn (Some (Etempvar _j tuint)))))
|}.

Definition f_bw_fixed_match := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_w, (tptr (Tstruct _bw noattr))) :: (_len, tuint) ::
                (_dist, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_j, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'6, tuchar) :: (_t'5, tushort) ::
               (_t'4, tuchar) :: (_t'3, tushort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _len_code (Tfunction (tuint :: nil) tuint cc_default))
      ((Etempvar _len tuint) :: nil))
    (Sset _i (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _dist_code (Tfunction (tuint :: nil) tuint cc_default))
        ((Etempvar _dist tuint) :: nil))
      (Sset _j (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall None
        (Evar _bw_fixed (Tfunction
                          ((tptr (Tstruct _bw noattr)) :: tuint :: nil) tvoid
                          cc_default))
        ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
         (Ebinop Oadd (Econst_int (Int.repr 257) tint) (Etempvar _i tuint)
           tuint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Evar _x_inflate_dict__ref_lbase (tarray tushort 29))
                (Etempvar _i tuint) (tptr tushort)) tushort))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Evar _x_inflate_dict__ref_lext (tarray tuchar 29))
                  (Etempvar _i tuint) (tptr tuchar)) tuchar))
            (Scall None
              (Evar _bw_bits (Tfunction
                               ((tptr (Tstruct _bw noattr)) :: tuint ::
                                tuint :: nil) tvoid cc_default))
              ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
               (Ebinop Osub (Etempvar _len tuint) (Etempvar _t'5 tushort)
                 tuint) :: (Etempvar _t'6 tuchar) :: nil))))
        (Ssequence
          (Scall None
            (Evar _bw_code (Tfunction
                             ((tptr (Tstruct _bw noattr)) :: tuint ::
                              tuint :: nil) tvoid cc_default))
            ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
             (Etempvar _j tuint) :: (Econst_int (Int.repr 5) tint) :: nil))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Evar _x_inflate_dict__ref_dbase (tarray tushort 30))
                  (Etempvar _j tuint) (tptr tushort)) tushort))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Evar _x_inflate_dict__ref_dext (tarray tuchar 30))
                    (Etempvar _j tuint) (tptr tuchar)) tuchar))
              (Scall None
                (Evar _bw_bits (Tfunction
                                 ((tptr (Tstruct _bw noattr)) :: tuint ::
                                  tuint :: nil) tvoid cc_default))
                ((Etempvar _w (tptr (Tstruct _bw noattr))) ::
                 (Ebinop Osub (Etempvar _dist tuint) (Etempvar _t'3 tushort)
                   tuint) :: (Etempvar _t'4 tuchar) :: nil)))))))))
|}.

Definition f_hist := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_dict, (tptr tuchar)) :: (_dlen, tuint) ::
                (_data, (tptr tuchar)) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _k tuint) (Etempvar _dlen tuint) tint)
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _dict (tptr tuchar)) (Etempvar _k tuint)
            (tptr tuchar)) tuchar))
      (Sset _t'1 (Ecast (Etempvar _t'3 tuchar) tint)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _data (tptr tuchar))
            (Ebinop Osub (Etempvar _k tuint) (Etempvar _dlen tuint) tuint)
            (tptr tuchar)) tuchar))
      (Sset _t'1 (Ecast (Etempvar _t'2 tuchar) tint))))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_w, (Tstruct _bw noattr)) ::
              (_s, (Tstruct _z_stream_s noattr)) ::
              (_osnap, (tptr tuchar)) :: (_dl, tuint) :: nil);
  fn_temps := ((_wrap, tuchar) :: (_flevel, tuchar) :: (_isel, tuchar) ::
               (_wsel, tuchar) :: (_wb, tuint) :: (_dlen, tuint) ::
               (_zlib, tint) :: (_dict, (tptr tuchar)) ::
               (_bad, (tptr tuchar)) :: (_data, (tptr tuchar)) ::
               (_src, (tptr tuchar)) :: (_blen, tuint) ::
               (_dictid, tulong) :: (_maxd, tuint) :: (_cmf, tuint) ::
               (_flg0, tuint) :: (_flg, tuint) :: (_n, tuint) ::
               (_more, tuchar) :: (_btype, tuchar) :: (_last, tuint) ::
               (_len, tuint) :: (_kind, tuchar) :: (_lit, tuchar) ::
               (_len__1, tuint) :: (_dist, tuint) :: (_i, tuint) ::
               (_a, tulong) :: (_slen, tuint) :: (_iw, tint) :: (_r, tint) ::
               (_dict_set, tint) :: (_pos, tuint) :: (_lim, tuint) ::
               (_opos, tuint) :: (_step, tuint) :: (_aout, tuint) ::
               (_flush, tint) :: (_ain, tuint) :: (_ib, (tptr tuchar)) ::
               (_ob, (tptr tuchar)) :: (_made, tuint) :: (_have, tulong) ::
               (_gd, (tptr tuchar)) :: (_i__1, tuint) :: (_t'54, tint) ::
               (_t'53, tuchar) :: (_t'52, tint) :: (_t'51, (tptr tvoid)) ::
               (_t'50, tulong) :: (_t'49, tint) :: (_t'48, tint) ::
               (_t'47, tint) :: (_t'46, tint) :: (_t'45, tint) ::
               (_t'44, tint) :: (_t'43, tint) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tint) :: (_t'39, (tptr tuchar)) ::
               (_t'38, (tptr tuchar)) :: (_t'37, tuint) :: (_t'36, tuint) ::
               (_t'35, tuint) :: (_t'34, tuint) :: (_t'33, tint) ::
               (_t'32, tint) :: (_t'31, tint) :: (_t'30, tulong) ::
               (_t'29, tuchar) :: (_t'28, tint) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tint) :: (_t'24, tuint) ::
               (_t'23, tuint) :: (_t'22, tuchar) :: (_t'21, tuchar) ::
               (_t'20, tuint) :: (_t'19, tuchar) :: (_t'18, tuchar) ::
               (_t'17, tulong) :: (_t'16, tuint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, (tptr tvoid)) ::
               (_t'11, (tptr tvoid)) :: (_t'10, (tptr tvoid)) ::
               (_t'9, tuint) :: (_t'8, (tptr tvoid)) :: (_t'7, tint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tuchar) ::
               (_t'70, tuchar) :: (_t'69, tuint) :: (_t'68, tuint) ::
               (_t'67, tuint) :: (_t'66, tuint) :: (_t'65, tuint) ::
               (_t'64, tuint) :: (_t'63, tuint) :: (_t'62, tuint) ::
               (_t'61, tulong) :: (_t'60, tuint) :: (_t'59, tuint) ::
               (_t'58, tuint) :: (_t'57, tuint) :: (_t'56, tuchar) ::
               (_t'55, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
        nil)
      (Sset _wrap (Ecast (Etempvar _t'1 tuchar) tuchar)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
        (Sset _flevel (Ecast (Etempvar _t'2 tuchar) tuchar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
          (Sset _isel (Ecast (Etempvar _t'3 tuchar) tuchar)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
            (Sset _wsel (Ecast (Etempvar _t'4 tuchar) tuchar)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
              (Sset _wb (Etempvar _t'5 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
                (Sset _dlen (Etempvar _t'6 tuint)))
              (Ssequence
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _wb tuint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    (Sset _t'7
                      (Ecast
                        (Ebinop Ole (Etempvar _wb tuint)
                          (Econst_int (Int.repr 15) tint) tint) tbool))
                    (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                  (Scall None
                    (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                       cc_default))
                    ((Etempvar _t'7 tint) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                       cc_default))
                    ((Ebinop Ole (Etempvar _dlen tuint)
                       (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                         (Econst_int (Int.repr 16) tint) tuint) tint) :: nil))
                  (Ssequence
                    (Sset _zlib
                      (Ebinop One (Etempvar _wrap tuchar)
                        (Econst_int (Int.repr 0) tint) tint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'8)
                          (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                     (tptr tvoid) cc_default))
                          ((Etempvar _dlen tuint) :: nil))
                        (Sset _dict (Etempvar _t'8 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq (Etempvar _dlen tuint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Sset _t'9
                                (Ecast (Econst_int (Int.repr 1) tint) tuint))
                              (Sset _t'9
                                (Ecast (Etempvar _dlen tuint) tuint)))
                            (Scall (Some _t'10)
                              (Evar _quickproof_malloc (Tfunction
                                                         (tulong :: nil)
                                                         (tptr tvoid)
                                                         cc_default))
                              ((Etempvar _t'9 tuint) :: nil)))
                          (Sset _bad (Etempvar _t'10 (tptr tvoid))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _quickproof_malloc (Tfunction
                                                         (tulong :: nil)
                                                         (tptr tvoid)
                                                         cc_default))
                              ((Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                 (Econst_int (Int.repr 18) tint) tuint) ::
                               nil))
                            (Sset _data (Etempvar _t'11 (tptr tvoid))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _quickproof_malloc (Tfunction
                                                           (tulong :: nil)
                                                           (tptr tvoid)
                                                           cc_default))
                                ((Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                   (Econst_int (Int.repr 19) tint) tuint) ::
                                 nil))
                              (Sset _src (Etempvar _t'12 (tptr tvoid))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _dict (tptr tuchar))
                                                   (Ecast
                                                     (Econst_int (Int.repr 0) tint)
                                                     (tptr tvoid)) tint)
                                      (Sset _t'13
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _t'13
                                        (Ecast
                                          (Ebinop Oeq
                                            (Etempvar _bad (tptr tuchar))
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tvoid)) tint) tbool)))
                                    (Sifthenelse (Etempvar _t'13 tint)
                                      (Sset _t'14
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _t'14
                                        (Ecast
                                          (Ebinop Oeq
                                            (Etempvar _data (tptr tuchar))
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr tvoid)) tint) tbool))))
                                  (Sifthenelse (Etempvar _t'14 tint)
                                    (Sset _t'15
                                      (Econst_int (Int.repr 1) tint))
                                    (Sset _t'15
                                      (Ecast
                                        (Ebinop Oeq
                                          (Etempvar _src (tptr tuchar))
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tvoid)) tint) tbool))))
                                (Sifthenelse (Etempvar _t'15 tint)
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                  Sskip))
                              (Ssequence
                                (Scall None
                                  (Evar _nondet_bytes (Tfunction
                                                        ((tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                  ((Etempvar _dict (tptr tuchar)) ::
                                   (Etempvar _dlen tuint) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _dlen tuint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sset _t'16
                                        (Ecast (Econst_int (Int.repr 1) tint)
                                          tuint))
                                      (Sset _t'16
                                        (Ecast (Etempvar _dlen tuint) tuint)))
                                    (Sset _blen (Etempvar _t'16 tuint)))
                                  (Ssequence
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _dlen tuint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _bad (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Scall None
                                          (Evar _bytes_copy (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                          ((Etempvar _bad (tptr tuchar)) ::
                                           (Etempvar _dict (tptr tuchar)) ::
                                           (Etempvar _dlen tuint) :: nil))
                                        (Ssequence
                                          (Sset _t'70
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _dict (tptr tuchar))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuchar)) tuchar))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _bad (tptr tuchar))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ebinop Oxor
                                                (Etempvar _t'70 tuchar)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) tuchar)))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'17)
                                          (Evar _ref_adler32 (Tfunction
                                                               (tulong ::
                                                                (tptr tuchar) ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                          ((Econst_int (Int.repr 1) tint) ::
                                           (Etempvar _dict (tptr tuchar)) ::
                                           (Etempvar _dlen tuint) :: nil))
                                        (Sset _dictid
                                          (Etempvar _t'17 tulong)))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Evar _w (Tstruct _bw noattr))
                                            _buf (tptr tuchar))
                                          (Etempvar _src (tptr tuchar)))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Evar _w (Tstruct _bw noattr))
                                              _len tuint)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Evar _w (Tstruct _bw noattr))
                                                _nb tuint)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Sset _maxd
                                                (Ebinop Oshl
                                                  (Econst_int (Int.repr 1) tuint)
                                                  (Etempvar _wb tuint) tuint))
                                              (Ssequence
                                                (Sifthenelse (Etempvar _zlib tint)
                                                  (Ssequence
                                                    (Sset _cmf
                                                      (Ebinop Oor
                                                        (Ebinop Oshl
                                                          (Ebinop Osub
                                                            (Etempvar _wb tuint)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 4) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _flg0
                                                        (Ebinop Oor
                                                          (Ebinop Oshl
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _flevel tuchar)
                                                                (Econst_int (Int.repr 3) tint)
                                                                tint) tuint)
                                                            (Econst_int (Int.repr 6) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 32) tint)
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _flg
                                                          (Ebinop Oadd
                                                            (Etempvar _flg0 tuint)
                                                            (Ebinop Omod
                                                              (Ebinop Osub
                                                                (Econst_int (Int.repr 31) tint)
                                                                (Ebinop Omod
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oshl
                                                                    (Etempvar _cmf tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Etempvar _flg0 tuint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 31) tint)
                                                                  tuint)
                                                                tuint)
                                                              (Econst_int (Int.repr 31) tint)
                                                              tuint) tuint))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _bw_byte 
                                                            (Tfunction
                                                              ((tptr (Tstruct _bw noattr)) ::
                                                               tuchar :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Eaddrof
                                                               (Evar _w (Tstruct _bw noattr))
                                                               (tptr (Tstruct _bw noattr))) ::
                                                             (Ecast
                                                               (Etempvar _cmf tuint)
                                                               tuchar) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _bw_byte 
                                                              (Tfunction
                                                                ((tptr (Tstruct _bw noattr)) ::
                                                                 tuchar ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Eaddrof
                                                                 (Evar _w (Tstruct _bw noattr))
                                                                 (tptr (Tstruct _bw noattr))) ::
                                                               (Ecast
                                                                 (Etempvar _flg tuint)
                                                                 tuchar) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _bw_byte 
                                                                (Tfunction
                                                                  ((tptr (Tstruct _bw noattr)) ::
                                                                   tuchar ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Eaddrof
                                                                   (Evar _w (Tstruct _bw noattr))
                                                                   (tptr (Tstruct _bw noattr))) ::
                                                                 (Ecast
                                                                   (Ebinop Oshr
                                                                    (Etempvar _dictid tulong)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tulong)
                                                                   tuchar) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _bw_byte 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                   (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _dictid tulong)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tulong)
                                                                    tuchar) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _dictid tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    tuchar) ::
                                                                    nil))
                                                                  (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _dictid tulong)
                                                                    tuchar) ::
                                                                    nil))))))))))
                                                  Sskip)
                                                (Ssequence
                                                  (Sset _n
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Ssequence
                                                    (Sloop
                                                      (Ssequence
                                                        Sskip
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'18)
                                                              (Evar _nondet_u8 
                                                              (Tfunction nil
                                                                tuchar
                                                                cc_default))
                                                              nil)
                                                            (Sset _more
                                                              (Ecast
                                                                (Etempvar _t'18 tuchar)
                                                                tuchar)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'19)
                                                                (Evar _nondet_u8 
                                                                (Tfunction
                                                                  nil tuchar
                                                                  cc_default))
                                                                nil)
                                                              (Sset _btype
                                                                (Ecast
                                                                  (Etempvar _t'19 tuchar)
                                                                  tuchar)))
                                                            (Ssequence
                                                              (Sset _last
                                                                (Ebinop Oeq
                                                                  (Etempvar _more tuchar)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'69
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint))
                                                                  (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'69 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil)))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _bw_bits 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Etempvar _last tuint) ::
                                                                    (Econst_int (Int.repr 1) tint) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _btype tuchar)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'20)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _len
                                                                    (Etempvar _t'20 tuint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 65535) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _len tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_bits 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_align 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'68
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'68 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)
                                                                    (Etempvar _len tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _len tuint)
                                                                    tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Eunop Onotint
                                                                    (Etempvar _len tuint)
                                                                    tuint)
                                                                    tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Eunop Onotint
                                                                    (Etempvar _len tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuchar) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _nondet_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _n tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _len tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'67
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _t'67 tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _n tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _len tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'66
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'66 tuint)
                                                                    (Etempvar _len tuint)
                                                                    tuint)))
                                                                    (Sset _n
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _len tuint)
                                                                    tuint)))))))))))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_bits 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Econst_int (Int.repr 1) tint) ::
                                                                    (Econst_int (Int.repr 2) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'21)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _kind
                                                                    (Ecast
                                                                    (Etempvar _t'21 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'65
                                                                    (Efield
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'65 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _kind tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _kind tuchar)
                                                                    (Econst_int (Int.repr 128) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _lit
                                                                    (Ecast
                                                                    (Etempvar _t'22 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Olt
                                                                    (Etempvar _n tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _n tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _lit tuchar))
                                                                    (Ssequence
                                                                    (Sset _n
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bw_fixed 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Etempvar _lit tuchar) ::
                                                                    nil))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'23)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _len__1
                                                                    (Etempvar _t'23 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _dist
                                                                    (Etempvar _t'24 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _len__1 tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    (Sset _t'25
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'25
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len__1 tuint)
                                                                    (Econst_int (Int.repr 258) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'25 tint)
                                                                    (Sset _t'26
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'26
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _dist tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sifthenelse (Etempvar _t'26 tint)
                                                                    (Sset _t'27
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _dist tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dlen tuint)
                                                                    (Etempvar _n tuint)
                                                                    tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sifthenelse (Etempvar _t'27 tint)
                                                                    (Sset _t'28
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _dist tuint)
                                                                    (Etempvar _maxd tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sifthenelse (Etempvar _t'28 tint)
                                                                    Scontinue
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _len__1 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tuint)
                                                                    (Etempvar _len__1 tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall (Some _t'29)
                                                                    (Evar _hist 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dlen tuint) ::
                                                                    (Etempvar _data (tptr tuchar)) ::
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Etempvar _dlen tuint)
                                                                    (Etempvar _n tuint)
                                                                    tuint)
                                                                    (Etempvar _i tuint)
                                                                    tuint)
                                                                    (Etempvar _dist tuint)
                                                                    tuint) ::
                                                                    nil))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _i tuint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'29 tuchar))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Sset _n
                                                                    (Ebinop Oadd
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _len__1 tuint)
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _bw_fixed_match 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Etempvar _len__1 tuint) ::
                                                                    (Etempvar _dist tuint) ::
                                                                    nil)))))))))))))
                                                                    Sskip)
                                                                    (Scall None
                                                                    (Evar _bw_fixed 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Econst_int (Int.repr 256) tint) ::
                                                                    nil)))))
                                                                    (Sifthenelse (Etempvar _last tuint)
                                                                    Sbreak
                                                                    Sskip))))))))
                                                      Sskip)
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _bw_align 
                                                        (Tfunction
                                                          ((tptr (Tstruct _bw noattr)) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _w (Tstruct _bw noattr))
                                                           (tptr (Tstruct _bw noattr))) ::
                                                         nil))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'64
                                                            (Efield
                                                              (Evar _w (Tstruct _bw noattr))
                                                              _len tuint))
                                                          (Scall None
                                                            (Evar _gp_assume 
                                                            (Tfunction
                                                              (tint :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Ebinop Ole
                                                               (Ebinop Oadd
                                                                 (Etempvar _t'64 tuint)
                                                                 (Econst_int (Int.repr 4) tint)
                                                                 tuint)
                                                               (Ebinop Oshl
                                                                 (Econst_int (Int.repr 1) tuint)
                                                                 (Econst_int (Int.repr 19) tint)
                                                                 tuint) tint) ::
                                                             nil)))
                                                        (Ssequence
                                                          (Sifthenelse (Etempvar _zlib tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'30)
                                                                  (Evar _ref_adler32 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Econst_int (Int.repr 1) tint) ::
                                                                   (Etempvar _data (tptr tuchar)) ::
                                                                   (Etempvar _n tuint) ::
                                                                   nil))
                                                                (Sset _a
                                                                  (Etempvar _t'30 tulong)))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _bw_byte 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                   (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _a tulong)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tulong)
                                                                    tuchar) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _a tulong)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tulong)
                                                                    tuchar) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Ebinop Oshr
                                                                    (Etempvar _a tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    tuchar) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _bw_byte 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _bw noattr)) ::
                                                                    tuchar ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _w (Tstruct _bw noattr))
                                                                    (tptr (Tstruct _bw noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _a tulong)
                                                                    tuchar) ::
                                                                    nil))))))
                                                            Sskip)
                                                          (Ssequence
                                                            (Sset _slen
                                                              (Efield
                                                                (Evar _w (Tstruct _bw noattr))
                                                                _len tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Eunop Onotbool
                                                                    (Etempvar _zlib tint)
                                                                    tint)
                                                                  (Sset _t'31
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Ecast
                                                                    (Etempvar _wb tuint)
                                                                    tint)
                                                                    tint)
                                                                    tint))
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _isel tuchar)
                                                                    (Econst_int (Int.repr 85) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _wb tuint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _isel tuchar)
                                                                    (Econst_int (Int.repr 170) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tint)))
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Ecast
                                                                    (Etempvar _wb tuint)
                                                                    tint)
                                                                    tint)
                                                                    tint))
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tint)))
                                                                    (Sset _t'31
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tint))))))
                                                                (Sset _iw
                                                                  (Etempvar _t'31 tint)))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _stream_defaults 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'32)
                                                                    (Evar _inflateInit2_ 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    (tptr tschar) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _iw tint) ::
                                                                    (Evar ___stringlit_x_inflate_dict_1 (tarray tschar 6)) ::
                                                                    (Ecast
                                                                    (Esizeof (Tstruct _z_stream_s noattr) tulong)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'32 tint)))
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _dict_set
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _zlib tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'33)
                                                                    (Evar _inflateSetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dlen tuint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'33 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sset _dict_set
                                                                    (Econst_int (Int.repr 1) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _pos
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _lim
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _opos
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'34)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _step
                                                                    (Etempvar _t'34 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'35)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _aout
                                                                    (Etempvar _t'35 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'36)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _flush
                                                                    (Ecast
                                                                    (Etempvar _t'36 tuint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _aout tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 20) tint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _step tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _slen tuint)
                                                                    (Etempvar _lim tuint)
                                                                    tuint)
                                                                    tint)
                                                                    (Sset _t'37
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _lim tuint)
                                                                    (Etempvar _step tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _t'37
                                                                    (Ecast
                                                                    (Etempvar _slen tuint)
                                                                    tuint)))
                                                                    (Sset _lim
                                                                    (Etempvar _t'37 tuint)))
                                                                    (Ssequence
                                                                    (Sset _ain
                                                                    (Ebinop Osub
                                                                    (Etempvar _lim tuint)
                                                                    (Etempvar _pos tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'38)
                                                                    (Evar _exact_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    (tptr tuchar)
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ain tuint) ::
                                                                    nil))
                                                                    (Sset _ib
                                                                    (Etempvar _t'38 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'39)
                                                                    (Evar _exact_space 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    (tptr (tptr tuchar)) ::
                                                                    nil)
                                                                    (tptr tuchar)
                                                                    cc_default))
                                                                    ((Etempvar _aout tuint) ::
                                                                    (Eaddrof
                                                                    (Evar _osnap (tptr tuchar))
                                                                    (tptr (tptr tuchar))) ::
                                                                    nil))
                                                                    (Sset _ob
                                                                    (Etempvar _t'39 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'40
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'40
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'40 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar))
                                                                    (Etempvar _ib (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint)
                                                                    (Etempvar _ain tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar))
                                                                    (Etempvar _ob (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint)
                                                                    (Etempvar _aout tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'41)
                                                                    (Evar _inflate 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _flush tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'41 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Sset _made
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _t'63 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sset _pos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pos tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _ain tuint)
                                                                    (Etempvar _t'62 tuint)
                                                                    tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _zlib tint)
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _dict_set tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'42
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'42 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _made tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _opos tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'43
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'43 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'61
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _adler
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'61 tulong)
                                                                    (Etempvar _dictid tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _wsel tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'44)
                                                                    (Evar _inflateSetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _bad (tptr tuchar)) ::
                                                                    (Etempvar _blen tuint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'44 tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'45)
                                                                    (Evar _inflateSetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dlen tuint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'45 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sset _dict_set
                                                                    (Econst_int (Int.repr 1) tint)))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'46
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'46 tint)
                                                                    (Sset _t'47
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'47
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'47 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _made tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _n tuint)
                                                                    (Etempvar _opos tuint)
                                                                    tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'48)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _ob (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _data (tptr tuchar))
                                                                    (Etempvar _opos tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _made tuint) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'48 tint) ::
                                                                    nil)))
                                                                    (Sset _opos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _opos tuint)
                                                                    (Etempvar _made tuint)
                                                                    tuint))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _dict_set tint)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'54
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _zlib tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'54
                                                                    (Ecast
                                                                    (Etempvar _t'54 tint)
                                                                    tbool))))
                                                                    (Sset _t'54
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'54 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _dl tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'49)
                                                                    (Evar _inflateGetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuint) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Eaddrof
                                                                    (Evar _dl tuint)
                                                                    (tptr tuint)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'49 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Etempvar _dlen tuint)
                                                                    tulong)
                                                                    (Etempvar _opos tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _have tulong)
                                                                    (Etempvar _maxd tuint)
                                                                    tint)
                                                                    (Sset _t'50
                                                                    (Ecast
                                                                    (Etempvar _have tulong)
                                                                    tulong))
                                                                    (Sset _t'50
                                                                    (Ecast
                                                                    (Etempvar _maxd tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Evar _dl tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'60 tuint)
                                                                    (Etempvar _t'50 tulong)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Evar _dl tuint))
                                                                    (Scall (Some _t'51)
                                                                    (Evar _quickproof_malloc 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _t'59 tuint) ::
                                                                    nil)))
                                                                    (Sset _gd
                                                                    (Etempvar _t'51 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _gd (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'52)
                                                                    (Evar _inflateGetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuint) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _gd (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'52 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i__1
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Evar _dl tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i__1 tuint)
                                                                    (Etempvar _t'58 tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Evar _dl tuint))
                                                                    (Scall (Some _t'53)
                                                                    (Evar _hist 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                                    ((Etempvar _dict (tptr tuchar)) ::
                                                                    (Etempvar _dlen tuint) ::
                                                                    (Etempvar _data (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tulong)
                                                                    (Etempvar _t'57 tuint)
                                                                    tulong)
                                                                    tuint)
                                                                    (Etempvar _i__1 tuint)
                                                                    tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _gd (tptr tuchar))
                                                                    (Etempvar _i__1 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'56 tuchar)
                                                                    (Etempvar _t'53 tuchar)
                                                                    tint) ::
                                                                    nil)))))
                                                                    (Sset _i__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i__1 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _gd (tptr tuchar)) ::
                                                                    nil))))))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ib (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ob (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'55 (tptr tuchar)) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip))))))))))))))))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _opos tuint)
                                                                    (Etempvar _n tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _slen tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _inflateEnd 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
 Composite _bw Struct
   (Member_plain _buf (tptr tuchar) :: Member_plain _len tuint ::
    Member_plain _nb tuint :: nil)
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
     cc_default)) :: (___stringlit_x_inflate_dict_1, Gvar v___stringlit_x_inflate_dict_1) ::
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
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_gp_assume,
   Gfun(External (EF_external "gp_assume"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_inflate,
   Gfun(External (EF_external "inflate"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_inflateEnd,
   Gfun(External (EF_external "inflateEnd"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_inflateSetDictionary,
   Gfun(External (EF_external "inflateSetDictionary"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: (tptr tuchar) :: tuint :: nil)
     tint cc_default)) ::
 (_inflateGetDictionary,
   Gfun(External (EF_external "inflateGetDictionary"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: (tptr tuchar) :: (tptr tuint) ::
      nil) tint cc_default)) ::
 (_inflateInit2_,
   Gfun(External (EF_external "inflateInit2_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: (tptr tschar) :: tint ::
      nil) tint cc_default)) ::
 (_ref_adler32, Gfun(Internal f_ref_adler32)) ::
 (_bytes_same, Gfun(Internal f_bytes_same)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_exact_copy, Gfun(Internal f_exact_copy)) ::
 (_exact_space, Gfun(Internal f_exact_space)) ::
 (_stream_defaults, Gfun(Internal f_stream_defaults)) ::
 (_bw_bit, Gfun(Internal f_bw_bit)) ::
 (_bw_bits, Gfun(Internal f_bw_bits)) ::
 (_bw_code, Gfun(Internal f_bw_code)) ::
 (_bw_byte, Gfun(Internal f_bw_byte)) ::
 (_bw_align, Gfun(Internal f_bw_align)) ::
 (_bw_fixed, Gfun(Internal f_bw_fixed)) :: (_x_inflate_dict__ref_lbase, Gvar v_x_inflate_dict__ref_lbase) ::
 (_x_inflate_dict__ref_lext, Gvar v_x_inflate_dict__ref_lext) :: (_x_inflate_dict__ref_dbase, Gvar v_x_inflate_dict__ref_dbase) ::
 (_x_inflate_dict__ref_dext, Gvar v_x_inflate_dict__ref_dext) :: (_len_code, Gfun(Internal f_len_code)) ::
 (_dist_code, Gfun(Internal f_dist_code)) ::
 (_bw_fixed_match, Gfun(Internal f_bw_fixed_match)) ::
 (_hist, Gfun(Internal f_hist)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _inflateInit2_ :: _inflateGetDictionary :: _inflateSetDictionary ::
 _inflateEnd :: _inflate :: _gp_assume :: _gp_assert :: _nondet_bytes ::
 _nondet_u32 :: _nondet_u8 :: _quickproof_free :: _quickproof_malloc ::
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



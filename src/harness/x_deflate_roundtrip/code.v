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
  Definition source_file := "harness/x_deflate_roundtrip.c".
  Definition normalized := true.
End Info.

Definition _R : ident := $"R".
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
Definition ___stringlit_x_deflate_roundtrip_1 : ident := $"__stringlit_x_deflate_roundtrip_1".
Definition _a : ident := $"a".
Definition _adler : ident := $"adler".
Definition _ain : ident := $"ain".
Definition _aout : ident := $"aout".
Definition _api : ident := $"api".
Definition _api_ok : ident := $"api_ok".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_same : ident := $"bytes_same".
Definition _cf : ident := $"cf".
Definition _cl : ident := $"cl".
Definition _clen : ident := $"clen".
Definition _comm_max : ident := $"comm_max".
Definition _comment : ident := $"comment".
Definition _comp : ident := $"comp".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _data_type : ident := $"data_type".
Definition _deflate : ident := $"deflate".
Definition _deflateEnd : ident := $"deflateEnd".
Definition _deflateInit2_ : ident := $"deflateInit2_".
Definition _deflateParams : ident := $"deflateParams".
Definition _deflateSetDictionary : ident := $"deflateSetDictionary".
Definition _deflateSetHeader : ident := $"deflateSetHeader".
Definition _deflateTune : ident := $"deflateTune".
Definition _deflate_params_ok : ident := $"deflate_params_ok".
Definition _deflate_run : ident := $"deflate_run".
Definition _dict : ident := $"dict".
Definition _dict_set : ident := $"dict_set".
Definition _dlen : ident := $"dlen".
Definition _done : ident := $"done".
Definition _draw_nonzero_bytes : ident := $"draw_nonzero_bytes".
Definition _drun : ident := $"drun".
Definition _dsel : ident := $"dsel".
Definition _ended : ident := $"ended".
Definition _exact_copy : ident := $"exact_copy".
Definition _exact_space : ident := $"exact_space".
Definition _extra : ident := $"extra".
Definition _extra_len : ident := $"extra_len".
Definition _extra_max : ident := $"extra_max".
Definition _finishing : ident := $"finishing".
Definition _flush : ident := $"flush".
Definition _fsel : ident := $"fsel".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _gz_header_s : ident := $"gz_header_s".
Definition _h : ident := $"h".
Definition _hcrc : ident := $"hcrc".
Definition _head_set : ident := $"head_set".
Definition _hsel : ident := $"hsel".
Definition _i : ident := $"i".
Definition _ib : ident := $"ib".
Definition _ih : ident := $"ih".
Definition _inflate : ident := $"inflate".
Definition _inflateEnd : ident := $"inflateEnd".
Definition _inflateGetHeader : ident := $"inflateGetHeader".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _inflateSetDictionary : ident := $"inflateSetDictionary".
Definition _init : ident := $"init".
Definition _internal_state : ident := $"internal_state".
Definition _iw : ident := $"iw".
Definition _level : ident := $"level".
Definition _lim : ident := $"lim".
Definition _made : ident := $"made".
Definition _main : ident := $"main".
Definition _mem : ident := $"mem".
Definition _method : ident := $"method".
Definition _msel : ident := $"msel".
Definition _msg : ident := $"msg".
Definition _mtime : ident := $"mtime".
Definition _mval : ident := $"mval".
Definition _n : ident := $"n".
Definition _name : ident := $"name".
Definition _name_max : ident := $"name_max".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nf : ident := $"nf".
Definition _nf_ : ident := $"nf_".
Definition _nl : ident := $"nl".
Definition _nlim : ident := $"nlim".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _ob : ident := $"ob".
Definition _opaque : ident := $"opaque".
Definition _os : ident := $"os".
Definition _osnap : ident := $"osnap".
Definition _p : ident := $"p".
Definition _params : ident := $"params".
Definition _plev : ident := $"plev".
Definition _pok : ident := $"pok".
Definition _pos : ident := $"pos".
Definition _psel : ident := $"psel".
Definition _pstrat : ident := $"pstrat".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _ref_adler32 : ident := $"ref_adler32".
Definition _reserved : ident := $"reserved".
Definition _s : ident := $"s".
Definition _s1 : ident := $"s1".
Definition _s2 : ident := $"s2".
Definition _snap : ident := $"snap".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _strategy : ident := $"strategy".
Definition _stream_defaults : ident := $"stream_defaults".
Definition _t : ident := $"t".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _t3 : ident := $"t3".
Definition _t4 : ident := $"t4".
Definition _text : ident := $"text".
Definition _time : ident := $"time".
Definition _tin : ident := $"tin".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _tout : ident := $"tout".
Definition _tsel : ident := $"tsel".
Definition _used : ident := $"used".
Definition _wb : ident := $"wb".
Definition _wbits : ident := $"wbits".
Definition _wrap : ident := $"wrap".
Definition _xf : ident := $"xf".
Definition _xflags : ident := $"xflags".
Definition _xlen : ident := $"xlen".
Definition _z_stream_s : ident := $"z_stream_s".
Definition _zalloc : ident := $"zalloc".
Definition _zfree : ident := $"zfree".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'100 : ident := 227%positive.
Definition _t'101 : ident := 228%positive.
Definition _t'102 : ident := 229%positive.
Definition _t'103 : ident := 230%positive.
Definition _t'104 : ident := 231%positive.
Definition _t'105 : ident := 232%positive.
Definition _t'106 : ident := 233%positive.
Definition _t'107 : ident := 234%positive.
Definition _t'108 : ident := 235%positive.
Definition _t'109 : ident := 236%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'110 : ident := 237%positive.
Definition _t'111 : ident := 238%positive.
Definition _t'112 : ident := 239%positive.
Definition _t'113 : ident := 240%positive.
Definition _t'114 : ident := 241%positive.
Definition _t'115 : ident := 242%positive.
Definition _t'116 : ident := 243%positive.
Definition _t'117 : ident := 244%positive.
Definition _t'118 : ident := 245%positive.
Definition _t'119 : ident := 246%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'120 : ident := 247%positive.
Definition _t'121 : ident := 248%positive.
Definition _t'122 : ident := 249%positive.
Definition _t'123 : ident := 250%positive.
Definition _t'124 : ident := 251%positive.
Definition _t'125 : ident := 252%positive.
Definition _t'126 : ident := 253%positive.
Definition _t'127 : ident := 254%positive.
Definition _t'128 : ident := 255%positive.
Definition _t'129 : ident := 256%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'130 : ident := 257%positive.
Definition _t'131 : ident := 258%positive.
Definition _t'132 : ident := 259%positive.
Definition _t'133 : ident := 260%positive.
Definition _t'134 : ident := 261%positive.
Definition _t'135 : ident := 262%positive.
Definition _t'136 : ident := 263%positive.
Definition _t'137 : ident := 264%positive.
Definition _t'138 : ident := 265%positive.
Definition _t'139 : ident := 266%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'140 : ident := 267%positive.
Definition _t'141 : ident := 268%positive.
Definition _t'142 : ident := 269%positive.
Definition _t'143 : ident := 270%positive.
Definition _t'144 : ident := 271%positive.
Definition _t'145 : ident := 272%positive.
Definition _t'146 : ident := 273%positive.
Definition _t'147 : ident := 274%positive.
Definition _t'148 : ident := 275%positive.
Definition _t'149 : ident := 276%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'150 : ident := 277%positive.
Definition _t'151 : ident := 278%positive.
Definition _t'152 : ident := 279%positive.
Definition _t'153 : ident := 280%positive.
Definition _t'154 : ident := 281%positive.
Definition _t'155 : ident := 282%positive.
Definition _t'156 : ident := 283%positive.
Definition _t'157 : ident := 284%positive.
Definition _t'158 : ident := 285%positive.
Definition _t'159 : ident := 286%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'160 : ident := 287%positive.
Definition _t'161 : ident := 288%positive.
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
Definition _t'84 : ident := 211%positive.
Definition _t'85 : ident := 212%positive.
Definition _t'86 : ident := 213%positive.
Definition _t'87 : ident := 214%positive.
Definition _t'88 : ident := 215%positive.
Definition _t'89 : ident := 216%positive.
Definition _t'9 : ident := 136%positive.
Definition _t'90 : ident := 217%positive.
Definition _t'91 : ident := 218%positive.
Definition _t'92 : ident := 219%positive.
Definition _t'93 : ident := 220%positive.
Definition _t'94 : ident := 221%positive.
Definition _t'95 : ident := 222%positive.
Definition _t'96 : ident := 223%positive.
Definition _t'97 : ident := 224%positive.
Definition _t'98 : ident := 225%positive.
Definition _t'99 : ident := 226%positive.

Definition v___stringlit_x_deflate_roundtrip_1 := {|
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

Definition f_deflate_params_ok := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_level, tint) :: (_method, tint) :: (_wbits, tint) ::
                (_mem, tint) :: (_strategy, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_wrap, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _wrap (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _level tint)
                   (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
      (Sset _level (Econst_int (Int.repr 6) tint))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _wbits tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _wbits tint)
                         (Eunop Oneg (Econst_int (Int.repr 15) tint) tint)
                         tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)
          (Ssequence
            (Sset _wrap (Econst_int (Int.repr 0) tint))
            (Sset _wbits (Eunop Oneg (Etempvar _wbits tint) tint))))
        (Sifthenelse (Ebinop Ogt (Etempvar _wbits tint)
                       (Econst_int (Int.repr 15) tint) tint)
          (Ssequence
            (Sset _wrap (Econst_int (Int.repr 2) tint))
            (Sset _wbits
              (Ebinop Osub (Etempvar _wbits tint)
                (Econst_int (Int.repr 16) tint) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _mem tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Sset _t'1
                            (Ecast
                              (Ebinop Ole (Etempvar _mem tint)
                                (Econst_int (Int.repr 9) tint) tint) tbool))
                          (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                        (Sifthenelse (Etempvar _t'1 tint)
                          (Sset _t'2
                            (Ecast
                              (Ebinop Oeq (Etempvar _method tint)
                                (Econst_int (Int.repr 8) tint) tint) tbool))
                          (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'2 tint)
                        (Sset _t'3
                          (Ecast
                            (Ebinop Oge (Etempvar _wbits tint)
                              (Econst_int (Int.repr 8) tint) tint) tbool))
                        (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'3 tint)
                      (Sset _t'4
                        (Ecast
                          (Ebinop Ole (Etempvar _wbits tint)
                            (Econst_int (Int.repr 15) tint) tint) tbool))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'4 tint)
                    (Sset _t'5
                      (Ecast
                        (Ebinop Oge (Etempvar _level tint)
                          (Econst_int (Int.repr 0) tint) tint) tbool))
                    (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'5 tint)
                  (Sset _t'6
                    (Ecast
                      (Ebinop Ole (Etempvar _level tint)
                        (Econst_int (Int.repr 9) tint) tint) tbool))
                  (Sset _t'6 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'6 tint)
                (Sset _t'7
                  (Ecast
                    (Ebinop Oge (Etempvar _strategy tint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'7 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'7 tint)
              (Sset _t'8
                (Ecast
                  (Ebinop Ole (Etempvar _strategy tint)
                    (Econst_int (Int.repr 4) tint) tint) tbool))
              (Sset _t'8 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'8 tint)
            (Sifthenelse (Ebinop One (Etempvar _wbits tint)
                           (Econst_int (Int.repr 8) tint) tint)
              (Sset _t'9 (Ecast (Econst_int (Int.repr 1) tint) tbool))
              (Ssequence
                (Sset _t'9
                  (Ecast
                    (Ebinop Oeq (Etempvar _wrap tint)
                      (Econst_int (Int.repr 1) tint) tint) tbool))
                (Sset _t'9 (Ecast (Etempvar _t'9 tint) tbool))))
            (Sset _t'9 (Econst_int (Int.repr 0) tint))))
        (Sreturn (Some (Etempvar _t'9 tint)))))))
|}.

Definition f_draw_nonzero_bytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_buf, (tptr tuchar)) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                          cc_default))
    ((Etempvar _buf (tptr tuchar)) :: (Etempvar _n tuint) :: nil))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _buf (tptr tuchar)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar))
          (Scall None
            (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
            ((Ebinop One (Etempvar _t'1 tuchar)
               (Econst_int (Int.repr 0) tint) tint) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_deflate_run := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_R, (tptr (Tstruct _drun noattr))) ::
                (_s, (tptr (Tstruct _z_stream_s noattr))) :: (_api, tint) ::
                nil);
  fn_vars := ((_osnap, (tptr tuchar)) :: nil);
  fn_temps := ((_mval, tint) :: (_t1, tint) :: (_t2, tint) :: (_t3, tint) ::
               (_t4, tint) :: (_mtime, tulong) :: (_msel, tuchar) ::
               (_tsel, tuchar) :: (_dsel, tuchar) :: (_hsel, tuchar) ::
               (_text, tuchar) :: (_os, tuchar) :: (_hcrc, tuchar) ::
               (_r, tint) :: (_pos, tuint) :: (_lim, tuint) ::
               (_finishing, tint) :: (_nlim, tuint) :: (_aout, tuint) ::
               (_fsel, tint) :: (_plev, tint) :: (_pstrat, tint) ::
               (_psel, tuchar) :: (_flush, tint) :: (_ain, tuint) ::
               (_ib, (tptr tuchar)) :: (_ob, (tptr tuchar)) ::
               (_tin, tulong) :: (_tout, tulong) :: (_params, tint) ::
               (_used, tuint) :: (_made, tuint) :: (_pok, tint) ::
               (_t'80, tint) :: (_t'79, tint) :: (_t'78, tint) ::
               (_t'77, tint) :: (_t'76, tint) :: (_t'75, tint) ::
               (_t'74, tint) :: (_t'73, tint) :: (_t'72, tint) ::
               (_t'71, tint) :: (_t'70, tint) :: (_t'69, tint) ::
               (_t'68, tint) :: (_t'67, tint) :: (_t'66, tint) ::
               (_t'65, tint) :: (_t'64, tint) :: (_t'63, tint) ::
               (_t'62, tint) :: (_t'61, tint) :: (_t'60, (tptr tuchar)) ::
               (_t'59, (tptr tuchar)) :: (_t'58, tint) :: (_t'57, tint) ::
               (_t'56, tint) :: (_t'55, tuchar) :: (_t'54, tuint) ::
               (_t'53, tuint) :: (_t'52, tuint) :: (_t'51, tuint) ::
               (_t'50, tuint) :: (_t'49, tint) :: (_t'48, tint) ::
               (_t'47, tint) :: (_t'46, tint) :: (_t'45, tint) ::
               (_t'44, tint) :: (_t'43, tint) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tint) :: (_t'39, tint) ::
               (_t'38, tint) :: (_t'37, tint) :: (_t'36, tint) ::
               (_t'35, tint) :: (_t'34, tint) :: (_t'33, tint) ::
               (_t'32, (tptr tvoid)) :: (_t'31, (tptr tvoid)) ::
               (_t'30, (tptr tvoid)) :: (_t'29, (tptr tvoid)) ::
               (_t'28, (tptr tvoid)) :: (_t'27, (tptr tvoid)) ::
               (_t'26, tint) :: (_t'25, tint) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tuchar) :: (_t'21, tuchar) ::
               (_t'20, tuchar) :: (_t'19, tuchar) :: (_t'18, tuchar) ::
               (_t'17, tuchar) :: (_t'16, tuchar) :: (_t'15, tuint) ::
               (_t'14, tuint) :: (_t'13, tuint) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: (_t'161, tuint) ::
               (_t'160, tuint) :: (_t'159, tuint) :: (_t'158, tuint) ::
               (_t'157, tuint) :: (_t'156, tuint) :: (_t'155, tuint) ::
               (_t'154, tuint) :: (_t'153, tuint) :: (_t'152, tuint) ::
               (_t'151, (tptr tuchar)) :: (_t'150, (tptr tuchar)) ::
               (_t'149, (tptr tuchar)) :: (_t'148, (tptr tuchar)) ::
               (_t'147, (tptr tuchar)) :: (_t'146, (tptr tuchar)) ::
               (_t'145, tuint) :: (_t'144, (tptr tuchar)) ::
               (_t'143, tuint) :: (_t'142, (tptr tuchar)) ::
               (_t'141, tuint) :: (_t'140, (tptr tuchar)) ::
               (_t'139, tuint) :: (_t'138, (tptr tuchar)) ::
               (_t'137, tuint) :: (_t'136, (tptr tuchar)) ::
               (_t'135, tuint) :: (_t'134, (tptr tuchar)) ::
               (_t'133, tuint) :: (_t'132, (tptr tuchar)) ::
               (_t'131, tuint) :: (_t'130, tint) :: (_t'129, tint) ::
               (_t'128, tint) :: (_t'127, tint) :: (_t'126, tint) ::
               (_t'125, tint) :: (_t'124, tint) :: (_t'123, tint) ::
               (_t'122, tint) :: (_t'121, tint) :: (_t'120, tint) ::
               (_t'119, tint) :: (_t'118, tint) :: (_t'117, tint) ::
               (_t'116, tint) :: (_t'115, tint) :: (_t'114, tint) ::
               (_t'113, tint) :: (_t'112, tint) :: (_t'111, tint) ::
               (_t'110, tint) :: (_t'109, tint) :: (_t'108, tuint) ::
               (_t'107, (tptr tuchar)) :: (_t'106, tint) ::
               (_t'105, tuint) :: (_t'104, (tptr tuchar)) ::
               (_t'103, tuint) :: (_t'102, (tptr tuchar)) ::
               (_t'101, (tptr tuchar)) :: (_t'100, tint) ::
               (_t'99, tulong) :: (_t'98, tuint) :: (_t'97, (tptr tuchar)) ::
               (_t'96, tuint) :: (_t'95, tuint) :: (_t'94, tuint) ::
               (_t'93, tuint) :: (_t'92, (tptr tuchar)) ::
               (_t'91, (tptr tuchar)) :: (_t'90, tulong) ::
               (_t'89, tulong) :: (_t'88, (tptr tuchar)) ::
               (_t'87, (tptr tuchar)) :: (_t'86, tuint) :: (_t'85, tuint) ::
               (_t'84, tulong) :: (_t'83, (tptr tuchar)) ::
               (_t'82, tulong) :: (_t'81, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sassign
      (Efield
        (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
          (Tstruct _drun noattr)) _level tint)
      (Ecast (Etempvar _t'1 tuint) tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sset _mval (Ecast (Etempvar _t'2 tuint) tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sassign
          (Efield
            (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
              (Tstruct _drun noattr)) _wbits tint)
          (Ecast (Etempvar _t'3 tuint) tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
          (Sassign
            (Efield
              (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
                (Tstruct _drun noattr)) _mem tint)
            (Ecast (Etempvar _t'4 tuint) tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sassign
              (Efield
                (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
                  (Tstruct _drun noattr)) _strategy tint)
              (Ecast (Etempvar _t'5 tuint) tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
              (Sassign
                (Efield
                  (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
                    (Tstruct _drun noattr)) _n tuint) (Etempvar _t'6 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
                (Sassign
                  (Efield
                    (Ederef (Etempvar _R (tptr (Tstruct _drun noattr)))
                      (Tstruct _drun noattr)) _dlen tuint)
                  (Etempvar _t'7 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
                  (Sset _t1 (Ecast (Etempvar _t'8 tuint) tint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'9)
                      (Evar _nondet_u32 (Tfunction nil tuint cc_default))
                      nil)
                    (Sset _t2 (Ecast (Etempvar _t'9 tuint) tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'10)
                        (Evar _nondet_u32 (Tfunction nil tuint cc_default))
                        nil)
                      (Sset _t3 (Ecast (Etempvar _t'10 tuint) tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'11)
                          (Evar _nondet_u32 (Tfunction nil tuint cc_default))
                          nil)
                        (Sset _t4 (Ecast (Etempvar _t'11 tuint) tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'12)
                            (Evar _nondet_u32 (Tfunction nil tuint
                                                cc_default)) nil)
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _R (tptr (Tstruct _drun noattr)))
                                (Tstruct _drun noattr)) _xlen tuint)
                            (Etempvar _t'12 tuint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'13)
                              (Evar _nondet_u32 (Tfunction nil tuint
                                                  cc_default)) nil)
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _R (tptr (Tstruct _drun noattr)))
                                  (Tstruct _drun noattr)) _nl tuint)
                              (Etempvar _t'13 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'14)
                                (Evar _nondet_u32 (Tfunction nil tuint
                                                    cc_default)) nil)
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                    (Tstruct _drun noattr)) _cl tuint)
                                (Etempvar _t'14 tuint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'15)
                                  (Evar _nondet_u32 (Tfunction nil tuint
                                                      cc_default)) nil)
                                (Sset _mtime
                                  (Ecast (Etempvar _t'15 tuint) tulong)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'16)
                                    (Evar _nondet_u8 (Tfunction nil tuchar
                                                       cc_default)) nil)
                                  (Sset _msel
                                    (Ecast (Etempvar _t'16 tuchar) tuchar)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'17)
                                      (Evar _nondet_u8 (Tfunction nil tuchar
                                                         cc_default)) nil)
                                    (Sset _tsel
                                      (Ecast (Etempvar _t'17 tuchar) tuchar)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'18)
                                        (Evar _nondet_u8 (Tfunction nil
                                                           tuchar cc_default))
                                        nil)
                                      (Sset _dsel
                                        (Ecast (Etempvar _t'18 tuchar)
                                          tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'19)
                                          (Evar _nondet_u8 (Tfunction nil
                                                             tuchar
                                                             cc_default))
                                          nil)
                                        (Sset _hsel
                                          (Ecast (Etempvar _t'19 tuchar)
                                            tuchar)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'20)
                                            (Evar _nondet_u8 (Tfunction nil
                                                               tuchar
                                                               cc_default))
                                            nil)
                                          (Sset _text
                                            (Ecast (Etempvar _t'20 tuchar)
                                              tuchar)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'21)
                                              (Evar _nondet_u8 (Tfunction nil
                                                                 tuchar
                                                                 cc_default))
                                              nil)
                                            (Sset _os
                                              (Ecast (Etempvar _t'21 tuchar)
                                                tuchar)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'22)
                                                (Evar _nondet_u8 (Tfunction
                                                                   nil tuchar
                                                                   cc_default))
                                                nil)
                                              (Sset _hcrc
                                                (Ecast
                                                  (Etempvar _t'22 tuchar)
                                                  tuchar)))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'160
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                        (Tstruct _drun noattr))
                                                      _n tuint))
                                                  (Sifthenelse (Ebinop Ole
                                                                 (Etempvar _t'160 tuint)
                                                                 (Ebinop Oshl
                                                                   (Econst_int (Int.repr 1) tuint)
                                                                   (Econst_int (Int.repr 20) tint)
                                                                   tuint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _t'161
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                            (Tstruct _drun noattr))
                                                          _dlen tuint))
                                                      (Sset _t'23
                                                        (Ecast
                                                          (Ebinop Ole
                                                            (Etempvar _t'161 tuint)
                                                            (Ebinop Oshl
                                                              (Econst_int (Int.repr 1) tuint)
                                                              (Econst_int (Int.repr 15) tint)
                                                              tuint) tint)
                                                          tbool)))
                                                    (Sset _t'23
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Scall None
                                                  (Evar _gp_assume (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _t'23 tint) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'158
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                            (Tstruct _drun noattr))
                                                          _xlen tuint))
                                                      (Sifthenelse (Ebinop Ole
                                                                    (Etempvar _t'158 tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    tuint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _t'159
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                (Tstruct _drun noattr))
                                                              _nl tuint))
                                                          (Sset _t'24
                                                            (Ecast
                                                              (Ebinop Ole
                                                                (Etempvar _t'159 tuint)
                                                                (Ebinop Oshl
                                                                  (Econst_int (Int.repr 1) tuint)
                                                                  (Econst_int (Int.repr 12) tint)
                                                                  tuint)
                                                                tint) tbool)))
                                                        (Sset _t'24
                                                          (Econst_int (Int.repr 0) tint))))
                                                    (Sifthenelse (Etempvar _t'24 tint)
                                                      (Ssequence
                                                        (Sset _t'157
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                              (Tstruct _drun noattr))
                                                            _cl tuint))
                                                        (Sset _t'25
                                                          (Ecast
                                                            (Ebinop Ole
                                                              (Etempvar _t'157 tuint)
                                                              (Ebinop Oshl
                                                                (Econst_int (Int.repr 1) tuint)
                                                                (Econst_int (Int.repr 12) tint)
                                                                tuint) tint)
                                                            tbool)))
                                                      (Sset _t'25
                                                        (Econst_int (Int.repr 0) tint))))
                                                  (Scall None
                                                    (Evar _gp_assume 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _t'25 tint) ::
                                                     nil)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _msel tuchar)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Sset _t'26
                                                        (Ecast
                                                          (Etempvar _mval tint)
                                                          tint))
                                                      (Sset _t'26
                                                        (Ecast
                                                          (Econst_int (Int.repr 8) tint)
                                                          tint)))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                          (Tstruct _drun noattr))
                                                        _method tint)
                                                      (Etempvar _t'26 tint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'156
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                              (Tstruct _drun noattr))
                                                            _n tuint))
                                                        (Scall (Some _t'27)
                                                          (Evar _quickproof_malloc 
                                                          (Tfunction
                                                            (tulong :: nil)
                                                            (tptr tvoid)
                                                            cc_default))
                                                          ((Etempvar _t'156 tuint) ::
                                                           nil)))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                            (Tstruct _drun noattr))
                                                          _data
                                                          (tptr tuchar))
                                                        (Etempvar _t'27 (tptr tvoid))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'155
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                (Tstruct _drun noattr))
                                                              _dlen tuint))
                                                          (Scall (Some _t'28)
                                                            (Evar _quickproof_malloc 
                                                            (Tfunction
                                                              (tulong :: nil)
                                                              (tptr tvoid)
                                                              cc_default))
                                                            ((Etempvar _t'155 tuint) ::
                                                             nil)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                              (Tstruct _drun noattr))
                                                            _dict
                                                            (tptr tuchar))
                                                          (Etempvar _t'28 (tptr tvoid))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'154
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                  (Tstruct _drun noattr))
                                                                _xlen tuint))
                                                            (Scall (Some _t'29)
                                                              (Evar _quickproof_malloc 
                                                              (Tfunction
                                                                (tulong ::
                                                                 nil)
                                                                (tptr tvoid)
                                                                cc_default))
                                                              ((Etempvar _t'154 tuint) ::
                                                               nil)))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                (Tstruct _drun noattr))
                                                              _xf
                                                              (tptr tuchar))
                                                            (Etempvar _t'29 (tptr tvoid))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'153
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                  _nl tuint))
                                                              (Scall (Some _t'30)
                                                                (Evar _quickproof_malloc 
                                                                (Tfunction
                                                                  (tulong ::
                                                                   nil)
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                                ((Ebinop Oadd
                                                                   (Etempvar _t'153 tuint)
                                                                   (Econst_int (Int.repr 1) tint)
                                                                   tuint) ::
                                                                 nil)))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                  (Tstruct _drun noattr))
                                                                _nf_
                                                                (tptr tuchar))
                                                              (Etempvar _t'30 (tptr tvoid))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'152
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cl
                                                                    tuint))
                                                                (Scall (Some _t'31)
                                                                  (Evar _quickproof_malloc 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                  ((Ebinop Oadd
                                                                    (Etempvar _t'152 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint) ::
                                                                   nil)))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                  _cf
                                                                  (tptr tuchar))
                                                                (Etempvar _t'31 (tptr tvoid))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'32)
                                                                  (Evar _quickproof_malloc 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                  ((Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 22) tint)
                                                                    tuint) ::
                                                                   nil))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _comp
                                                                    (tptr tuchar))
                                                                  (Etempvar _t'32 (tptr tvoid))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'150
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _data
                                                                    (tptr tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'150 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'33
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'151
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dict
                                                                    (tptr tuchar)))
                                                                    (Sset _t'33
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'151 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'33 tint)
                                                                    (Sset _t'34
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'149
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _xf
                                                                    (tptr tuchar)))
                                                                    (Sset _t'34
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'149 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'34 tint)
                                                                    (Sset _t'35
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'148
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf_
                                                                    (tptr tuchar)))
                                                                    (Sset _t'35
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'148 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'35 tint)
                                                                    (Sset _t'36
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'147
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cf
                                                                    (tptr tuchar)))
                                                                    (Sset _t'36
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'147 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'36 tint)
                                                                    (Sset _t'37
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'146
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _comp
                                                                    (tptr tuchar)))
                                                                    (Sset _t'37
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'146 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))))
                                                                  (Sifthenelse (Etempvar _t'37 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'144
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _data
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'145
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _n tuint))
                                                                    (Scall None
                                                                    (Evar _nondet_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'144 (tptr tuchar)) ::
                                                                    (Etempvar _t'145 tuint) ::
                                                                    nil))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'142
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dict
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'143
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dlen
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _nondet_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'142 (tptr tuchar)) ::
                                                                    (Etempvar _t'143 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'140
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _xf
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'141
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _xlen
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _nondet_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'140 (tptr tuchar)) ::
                                                                    (Etempvar _t'141 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'138
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf_
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'139
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nl
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _draw_nonzero_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'138 (tptr tuchar)) ::
                                                                    (Etempvar _t'139 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'136
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf_
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'137
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nl
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'136 (tptr tuchar))
                                                                    (Etempvar _t'137 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'134
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cf
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'135
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cl
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _draw_nonzero_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'134 (tptr tuchar)) ::
                                                                    (Etempvar _t'135 tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'132
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cf
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'133
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cl
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'132 (tptr tuchar))
                                                                    (Etempvar _t'133 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _clen
                                                                    tulong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _ended
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _api_ok
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dict_set
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _head_set
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'131
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _n tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf
                                                                    tuint)
                                                                    (Etempvar _t'131 tuint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _stream_defaults 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'126
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _level
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'127
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _method
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'128
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'129
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _mem
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'130
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _strategy
                                                                    tint))
                                                                    (Scall (Some _t'38)
                                                                    (Evar _deflateInit2_ 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    (tptr tschar) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _t'126 tint) ::
                                                                    (Etempvar _t'127 tint) ::
                                                                    (Etempvar _t'128 tint) ::
                                                                    (Etempvar _t'129 tint) ::
                                                                    (Etempvar _t'130 tint) ::
                                                                    (Evar ___stringlit_x_deflate_roundtrip_1 (tarray tschar 6)) ::
                                                                    (Ecast
                                                                    (Esizeof (Tstruct _z_stream_s noattr) tulong)
                                                                    tint) ::
                                                                    nil)))))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint)
                                                                    (Etempvar _t'38 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _api tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'124
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'124 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'39
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'125
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint))
                                                                    (Sset _t'39
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'125 tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'39 tint)
                                                                    (Sset _t'40
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'123
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint))
                                                                    (Sset _t'40
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'123 tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'40 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'118
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _level
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'119
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _method
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'120
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'121
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _mem
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'122
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _strategy
                                                                    tint))
                                                                    (Scall (Some _t'41)
                                                                    (Evar _deflate_params_ok 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'118 tint) ::
                                                                    (Etempvar _t'119 tint) ::
                                                                    (Etempvar _t'120 tint) ::
                                                                    (Etempvar _t'121 tint) ::
                                                                    (Etempvar _t'122 tint) ::
                                                                    nil)))))))
                                                                    (Ssequence
                                                                    (Sset _t'117
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'117 tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'41 tint)
                                                                    tint)
                                                                    tint) ::
                                                                    nil)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'116
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _init
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'116 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'114
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'114 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'115
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'115 tint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Etempvar _t'42 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Etempvar _t'42 tint)
                                                                    tint)))))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wrap
                                                                    tint)
                                                                    (Etempvar _t'42 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'109
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'109 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'113
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Eunop Oneg
                                                                    (Etempvar _t'113 tint)
                                                                    tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _t'110
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'110 tint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'112
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'112 tint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    tint)))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Etempvar _t'43 tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'111
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wbits
                                                                    tint))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Etempvar _t'111 tint)
                                                                    tint)))
                                                                    (Sset _t'43
                                                                    (Ecast
                                                                    (Etempvar _t'43 tint)
                                                                    tint)))))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wb tint)
                                                                    (Etempvar _t'43 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _tsel tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'44)
                                                                    (Evar _deflateTune 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _t1 tint) ::
                                                                    (Etempvar _t2 tint) ::
                                                                    (Etempvar _t3 tint) ::
                                                                    (Etempvar _t4 tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'44 tint)))
                                                                    (Sifthenelse (Etempvar _api tint)
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
                                                                    Sskip))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _dsel tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'107
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dict
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'108
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dlen
                                                                    tuint))
                                                                    (Scall (Some _t'45)
                                                                    (Evar _deflateSetDictionary 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _t'107 (tptr tuchar)) ::
                                                                    (Etempvar _t'108 tuint) ::
                                                                    nil))))
                                                                    (Sset _r
                                                                    (Etempvar _t'45 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _api tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'106
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'106 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Etempvar _t'46 tint)
                                                                    tbool))))
                                                                    (Sset _t'46
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'46 tint) ::
                                                                    nil)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'105
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dlen
                                                                    tuint))
                                                                    (Sset _t'47
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'105 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'47
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _dict_set
                                                                    tint)
                                                                    (Etempvar _t'47 tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _hsel tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _text
                                                                    tint)
                                                                    (Ebinop Oand
                                                                    (Etempvar _text tuchar)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _time
                                                                    tulong)
                                                                    (Etempvar _mtime tulong))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _xflags
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _os tint)
                                                                    (Etempvar _os tuchar))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'104
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _xf
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'104 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'103
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _xlen
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_len
                                                                    tuint)
                                                                    (Etempvar _t'103 tuint)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_max
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'102
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf_
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _name
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'102 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _name_max
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'101
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _cf
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _comment
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'101 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _comm_max
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _hcrc
                                                                    tint)
                                                                    (Ebinop Oand
                                                                    (Etempvar _hcrc tuchar)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _done
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'48)
                                                                    (Evar _deflateSetHeader 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    (tptr (Tstruct _gz_header_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    (tptr (Tstruct _gz_header_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'48 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _api tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'100
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'100 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'49
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'49
                                                                    (Ecast
                                                                    (Etempvar _t'49 tint)
                                                                    tbool))))
                                                                    (Sset _t'49
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'49 tint) ::
                                                                    nil)))
                                                                    Sskip)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _head_set
                                                                    tint)
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)))))))))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _pos
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _lim
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _finishing
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'50)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _nlim
                                                                    (Etempvar _t'50 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'51)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _aout
                                                                    (Etempvar _t'51 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'52)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _fsel
                                                                    (Ecast
                                                                    (Etempvar _t'52 tuint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'53)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _plev
                                                                    (Ecast
                                                                    (Etempvar _t'53 tuint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'54)
                                                                    (Evar _nondet_u32 
                                                                    (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _pstrat
                                                                    (Ecast
                                                                    (Etempvar _t'54 tuint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'55)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _psel
                                                                    (Ecast
                                                                    (Etempvar _t'55 tuchar)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _aout tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 20) tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'99
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _clen
                                                                    tulong))
                                                                    (Sset _t'56
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _aout tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 22) tint)
                                                                    tuint)
                                                                    (Etempvar _t'99 tulong)
                                                                    tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'56
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'56 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _flush
                                                                    (Etempvar _fsel tint))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _finishing tint)
                                                                    (Ssequence
                                                                    (Sset _flush
                                                                    (Econst_int (Int.repr 4) tint))
                                                                    (Sset _lim
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _nlim tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'98
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _n tuint))
                                                                    (Sset _t'57
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _nlim tuint)
                                                                    (Etempvar _t'98 tuint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'57
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'57 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'58
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'58
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assume 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'58 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _lim
                                                                    (Etempvar _nlim tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _finishing
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf
                                                                    tuint)
                                                                    (Etempvar _lim tuint)))
                                                                    Sskip)))))
                                                                    (Ssequence
                                                                    (Sset _ain
                                                                    (Ebinop Osub
                                                                    (Etempvar _lim tuint)
                                                                    (Etempvar _pos tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'97
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _data
                                                                    (tptr tuchar)))
                                                                    (Scall (Some _t'59)
                                                                    (Evar _exact_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    (tptr tuchar)
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _t'97 (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ain tuint) ::
                                                                    nil)))
                                                                    (Sset _ib
                                                                    (Etempvar _t'59 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'60)
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
                                                                    (Etempvar _t'60 (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'61
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'61
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'61 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar))
                                                                    (Etempvar _ib (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint)
                                                                    (Etempvar _ain tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar))
                                                                    (Etempvar _ob (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint)
                                                                    (Etempvar _aout tuint))
                                                                    (Ssequence
                                                                    (Sset _tin
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _tout
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _finishing tint)
                                                                    tint)
                                                                    (Sset _t'62
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _psel tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'62
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _params
                                                                    (Etempvar _t'62 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _params tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'63)
                                                                    (Evar _deflateParams 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _plev tint) ::
                                                                    (Etempvar _pstrat tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'63 tint)))
                                                                    (Ssequence
                                                                    (Scall (Some _t'64)
                                                                    (Evar _deflate 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _s (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _flush tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'64 tint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'96
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sset _used
                                                                    (Ebinop Osub
                                                                    (Etempvar _ain tuint)
                                                                    (Etempvar _t'96 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'95
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Sset _made
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _t'95 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _api tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'93
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _t'93 tuint)
                                                                    (Etempvar _ain tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'94
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Sset _t'65
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _t'94 tuint)
                                                                    (Etempvar _aout tuint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'65
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'65 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'91
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'91 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Etempvar _used tuint)
                                                                    (tptr tuchar))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'92
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar)))
                                                                    (Sset _t'66
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'92 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Etempvar _made tuint)
                                                                    (tptr tuchar))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'66
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'66 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'89
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'89 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _tin tulong)
                                                                    (Etempvar _used tuint)
                                                                    tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'90
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Sset _t'67
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'90 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _tout tulong)
                                                                    (Etempvar _made tuint)
                                                                    tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'67
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'67 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'88
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _data
                                                                    (tptr tuchar)))
                                                                    (Scall (Some _t'68)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _ib (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'88 (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ain tuint) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'68 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'87
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall (Some _t'69)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Etempvar _made tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'87 (tptr tuchar))
                                                                    (Etempvar _made tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _made tuint)
                                                                    tuint) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'69 tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _params tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _plev tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Sset _t'70
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _plev tint)
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'70
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'70 tint)
                                                                    (Sset _t'71
                                                                    (Ecast
                                                                    (Ebinop Oge
                                                                    (Etempvar _pstrat tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'71
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'71 tint)
                                                                    (Sset _t'72
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _pstrat tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'72
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _pok
                                                                    (Etempvar _t'72 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'73
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'73
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'73 tint)
                                                                    (Sset _t'74
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'74
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'74 tint) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Eunop Onotbool
                                                                    (Etempvar _pok tint)
                                                                    tint)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'75
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'75
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'75 tint)
                                                                    (Sset _t'76
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'76
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'76 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'86
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _nf
                                                                    tuint))
                                                                    (Sset _t'77
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _used tuint)
                                                                    tuint)
                                                                    (Etempvar _t'86 tuint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'77
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'77 tint)
                                                                    (Ssequence
                                                                    (Sset _t'85
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _s (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sset _t'78
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'85 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'78
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'78 tint) ::
                                                                    nil)))
                                                                    Sskip)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'79
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _made tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'79
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'79 tint) ::
                                                                    nil)))
                                                                    Sskip)))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'83
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _comp
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'84
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _clen
                                                                    tulong))
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
                                                                    (Etempvar _t'83 (tptr tuchar))
                                                                    (Etempvar _t'84 tulong)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Etempvar _made tuint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'82
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _clen
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _clen
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'82 tulong)
                                                                    (Etempvar _made tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _pos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _used tuint)
                                                                    tuint))
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
                                                                    (Sset _t'81
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'81 (tptr tuchar)) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _params tint)
                                                                    tint)
                                                                    (Sset _t'80
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'80
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'80 tint)
                                                                    Sbreak
                                                                    Sskip)))))))))))))))))))))))))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _R (tptr (Tstruct _drun noattr)))
                                                                    (Tstruct _drun noattr))
                                                                    _ended
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_R, (Tstruct _drun noattr)) ::
              (_s, (Tstruct _z_stream_s noattr)) ::
              (_t, (Tstruct _z_stream_s noattr)) ::
              (_ih, (Tstruct _gz_header_s noattr)) :: nil);
  fn_temps := ((_iw, tint) :: (_r, tint) :: (_ib, (tptr tuchar)) ::
               (_ob, (tptr tuchar)) :: (_t'30, tint) :: (_t'29, tint) ::
               (_t'28, tint) :: (_t'27, tint) :: (_t'26, tint) ::
               (_t'25, tint) :: (_t'24, tint) :: (_t'23, tint) ::
               (_t'22, tint) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, tulong) :: (_t'17, tint) ::
               (_t'16, tint) :: (_t'15, (tptr tvoid)) ::
               (_t'14, (tptr tuchar)) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, (tptr tvoid)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'85, tint) :: (_t'84, tint) :: (_t'83, tint) ::
               (_t'82, tint) :: (_t'81, tuint) :: (_t'80, tuint) ::
               (_t'79, tuint) :: (_t'78, tuint) :: (_t'77, tuint) ::
               (_t'76, tuint) :: (_t'75, (tptr tuchar)) ::
               (_t'74, (tptr tuchar)) :: (_t'73, (tptr tuchar)) ::
               (_t'72, tint) :: (_t'71, tint) :: (_t'70, tint) ::
               (_t'69, tuint) :: (_t'68, (tptr tuchar)) :: (_t'67, tulong) ::
               (_t'66, (tptr tuchar)) :: (_t'65, tuint) :: (_t'64, tulong) ::
               (_t'63, tuint) :: (_t'62, tint) :: (_t'61, tint) ::
               (_t'60, tuint) :: (_t'59, (tptr tuchar)) :: (_t'58, tulong) ::
               (_t'57, tuint) :: (_t'56, (tptr tuchar)) :: (_t'55, tuint) ::
               (_t'54, tuint) :: (_t'53, tuint) :: (_t'52, (tptr tuchar)) ::
               (_t'51, tint) :: (_t'50, tulong) :: (_t'49, tulong) ::
               (_t'48, tint) :: (_t'47, tint) :: (_t'46, tint) ::
               (_t'45, tint) :: (_t'44, tint) :: (_t'43, tint) ::
               (_t'42, tuint) :: (_t'41, (tptr tuchar)) ::
               (_t'40, (tptr tuchar)) :: (_t'39, tuint) :: (_t'38, tuint) ::
               (_t'37, tuint) :: (_t'36, (tptr tuchar)) ::
               (_t'35, (tptr tuchar)) :: (_t'34, tuint) ::
               (_t'33, (tptr tuchar)) :: (_t'32, (tptr tuchar)) ::
               (_t'31, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _deflate_run (Tfunction
                               ((tptr (Tstruct _drun noattr)) ::
                                (tptr (Tstruct _z_stream_s noattr)) ::
                                tint :: nil) tint cc_default))
          ((Eaddrof (Evar _R (Tstruct _drun noattr))
             (tptr (Tstruct _drun noattr))) ::
           (Eaddrof (Evar _s (Tstruct _z_stream_s noattr))
             (tptr (Tstruct _z_stream_s noattr))) ::
           (Econst_int (Int.repr 0) tint) :: nil))
        (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'85 (Efield (Evar _R (Tstruct _drun noattr)) _init tint))
            (Sset _t'2
              (Ecast
                (Ebinop One (Etempvar _t'85 tint)
                  (Econst_int (Int.repr 0) tint) tint) tbool)))))
      (Sifthenelse (Etempvar _t'2 tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _deflateEnd (Tfunction
                              ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                              tint cc_default))
          ((Eaddrof (Evar _s (Tstruct _z_stream_s noattr))
             (tptr (Tstruct _z_stream_s noattr))) :: nil))
        (Scall None
          (Evar _gp_assert (Tfunction (tint :: nil) tvoid cc_default))
          ((Ebinop Oeq (Etempvar _t'3 tint) (Econst_int (Int.repr 0) tint)
             tint) :: nil)))
      (Ssequence
        (Scall None
          (Evar _stream_defaults (Tfunction
                                   ((tptr (Tstruct _z_stream_s noattr)) ::
                                    nil) tvoid cc_default))
          ((Eaddrof (Evar _t (Tstruct _z_stream_s noattr))
             (tptr (Tstruct _z_stream_s noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'82
                (Efield (Evar _R (Tstruct _drun noattr)) _wrap tint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'82 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _t'84
                    (Efield (Evar _R (Tstruct _drun noattr)) _wb tint))
                  (Sset _t'4
                    (Ecast (Eunop Oneg (Etempvar _t'84 tint) tint) tint)))
                (Ssequence
                  (Sset _t'83
                    (Efield (Evar _R (Tstruct _drun noattr)) _wrap tint))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'83 tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Ssequence
                      (Sset _t'4 (Ecast (Econst_int (Int.repr 0) tint) tint))
                      (Sset _t'4 (Ecast (Etempvar _t'4 tint) tint)))
                    (Ssequence
                      (Sset _t'4
                        (Ecast (Econst_int (Int.repr 32) tint) tint))
                      (Sset _t'4 (Ecast (Etempvar _t'4 tint) tint)))))))
            (Sset _iw (Etempvar _t'4 tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _inflateInit2_ (Tfunction
                                       ((tptr (Tstruct _z_stream_s noattr)) ::
                                        tint :: (tptr tschar) :: tint :: nil)
                                       tint cc_default))
                ((Eaddrof (Evar _t (Tstruct _z_stream_s noattr))
                   (tptr (Tstruct _z_stream_s noattr))) ::
                 (Etempvar _iw tint) ::
                 (Evar ___stringlit_x_deflate_roundtrip_1 (tarray tschar 6)) ::
                 (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong) tint) ::
                 nil))
              (Sset _r (Etempvar _t'5 tint)))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _r tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Ssequence
                  (Sset _t'72
                    (Efield (Evar _R (Tstruct _drun noattr)) _head_set tint))
                  (Sifthenelse (Etempvar _t'72 tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'81
                            (Efield (Evar _R (Tstruct _drun noattr)) _xlen
                              tuint))
                          (Scall (Some _t'6)
                            (Evar _quickproof_malloc (Tfunction
                                                       (tulong :: nil)
                                                       (tptr tvoid)
                                                       cc_default))
                            ((Etempvar _t'81 tuint) :: nil)))
                        (Sassign
                          (Efield (Evar _ih (Tstruct _gz_header_s noattr))
                            _extra (tptr tuchar))
                          (Etempvar _t'6 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'80
                            (Efield (Evar _R (Tstruct _drun noattr)) _xlen
                              tuint))
                          (Sassign
                            (Efield (Evar _ih (Tstruct _gz_header_s noattr))
                              _extra_max tuint) (Etempvar _t'80 tuint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'79
                                (Efield (Evar _R (Tstruct _drun noattr)) _nl
                                  tuint))
                              (Scall (Some _t'7)
                                (Evar _quickproof_malloc (Tfunction
                                                           (tulong :: nil)
                                                           (tptr tvoid)
                                                           cc_default))
                                ((Ebinop Oadd (Etempvar _t'79 tuint)
                                   (Econst_int (Int.repr 1) tint) tuint) ::
                                 nil)))
                            (Sassign
                              (Efield
                                (Evar _ih (Tstruct _gz_header_s noattr))
                                _name (tptr tuchar))
                              (Etempvar _t'7 (tptr tvoid))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'78
                                (Efield (Evar _R (Tstruct _drun noattr)) _nl
                                  tuint))
                              (Sassign
                                (Efield
                                  (Evar _ih (Tstruct _gz_header_s noattr))
                                  _name_max tuint)
                                (Ebinop Oadd (Etempvar _t'78 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'77
                                    (Efield (Evar _R (Tstruct _drun noattr))
                                      _cl tuint))
                                  (Scall (Some _t'8)
                                    (Evar _quickproof_malloc (Tfunction
                                                               (tulong ::
                                                                nil)
                                                               (tptr tvoid)
                                                               cc_default))
                                    ((Ebinop Oadd (Etempvar _t'77 tuint)
                                       (Econst_int (Int.repr 1) tint) tuint) ::
                                     nil)))
                                (Sassign
                                  (Efield
                                    (Evar _ih (Tstruct _gz_header_s noattr))
                                    _comment (tptr tuchar))
                                  (Etempvar _t'8 (tptr tvoid))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'76
                                    (Efield (Evar _R (Tstruct _drun noattr))
                                      _cl tuint))
                                  (Sassign
                                    (Efield
                                      (Evar _ih (Tstruct _gz_header_s noattr))
                                      _comm_max tuint)
                                    (Ebinop Oadd (Etempvar _t'76 tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'74
                                          (Efield
                                            (Evar _ih (Tstruct _gz_header_s noattr))
                                            _extra (tptr tuchar)))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _t'74 (tptr tuchar))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          (Sset _t'9
                                            (Econst_int (Int.repr 1) tint))
                                          (Ssequence
                                            (Sset _t'75
                                              (Efield
                                                (Evar _ih (Tstruct _gz_header_s noattr))
                                                _name (tptr tuchar)))
                                            (Sset _t'9
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _t'75 (tptr tuchar))
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    (tptr tvoid)) tint)
                                                tbool)))))
                                      (Sifthenelse (Etempvar _t'9 tint)
                                        (Sset _t'10
                                          (Econst_int (Int.repr 1) tint))
                                        (Ssequence
                                          (Sset _t'73
                                            (Efield
                                              (Evar _ih (Tstruct _gz_header_s noattr))
                                              _comment (tptr tuchar)))
                                          (Sset _t'10
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _t'73 (tptr tuchar))
                                                (Ecast
                                                  (Econst_int (Int.repr 0) tint)
                                                  (tptr tvoid)) tint) tbool)))))
                                    (Sifthenelse (Etempvar _t'10 tint)
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                      Sskip))
                                  (Ssequence
                                    (Scall (Some _t'11)
                                      (Evar _inflateGetHeader (Tfunction
                                                                ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                 (tptr (Tstruct _gz_header_s noattr)) ::
                                                                 nil) tint
                                                                cc_default))
                                      ((Eaddrof
                                         (Evar _t (Tstruct _z_stream_s noattr))
                                         (tptr (Tstruct _z_stream_s noattr))) ::
                                       (Eaddrof
                                         (Evar _ih (Tstruct _gz_header_s noattr))
                                         (tptr (Tstruct _gz_header_s noattr))) ::
                                       nil))
                                    (Scall None
                                      (Evar _gp_assert (Tfunction
                                                         (tint :: nil) tvoid
                                                         cc_default))
                                      ((Ebinop Oeq (Etempvar _t'11 tint)
                                         (Econst_int (Int.repr 0) tint) tint) ::
                                       nil))))))))))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'70
                        (Efield (Evar _R (Tstruct _drun noattr)) _wrap tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'70 tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                          (Sset _t'71
                            (Efield (Evar _R (Tstruct _drun noattr))
                              _dict_set tint))
                          (Sset _t'13 (Ecast (Etempvar _t'71 tint) tbool)))
                        (Sset _t'13 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'13 tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'68
                              (Efield (Evar _R (Tstruct _drun noattr)) _dict
                                (tptr tuchar)))
                            (Ssequence
                              (Sset _t'69
                                (Efield (Evar _R (Tstruct _drun noattr))
                                  _dlen tuint))
                              (Scall (Some _t'12)
                                (Evar _inflateSetDictionary (Tfunction
                                                              ((tptr (Tstruct _z_stream_s noattr)) ::
                                                               (tptr tuchar) ::
                                                               tuint :: nil)
                                                              tint
                                                              cc_default))
                                ((Eaddrof
                                   (Evar _t (Tstruct _z_stream_s noattr))
                                   (tptr (Tstruct _z_stream_s noattr))) ::
                                 (Etempvar _t'68 (tptr tuchar)) ::
                                 (Etempvar _t'69 tuint) :: nil))))
                          (Sset _r (Etempvar _t'12 tint)))
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                                         (Eunop Oneg
                                           (Econst_int (Int.repr 4) tint)
                                           tint) tint)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            Sskip)
                          (Scall None
                            (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                               cc_default))
                            ((Ebinop Oeq (Etempvar _r tint)
                               (Econst_int (Int.repr 0) tint) tint) :: nil))))
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'66
                          (Efield (Evar _R (Tstruct _drun noattr)) _comp
                            (tptr tuchar)))
                        (Ssequence
                          (Sset _t'67
                            (Efield (Evar _R (Tstruct _drun noattr)) _clen
                              tulong))
                          (Scall (Some _t'14)
                            (Evar _exact_copy (Tfunction
                                                ((tptr tuchar) :: tuint ::
                                                 nil) (tptr tuchar)
                                                cc_default))
                            ((Etempvar _t'66 (tptr tuchar)) ::
                             (Ecast (Etempvar _t'67 tulong) tuint) :: nil))))
                      (Sset _ib (Etempvar _t'14 (tptr tuchar))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'65
                            (Efield (Evar _R (Tstruct _drun noattr)) _nf
                              tuint))
                          (Scall (Some _t'15)
                            (Evar _quickproof_malloc (Tfunction
                                                       (tulong :: nil)
                                                       (tptr tvoid)
                                                       cc_default))
                            ((Etempvar _t'65 tuint) :: nil)))
                        (Sset _ob (Etempvar _t'15 (tptr tvoid))))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _ib (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Sset _t'16 (Econst_int (Int.repr 1) tint))
                            (Sset _t'16
                              (Ecast
                                (Ebinop Oeq (Etempvar _ob (tptr tuchar))
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid)) tint) tbool)))
                          (Sifthenelse (Etempvar _t'16 tint)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            Sskip))
                        (Ssequence
                          (Sassign
                            (Efield (Evar _t (Tstruct _z_stream_s noattr))
                              _next_in (tptr tuchar))
                            (Etempvar _ib (tptr tuchar)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'64
                                (Efield (Evar _R (Tstruct _drun noattr))
                                  _clen tulong))
                              (Sassign
                                (Efield
                                  (Evar _t (Tstruct _z_stream_s noattr))
                                  _avail_in tuint)
                                (Ecast (Etempvar _t'64 tulong) tuint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Evar _t (Tstruct _z_stream_s noattr))
                                  _next_out (tptr tuchar))
                                (Etempvar _ob (tptr tuchar)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'63
                                    (Efield (Evar _R (Tstruct _drun noattr))
                                      _nf tuint))
                                  (Sassign
                                    (Efield
                                      (Evar _t (Tstruct _z_stream_s noattr))
                                      _avail_out tuint)
                                    (Etempvar _t'63 tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'17)
                                      (Evar _inflate (Tfunction
                                                       ((tptr (Tstruct _z_stream_s noattr)) ::
                                                        tint :: nil) tint
                                                       cc_default))
                                      ((Eaddrof
                                         (Evar _t (Tstruct _z_stream_s noattr))
                                         (tptr (Tstruct _z_stream_s noattr))) ::
                                       (Econst_int (Int.repr 4) tint) :: nil))
                                    (Sset _r (Etempvar _t'17 tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'61
                                          (Efield
                                            (Evar _R (Tstruct _drun noattr))
                                            _wrap tint))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _t'61 tint)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _t'62
                                              (Efield
                                                (Evar _R (Tstruct _drun noattr))
                                                _dict_set tint))
                                            (Sset _t'21
                                              (Ecast (Etempvar _t'62 tint)
                                                tbool)))
                                          (Sset _t'21
                                            (Econst_int (Int.repr 0) tint))))
                                      (Sifthenelse (Etempvar _t'21 tint)
                                        (Ssequence
                                          (Scall None
                                            (Evar _gp_assert (Tfunction
                                                               (tint :: nil)
                                                               tvoid
                                                               cc_default))
                                            ((Ebinop Oeq (Etempvar _r tint)
                                               (Econst_int (Int.repr 2) tint)
                                               tint) :: nil))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'59
                                                  (Efield
                                                    (Evar _R (Tstruct _drun noattr))
                                                    _dict (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'60
                                                    (Efield
                                                      (Evar _R (Tstruct _drun noattr))
                                                      _dlen tuint))
                                                  (Scall (Some _t'18)
                                                    (Evar _ref_adler32 
                                                    (Tfunction
                                                      (tulong ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tulong
                                                      cc_default))
                                                    ((Econst_int (Int.repr 1) tint) ::
                                                     (Etempvar _t'59 (tptr tuchar)) ::
                                                     (Etempvar _t'60 tuint) ::
                                                     nil))))
                                              (Ssequence
                                                (Sset _t'58
                                                  (Efield
                                                    (Evar _t (Tstruct _z_stream_s noattr))
                                                    _adler tulong))
                                                (Scall None
                                                  (Evar _gp_assert (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Ebinop Oeq
                                                     (Etempvar _t'58 tulong)
                                                     (Etempvar _t'18 tulong)
                                                     tint) :: nil))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'56
                                                    (Efield
                                                      (Evar _R (Tstruct _drun noattr))
                                                      _dict (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'57
                                                      (Efield
                                                        (Evar _R (Tstruct _drun noattr))
                                                        _dlen tuint))
                                                    (Scall (Some _t'19)
                                                      (Evar _inflateSetDictionary 
                                                      (Tfunction
                                                        ((tptr (Tstruct _z_stream_s noattr)) ::
                                                         (tptr tuchar) ::
                                                         tuint :: nil) tint
                                                        cc_default))
                                                      ((Eaddrof
                                                         (Evar _t (Tstruct _z_stream_s noattr))
                                                         (tptr (Tstruct _z_stream_s noattr))) ::
                                                       (Etempvar _t'56 (tptr tuchar)) ::
                                                       (Etempvar _t'57 tuint) ::
                                                       nil))))
                                                (Sset _r
                                                  (Etempvar _t'19 tint)))
                                              (Ssequence
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _r tint)
                                                               (Eunop Oneg
                                                                 (Econst_int (Int.repr 4) tint)
                                                                 tint) tint)
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                  Sskip)
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _gp_assert 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Ebinop Oeq
                                                       (Etempvar _r tint)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint) :: nil))
                                                  (Ssequence
                                                    (Scall (Some _t'20)
                                                      (Evar _inflate 
                                                      (Tfunction
                                                        ((tptr (Tstruct _z_stream_s noattr)) ::
                                                         tint :: nil) tint
                                                        cc_default))
                                                      ((Eaddrof
                                                         (Evar _t (Tstruct _z_stream_s noattr))
                                                         (tptr (Tstruct _z_stream_s noattr))) ::
                                                       (Econst_int (Int.repr 4) tint) ::
                                                       nil))
                                                    (Sset _r
                                                      (Etempvar _t'20 tint))))))))
                                        Sskip))
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _r tint)
                                                     (Eunop Oneg
                                                       (Econst_int (Int.repr 4) tint)
                                                       tint) tint)
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                        Sskip)
                                      (Ssequence
                                        (Scall None
                                          (Evar _gp_assert (Tfunction
                                                             (tint :: nil)
                                                             tvoid
                                                             cc_default))
                                          ((Ebinop Oeq (Etempvar _r tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint) :: nil))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'54
                                                (Efield
                                                  (Evar _t (Tstruct _z_stream_s noattr))
                                                  _avail_in tuint))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _t'54 tuint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sset _t'55
                                                    (Efield
                                                      (Evar _t (Tstruct _z_stream_s noattr))
                                                      _avail_out tuint))
                                                  (Sset _t'22
                                                    (Ecast
                                                      (Ebinop Oeq
                                                        (Etempvar _t'55 tuint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint) tbool)))
                                                (Sset _t'22
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _t'22 tint) :: nil)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'52
                                                  (Efield
                                                    (Evar _R (Tstruct _drun noattr))
                                                    _data (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'53
                                                    (Efield
                                                      (Evar _R (Tstruct _drun noattr))
                                                      _nf tuint))
                                                  (Scall (Some _t'23)
                                                    (Evar _bytes_same 
                                                    (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                                    ((Etempvar _ob (tptr tuchar)) ::
                                                     (Etempvar _t'52 (tptr tuchar)) ::
                                                     (Etempvar _t'53 tuint) ::
                                                     nil))))
                                              (Scall None
                                                (Evar _gp_assert (Tfunction
                                                                   (tint ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                                ((Etempvar _t'23 tint) ::
                                                 nil)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'31
                                                  (Efield
                                                    (Evar _R (Tstruct _drun noattr))
                                                    _head_set tint))
                                                (Sifthenelse (Etempvar _t'31 tint)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'51
                                                        (Efield
                                                          (Evar _ih (Tstruct _gz_header_s noattr))
                                                          _done tint))
                                                      (Scall None
                                                        (Evar _gp_assert 
                                                        (Tfunction
                                                          (tint :: nil) tvoid
                                                          cc_default))
                                                        ((Ebinop Oeq
                                                           (Etempvar _t'51 tint)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint) :: nil)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'47
                                                                (Efield
                                                                  (Evar _ih (Tstruct _gz_header_s noattr))
                                                                  _text tint))
                                                              (Ssequence
                                                                (Sset _t'48
                                                                  (Efield
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _text
                                                                    tint))
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _t'47 tint)
                                                                    (Etempvar _t'48 tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _t'49
                                                                    (Efield
                                                                    (Evar _ih (Tstruct _gz_header_s noattr))
                                                                    _time
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _time
                                                                    tulong))
                                                                    (Sset _t'24
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'49 tulong)
                                                                    (Etempvar _t'50 tulong)
                                                                    tint)
                                                                    tbool))))
                                                                  (Sset _t'24
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                            (Sifthenelse (Etempvar _t'24 tint)
                                                              (Ssequence
                                                                (Sset _t'45
                                                                  (Efield
                                                                    (Evar _ih (Tstruct _gz_header_s noattr))
                                                                    _os tint))
                                                                (Ssequence
                                                                  (Sset _t'46
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _os tint))
                                                                  (Sset _t'25
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'45 tint)
                                                                    (Etempvar _t'46 tint)
                                                                    tint)
                                                                    tbool))))
                                                              (Sset _t'25
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'25 tint)
                                                            (Ssequence
                                                              (Sset _t'43
                                                                (Efield
                                                                  (Evar _ih (Tstruct _gz_header_s noattr))
                                                                  _hcrc tint))
                                                              (Ssequence
                                                                (Sset _t'44
                                                                  (Efield
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _h
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _hcrc
                                                                    tint))
                                                                (Sset _t'26
                                                                  (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'43 tint)
                                                                    (Etempvar _t'44 tint)
                                                                    tint)
                                                                    tbool))))
                                                            (Sset _t'26
                                                              (Econst_int (Int.repr 0) tint))))
                                                        (Scall None
                                                          (Evar _gp_assert 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Etempvar _t'26 tint) ::
                                                           nil)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'38
                                                              (Efield
                                                                (Evar _ih (Tstruct _gz_header_s noattr))
                                                                _extra_len
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'39
                                                                (Efield
                                                                  (Evar _R (Tstruct _drun noattr))
                                                                  _xlen
                                                                  tuint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _t'38 tuint)
                                                                  (Etempvar _t'39 tuint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Evar _ih (Tstruct _gz_header_s noattr))
                                                                    _extra
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _xf
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _xlen
                                                                    tuint))
                                                                    (Scall (Some _t'28)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'40 (tptr tuchar)) ::
                                                                    (Etempvar _t'41 (tptr tuchar)) ::
                                                                    (Etempvar _t'42 tuint) ::
                                                                    nil)))))
                                                                  (Sset _t'27
                                                                    (Ecast
                                                                    (Etempvar _t'28 tint)
                                                                    tbool)))
                                                                (Sset _t'27
                                                                  (Econst_int (Int.repr 0) tint)))))
                                                          (Scall None
                                                            (Evar _gp_assert 
                                                            (Tfunction
                                                              (tint :: nil)
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _t'27 tint) ::
                                                             nil)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'35
                                                                (Efield
                                                                  (Evar _ih (Tstruct _gz_header_s noattr))
                                                                  _name
                                                                  (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'36
                                                                  (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _nf_
                                                                    (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sset _t'37
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _nl
                                                                    tuint))
                                                                  (Scall (Some _t'29)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'35 (tptr tuchar)) ::
                                                                    (Etempvar _t'36 (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'37 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint) ::
                                                                    nil)))))
                                                            (Scall None
                                                              (Evar _gp_assert 
                                                              (Tfunction
                                                                (tint :: nil)
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _t'29 tint) ::
                                                               nil)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'32
                                                                (Efield
                                                                  (Evar _ih (Tstruct _gz_header_s noattr))
                                                                  _comment
                                                                  (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'33
                                                                  (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _cf
                                                                    (tptr tuchar)))
                                                                (Ssequence
                                                                  (Sset _t'34
                                                                    (Efield
                                                                    (Evar _R (Tstruct _drun noattr))
                                                                    _cl
                                                                    tuint))
                                                                  (Scall (Some _t'30)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'32 (tptr tuchar)) ::
                                                                    (Etempvar _t'33 (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'34 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint) ::
                                                                    nil)))))
                                                            (Scall None
                                                              (Evar _gp_assert 
                                                              (Tfunction
                                                                (tint :: nil)
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _t'30 tint) ::
                                                               nil)))))))
                                                  Sskip))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _inflateEnd (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _t (Tstruct _z_stream_s noattr))
                                                     (tptr (Tstruct _z_stream_s noattr))) ::
                                                   nil))
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))))
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
 Composite _gz_header_s Struct
   (Member_plain _text tint :: Member_plain _time tulong ::
    Member_plain _xflags tint :: Member_plain _os tint ::
    Member_plain _extra (tptr tuchar) :: Member_plain _extra_len tuint ::
    Member_plain _extra_max tuint :: Member_plain _name (tptr tuchar) ::
    Member_plain _name_max tuint :: Member_plain _comment (tptr tuchar) ::
    Member_plain _comm_max tuint :: Member_plain _hcrc tint ::
    Member_plain _done tint :: nil)
   noattr ::
 Composite _drun Struct
   (Member_plain _level tint :: Member_plain _method tint ::
    Member_plain _wbits tint :: Member_plain _mem tint ::
    Member_plain _strategy tint :: Member_plain _init tint ::
    Member_plain _wrap tint :: Member_plain _wb tint ::
    Member_plain _data (tptr tuchar) :: Member_plain _n tuint ::
    Member_plain _nf tuint :: Member_plain _dict (tptr tuchar) ::
    Member_plain _dlen tuint :: Member_plain _dict_set tint ::
    Member_plain _head_set tint ::
    Member_plain _h (Tstruct _gz_header_s noattr) ::
    Member_plain _xf (tptr tuchar) :: Member_plain _nf_ (tptr tuchar) ::
    Member_plain _cf (tptr tuchar) :: Member_plain _xlen tuint ::
    Member_plain _nl tuint :: Member_plain _cl tuint ::
    Member_plain _comp (tptr tuchar) :: Member_plain _clen tulong ::
    Member_plain _ended tint :: Member_plain _api_ok tint :: nil)
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
     cc_default)) :: (___stringlit_x_deflate_roundtrip_1, Gvar v___stringlit_x_deflate_roundtrip_1) ::
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
 (_deflate,
   Gfun(External (EF_external "deflate"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_deflateEnd,
   Gfun(External (EF_external "deflateEnd"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_inflate,
   Gfun(External (EF_external "inflate"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_inflateEnd,
   Gfun(External (EF_external "inflateEnd"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_deflateSetDictionary,
   Gfun(External (EF_external "deflateSetDictionary"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: (tptr tuchar) :: tuint :: nil)
     tint cc_default)) ::
 (_deflateParams,
   Gfun(External (EF_external "deflateParams"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: tint :: nil) tint
     cc_default)) ::
 (_deflateTune,
   Gfun(External (EF_external "deflateTune"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xint ::
                      AST.Xint :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: tint :: tint :: tint ::
      nil) tint cc_default)) ::
 (_deflateSetHeader,
   Gfun(External (EF_external "deflateSetHeader"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) ::
      (tptr (Tstruct _gz_header_s noattr)) :: nil) tint cc_default)) ::
 (_inflateSetDictionary,
   Gfun(External (EF_external "inflateSetDictionary"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: (tptr tuchar) :: tuint :: nil)
     tint cc_default)) ::
 (_inflateGetHeader,
   Gfun(External (EF_external "inflateGetHeader"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) ::
      (tptr (Tstruct _gz_header_s noattr)) :: nil) tint cc_default)) ::
 (_deflateInit2_,
   Gfun(External (EF_external "deflateInit2_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xint ::
                      AST.Xint :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: tint :: tint :: tint ::
      tint :: (tptr tschar) :: tint :: nil) tint cc_default)) ::
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
 (_deflate_params_ok, Gfun(Internal f_deflate_params_ok)) ::
 (_draw_nonzero_bytes, Gfun(Internal f_draw_nonzero_bytes)) ::
 (_deflate_run, Gfun(Internal f_deflate_run)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _inflateInit2_ :: _deflateInit2_ :: _inflateGetHeader ::
 _inflateSetDictionary :: _deflateSetHeader :: _deflateTune ::
 _deflateParams :: _deflateSetDictionary :: _inflateEnd :: _inflate ::
 _deflateEnd :: _deflate :: _gp_assume :: _gp_assert :: _nondet_bytes ::
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



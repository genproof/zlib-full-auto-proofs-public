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
  Definition source_file := "harness/x_inflate_buffers.c".
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
Definition ___stringlit_x_inflate_buffers_1 : ident := $"__stringlit_x_inflate_buffers_1".
Definition _a : ident := $"a".
Definition _adler : ident := $"adler".
Definition _ain : ident := $"ain".
Definition _aout : ident := $"aout".
Definition _arg : ident := $"arg".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _b : ident := $"b".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_same : ident := $"bytes_same".
Definition _d : ident := $"d".
Definition _data_type : ident := $"data_type".
Definition _dl : ident := $"dl".
Definition _exact_copy : ident := $"exact_copy".
Definition _exact_space : ident := $"exact_space".
Definition _flush : ident := $"flush".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _ib : ident := $"ib".
Definition _in_null : ident := $"in_null".
Definition _inflate : ident := $"inflate".
Definition _inflateCodesUsed : ident := $"inflateCodesUsed".
Definition _inflateEnd : ident := $"inflateEnd".
Definition _inflateGetDictionary : ident := $"inflateGetDictionary".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _inflateMark : ident := $"inflateMark".
Definition _inflatePrime : ident := $"inflatePrime".
Definition _inflateReset : ident := $"inflateReset".
Definition _inflateReset2 : ident := $"inflateReset2".
Definition _inflateSetDictionary : ident := $"inflateSetDictionary".
Definition _inflateSync : ident := $"inflateSync".
Definition _inflateSyncPoint : ident := $"inflateSyncPoint".
Definition _inflateValidate : ident := $"inflateValidate".
Definition _inflate_wbits_ok : ident := $"inflate_wbits_ok".
Definition _internal_state : ident := $"internal_state".
Definition _lim : ident := $"lim".
Definition _made : ident := $"made".
Definition _main : ident := $"main".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nin : ident := $"nin".
Definition _nlim : ident := $"nlim".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _nout : ident := $"nout".
Definition _ob : ident := $"ob".
Definition _op : ident := $"op".
Definition _opaque : ident := $"opaque".
Definition _osnap : ident := $"osnap".
Definition _out_null : ident := $"out_null".
Definition _p : ident := $"p".
Definition _pos : ident := $"pos".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _reserved : ident := $"reserved".
Definition _reset : ident := $"reset".
Definition _s : ident := $"s".
Definition _snap : ident := $"snap".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _stop : ident := $"stop".
Definition _stream_defaults : ident := $"stream_defaults".
Definition _tin : ident := $"tin".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _tout : ident := $"tout".
Definition _used : ident := $"used".
Definition _w : ident := $"w".
Definition _wbits : ident := $"wbits".
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
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_x_inflate_buffers_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
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

Definition f_inflate_wbits_ok := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_w, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _w tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _w tint)
                     (Eunop Oneg (Econst_int (Int.repr 15) tint) tint) tint)
        (Sset _t'1
          (Ecast
            (Ebinop Ole (Etempvar _w tint)
              (Eunop Oneg (Econst_int (Int.repr 8) tint) tint) tint) tbool))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Etempvar _t'1 tint))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _w tint)
                   (Econst_int (Int.repr 48) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Sset _w
        (Ebinop Oand (Etempvar _w tint) (Econst_int (Int.repr 15) tint) tint))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _w tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Sifthenelse (Ebinop Oge (Etempvar _w tint)
                         (Econst_int (Int.repr 8) tint) tint)
            (Ssequence
              (Sset _t'2
                (Ecast
                  (Ebinop Ole (Etempvar _w tint)
                    (Econst_int (Int.repr 15) tint) tint) tbool))
              (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool)))
            (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tbool))))
        (Sreturn (Some (Etempvar _t'2 tint)))))))
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

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_s, (Tstruct _z_stream_s noattr)) ::
              (_osnap, (tptr tuchar)) :: (_dl, tuint) :: nil);
  fn_temps := ((_wbits, tint) :: (_n, tuint) :: (_src, (tptr tuchar)) ::
               (_r, tint) :: (_pos, tuint) :: (_lim, tuint) ::
               (_nlim, tuint) :: (_aout, tuint) :: (_flush, tint) ::
               (_arg, tuint) :: (_op, tuchar) :: (_in_null, tuchar) ::
               (_out_null, tuchar) :: (_stop, tuchar) :: (_ain, tuint) ::
               (_ib, (tptr tuchar)) :: (_ob, (tptr tuchar)) ::
               (_nin, tint) :: (_nout, tint) :: (_tin, tulong) ::
               (_tout, tulong) :: (_reset, tint) :: (_used, tuint) ::
               (_made, tuint) :: (_t'50, tint) :: (_t'49, tint) ::
               (_t'48, tint) :: (_t'47, tint) :: (_t'46, tint) ::
               (_t'45, tint) :: (_t'44, tint) :: (_t'43, tint) ::
               (_t'42, tint) :: (_t'41, tint) :: (_t'40, tint) ::
               (_t'39, tint) :: (_t'38, tint) :: (_t'37, tint) ::
               (_t'36, tint) :: (_t'35, tint) :: (_t'34, tint) ::
               (_t'33, tint) :: (_t'32, tint) :: (_t'31, tint) ::
               (_t'30, tint) :: (_t'29, tint) :: (_t'28, tint) ::
               (_t'27, tint) :: (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, (tptr tvoid)) :: (_t'23, (tptr tvoid)) ::
               (_t'22, tint) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, (tptr tuchar)) :: (_t'18, (tptr tuchar)) ::
               (_t'17, tint) :: (_t'16, tuchar) :: (_t'15, tuchar) ::
               (_t'14, tuchar) :: (_t'13, tuchar) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tuint) :: (_t'1, tuint) :: (_t'74, tulong) ::
               (_t'73, tulong) :: (_t'72, tuint) :: (_t'71, tuint) ::
               (_t'70, tuint) :: (_t'69, (tptr tuchar)) :: (_t'68, tuint) ::
               (_t'67, tuint) :: (_t'66, (tptr tuchar)) :: (_t'65, tuint) ::
               (_t'64, tuint) :: (_t'63, tuint) :: (_t'62, tuint) ::
               (_t'61, tuint) :: (_t'60, (tptr tuchar)) ::
               (_t'59, (tptr tuchar)) :: (_t'58, (tptr tuchar)) ::
               (_t'57, (tptr tuchar)) :: (_t'56, (tptr tuchar)) ::
               (_t'55, tulong) :: (_t'54, tulong) :: (_t'53, tulong) ::
               (_t'52, tulong) :: (_t'51, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sset _wbits (Ecast (Etempvar _t'1 tuint) tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sset _n (Etempvar _t'2 tuint)))
      (Ssequence
        (Scall None
          (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
          ((Ebinop Ole (Etempvar _n tuint)
             (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
               (Econst_int (Int.repr 24) tint) tuint) tint) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                         (tptr tvoid) cc_default))
              ((Etempvar _n tuint) :: nil))
            (Sset _src (Etempvar _t'3 (tptr tvoid))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _src (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip)
            (Ssequence
              (Scall None
                (Evar _nondet_bytes (Tfunction
                                      ((tptr tuchar) :: tulong :: nil) tvoid
                                      cc_default))
                ((Etempvar _src (tptr tuchar)) :: (Etempvar _n tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _stream_defaults (Tfunction
                                           ((tptr (Tstruct _z_stream_s noattr)) ::
                                            nil) tvoid cc_default))
                  ((Eaddrof (Evar _s (Tstruct _z_stream_s noattr))
                     (tptr (Tstruct _z_stream_s noattr))) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _inflateInit2_ (Tfunction
                                             ((tptr (Tstruct _z_stream_s noattr)) ::
                                              tint :: (tptr tschar) ::
                                              tint :: nil) tint cc_default))
                      ((Eaddrof (Evar _s (Tstruct _z_stream_s noattr))
                         (tptr (Tstruct _z_stream_s noattr))) ::
                       (Etempvar _wbits tint) ::
                       (Evar ___stringlit_x_inflate_buffers_1 (tarray tschar 6)) ::
                       (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong)
                         tint) :: nil))
                    (Sset _r (Etempvar _t'4 tint)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _r tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Sset _t'5 (Econst_int (Int.repr 1) tint))
                          (Sset _t'5
                            (Ecast
                              (Ebinop Oeq (Etempvar _r tint)
                                (Eunop Oneg (Econst_int (Int.repr 2) tint)
                                  tint) tint) tbool)))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Sset _t'6 (Econst_int (Int.repr 1) tint))
                          (Sset _t'6
                            (Ecast
                              (Ebinop Oeq (Etempvar _r tint)
                                (Eunop Oneg (Econst_int (Int.repr 4) tint)
                                  tint) tint) tbool))))
                      (Scall None
                        (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                           cc_default))
                        ((Etempvar _t'6 tint) :: nil)))
                    (Ssequence
                      (Sifthenelse (Ebinop One (Etempvar _r tint)
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 4) tint) tint)
                                     tint)
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _inflate_wbits_ok (Tfunction (tint :: nil)
                                                      tint cc_default))
                            ((Etempvar _wbits tint) :: nil))
                          (Scall None
                            (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                               cc_default))
                            ((Ebinop Oeq
                               (Ebinop Oeq (Etempvar _r tint)
                                 (Eunop Oneg (Econst_int (Int.repr 2) tint)
                                   tint) tint)
                               (Eunop Onotbool (Etempvar _t'7 tint) tint)
                               tint) :: nil)))
                        Sskip)
                      (Ssequence
                        (Sifthenelse (Ebinop One (Etempvar _r tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Ssequence
                            (Scall None
                              (Evar _quickproof_free (Tfunction
                                                       ((tptr tvoid) :: nil)
                                                       tvoid cc_default))
                              ((Etempvar _src (tptr tuchar)) :: nil))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                          Sskip)
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'73
                                (Efield
                                  (Evar _s (Tstruct _z_stream_s noattr))
                                  _total_in tulong))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _t'73 tulong)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _t'74
                                    (Efield
                                      (Evar _s (Tstruct _z_stream_s noattr))
                                      _total_out tulong))
                                  (Sset _t'8
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _t'74 tulong)
                                        (Econst_int (Int.repr 0) tint) tint)
                                      tbool)))
                                (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                            (Scall None
                              (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Etempvar _t'8 tint) :: nil)))
                          (Ssequence
                            (Sset _pos (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sset _lim (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sloop
                                  (Ssequence
                                    Sskip
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'9)
                                          (Evar _nondet_u32 (Tfunction nil
                                                              tuint
                                                              cc_default))
                                          nil)
                                        (Sset _nlim (Etempvar _t'9 tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'10)
                                            (Evar _nondet_u32 (Tfunction nil
                                                                tuint
                                                                cc_default))
                                            nil)
                                          (Sset _aout (Etempvar _t'10 tuint)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'11)
                                              (Evar _nondet_u32 (Tfunction
                                                                  nil tuint
                                                                  cc_default))
                                              nil)
                                            (Sset _flush
                                              (Ecast (Etempvar _t'11 tuint)
                                                tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'12)
                                                (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                nil)
                                              (Sset _arg
                                                (Etempvar _t'12 tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'13)
                                                  (Evar _nondet_u8 (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                  nil)
                                                (Sset _op
                                                  (Ecast
                                                    (Etempvar _t'13 tuchar)
                                                    tuchar)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'14)
                                                    (Evar _nondet_u8 
                                                    (Tfunction nil tuchar
                                                      cc_default)) nil)
                                                  (Sset _in_null
                                                    (Ecast
                                                      (Etempvar _t'14 tuchar)
                                                      tuchar)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'15)
                                                      (Evar _nondet_u8 
                                                      (Tfunction nil tuchar
                                                        cc_default)) nil)
                                                    (Sset _out_null
                                                      (Ecast
                                                        (Etempvar _t'15 tuchar)
                                                        tuchar)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'16)
                                                        (Evar _nondet_u8 
                                                        (Tfunction nil tuchar
                                                          cc_default)) nil)
                                                      (Sset _stop
                                                        (Ecast
                                                          (Etempvar _t'16 tuchar)
                                                          tuchar)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Ole
                                                            (Etempvar _pos tuint)
                                                            (Etempvar _nlim tuint)
                                                            tint)
                                                          (Sset _t'17
                                                            (Ecast
                                                              (Ebinop Ole
                                                                (Etempvar _nlim tuint)
                                                                (Etempvar _n tuint)
                                                                tint) tbool))
                                                          (Sset _t'17
                                                            (Econst_int (Int.repr 0) tint)))
                                                        (Scall None
                                                          (Evar _gp_assume 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Etempvar _t'17 tint) ::
                                                           nil)))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _gp_assume 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Ebinop Ole
                                                             (Etempvar _aout tuint)
                                                             (Ebinop Oshl
                                                               (Econst_int (Int.repr 1) tuint)
                                                               (Econst_int (Int.repr 20) tint)
                                                               tuint) tint) ::
                                                           nil))
                                                        (Ssequence
                                                          (Sset _lim
                                                            (Etempvar _nlim tuint))
                                                          (Ssequence
                                                            (Sset _ain
                                                              (Ebinop Osub
                                                                (Etempvar _lim tuint)
                                                                (Etempvar _pos tuint)
                                                                tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'18)
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
                                                                  (Etempvar _t'18 (tptr tuchar))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'19)
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
                                                                    (Etempvar _t'19 (tptr tuchar))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'20
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'20 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 200) tint)
                                                                    tint)
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _in_null tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'21
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _nin
                                                                    (Etempvar _t'21 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 200) tint)
                                                                    tint)
                                                                    (Sset _t'22
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _out_null tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'22
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _nout
                                                                    (Etempvar _t'22 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _nin tint)
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    (tptr tvoid)))
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (tptr tvoid))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'23 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint)
                                                                    (Etempvar _ain tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _nout tint)
                                                                    (Sset _t'24
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    (tptr tvoid)))
                                                                    (Sset _t'24
                                                                    (Ecast
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (tptr tvoid))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar))
                                                                    (Etempvar _t'24 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint)
                                                                    (Etempvar _aout tuint))
                                                                    (Ssequence
                                                                    (Sset _tin
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _tout
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _reset
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 200) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'25)
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
                                                                    (Etempvar _t'25 tint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 210) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _inflateSync 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'26 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'27
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'27 tint)
                                                                    (Sset _t'28
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sifthenelse (Etempvar _t'28 tint)
                                                                    (Sset _t'29
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'29
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
                                                                    ((Etempvar _t'29 tint) ::
                                                                    nil))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 220) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _dl tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'30)
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
                                                                    (Sset _r
                                                                    (Etempvar _t'30 tint)))
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
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'72
                                                                    (Evar _dl tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _t'72 tuint)
                                                                    (Econst_int (Int.repr 32768) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'65
                                                                    (Evar _dl tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _t'65 tuint)
                                                                    (Etempvar _aout tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'31)
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
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'31 tint)))
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
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'68
                                                                    (Evar _dl tuint))
                                                                    (Ssequence
                                                                    (Sset _t'69
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'70
                                                                    (Evar _dl tuint))
                                                                    (Ssequence
                                                                    (Sset _t'71
                                                                    (Evar _dl tuint))
                                                                    (Scall (Some _t'32)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Etempvar _t'68 tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'69 (tptr tuchar))
                                                                    (Etempvar _t'70 tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _t'71 tuint)
                                                                    tuint) ::
                                                                    nil))))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'32 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'66
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'67
                                                                    (Evar _dl tuint))
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'66 (tptr tuchar)) ::
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Etempvar _t'67 tuint) ::
                                                                    nil)))))))
                                                                    Sskip))))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 230) tint)
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
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Etempvar _aout tuint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'33 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'34
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'34
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'34 tint)
                                                                    (Sset _t'35
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'35
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sifthenelse (Etempvar _t'35 tint)
                                                                    (Sset _t'36
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'36
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
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
                                                                    ((Etempvar _t'36 tint) ::
                                                                    nil))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 235) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'37)
                                                                    (Evar _inflatePrime 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _arg tuint)
                                                                    tint) ::
                                                                    (Etempvar _flush tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'37 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'38
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'38
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'38 tint) ::
                                                                    nil))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 240) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'39)
                                                                    (Evar _inflateReset 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'39 tint)))
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
                                                                    (Sset _reset
                                                                    (Econst_int (Int.repr 1) tint))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 245) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'40)
                                                                    (Evar _inflateReset2 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _arg tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'40 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'41)
                                                                    (Evar _inflate_wbits_ok 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ecast
                                                                    (Etempvar _arg tuint)
                                                                    tint) ::
                                                                    nil))
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
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Etempvar _t'41 tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'42
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'42 tint) ::
                                                                    nil)))
                                                                    (Sset _reset
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 250) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'43)
                                                                    (Evar _inflateValidate 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Ecast
                                                                    (Etempvar _arg tuint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'43 tint)))
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
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 252) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _inflateMark 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil)
                                                                    tlong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 254) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _inflateCodesUsed 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'44)
                                                                    (Evar _inflateSyncPoint 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    nil))
                                                                    (Sset _r
                                                                    (Etempvar _t'44 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'45
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'45
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'45 tint) ::
                                                                    nil))))))))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'64
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _t'64 tuint)
                                                                    (Etempvar _ain tuint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Ole
                                                                    (Etempvar _t'63 tuint)
                                                                    (Etempvar _aout tuint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sset _used
                                                                    (Ebinop Osub
                                                                    (Etempvar _ain tuint)
                                                                    (Etempvar _t'62 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'61
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Sset _made
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _t'61 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _nin tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'60 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'59 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ib (tptr tuchar))
                                                                    (Etempvar _used tuint)
                                                                    (tptr tuchar))
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _nout tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'58 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint) ::
                                                                    nil)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _made tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'57 (tptr tuchar))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Etempvar _made tuint)
                                                                    (tptr tuchar))
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'46)
                                                                    (Evar _bytes_same 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _ib (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _ain tuint) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'46 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall (Some _t'47)
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
                                                                    (Etempvar _t'56 (tptr tuchar))
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
                                                                    ((Etempvar _t'47 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _reset tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'54 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Sset _t'48
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'55 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'48
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'48 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _op tuchar)
                                                                    (Econst_int (Int.repr 200) tint)
                                                                    tint)
                                                                    (Sset _t'49
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'49
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'49 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'53 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _tin tulong)
                                                                    (Etempvar _used tuint)
                                                                    tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'52 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _tout tulong)
                                                                    (Etempvar _made tuint)
                                                                    tulong)
                                                                    tint) ::
                                                                    nil))))
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Sset _pos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _used tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _reset tint)
                                                                    (Sset _lim
                                                                    (Etempvar _pos tuint))
                                                                    Sskip)
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
                                                                    (Sset _t'51
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'51 (tptr tuchar)) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _stop tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)))))))))))))))))))))))))))))))))))))))))
                                  Sskip)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'50)
                                      (Evar _inflateEnd (Tfunction
                                                          ((tptr (Tstruct _z_stream_s noattr)) ::
                                                           nil) tint
                                                          cc_default))
                                      ((Eaddrof
                                         (Evar _s (Tstruct _z_stream_s noattr))
                                         (tptr (Tstruct _z_stream_s noattr))) ::
                                       nil))
                                    (Sset _r (Etempvar _t'50 tint)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _gp_assert (Tfunction
                                                         (tint :: nil) tvoid
                                                         cc_default))
                                      ((Ebinop Oeq (Etempvar _r tint)
                                         (Econst_int (Int.repr 0) tint) tint) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _quickproof_free (Tfunction
                                                                 ((tptr tvoid) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                        ((Etempvar _src (tptr tuchar)) ::
                                         nil))
                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))
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
     cc_default)) :: (___stringlit_x_inflate_buffers_1, Gvar v___stringlit_x_inflate_buffers_1) ::
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
 (_inflateSync,
   Gfun(External (EF_external "inflateSync"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_inflateReset,
   Gfun(External (EF_external "inflateReset"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_inflateReset2,
   Gfun(External (EF_external "inflateReset2"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_inflatePrime,
   Gfun(External (EF_external "inflatePrime"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: tint :: nil) tint
     cc_default)) ::
 (_inflateMark,
   Gfun(External (EF_external "inflateMark"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tlong cc_default)) ::
 (_inflateInit2_,
   Gfun(External (EF_external "inflateInit2_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: (tptr tschar) :: tint ::
      nil) tint cc_default)) ::
 (_inflateSyncPoint,
   Gfun(External (EF_external "inflateSyncPoint"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_inflateValidate,
   Gfun(External (EF_external "inflateValidate"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_inflateCodesUsed,
   Gfun(External (EF_external "inflateCodesUsed"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tulong cc_default)) ::
 (_bytes_same, Gfun(Internal f_bytes_same)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_exact_copy, Gfun(Internal f_exact_copy)) ::
 (_exact_space, Gfun(Internal f_exact_space)) ::
 (_inflate_wbits_ok, Gfun(Internal f_inflate_wbits_ok)) ::
 (_stream_defaults, Gfun(Internal f_stream_defaults)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _inflateCodesUsed :: _inflateValidate :: _inflateSyncPoint ::
 _inflateInit2_ :: _inflateMark :: _inflatePrime :: _inflateReset2 ::
 _inflateReset :: _inflateSync :: _inflateGetDictionary ::
 _inflateSetDictionary :: _inflateEnd :: _inflate :: _gp_assume ::
 _gp_assert :: _nondet_bytes :: _nondet_u32 :: _nondet_u8 ::
 _quickproof_free :: _quickproof_malloc :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.



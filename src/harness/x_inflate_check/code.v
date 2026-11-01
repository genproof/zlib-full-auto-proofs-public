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
  Definition source_file := "harness/x_inflate_check.c".
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
Definition ___stringlit_x_inflate_check_1 : ident := $"__stringlit_x_inflate_check_1".
Definition _a : ident := $"a".
Definition _adler : ident := $"adler".
Definition _adler0 : ident := $"adler0".
Definition _ain : ident := $"ain".
Definition _aout : ident := $"aout".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _b : ident := $"b".
Definition _be32 : ident := $"be32".
Definition _buf : ident := $"buf".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _c : ident := $"c".
Definition _d : ident := $"d".
Definition _data_type : ident := $"data_type".
Definition _exact_copy : ident := $"exact_copy".
Definition _exact_space : ident := $"exact_space".
Definition _flush : ident := $"flush".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _gz : ident := $"gz".
Definition _i : ident := $"i".
Definition _ib : ident := $"ib".
Definition _inflate : ident := $"inflate".
Definition _inflateEnd : ident := $"inflateEnd".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _internal_state : ident := $"internal_state".
Definition _k : ident := $"k".
Definition _le32 : ident := $"le32".
Definition _made : ident := $"made".
Definition _main : ident := $"main".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nlim : ident := $"nlim".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _ob : ident := $"ob".
Definition _opaque : ident := $"opaque".
Definition _osnap : ident := $"osnap".
Definition _p : ident := $"p".
Definition _pos : ident := $"pos".
Definition _q : ident := $"q".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _r : ident := $"r".
Definition _ra : ident := $"ra".
Definition _raw : ident := $"raw".
Definition _rc : ident := $"rc".
Definition _ref_adler32 : ident := $"ref_adler32".
Definition _ref_crc32 : ident := $"ref_crc32".
Definition _ref_crc_byte : ident := $"ref_crc_byte".
Definition _reserved : ident := $"reserved".
Definition _s : ident := $"s".
Definition _s1 : ident := $"s1".
Definition _s2 : ident := $"s2".
Definition _snap : ident := $"snap".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _stop : ident := $"stop".
Definition _stream_defaults : ident := $"stream_defaults".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _tout : ident := $"tout".
Definition _used : ident := $"used".
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_x_inflate_check_1 := {|
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

Definition f_ref_crc_byte := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_c, tulong) :: (_b, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c (Ebinop Oxor (Etempvar _c tulong) (Etempvar _b tuchar) tulong))
  (Ssequence
    (Ssequence
      (Sset _k (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _k tint)
                         (Econst_int (Int.repr 8) tint) tint)
            Sskip
            Sbreak)
          (Sifthenelse (Ebinop Oand (Etempvar _c tulong)
                         (Econst_int (Int.repr 1) tint) tulong)
            (Sset _c
              (Ebinop Oxor
                (Ebinop Oshr (Etempvar _c tulong)
                  (Econst_int (Int.repr 1) tint) tulong)
                (Econst_long (Int64.repr 3988292384) tulong) tulong))
            (Sset _c
              (Ebinop Oshr (Etempvar _c tulong)
                (Econst_int (Int.repr 1) tint) tulong))))
        (Sset _k
          (Ebinop Oadd (Etempvar _k tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _c tulong)))))
|}.

Definition f_ref_crc32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_c, tulong) :: (_buf, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tulong) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Ebinop Oand (Eunop Onotint (Etempvar _c tulong) tulong)
      (Econst_int (Int.repr (-1)) tuint) tulong))
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
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar))
              (Scall (Some _t'1)
                (Evar _ref_crc_byte (Tfunction (tulong :: tuchar :: nil)
                                      tulong cc_default))
                ((Etempvar _c tulong) :: (Etempvar _t'2 tuchar) :: nil)))
            (Sset _c (Etempvar _t'1 tulong))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Ebinop Oand (Eunop Onotint (Etempvar _c tulong) tulong)
                     (Econst_int (Int.repr (-1)) tuint) tulong)))))
|}.

Definition f_be32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 0) tint)
        (tptr tuchar)) tuchar))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _p (tptr tuchar))
          (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _p (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oor
                         (Ebinop Oor
                           (Ebinop Oor
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'1 tuchar) tulong)
                               (Econst_int (Int.repr 24) tint) tulong)
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'2 tuchar) tulong)
                               (Econst_int (Int.repr 16) tint) tulong)
                             tulong)
                           (Ebinop Oshl (Ecast (Etempvar _t'3 tuchar) tulong)
                             (Econst_int (Int.repr 8) tint) tulong) tulong)
                         (Etempvar _t'4 tuchar) tulong)))))))
|}.

Definition f_le32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tuchar) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 3) tint)
        (tptr tuchar)) tuchar))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _p (tptr tuchar))
          (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Etempvar _p (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oor
                         (Ebinop Oor
                           (Ebinop Oor
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'1 tuchar) tulong)
                               (Econst_int (Int.repr 24) tint) tulong)
                             (Ebinop Oshl
                               (Ecast (Etempvar _t'2 tuchar) tulong)
                               (Econst_int (Int.repr 16) tint) tulong)
                             tulong)
                           (Ebinop Oshl (Ecast (Etempvar _t'3 tuchar) tulong)
                             (Econst_int (Int.repr 8) tint) tulong) tulong)
                         (Etempvar _t'4 tuchar) tulong)))))))
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

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_s, (Tstruct _z_stream_s noattr)) ::
              (_osnap, (tptr tuchar)) :: nil);
  fn_temps := ((_wbits, tint) :: (_n, tuint) :: (_src, (tptr tuchar)) ::
               (_adler0, tulong) :: (_r, tint) :: (_raw, tint) ::
               (_gz, tint) :: (_pos, tuint) :: (_tout, tulong) ::
               (_ra, tulong) :: (_rc, tulong) :: (_nlim, tuint) ::
               (_aout, tuint) :: (_flush, tint) :: (_stop, tuchar) ::
               (_ain, tuint) :: (_ib, (tptr tuchar)) ::
               (_ob, (tptr tuchar)) :: (_used, tuint) :: (_made, tuint) ::
               (_t'27, tint) :: (_t'26, tulong) :: (_t'25, tulong) ::
               (_t'24, tulong) :: (_t'23, tint) :: (_t'22, tint) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tulong) ::
               (_t'18, tulong) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, (tptr tuchar)) :: (_t'14, (tptr tuchar)) ::
               (_t'13, tint) :: (_t'12, tuchar) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, (tptr tvoid)) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'46, tuchar) :: (_t'45, tuchar) ::
               (_t'44, tuint) :: (_t'43, tuint) :: (_t'42, tulong) ::
               (_t'41, tuchar) :: (_t'40, tuchar) :: (_t'39, tuchar) ::
               (_t'38, tuchar) :: (_t'37, tulong) :: (_t'36, tuchar) ::
               (_t'35, tuchar) :: (_t'34, tuchar) :: (_t'33, tuchar) ::
               (_t'32, tulong) :: (_t'31, tulong) :: (_t'30, tulong) ::
               (_t'29, tulong) :: (_t'28, (tptr tuchar)) :: nil);
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
                  (Sset _adler0
                    (Efield (Evar _s (Tstruct _z_stream_s noattr)) _adler
                      tulong))
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
                         (Evar ___stringlit_x_inflate_check_1 (tarray tschar 6)) ::
                         (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong)
                           tint) :: nil))
                      (Sset _r (Etempvar _t'4 tint)))
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
                        (Sset _raw
                          (Ebinop Olt (Etempvar _wbits tint)
                            (Econst_int (Int.repr 0) tint) tint))
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Eunop Onotbool (Etempvar _raw tint)
                                           tint)
                              (Ssequence
                                (Sifthenelse (Ebinop Oge
                                               (Etempvar _wbits tint)
                                               (Econst_int (Int.repr 16) tint)
                                               tint)
                                  (Sset _t'6
                                    (Ecast
                                      (Ebinop Olt (Etempvar _wbits tint)
                                        (Econst_int (Int.repr 32) tint) tint)
                                      tbool))
                                  (Sset _t'6 (Econst_int (Int.repr 0) tint)))
                                (Sifthenelse (Etempvar _t'6 tint)
                                  (Sset _t'5
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oge
                                                     (Etempvar _wbits tint)
                                                     (Econst_int (Int.repr 32) tint)
                                                     tint)
                                        (Sset _t'7
                                          (Ecast
                                            (Ebinop Oge (Etempvar _n tuint)
                                              (Econst_int (Int.repr 2) tint)
                                              tint) tbool))
                                        (Sset _t'7
                                          (Econst_int (Int.repr 0) tint)))
                                      (Sifthenelse (Etempvar _t'7 tint)
                                        (Ssequence
                                          (Sset _t'46
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _src (tptr tuchar))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuchar)) tuchar))
                                          (Sset _t'8
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _t'46 tuchar)
                                                (Econst_int (Int.repr 31) tint)
                                                tint) tbool)))
                                        (Sset _t'8
                                          (Econst_int (Int.repr 0) tint))))
                                    (Sifthenelse (Etempvar _t'8 tint)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'45
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _src (tptr tuchar))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuchar)) tuchar))
                                            (Sset _t'5
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _t'45 tuchar)
                                                  (Econst_int (Int.repr 139) tint)
                                                  tint) tbool)))
                                          (Sset _t'5
                                            (Ecast (Etempvar _t'5 tint)
                                              tbool)))
                                        (Sset _t'5
                                          (Ecast (Etempvar _t'5 tint) tbool)))
                                      (Ssequence
                                        (Sset _t'5
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tbool))
                                        (Sset _t'5
                                          (Ecast (Etempvar _t'5 tint) tbool)))))))
                              (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                            (Sset _gz (Etempvar _t'5 tint)))
                          (Ssequence
                            (Sset _pos (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sset _tout
                                (Ecast (Econst_int (Int.repr 0) tint) tulong))
                              (Ssequence
                                (Sset _ra
                                  (Ecast (Econst_int (Int.repr 1) tint)
                                    tulong))
                                (Ssequence
                                  (Sset _rc
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        Sskip
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'9)
                                              (Evar _nondet_u32 (Tfunction
                                                                  nil tuint
                                                                  cc_default))
                                              nil)
                                            (Sset _nlim
                                              (Etempvar _t'9 tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'10)
                                                (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                nil)
                                              (Sset _aout
                                                (Etempvar _t'10 tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'11)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil)
                                                (Sset _flush
                                                  (Ecast
                                                    (Etempvar _t'11 tuint)
                                                    tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'12)
                                                    (Evar _nondet_u8 
                                                    (Tfunction nil tuchar
                                                      cc_default)) nil)
                                                  (Sset _stop
                                                    (Ecast
                                                      (Etempvar _t'12 tuchar)
                                                      tuchar)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Ole
                                                                   (Etempvar _pos tuint)
                                                                   (Etempvar _nlim tuint)
                                                                   tint)
                                                      (Sset _t'13
                                                        (Ecast
                                                          (Ebinop Ole
                                                            (Etempvar _nlim tuint)
                                                            (Etempvar _n tuint)
                                                            tint) tbool))
                                                      (Sset _t'13
                                                        (Econst_int (Int.repr 0) tint)))
                                                    (Scall None
                                                      (Evar _gp_assume 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Etempvar _t'13 tint) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _gp_assume 
                                                      (Tfunction
                                                        (tint :: nil) tvoid
                                                        cc_default))
                                                      ((Ebinop Ole
                                                         (Etempvar _aout tuint)
                                                         (Ebinop Oshl
                                                           (Econst_int (Int.repr 1) tuint)
                                                           (Econst_int (Int.repr 20) tint)
                                                           tuint) tint) ::
                                                       nil))
                                                    (Ssequence
                                                      (Sset _ain
                                                        (Ebinop Osub
                                                          (Etempvar _nlim tuint)
                                                          (Etempvar _pos tuint)
                                                          tuint))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'14)
                                                            (Evar _exact_copy 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               tuint :: nil)
                                                              (tptr tuchar)
                                                              cc_default))
                                                            ((Ebinop Oadd
                                                               (Etempvar _src (tptr tuchar))
                                                               (Etempvar _pos tuint)
                                                               (tptr tuchar)) ::
                                                             (Etempvar _ain tuint) ::
                                                             nil))
                                                          (Sset _ib
                                                            (Etempvar _t'14 (tptr tuchar))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'15)
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
                                                              (Etempvar _t'15 (tptr tuchar))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _ib (tptr tuchar))
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                  tint)
                                                                (Sset _t'16
                                                                  (Econst_int (Int.repr 1) tint))
                                                                (Sset _t'16
                                                                  (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ob (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                              (Sifthenelse (Etempvar _t'16 tint)
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
                                                                    (Scall (Some _t'17)
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
                                                                    (Etempvar _t'17 tint)))
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
                                                                    (Sset _t'44
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Sset _used
                                                                    (Ebinop Osub
                                                                    (Etempvar _ain tuint)
                                                                    (Etempvar _t'44 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Efield
                                                                    (Evar _s (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Sset _made
                                                                    (Ebinop Osub
                                                                    (Etempvar _aout tuint)
                                                                    (Etempvar _t'43 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _pos
                                                                    (Ebinop Oadd
                                                                    (Etempvar _pos tuint)
                                                                    (Etempvar _used tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _tout
                                                                    (Ebinop Oadd
                                                                    (Etempvar _tout tulong)
                                                                    (Etempvar _made tuint)
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'18)
                                                                    (Evar _ref_adler32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _ra tulong) ::
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Etempvar _made tuint) ::
                                                                    nil))
                                                                    (Sset _ra
                                                                    (Etempvar _t'18 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'19)
                                                                    (Evar _ref_crc32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _rc tulong) ::
                                                                    (Etempvar _ob (tptr tuchar)) ::
                                                                    (Etempvar _made tuint) ::
                                                                    nil))
                                                                    (Sset _rc
                                                                    (Etempvar _t'19 tulong)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _raw tint)
                                                                    (Ssequence
                                                                    (Sset _t'42
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
                                                                    (Etempvar _t'42 tulong)
                                                                    (Etempvar _adler0 tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _tout tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sifthenelse (Etempvar _gz tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'40 tuchar)
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'41 tuchar)
                                                                    (Econst_int (Int.repr 139) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'20
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'20 tint)
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'39 tuchar)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'21
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'21 tint)
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'22
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'38 tuchar)
                                                                    (Econst_int (Int.repr 224) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'22
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'22 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'37
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
                                                                    (Etempvar _t'37 tulong)
                                                                    (Etempvar _rc tulong)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'35 tuchar)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Ebinop Oshr
                                                                    (Etempvar _t'36 tuchar)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'23
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'23 tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
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
                                                                    (Ebinop Omod
                                                                    (Ebinop Oor
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'33 tuchar)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Etempvar _t'34 tuchar)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Sset _t'32
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
                                                                    (Etempvar _t'32 tulong)
                                                                    (Etempvar _ra tulong)
                                                                    tint) ::
                                                                    nil))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _r tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _raw tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'27
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'27 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'31
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
                                                                    (Etempvar _t'31 tulong)
                                                                    (Etempvar _tout tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _gz tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oge
                                                                    (Etempvar _pos tuint)
                                                                    (Econst_int (Int.repr 18) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
                                                                    (Evar _le32 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'24 tulong)
                                                                    (Etempvar _rc tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'25)
                                                                    (Evar _le32 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'25 tulong)
                                                                    (Ebinop Oand
                                                                    (Etempvar _tout tulong)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'30
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
                                                                    (Etempvar _t'30 tulong)
                                                                    (Etempvar _rc tulong)
                                                                    tint) ::
                                                                    nil))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oge
                                                                    (Etempvar _pos tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _be32 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _src (tptr tuchar))
                                                                    (Etempvar _pos tuint)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuchar)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'26 tulong)
                                                                    (Etempvar _ra tulong)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'29
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
                                                                    (Etempvar _t'29 tulong)
                                                                    (Etempvar _ra tulong)
                                                                    tint) ::
                                                                    nil)))))))
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
                                                                    (Sset _t'28
                                                                    (Evar _osnap (tptr tuchar)))
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'28 (tptr tuchar)) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _stop tuchar)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)))))))))))))))))))))))))))))
                                      Sskip)
                                    (Ssequence
                                      (Scall None
                                        (Evar _inflateEnd (Tfunction
                                                            ((tptr (Tstruct _z_stream_s noattr)) ::
                                                             nil) tint
                                                            cc_default))
                                        ((Eaddrof
                                           (Evar _s (Tstruct _z_stream_s noattr))
                                           (tptr (Tstruct _z_stream_s noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _quickproof_free (Tfunction
                                                                   ((tptr tvoid) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                          ((Etempvar _src (tptr tuchar)) ::
                                           nil))
                                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))
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
     cc_default)) :: (___stringlit_x_inflate_check_1, Gvar v___stringlit_x_inflate_check_1) ::
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
 (_inflateInit2_,
   Gfun(External (EF_external "inflateInit2_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: (tptr tschar) :: tint ::
      nil) tint cc_default)) ::
 (_ref_adler32, Gfun(Internal f_ref_adler32)) ::
 (_ref_crc_byte, Gfun(Internal f_ref_crc_byte)) ::
 (_ref_crc32, Gfun(Internal f_ref_crc32)) ::
 (_be32, Gfun(Internal f_be32)) :: (_le32, Gfun(Internal f_le32)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_exact_copy, Gfun(Internal f_exact_copy)) ::
 (_exact_space, Gfun(Internal f_exact_space)) ::
 (_stream_defaults, Gfun(Internal f_stream_defaults)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _inflateInit2_ :: _inflateEnd :: _inflate :: _gp_assume ::
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



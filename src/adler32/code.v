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
  Definition source_file := "adler32.c".
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
Definition _adler : ident := $"adler".
Definition _adler1 : ident := $"adler1".
Definition _adler2 : ident := $"adler2".
Definition _adler32 : ident := $"adler32".
Definition _adler32_combine : ident := $"adler32_combine".
Definition _adler32_combine64 : ident := $"adler32_combine64".
Definition _adler32_combine_ : ident := $"adler32_combine_".
Definition _adler32_z : ident := $"adler32_z".
Definition _buf : ident := $"buf".
Definition _len : ident := $"len".
Definition _len2 : ident := $"len2".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _rem : ident := $"rem".
Definition _sum1 : ident := $"sum1".
Definition _sum2 : ident := $"sum2".
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_adler32_z := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_adler, tulong) :: (_buf, (tptr tuchar)) ::
                (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_sum2, tulong) :: (_n, tuint) :: (_t'5, (tptr tuchar)) ::
               (_t'4, tulong) :: (_t'3, tuint) :: (_t'2, (tptr tuchar)) ::
               (_t'1, tulong) :: (_t'40, tuchar) :: (_t'39, tuchar) ::
               (_t'38, tuchar) :: (_t'37, tuchar) :: (_t'36, tuchar) ::
               (_t'35, tuchar) :: (_t'34, tuchar) :: (_t'33, tuchar) ::
               (_t'32, tuchar) :: (_t'31, tuchar) :: (_t'30, tuchar) ::
               (_t'29, tuchar) :: (_t'28, tuchar) :: (_t'27, tuchar) ::
               (_t'26, tuchar) :: (_t'25, tuchar) :: (_t'24, tuchar) ::
               (_t'23, tuchar) :: (_t'22, tuchar) :: (_t'21, tuchar) ::
               (_t'20, tuchar) :: (_t'19, tuchar) :: (_t'18, tuchar) ::
               (_t'17, tuchar) :: (_t'16, tuchar) :: (_t'15, tuchar) ::
               (_t'14, tuchar) :: (_t'13, tuchar) :: (_t'12, tuchar) ::
               (_t'11, tuchar) :: (_t'10, tuchar) :: (_t'9, tuchar) ::
               (_t'8, tuchar) :: (_t'7, tuchar) :: (_t'6, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _sum2
    (Ebinop Oand
      (Ebinop Oshr (Etempvar _adler tulong) (Econst_int (Int.repr 16) tint)
        tulong) (Econst_int (Int.repr 65535) tint) tulong))
  (Ssequence
    (Sset _adler
      (Ebinop Oand (Etempvar _adler tulong)
        (Econst_int (Int.repr 65535) tint) tulong))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _buf (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Econst_long (Int64.repr 1) tlong)))
        Sskip)
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _len tulong)
                       (Econst_int (Int.repr 1) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'40
                (Ederef
                  (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                    (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
              (Sset _adler
                (Ebinop Oadd (Etempvar _adler tulong) (Etempvar _t'40 tuchar)
                  tulong)))
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _adler tulong)
                             (Econst_int (Int.repr 65521) tuint) tint)
                (Sset _adler
                  (Ebinop Osub (Etempvar _adler tulong)
                    (Econst_int (Int.repr 65521) tuint) tulong))
                Sskip)
              (Ssequence
                (Sset _sum2
                  (Ebinop Oadd (Etempvar _sum2 tulong)
                    (Etempvar _adler tulong) tulong))
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _sum2 tulong)
                                 (Econst_int (Int.repr 65521) tuint) tint)
                    (Sset _sum2
                      (Ebinop Osub (Etempvar _sum2 tulong)
                        (Econst_int (Int.repr 65521) tuint) tulong))
                    Sskip)
                  (Sreturn (Some (Ebinop Oor (Etempvar _adler tulong)
                                   (Ebinop Oshl (Etempvar _sum2 tulong)
                                     (Econst_int (Int.repr 16) tint) tulong)
                                   tulong)))))))
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _buf (tptr tuchar))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Econst_long (Int64.repr 1) tlong)))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _len tulong)
                           (Econst_int (Int.repr 16) tint) tint)
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'1 (Etempvar _len tulong))
                        (Sset _len
                          (Ebinop Osub (Etempvar _t'1 tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))
                      (Sifthenelse (Etempvar _t'1 tulong) Sskip Sbreak))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'2 (Etempvar _buf (tptr tuchar)))
                          (Sset _buf
                            (Ebinop Oadd (Etempvar _t'2 (tptr tuchar))
                              (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                        (Ssequence
                          (Sset _t'39
                            (Ederef (Etempvar _t'2 (tptr tuchar)) tuchar))
                          (Sset _adler
                            (Ebinop Oadd (Etempvar _adler tulong)
                              (Etempvar _t'39 tuchar) tulong))))
                      (Sset _sum2
                        (Ebinop Oadd (Etempvar _sum2 tulong)
                          (Etempvar _adler tulong) tulong))))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _adler tulong)
                                 (Econst_int (Int.repr 65521) tuint) tint)
                    (Sset _adler
                      (Ebinop Osub (Etempvar _adler tulong)
                        (Econst_int (Int.repr 65521) tuint) tulong))
                    Sskip)
                  (Ssequence
                    (Sset _sum2
                      (Ebinop Omod (Etempvar _sum2 tulong)
                        (Econst_int (Int.repr 65521) tuint) tulong))
                    (Sreturn (Some (Ebinop Oor (Etempvar _adler tulong)
                                     (Ebinop Oshl (Etempvar _sum2 tulong)
                                       (Econst_int (Int.repr 16) tint)
                                       tulong) tulong))))))
              Sskip)
            (Ssequence
              (Swhile
                (Ebinop Oge (Etempvar _len tulong)
                  (Econst_int (Int.repr 5552) tint) tint)
                (Ssequence
                  (Sset _len
                    (Ebinop Osub (Etempvar _len tulong)
                      (Econst_int (Int.repr 5552) tint) tulong))
                  (Ssequence
                    (Sset _n
                      (Ebinop Odiv (Econst_int (Int.repr 5552) tint)
                        (Econst_int (Int.repr 16) tint) tint))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'38
                                (Ederef
                                  (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr tuchar)) tuchar))
                              (Sset _adler
                                (Ebinop Oadd (Etempvar _adler tulong)
                                  (Etempvar _t'38 tuchar) tulong)))
                            (Sset _sum2
                              (Ebinop Oadd (Etempvar _sum2 tulong)
                                (Etempvar _adler tulong) tulong)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'37
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _buf (tptr tuchar))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 0) tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr tuchar)) tuchar))
                                (Sset _adler
                                  (Ebinop Oadd (Etempvar _adler tulong)
                                    (Etempvar _t'37 tuchar) tulong)))
                              (Sset _sum2
                                (Ebinop Oadd (Etempvar _sum2 tulong)
                                  (Etempvar _adler tulong) tulong)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'36
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _buf (tptr tuchar))
                                        (Ebinop Oadd
                                          (Econst_int (Int.repr 0) tint)
                                          (Econst_int (Int.repr 2) tint)
                                          tint) (tptr tuchar)) tuchar))
                                  (Sset _adler
                                    (Ebinop Oadd (Etempvar _adler tulong)
                                      (Etempvar _t'36 tuchar) tulong)))
                                (Sset _sum2
                                  (Ebinop Oadd (Etempvar _sum2 tulong)
                                    (Etempvar _adler tulong) tulong)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'35
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _buf (tptr tuchar))
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Econst_int (Int.repr 0) tint)
                                              (Econst_int (Int.repr 2) tint)
                                              tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (tptr tuchar)) tuchar))
                                    (Sset _adler
                                      (Ebinop Oadd (Etempvar _adler tulong)
                                        (Etempvar _t'35 tuchar) tulong)))
                                  (Sset _sum2
                                    (Ebinop Oadd (Etempvar _sum2 tulong)
                                      (Etempvar _adler tulong) tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'34
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _buf (tptr tuchar))
                                            (Ebinop Oadd
                                              (Econst_int (Int.repr 0) tint)
                                              (Econst_int (Int.repr 4) tint)
                                              tint) (tptr tuchar)) tuchar))
                                      (Sset _adler
                                        (Ebinop Oadd (Etempvar _adler tulong)
                                          (Etempvar _t'34 tuchar) tulong)))
                                    (Sset _sum2
                                      (Ebinop Oadd (Etempvar _sum2 tulong)
                                        (Etempvar _adler tulong) tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'33
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _buf (tptr tuchar))
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 4) tint)
                                                  tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tuchar)) tuchar))
                                        (Sset _adler
                                          (Ebinop Oadd
                                            (Etempvar _adler tulong)
                                            (Etempvar _t'33 tuchar) tulong)))
                                      (Sset _sum2
                                        (Ebinop Oadd (Etempvar _sum2 tulong)
                                          (Etempvar _adler tulong) tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'32
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _buf (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 0) tint)
                                                    (Econst_int (Int.repr 4) tint)
                                                    tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tuchar))
                                              tuchar))
                                          (Sset _adler
                                            (Ebinop Oadd
                                              (Etempvar _adler tulong)
                                              (Etempvar _t'32 tuchar) tulong)))
                                        (Sset _sum2
                                          (Ebinop Oadd
                                            (Etempvar _sum2 tulong)
                                            (Etempvar _adler tulong) tulong)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'31
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _buf (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Econst_int (Int.repr 0) tint)
                                                        (Econst_int (Int.repr 4) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar))
                                            (Sset _adler
                                              (Ebinop Oadd
                                                (Etempvar _adler tulong)
                                                (Etempvar _t'31 tuchar)
                                                tulong)))
                                          (Sset _sum2
                                            (Ebinop Oadd
                                              (Etempvar _sum2 tulong)
                                              (Etempvar _adler tulong)
                                              tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'30
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _buf (tptr tuchar))
                                                    (Econst_int (Int.repr 8) tint)
                                                    (tptr tuchar)) tuchar))
                                              (Sset _adler
                                                (Ebinop Oadd
                                                  (Etempvar _adler tulong)
                                                  (Etempvar _t'30 tuchar)
                                                  tulong)))
                                            (Sset _sum2
                                              (Ebinop Oadd
                                                (Etempvar _sum2 tulong)
                                                (Etempvar _adler tulong)
                                                tulong)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'29
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _buf (tptr tuchar))
                                                      (Ebinop Oadd
                                                        (Econst_int (Int.repr 8) tint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint) (tptr tuchar))
                                                    tuchar))
                                                (Sset _adler
                                                  (Ebinop Oadd
                                                    (Etempvar _adler tulong)
                                                    (Etempvar _t'29 tuchar)
                                                    tulong)))
                                              (Sset _sum2
                                                (Ebinop Oadd
                                                  (Etempvar _sum2 tulong)
                                                  (Etempvar _adler tulong)
                                                  tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'28
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _buf (tptr tuchar))
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 8) tint)
                                                          (Econst_int (Int.repr 2) tint)
                                                          tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sset _adler
                                                    (Ebinop Oadd
                                                      (Etempvar _adler tulong)
                                                      (Etempvar _t'28 tuchar)
                                                      tulong)))
                                                (Sset _sum2
                                                  (Ebinop Oadd
                                                    (Etempvar _sum2 tulong)
                                                    (Etempvar _adler tulong)
                                                    tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'27
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _buf (tptr tuchar))
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Econst_int (Int.repr 8) tint)
                                                              (Econst_int (Int.repr 2) tint)
                                                              tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _adler
                                                      (Ebinop Oadd
                                                        (Etempvar _adler tulong)
                                                        (Etempvar _t'27 tuchar)
                                                        tulong)))
                                                  (Sset _sum2
                                                    (Ebinop Oadd
                                                      (Etempvar _sum2 tulong)
                                                      (Etempvar _adler tulong)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'26
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _buf (tptr tuchar))
                                                            (Ebinop Oadd
                                                              (Econst_int (Int.repr 8) tint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Sset _adler
                                                        (Ebinop Oadd
                                                          (Etempvar _adler tulong)
                                                          (Etempvar _t'26 tuchar)
                                                          tulong)))
                                                    (Sset _sum2
                                                      (Ebinop Oadd
                                                        (Etempvar _sum2 tulong)
                                                        (Etempvar _adler tulong)
                                                        tulong)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'25
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _buf (tptr tuchar))
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Sset _adler
                                                          (Ebinop Oadd
                                                            (Etempvar _adler tulong)
                                                            (Etempvar _t'25 tuchar)
                                                            tulong)))
                                                      (Sset _sum2
                                                        (Ebinop Oadd
                                                          (Etempvar _sum2 tulong)
                                                          (Etempvar _adler tulong)
                                                          tulong)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'24
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _buf (tptr tuchar))
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Sset _adler
                                                            (Ebinop Oadd
                                                              (Etempvar _adler tulong)
                                                              (Etempvar _t'24 tuchar)
                                                              tulong)))
                                                        (Sset _sum2
                                                          (Ebinop Oadd
                                                            (Etempvar _sum2 tulong)
                                                            (Etempvar _adler tulong)
                                                            tulong)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'23
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _buf (tptr tuchar))
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Sset _adler
                                                              (Ebinop Oadd
                                                                (Etempvar _adler tulong)
                                                                (Etempvar _t'23 tuchar)
                                                                tulong)))
                                                          (Sset _sum2
                                                            (Ebinop Oadd
                                                              (Etempvar _sum2 tulong)
                                                              (Etempvar _adler tulong)
                                                              tulong)))
                                                        (Sset _buf
                                                          (Ebinop Oadd
                                                            (Etempvar _buf (tptr tuchar))
                                                            (Econst_int (Int.repr 16) tint)
                                                            (tptr tuchar)))))))))))))))))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Ecast
                                (Ebinop Osub (Etempvar _n tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)
                                tuint))
                            (Sset _n (Etempvar _t'3 tuint)))
                          (Sifthenelse (Etempvar _t'3 tuint) Sskip Sbreak)))
                      (Ssequence
                        (Sset _adler
                          (Ebinop Omod (Etempvar _adler tulong)
                            (Econst_int (Int.repr 65521) tuint) tulong))
                        (Sset _sum2
                          (Ebinop Omod (Etempvar _sum2 tulong)
                            (Econst_int (Int.repr 65521) tuint) tulong)))))))
              (Ssequence
                (Sifthenelse (Etempvar _len tulong)
                  (Ssequence
                    (Swhile
                      (Ebinop Oge (Etempvar _len tulong)
                        (Econst_int (Int.repr 16) tint) tint)
                      (Ssequence
                        (Sset _len
                          (Ebinop Osub (Etempvar _len tulong)
                            (Econst_int (Int.repr 16) tint) tulong))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'22
                                (Ederef
                                  (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr tuchar)) tuchar))
                              (Sset _adler
                                (Ebinop Oadd (Etempvar _adler tulong)
                                  (Etempvar _t'22 tuchar) tulong)))
                            (Sset _sum2
                              (Ebinop Oadd (Etempvar _sum2 tulong)
                                (Etempvar _adler tulong) tulong)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'21
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _buf (tptr tuchar))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 0) tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr tuchar)) tuchar))
                                (Sset _adler
                                  (Ebinop Oadd (Etempvar _adler tulong)
                                    (Etempvar _t'21 tuchar) tulong)))
                              (Sset _sum2
                                (Ebinop Oadd (Etempvar _sum2 tulong)
                                  (Etempvar _adler tulong) tulong)))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'20
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _buf (tptr tuchar))
                                        (Ebinop Oadd
                                          (Econst_int (Int.repr 0) tint)
                                          (Econst_int (Int.repr 2) tint)
                                          tint) (tptr tuchar)) tuchar))
                                  (Sset _adler
                                    (Ebinop Oadd (Etempvar _adler tulong)
                                      (Etempvar _t'20 tuchar) tulong)))
                                (Sset _sum2
                                  (Ebinop Oadd (Etempvar _sum2 tulong)
                                    (Etempvar _adler tulong) tulong)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'19
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _buf (tptr tuchar))
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Econst_int (Int.repr 0) tint)
                                              (Econst_int (Int.repr 2) tint)
                                              tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (tptr tuchar)) tuchar))
                                    (Sset _adler
                                      (Ebinop Oadd (Etempvar _adler tulong)
                                        (Etempvar _t'19 tuchar) tulong)))
                                  (Sset _sum2
                                    (Ebinop Oadd (Etempvar _sum2 tulong)
                                      (Etempvar _adler tulong) tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'18
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _buf (tptr tuchar))
                                            (Ebinop Oadd
                                              (Econst_int (Int.repr 0) tint)
                                              (Econst_int (Int.repr 4) tint)
                                              tint) (tptr tuchar)) tuchar))
                                      (Sset _adler
                                        (Ebinop Oadd (Etempvar _adler tulong)
                                          (Etempvar _t'18 tuchar) tulong)))
                                    (Sset _sum2
                                      (Ebinop Oadd (Etempvar _sum2 tulong)
                                        (Etempvar _adler tulong) tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _buf (tptr tuchar))
                                              (Ebinop Oadd
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 4) tint)
                                                  tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tuchar)) tuchar))
                                        (Sset _adler
                                          (Ebinop Oadd
                                            (Etempvar _adler tulong)
                                            (Etempvar _t'17 tuchar) tulong)))
                                      (Sset _sum2
                                        (Ebinop Oadd (Etempvar _sum2 tulong)
                                          (Etempvar _adler tulong) tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'16
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _buf (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 0) tint)
                                                    (Econst_int (Int.repr 4) tint)
                                                    tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tuchar))
                                              tuchar))
                                          (Sset _adler
                                            (Ebinop Oadd
                                              (Etempvar _adler tulong)
                                              (Etempvar _t'16 tuchar) tulong)))
                                        (Sset _sum2
                                          (Ebinop Oadd
                                            (Etempvar _sum2 tulong)
                                            (Etempvar _adler tulong) tulong)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'15
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _buf (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Econst_int (Int.repr 0) tint)
                                                        (Econst_int (Int.repr 4) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar))
                                            (Sset _adler
                                              (Ebinop Oadd
                                                (Etempvar _adler tulong)
                                                (Etempvar _t'15 tuchar)
                                                tulong)))
                                          (Sset _sum2
                                            (Ebinop Oadd
                                              (Etempvar _sum2 tulong)
                                              (Etempvar _adler tulong)
                                              tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'14
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _buf (tptr tuchar))
                                                    (Econst_int (Int.repr 8) tint)
                                                    (tptr tuchar)) tuchar))
                                              (Sset _adler
                                                (Ebinop Oadd
                                                  (Etempvar _adler tulong)
                                                  (Etempvar _t'14 tuchar)
                                                  tulong)))
                                            (Sset _sum2
                                              (Ebinop Oadd
                                                (Etempvar _sum2 tulong)
                                                (Etempvar _adler tulong)
                                                tulong)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _buf (tptr tuchar))
                                                      (Ebinop Oadd
                                                        (Econst_int (Int.repr 8) tint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint) (tptr tuchar))
                                                    tuchar))
                                                (Sset _adler
                                                  (Ebinop Oadd
                                                    (Etempvar _adler tulong)
                                                    (Etempvar _t'13 tuchar)
                                                    tulong)))
                                              (Sset _sum2
                                                (Ebinop Oadd
                                                  (Etempvar _sum2 tulong)
                                                  (Etempvar _adler tulong)
                                                  tulong)))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _buf (tptr tuchar))
                                                        (Ebinop Oadd
                                                          (Econst_int (Int.repr 8) tint)
                                                          (Econst_int (Int.repr 2) tint)
                                                          tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sset _adler
                                                    (Ebinop Oadd
                                                      (Etempvar _adler tulong)
                                                      (Etempvar _t'12 tuchar)
                                                      tulong)))
                                                (Sset _sum2
                                                  (Ebinop Oadd
                                                    (Etempvar _sum2 tulong)
                                                    (Etempvar _adler tulong)
                                                    tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _buf (tptr tuchar))
                                                          (Ebinop Oadd
                                                            (Ebinop Oadd
                                                              (Econst_int (Int.repr 8) tint)
                                                              (Econst_int (Int.repr 2) tint)
                                                              tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sset _adler
                                                      (Ebinop Oadd
                                                        (Etempvar _adler tulong)
                                                        (Etempvar _t'11 tuchar)
                                                        tulong)))
                                                  (Sset _sum2
                                                    (Ebinop Oadd
                                                      (Etempvar _sum2 tulong)
                                                      (Etempvar _adler tulong)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'10
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _buf (tptr tuchar))
                                                            (Ebinop Oadd
                                                              (Econst_int (Int.repr 8) tint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Sset _adler
                                                        (Ebinop Oadd
                                                          (Etempvar _adler tulong)
                                                          (Etempvar _t'10 tuchar)
                                                          tulong)))
                                                    (Sset _sum2
                                                      (Ebinop Oadd
                                                        (Etempvar _sum2 tulong)
                                                        (Etempvar _adler tulong)
                                                        tulong)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'9
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _buf (tptr tuchar))
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Sset _adler
                                                          (Ebinop Oadd
                                                            (Etempvar _adler tulong)
                                                            (Etempvar _t'9 tuchar)
                                                            tulong)))
                                                      (Sset _sum2
                                                        (Ebinop Oadd
                                                          (Etempvar _sum2 tulong)
                                                          (Etempvar _adler tulong)
                                                          tulong)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'8
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _buf (tptr tuchar))
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Sset _adler
                                                            (Ebinop Oadd
                                                              (Etempvar _adler tulong)
                                                              (Etempvar _t'8 tuchar)
                                                              tulong)))
                                                        (Sset _sum2
                                                          (Ebinop Oadd
                                                            (Etempvar _sum2 tulong)
                                                            (Etempvar _adler tulong)
                                                            tulong)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'7
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _buf (tptr tuchar))
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Sset _adler
                                                              (Ebinop Oadd
                                                                (Etempvar _adler tulong)
                                                                (Etempvar _t'7 tuchar)
                                                                tulong)))
                                                          (Sset _sum2
                                                            (Ebinop Oadd
                                                              (Etempvar _sum2 tulong)
                                                              (Etempvar _adler tulong)
                                                              tulong)))
                                                        (Sset _buf
                                                          (Ebinop Oadd
                                                            (Etempvar _buf (tptr tuchar))
                                                            (Econst_int (Int.repr 16) tint)
                                                            (tptr tuchar)))))))))))))))))))))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'4 (Etempvar _len tulong))
                              (Sset _len
                                (Ebinop Osub (Etempvar _t'4 tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)))
                            (Sifthenelse (Etempvar _t'4 tulong) Sskip Sbreak))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'5 (Etempvar _buf (tptr tuchar)))
                                (Sset _buf
                                  (Ebinop Oadd (Etempvar _t'5 (tptr tuchar))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuchar))))
                              (Ssequence
                                (Sset _t'6
                                  (Ederef (Etempvar _t'5 (tptr tuchar))
                                    tuchar))
                                (Sset _adler
                                  (Ebinop Oadd (Etempvar _adler tulong)
                                    (Etempvar _t'6 tuchar) tulong))))
                            (Sset _sum2
                              (Ebinop Oadd (Etempvar _sum2 tulong)
                                (Etempvar _adler tulong) tulong))))
                        Sskip)
                      (Ssequence
                        (Sset _adler
                          (Ebinop Omod (Etempvar _adler tulong)
                            (Econst_int (Int.repr 65521) tuint) tulong))
                        (Sset _sum2
                          (Ebinop Omod (Etempvar _sum2 tulong)
                            (Econst_int (Int.repr 65521) tuint) tulong)))))
                  Sskip)
                (Sreturn (Some (Ebinop Oor (Etempvar _adler tulong)
                                 (Ebinop Oshl (Etempvar _sum2 tulong)
                                   (Econst_int (Int.repr 16) tint) tulong)
                                 tulong)))))))))))
|}.

Definition f_adler32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_adler, tulong) :: (_buf, (tptr tuchar)) :: (_len, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _adler32_z (Tfunction (tulong :: (tptr tuchar) :: tulong :: nil)
                       tulong cc_default))
    ((Etempvar _adler tulong) :: (Etempvar _buf (tptr tuchar)) ::
     (Etempvar _len tuint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_adler32_combine_ := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_adler1, tulong) :: (_adler2, tulong) :: (_len2, tlong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_sum1, tulong) :: (_sum2, tulong) :: (_rem, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _len2 tlong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_long (Int64.repr 4294967295) tulong)))
    Sskip)
  (Ssequence
    (Sset _len2
      (Ebinop Omod (Etempvar _len2 tlong) (Econst_int (Int.repr 65521) tuint)
        tlong))
    (Ssequence
      (Sset _rem (Ecast (Etempvar _len2 tlong) tuint))
      (Ssequence
        (Sset _sum1
          (Ebinop Oand (Etempvar _adler1 tulong)
            (Econst_int (Int.repr 65535) tint) tulong))
        (Ssequence
          (Sset _sum2
            (Ebinop Omul (Etempvar _rem tuint) (Etempvar _sum1 tulong)
              tulong))
          (Ssequence
            (Sset _sum2
              (Ebinop Omod (Etempvar _sum2 tulong)
                (Econst_int (Int.repr 65521) tuint) tulong))
            (Ssequence
              (Sset _sum1
                (Ebinop Oadd (Etempvar _sum1 tulong)
                  (Ebinop Osub
                    (Ebinop Oadd
                      (Ebinop Oand (Etempvar _adler2 tulong)
                        (Econst_int (Int.repr 65535) tint) tulong)
                      (Econst_int (Int.repr 65521) tuint) tulong)
                    (Econst_int (Int.repr 1) tint) tulong) tulong))
              (Ssequence
                (Sset _sum2
                  (Ebinop Oadd (Etempvar _sum2 tulong)
                    (Ebinop Osub
                      (Ebinop Oadd
                        (Ebinop Oadd
                          (Ebinop Oand
                            (Ebinop Oshr (Etempvar _adler1 tulong)
                              (Econst_int (Int.repr 16) tint) tulong)
                            (Econst_int (Int.repr 65535) tint) tulong)
                          (Ebinop Oand
                            (Ebinop Oshr (Etempvar _adler2 tulong)
                              (Econst_int (Int.repr 16) tint) tulong)
                            (Econst_int (Int.repr 65535) tint) tulong)
                          tulong) (Econst_int (Int.repr 65521) tuint) tulong)
                      (Etempvar _rem tuint) tulong) tulong))
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _sum1 tulong)
                                 (Econst_int (Int.repr 65521) tuint) tint)
                    (Sset _sum1
                      (Ebinop Osub (Etempvar _sum1 tulong)
                        (Econst_int (Int.repr 65521) tuint) tulong))
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _sum1 tulong)
                                   (Econst_int (Int.repr 65521) tuint) tint)
                      (Sset _sum1
                        (Ebinop Osub (Etempvar _sum1 tulong)
                          (Econst_int (Int.repr 65521) tuint) tulong))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Ebinop Oge (Etempvar _sum2 tulong)
                                     (Ebinop Oshl
                                       (Ecast
                                         (Econst_int (Int.repr 65521) tuint)
                                         tulong)
                                       (Econst_int (Int.repr 1) tint) tulong)
                                     tint)
                        (Sset _sum2
                          (Ebinop Osub (Etempvar _sum2 tulong)
                            (Ebinop Oshl
                              (Ecast (Econst_int (Int.repr 65521) tuint)
                                tulong) (Econst_int (Int.repr 1) tint)
                              tulong) tulong))
                        Sskip)
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _sum2 tulong)
                                       (Econst_int (Int.repr 65521) tuint)
                                       tint)
                          (Sset _sum2
                            (Ebinop Osub (Etempvar _sum2 tulong)
                              (Econst_int (Int.repr 65521) tuint) tulong))
                          Sskip)
                        (Sreturn (Some (Ebinop Oor (Etempvar _sum1 tulong)
                                         (Ebinop Oshl (Etempvar _sum2 tulong)
                                           (Econst_int (Int.repr 16) tint)
                                           tulong) tulong)))))))))))))))
|}.

Definition f_adler32_combine := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_adler1, tulong) :: (_adler2, tulong) :: (_len2, tlong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _adler32_combine_ (Tfunction (tulong :: tulong :: tlong :: nil)
                              tulong cc_default))
    ((Etempvar _adler1 tulong) :: (Etempvar _adler2 tulong) ::
     (Etempvar _len2 tlong) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_adler32_combine64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_adler1, tulong) :: (_adler2, tulong) :: (_len2, tlong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _adler32_combine_ (Tfunction (tulong :: tulong :: tlong :: nil)
                              tulong cc_default))
    ((Etempvar _adler1 tulong) :: (Etempvar _adler2 tulong) ::
     (Etempvar _len2 tlong) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_adler32_z, Gfun(Internal f_adler32_z)) ::
 (_adler32, Gfun(Internal f_adler32)) ::
 (_adler32_combine_, Gfun(Internal f_adler32_combine_)) ::
 (_adler32_combine, Gfun(Internal f_adler32_combine)) ::
 (_adler32_combine64, Gfun(Internal f_adler32_combine64)) :: nil).

Definition public_idents : list ident :=
(_adler32_combine64 :: _adler32_combine :: _adler32 :: _adler32_z ::
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



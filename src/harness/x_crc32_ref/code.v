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
  Definition source_file := "harness/x_crc32_ref.c".
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
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_same : ident := $"bytes_same".
Definition _c : ident := $"c".
Definition _crc : ident := $"crc".
Definition _crc32 : ident := $"crc32".
Definition _crc32_z : ident := $"crc32_z".
Definition _d : ident := $"d".
Definition _get_crc_table : ident := $"get_crc_table".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _i : ident := $"i".
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _main : ident := $"main".
Definition _n : ident := $"n".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _ref_crc32 : ident := $"ref_crc32".
Definition _ref_crc_byte : ident := $"ref_crc_byte".
Definition _s : ident := $"s".
Definition _snap : ident := $"snap".
Definition _t : ident := $"t".
Definition _want : ident := $"want".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_crc, tulong) :: nil);
  fn_temps := ((_n, tuint) :: (_k, tuint) :: (_len, tuint) ::
               (_buf, (tptr tuchar)) :: (_snap, (tptr tuchar)) ::
               (_want, tulong) :: (_a, tulong) :: (_t, (tptr tuint)) ::
               (_i, tuint) :: (_t'16, tulong) :: (_t'15, (tptr tuint)) ::
               (_t'14, tint) :: (_t'13, tulong) :: (_t'12, tulong) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tint) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'23, tulong) :: (_t'22, tulong) :: (_t'21, tulong) ::
               (_t'20, tulong) :: (_t'19, tulong) :: (_t'18, tulong) ::
               (_t'17, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
      ((Ecast (Eaddrof (Evar _crc tulong) (tptr tulong)) (tptr tuchar)) ::
       (Esizeof tulong tulong) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sset _n (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
          (Sset _k (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sset _len (Etempvar _t'3 tuint)))
          (Ssequence
            (Scall None
              (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
              ((Ebinop Ole (Etempvar _n tuint)
                 (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                   (Econst_int (Int.repr 20) tint) tuint) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
                ((Ebinop Ole (Etempvar _k tuint) (Etempvar _n tuint) tint) ::
                 nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                               (tptr tvoid) cc_default))
                    ((Etempvar _n tuint) :: nil))
                  (Sset _buf (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                 (tptr tvoid) cc_default))
                      ((Etempvar _n tuint) :: nil))
                    (Sset _snap (Etempvar _t'5 (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _buf (tptr tuchar))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Sset _t'6 (Econst_int (Int.repr 1) tint))
                        (Sset _t'6
                          (Ecast
                            (Ebinop Oeq (Etempvar _snap (tptr tuchar))
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) tint) tbool)))
                      (Sifthenelse (Etempvar _t'6 tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        Sskip))
                    (Ssequence
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Etempvar _buf (tptr tuchar)) ::
                         (Etempvar _n tuint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _bytes_copy (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                          ((Etempvar _snap (tptr tuchar)) ::
                           (Etempvar _buf (tptr tuchar)) ::
                           (Etempvar _n tuint) :: nil))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'23 (Evar _crc tulong))
                              (Scall (Some _t'7)
                                (Evar _ref_crc32 (Tfunction
                                                   (tulong ::
                                                    (tptr tuchar) ::
                                                    tulong :: nil) tulong
                                                   cc_default))
                                ((Etempvar _t'23 tulong) ::
                                 (Etempvar _buf (tptr tuchar)) ::
                                 (Etempvar _n tuint) :: nil)))
                            (Sset _want (Etempvar _t'7 tulong)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'22 (Evar _crc tulong))
                                (Scall (Some _t'8)
                                  (Evar _crc32_z (Tfunction
                                                   (tulong ::
                                                    (tptr tuchar) ::
                                                    tulong :: nil) tulong
                                                   cc_default))
                                  ((Etempvar _t'22 tulong) ::
                                   (Etempvar _buf (tptr tuchar)) ::
                                   (Etempvar _n tuint) :: nil)))
                              (Sset _a (Etempvar _t'8 tulong)))
                            (Ssequence
                              (Scall None
                                (Evar _gp_assert (Tfunction (tint :: nil)
                                                   tvoid cc_default))
                                ((Ebinop Oeq (Etempvar _a tulong)
                                   (Etempvar _want tulong) tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _gp_assert (Tfunction (tint :: nil)
                                                     tvoid cc_default))
                                  ((Ebinop Ole (Etempvar _a tulong)
                                     (Econst_int (Int.repr (-1)) tuint) tint) ::
                                   nil))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'21 (Evar _crc tulong))
                                      (Scall (Some _t'9)
                                        (Evar _crc32 (Tfunction
                                                       (tulong ::
                                                        (tptr tuchar) ::
                                                        tuint :: nil) tulong
                                                       cc_default))
                                        ((Etempvar _t'21 tulong) ::
                                         (Etempvar _buf (tptr tuchar)) ::
                                         (Etempvar _n tuint) :: nil)))
                                    (Scall None
                                      (Evar _gp_assert (Tfunction
                                                         (tint :: nil) tvoid
                                                         cc_default))
                                      ((Ebinop Oeq (Etempvar _t'9 tulong)
                                         (Etempvar _want tulong) tint) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'20 (Evar _crc tulong))
                                          (Scall (Some _t'10)
                                            (Evar _crc32_z (Tfunction
                                                             (tulong ::
                                                              (tptr tuchar) ::
                                                              tulong :: nil)
                                                             tulong
                                                             cc_default))
                                            ((Etempvar _t'20 tulong) ::
                                             (Etempvar _buf (tptr tuchar)) ::
                                             (Etempvar _k tuint) :: nil)))
                                        (Scall (Some _t'11)
                                          (Evar _crc32_z (Tfunction
                                                           (tulong ::
                                                            (tptr tuchar) ::
                                                            tulong :: nil)
                                                           tulong cc_default))
                                          ((Etempvar _t'10 tulong) ::
                                           (Ebinop Oadd
                                             (Etempvar _buf (tptr tuchar))
                                             (Etempvar _k tuint)
                                             (tptr tuchar)) ::
                                           (Ebinop Osub (Etempvar _n tuint)
                                             (Etempvar _k tuint) tuint) ::
                                           nil)))
                                      (Scall None
                                        (Evar _gp_assert (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Ebinop Oeq (Etempvar _t'11 tulong)
                                           (Etempvar _want tulong) tint) ::
                                         nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'19 (Evar _crc tulong))
                                          (Scall (Some _t'12)
                                            (Evar _crc32 (Tfunction
                                                           (tulong ::
                                                            (tptr tuchar) ::
                                                            tuint :: nil)
                                                           tulong cc_default))
                                            ((Etempvar _t'19 tulong) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Etempvar _len tuint) :: nil)))
                                        (Scall None
                                          (Evar _gp_assert (Tfunction
                                                             (tint :: nil)
                                                             tvoid
                                                             cc_default))
                                          ((Ebinop Oeq
                                             (Etempvar _t'12 tulong)
                                             (Econst_int (Int.repr 0) tint)
                                             tint) :: nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'18 (Evar _crc tulong))
                                            (Scall (Some _t'13)
                                              (Evar _crc32_z (Tfunction
                                                               (tulong ::
                                                                (tptr tuchar) ::
                                                                tulong ::
                                                                nil) tulong
                                                               cc_default))
                                              ((Etempvar _t'18 tulong) ::
                                               (Econst_int (Int.repr 0) tint) ::
                                               (Etempvar _len tuint) :: nil)))
                                          (Scall None
                                            (Evar _gp_assert (Tfunction
                                                               (tint :: nil)
                                                               tvoid
                                                               cc_default))
                                            ((Ebinop Oeq
                                               (Etempvar _t'13 tulong)
                                               (Econst_int (Int.repr 0) tint)
                                               tint) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'14)
                                              (Evar _bytes_same (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   tulong ::
                                                                   nil) tint
                                                                  cc_default))
                                              ((Etempvar _buf (tptr tuchar)) ::
                                               (Etempvar _snap (tptr tuchar)) ::
                                               (Etempvar _n tuint) :: nil))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _t'14 tint) :: nil)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'15)
                                                (Evar _get_crc_table 
                                                (Tfunction nil (tptr tuint)
                                                  cc_default)) nil)
                                              (Sset _t
                                                (Etempvar _t'15 (tptr tuint))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _i
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _i tuint)
                                                                   (Econst_int (Int.repr 256) tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Scall (Some _t'16)
                                                        (Evar _ref_crc_byte 
                                                        (Tfunction
                                                          (tulong ::
                                                           tuchar :: nil)
                                                          tulong cc_default))
                                                        ((Econst_int (Int.repr 0) tint) ::
                                                         (Ecast
                                                           (Etempvar _i tuint)
                                                           tuchar) :: nil))
                                                      (Ssequence
                                                        (Sset _t'17
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t (tptr tuint))
                                                              (Etempvar _i tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall None
                                                          (Evar _gp_assert 
                                                          (Tfunction
                                                            (tint :: nil)
                                                            tvoid cc_default))
                                                          ((Ebinop Oeq
                                                             (Etempvar _t'17 tuint)
                                                             (Etempvar _t'16 tulong)
                                                             tint) :: nil)))))
                                                  (Sset _i
                                                    (Ebinop Oadd
                                                      (Etempvar _i tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint))))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _buf (tptr tuchar)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _snap (tptr tuchar)) ::
                                                     nil))
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
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
 (_crc32,
   Gfun(External (EF_external "crc32"
                   (mksignature (AST.Xlong :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ::
 (_crc32_z,
   Gfun(External (EF_external "crc32_z"
                   (mksignature (AST.Xlong :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     (tulong :: (tptr tuchar) :: tulong :: nil) tulong cc_default)) ::
 (_get_crc_table,
   Gfun(External (EF_external "get_crc_table"
                   (mksignature nil AST.Xptr cc_default)) nil (tptr tuint)
     cc_default)) :: (_ref_crc_byte, Gfun(Internal f_ref_crc_byte)) ::
 (_ref_crc32, Gfun(Internal f_ref_crc32)) ::
 (_bytes_same, Gfun(Internal f_bytes_same)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _get_crc_table :: _crc32_z :: _crc32 :: _gp_assume :: _gp_assert ::
 _nondet_bytes :: _nondet_u32 :: _quickproof_free :: _quickproof_malloc ::
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



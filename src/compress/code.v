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
  Definition source_file := "compress.c".
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
Definition ___stringlit_compress_1 : ident := $"__stringlit_compress_1".
Definition _adler : ident := $"adler".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _bound : ident := $"bound".
Definition _compress : ident := $"compress".
Definition _compress2 : ident := $"compress2".
Definition _compress2_z : ident := $"compress2_z".
Definition _compressBound : ident := $"compressBound".
Definition _compressBound_z : ident := $"compressBound_z".
Definition _compress_z : ident := $"compress_z".
Definition _data_type : ident := $"data_type".
Definition _deflate : ident := $"deflate".
Definition _deflateEnd : ident := $"deflateEnd".
Definition _deflateInit_ : ident := $"deflateInit_".
Definition _dest : ident := $"dest".
Definition _destLen : ident := $"destLen".
Definition _err : ident := $"err".
Definition _got : ident := $"got".
Definition _internal_state : ident := $"internal_state".
Definition _left : ident := $"left".
Definition _level : ident := $"level".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _msg : ident := $"msg".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _opaque : ident := $"opaque".
Definition _reserved : ident := $"reserved".
Definition _ret : ident := $"ret".
Definition _source : ident := $"source".
Definition _sourceLen : ident := $"sourceLen".
Definition _state : ident := $"state".
Definition _stream : ident := $"stream".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
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
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_compress_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_compress2_z := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tuchar)) :: (_destLen, (tptr tulong)) ::
                (_source, (tptr tuchar)) :: (_sourceLen, tulong) ::
                (_level, tint) :: nil);
  fn_vars := ((_stream, (Tstruct _z_stream_s noattr)) :: nil);
  fn_temps := ((_err, tint) :: (_max, tuint) :: (_left, tulong) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'15, tulong) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, (tptr tuchar)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _max (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tuint))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _sourceLen tulong)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'1
              (Ecast
                (Ebinop Oeq (Etempvar _source (tptr tuchar))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                tbool))
            (Sset _t'1 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'1 tint)
            (Sset _t'2 (Econst_int (Int.repr 1) tint))
            (Sset _t'2
              (Ecast
                (Ebinop Oeq (Etempvar _destLen (tptr tulong))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                tbool))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sset _t'3 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'15 (Ederef (Etempvar _destLen (tptr tulong)) tulong))
            (Sifthenelse (Ebinop Ogt (Etempvar _t'15 tulong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _t'3
                  (Ecast
                    (Ebinop Oeq (Etempvar _dest (tptr tuchar))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                      tint) tbool))
                (Sset _t'3 (Ecast (Etempvar _t'3 tint) tbool)))
              (Sset _t'3 (Ecast (Econst_int (Int.repr 0) tint) tbool))))))
      (Sifthenelse (Etempvar _t'3 tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
        Sskip))
    (Ssequence
      (Sset _left (Ederef (Etempvar _destLen (tptr tulong)) tulong))
      (Ssequence
        (Sassign (Ederef (Etempvar _destLen (tptr tulong)) tulong)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield (Evar _stream (Tstruct _z_stream_s noattr)) _zalloc
              (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                      (tptr tvoid) cc_default)))
            (Ecast (Econst_int (Int.repr 0) tint)
              (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                      (tptr tvoid) cc_default))))
          (Ssequence
            (Sassign
              (Efield (Evar _stream (Tstruct _z_stream_s noattr)) _zfree
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default)))
              (Ecast (Econst_int (Int.repr 0) tint)
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))))
            (Ssequence
              (Sassign
                (Efield (Evar _stream (Tstruct _z_stream_s noattr)) _opaque
                  (tptr tvoid))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _deflateInit_ (Tfunction
                                          ((tptr (Tstruct _z_stream_s noattr)) ::
                                           tint :: (tptr tschar) :: tint ::
                                           nil) tint cc_default))
                    ((Eaddrof (Evar _stream (Tstruct _z_stream_s noattr))
                       (tptr (Tstruct _z_stream_s noattr))) ::
                     (Etempvar _level tint) ::
                     (Evar ___stringlit_compress_1 (tarray tschar 6)) ::
                     (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong)
                       tint) :: nil))
                  (Sset _err (Etempvar _t'4 tint)))
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _err tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sreturn (Some (Etempvar _err tint)))
                    Sskip)
                  (Ssequence
                    (Sassign
                      (Efield (Evar _stream (Tstruct _z_stream_s noattr))
                        _next_out (tptr tuchar))
                      (Etempvar _dest (tptr tuchar)))
                    (Ssequence
                      (Sassign
                        (Efield (Evar _stream (Tstruct _z_stream_s noattr))
                          _avail_out tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Efield (Evar _stream (Tstruct _z_stream_s noattr))
                            _next_in (tptr tuchar))
                          (Ecast (Etempvar _source (tptr tuchar))
                            (tptr tuchar)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Evar _stream (Tstruct _z_stream_s noattr))
                              _avail_in tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sset _t'13
                                    (Efield
                                      (Evar _stream (Tstruct _z_stream_s noattr))
                                      _avail_out tuint))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _t'13 tuint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _left tulong)
                                                       (Ecast
                                                         (Etempvar _max tuint)
                                                         tulong) tint)
                                          (Sset _t'5
                                            (Ecast (Etempvar _max tuint)
                                              tuint))
                                          (Sset _t'5
                                            (Ecast
                                              (Ecast (Etempvar _left tulong)
                                                tuint) tuint)))
                                        (Sassign
                                          (Efield
                                            (Evar _stream (Tstruct _z_stream_s noattr))
                                            _avail_out tuint)
                                          (Etempvar _t'5 tuint)))
                                      (Ssequence
                                        (Sset _t'14
                                          (Efield
                                            (Evar _stream (Tstruct _z_stream_s noattr))
                                            _avail_out tuint))
                                        (Sset _left
                                          (Ebinop Osub
                                            (Etempvar _left tulong)
                                            (Etempvar _t'14 tuint) tulong))))
                                    Sskip))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'11
                                      (Efield
                                        (Evar _stream (Tstruct _z_stream_s noattr))
                                        _avail_in tuint))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'11 tuint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _sourceLen tulong)
                                                         (Ecast
                                                           (Etempvar _max tuint)
                                                           tulong) tint)
                                            (Sset _t'6
                                              (Ecast (Etempvar _max tuint)
                                                tuint))
                                            (Sset _t'6
                                              (Ecast
                                                (Ecast
                                                  (Etempvar _sourceLen tulong)
                                                  tuint) tuint)))
                                          (Sassign
                                            (Efield
                                              (Evar _stream (Tstruct _z_stream_s noattr))
                                              _avail_in tuint)
                                            (Etempvar _t'6 tuint)))
                                        (Ssequence
                                          (Sset _t'12
                                            (Efield
                                              (Evar _stream (Tstruct _z_stream_s noattr))
                                              _avail_in tuint))
                                          (Sset _sourceLen
                                            (Ebinop Osub
                                              (Etempvar _sourceLen tulong)
                                              (Etempvar _t'12 tuint) tulong))))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Etempvar _sourceLen tulong)
                                        (Sset _t'7
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tint))
                                        (Sset _t'7
                                          (Ecast
                                            (Econst_int (Int.repr 4) tint)
                                            tint)))
                                      (Scall (Some _t'8)
                                        (Evar _deflate (Tfunction
                                                         ((tptr (Tstruct _z_stream_s noattr)) ::
                                                          tint :: nil) tint
                                                         cc_default))
                                        ((Eaddrof
                                           (Evar _stream (Tstruct _z_stream_s noattr))
                                           (tptr (Tstruct _z_stream_s noattr))) ::
                                         (Etempvar _t'7 tint) :: nil)))
                                    (Sset _err (Etempvar _t'8 tint)))))
                              (Sifthenelse (Ebinop Oeq (Etempvar _err tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                Sskip
                                Sbreak))
                            (Ssequence
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Evar _stream (Tstruct _z_stream_s noattr))
                                    _next_out (tptr tuchar)))
                                (Sassign
                                  (Ederef (Etempvar _destLen (tptr tulong))
                                    tulong)
                                  (Ecast
                                    (Ebinop Osub
                                      (Etempvar _t'10 (tptr tuchar))
                                      (Etempvar _dest (tptr tuchar)) tlong)
                                    tulong)))
                              (Ssequence
                                (Scall None
                                  (Evar _deflateEnd (Tfunction
                                                      ((tptr (Tstruct _z_stream_s noattr)) ::
                                                       nil) tint cc_default))
                                  ((Eaddrof
                                     (Evar _stream (Tstruct _z_stream_s noattr))
                                     (tptr (Tstruct _z_stream_s noattr))) ::
                                   nil))
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _err tint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)
                                    (Sset _t'9
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tint))
                                    (Sset _t'9
                                      (Ecast (Etempvar _err tint) tint)))
                                  (Sreturn (Some (Etempvar _t'9 tint))))))))))))))))))))
|}.

Definition f_compress2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tuchar)) :: (_destLen, (tptr tulong)) ::
                (_source, (tptr tuchar)) :: (_sourceLen, tulong) ::
                (_level, tint) :: nil);
  fn_vars := ((_got, tulong) :: nil);
  fn_temps := ((_ret, tint) :: (_t'1, tint) :: (_t'3, tulong) ::
               (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3 (Ederef (Etempvar _destLen (tptr tulong)) tulong))
    (Sassign (Evar _got tulong) (Etempvar _t'3 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _compress2_z (Tfunction
                             ((tptr tuchar) :: (tptr tulong) ::
                              (tptr tuchar) :: tulong :: tint :: nil) tint
                             cc_default))
        ((Etempvar _dest (tptr tuchar)) ::
         (Eaddrof (Evar _got tulong) (tptr tulong)) ::
         (Etempvar _source (tptr tuchar)) :: (Etempvar _sourceLen tulong) ::
         (Etempvar _level tint) :: nil))
      (Sset _ret (Etempvar _t'1 tint)))
    (Ssequence
      (Ssequence
        (Sset _t'2 (Evar _got tulong))
        (Sassign (Ederef (Etempvar _destLen (tptr tulong)) tulong)
          (Ecast (Etempvar _t'2 tulong) tulong)))
      (Sreturn (Some (Etempvar _ret tint))))))
|}.

Definition f_compress_z := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tuchar)) :: (_destLen, (tptr tulong)) ::
                (_source, (tptr tuchar)) :: (_sourceLen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _compress2_z (Tfunction
                         ((tptr tuchar) :: (tptr tulong) :: (tptr tuchar) ::
                          tulong :: tint :: nil) tint cc_default))
    ((Etempvar _dest (tptr tuchar)) :: (Etempvar _destLen (tptr tulong)) ::
     (Etempvar _source (tptr tuchar)) :: (Etempvar _sourceLen tulong) ::
     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_compress := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tuchar)) :: (_destLen, (tptr tulong)) ::
                (_source, (tptr tuchar)) :: (_sourceLen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _compress2 (Tfunction
                       ((tptr tuchar) :: (tptr tulong) :: (tptr tuchar) ::
                        tulong :: tint :: nil) tint cc_default))
    ((Etempvar _dest (tptr tuchar)) :: (Etempvar _destLen (tptr tulong)) ::
     (Etempvar _source (tptr tuchar)) :: (Etempvar _sourceLen tulong) ::
     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_compressBound_z := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_sourceLen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bound, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _bound
    (Ebinop Oadd
      (Ebinop Oadd
        (Ebinop Oadd
          (Ebinop Oadd (Etempvar _sourceLen tulong)
            (Ebinop Oshr (Etempvar _sourceLen tulong)
              (Econst_int (Int.repr 12) tint) tulong) tulong)
          (Ebinop Oshr (Etempvar _sourceLen tulong)
            (Econst_int (Int.repr 14) tint) tulong) tulong)
        (Ebinop Oshr (Etempvar _sourceLen tulong)
          (Econst_int (Int.repr 25) tint) tulong) tulong)
      (Econst_int (Int.repr 13) tint) tulong))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _bound tulong)
                   (Etempvar _sourceLen tulong) tint)
      (Sset _t'1
        (Ecast
          (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tulong)
          tulong))
      (Sset _t'1 (Ecast (Etempvar _bound tulong) tulong)))
    (Sreturn (Some (Etempvar _t'1 tulong)))))
|}.

Definition f_compressBound := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_sourceLen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bound, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _compressBound_z (Tfunction (tulong :: nil) tulong cc_default))
      ((Etempvar _sourceLen tulong) :: nil))
    (Sset _bound (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop One (Ecast (Etempvar _bound tulong) tulong)
                   (Etempvar _bound tulong) tint)
      (Sset _t'2
        (Ecast
          (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tulong)
          tulong))
      (Sset _t'2 (Ecast (Ecast (Etempvar _bound tulong) tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
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
     cc_default)) :: (___stringlit_compress_1, Gvar v___stringlit_compress_1) ::
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
 (_deflate,
   Gfun(External (EF_external "deflate"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: nil) tint cc_default)) ::
 (_deflateEnd,
   Gfun(External (EF_external "deflateEnd"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: nil) tint cc_default)) ::
 (_deflateInit_,
   Gfun(External (EF_external "deflateInit_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: (tptr tschar) :: tint ::
      nil) tint cc_default)) ::
 (_compress2_z, Gfun(Internal f_compress2_z)) ::
 (_compress2, Gfun(Internal f_compress2)) ::
 (_compress_z, Gfun(Internal f_compress_z)) ::
 (_compress, Gfun(Internal f_compress)) ::
 (_compressBound_z, Gfun(Internal f_compressBound_z)) ::
 (_compressBound, Gfun(Internal f_compressBound)) :: nil).

Definition public_idents : list ident :=
(_compressBound :: _compressBound_z :: _compress :: _compress_z ::
 _compress2 :: _compress2_z :: _deflateInit_ :: _deflateEnd :: _deflate ::
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



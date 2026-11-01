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
  Definition source_file := "harness/res_memory_inflate.c".
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
Definition ___stringlit_res_memory_inflate_1 : ident := $"__stringlit_res_memory_inflate_1".
Definition _address : ident := $"address".
Definition _adler : ident := $"adler".
Definition _alloc_any_bytes : ident := $"alloc_any_bytes".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _block : ident := $"block".
Definition _bytes : ident := $"bytes".
Definition _clip : ident := $"clip".
Definition _code : ident := $"code".
Definition _count : ident := $"count".
Definition _count__1 : ident := $"count__1".
Definition _counted_alloc : ident := $"counted_alloc".
Definition _counted_free : ident := $"counted_free".
Definition _counted_stream : ident := $"counted_stream".
Definition _data_type : ident := $"data_type".
Definition _failed : ident := $"failed".
Definition _gp_assert : ident := $"gp_assert".
Definition _gp_assume : ident := $"gp_assume".
Definition _in : ident := $"in".
Definition _in_len : ident := $"in_len".
Definition _inflate : ident := $"inflate".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _inflate_window_ok : ident := $"inflate_window_ok".
Definition _input : ident := $"input".
Definition _input_len : ident := $"input_len".
Definition _internal_state : ident := $"internal_state".
Definition _items : ident := $"items".
Definition _low : ident := $"low".
Definition _main : ident := $"main".
Definition _max : ident := $"max".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _now : ident := $"now".
Definition _opaque : ident := $"opaque".
Definition _out : ident := $"out".
Definition _out_len : ident := $"out_len".
Definition _peak : ident := $"peak".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _raw : ident := $"raw".
Definition _read : ident := $"read".
Definition _reserved : ident := $"reserved".
Definition _room : ident := $"room".
Definition _set_buffer : ident := $"set_buffer".
Definition _size : ident := $"size".
Definition _state : ident := $"state".
Definition _strm : ident := $"strm".
Definition _take : ident := $"take".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _upto : ident := $"upto".
Definition _value : ident := $"value".
Definition _w : ident := $"w".
Definition _window_bits : ident := $"window_bits".
Definition _wrapped : ident := $"wrapped".
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
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_res_memory_inflate_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_upto := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_max, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_value, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _value (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _value tulong) (Etempvar _max tulong)
                   tint)
      (Sset _t'2 (Ecast (Etempvar _value tulong) tulong))
      (Sset _t'2 (Ecast (Etempvar _max tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_clip := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _n tulong)
                 (Ebinop Oadd
                   (Ebinop Omul (Econst_int (Int.repr 2147483647) tint)
                     (Econst_int (Int.repr 2) tuint) tuint)
                   (Econst_int (Int.repr 1) tuint) tuint) tint)
    (Sset _t'1 (Ecast (Ecast (Etempvar _n tulong) tuint) tuint))
    (Sset _t'1
      (Ecast
        (Ebinop Oadd
          (Ebinop Omul (Econst_int (Int.repr 2147483647) tint)
            (Econst_int (Int.repr 2) tuint) tuint)
          (Econst_int (Int.repr 1) tuint) tuint) tuint)))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_alloc_any_bytes := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bytes, (tptr tuchar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default)) ((Etempvar _n tulong) :: nil))
    (Sset _bytes (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _bytes (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Etempvar _bytes (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _bytes (tptr tuchar))))))
|}.

Definition f_set_buffer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_in, (tptr tuchar)) :: (_in_len, tulong) ::
                (_out, (tptr tuchar)) :: (_out_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
        (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar))
    (Etempvar _in (tptr tuchar)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
          (Tstruct _z_stream_s noattr)) _avail_in tuint)
      (Ecast (Etempvar _in_len tulong) tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _next_out (tptr tuchar))
        (Etempvar _out (tptr tuchar)))
      (Sassign
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _avail_out tuint)
        (Ecast (Etempvar _out_len tulong) tuint)))))
|}.

Definition f_inflate_window_ok := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_window_bits, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_low, tint) :: (_raw, tint) :: (_wrapped, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _low
    (Ebinop Oand (Etempvar _window_bits tint) (Econst_int (Int.repr 15) tint)
      tint))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _window_bits tint)
                     (Eunop Oneg (Econst_int (Int.repr 15) tint) tint) tint)
        (Sset _t'1
          (Ecast
            (Ebinop Ole (Etempvar _window_bits tint)
              (Eunop Oneg (Econst_int (Int.repr 8) tint) tint) tint) tbool))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sset _raw (Etempvar _t'1 tint)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _window_bits tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'2
              (Ecast
                (Ebinop Olt (Etempvar _window_bits tint)
                  (Econst_int (Int.repr 48) tint) tint) tbool))
            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'2 tint)
            (Sifthenelse (Ebinop Oeq (Etempvar _low tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _t'3 (Ecast (Econst_int (Int.repr 1) tint) tbool))
              (Ssequence
                (Sset _t'3
                  (Ecast
                    (Ebinop Oge (Etempvar _low tint)
                      (Econst_int (Int.repr 8) tint) tint) tbool))
                (Sset _t'3 (Ecast (Etempvar _t'3 tint) tbool))))
            (Sset _t'3 (Econst_int (Int.repr 0) tint))))
        (Sset _wrapped (Etempvar _t'3 tint)))
      (Ssequence
        (Sifthenelse (Etempvar _raw tint)
          (Sset _t'4 (Econst_int (Int.repr 1) tint))
          (Sset _t'4 (Ecast (Etempvar _wrapped tint) tbool)))
        (Sreturn (Some (Etempvar _t'4 tint)))))))
|}.

Definition f_counted_alloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_opaque, (tptr tvoid)) :: (_items, tuint) ::
                (_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_count__1, (tptr (Tstruct _count noattr))) ::
               (_bytes, tulong) :: (_block, (tptr tulong)) ::
               (_t'1, (tptr tvoid)) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _count__1 (Etempvar _opaque (tptr tvoid)))
  (Ssequence
    (Sset _bytes
      (Ebinop Omul (Ecast (Etempvar _items tuint) tulong)
        (Etempvar _size tuint) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                     cc_default))
          ((Ebinop Oadd (Esizeof tulong tulong) (Etempvar _bytes tulong)
             tulong) :: nil))
        (Sset _block (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _block (tptr tulong))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                  (Tstruct _count noattr)) _failed tint)
              (Econst_int (Int.repr 1) tint))
            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
          Sskip)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _block (tptr tulong))
                (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
            (Etempvar _bytes tulong))
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                    (Tstruct _count noattr)) _now tulong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                    (Tstruct _count noattr)) _now tulong)
                (Ebinop Oadd (Etempvar _t'5 tulong) (Etempvar _bytes tulong)
                  tulong)))
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef
                      (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                      (Tstruct _count noattr)) _now tulong))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                        (Tstruct _count noattr)) _peak tulong))
                  (Sifthenelse (Ebinop Ogt (Etempvar _t'2 tulong)
                                 (Etempvar _t'3 tulong) tint)
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                            (Tstruct _count noattr)) _now tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                            (Tstruct _count noattr)) _peak tulong)
                        (Etempvar _t'4 tulong)))
                    Sskip)))
              (Sreturn (Some (Ebinop Oadd (Etempvar _block (tptr tulong))
                               (Econst_int (Int.repr 1) tint) (tptr tulong)))))))))))
|}.

Definition f_counted_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_opaque, (tptr tvoid)) :: (_address, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_count__1, (tptr (Tstruct _count noattr))) ::
               (_block, (tptr tulong)) :: (_t'2, tulong) :: (_t'1, tulong) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _count__1 (Etempvar _opaque (tptr tvoid)))
  (Ssequence
    (Sset _block
      (Ebinop Osub (Ecast (Etempvar _address (tptr tvoid)) (tptr tulong))
        (Econst_int (Int.repr 1) tint) (tptr tulong)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
              (Tstruct _count noattr)) _now tulong))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _block (tptr tulong))
                (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
          (Sassign
            (Efield
              (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
                (Tstruct _count noattr)) _now tulong)
            (Ebinop Osub (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
              tulong))))
      (Scall None
        (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                 cc_default))
        ((Etempvar _block (tptr tulong)) :: nil)))))
|}.

Definition f_counted_stream := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_count__1, (tptr (Tstruct _count noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
        (Tstruct _count noattr)) _now tulong) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
          (Tstruct _count noattr)) _peak tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _count__1 (tptr (Tstruct _count noattr)))
            (Tstruct _count noattr)) _failed tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _zalloc
            (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                    (tptr tvoid) cc_default)))
          (Evar _counted_alloc (Tfunction
                                 ((tptr tvoid) :: tuint :: tuint :: nil)
                                 (tptr tvoid) cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zfree
              (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                      cc_default)))
            (Evar _counted_free (Tfunction
                                  ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                                  cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid))
              (Etempvar _count__1 (tptr (Tstruct _count noattr))))
            (Scall None
              (Evar _set_buffer (Tfunction
                                  ((tptr (Tstruct _z_stream_s noattr)) ::
                                   (tptr tuchar) :: tulong ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
              ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 0) tint) :: nil))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_count__1, (Tstruct _count noattr)) ::
              (_strm, (Tstruct _z_stream_s noattr)) :: nil);
  fn_temps := ((_window_bits, tint) :: (_input_len, tulong) ::
               (_input, (tptr tuchar)) :: (_code, tint) :: (_w, tint) ::
               (_read, tulong) :: (_take, tulong) :: (_room, tulong) ::
               (_out, (tptr tuchar)) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tuint) :: (_t'11, (tptr tvoid)) :: (_t'10, tuint) ::
               (_t'9, tulong) :: (_t'8, tuint) :: (_t'7, tuchar) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, (tptr tuchar)) ::
               (_t'3, tulong) :: (_t'2, tint) :: (_t'1, tuint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tulong) ::
               (_t'15, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sset _window_bits (Ecast (Etempvar _t'1 tuint) tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _inflate_window_ok (Tfunction (tint :: nil) tint cc_default))
          ((Etempvar _window_bits tint) :: nil))
        (Scall None
          (Evar _gp_assume (Tfunction (tint :: nil) tvoid cc_default))
          ((Etempvar _t'2 tint) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _upto (Tfunction (tulong :: nil) tulong cc_default))
            ((Econst_long (Int64.repr 9223372036854775807) tlong) :: nil))
          (Sset _input_len (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _alloc_any_bytes (Tfunction (tulong :: nil) (tptr tuchar)
                                       cc_default))
              ((Etempvar _input_len tulong) :: nil))
            (Sset _input (Etempvar _t'4 (tptr tuchar))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _input (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip)
            (Ssequence
              (Scall None
                (Evar _counted_stream (Tfunction
                                        ((tptr (Tstruct _z_stream_s noattr)) ::
                                         (tptr (Tstruct _count noattr)) ::
                                         nil) tvoid cc_default))
                ((Eaddrof (Evar _strm (Tstruct _z_stream_s noattr))
                   (tptr (Tstruct _z_stream_s noattr))) ::
                 (Eaddrof (Evar _count__1 (Tstruct _count noattr))
                   (tptr (Tstruct _count noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _inflateInit2_ (Tfunction
                                           ((tptr (Tstruct _z_stream_s noattr)) ::
                                            tint :: (tptr tschar) :: tint ::
                                            nil) tint cc_default))
                    ((Eaddrof (Evar _strm (Tstruct _z_stream_s noattr))
                       (tptr (Tstruct _z_stream_s noattr))) ::
                     (Etempvar _window_bits tint) ::
                     (Evar ___stringlit_res_memory_inflate_1 (tarray tschar 6)) ::
                     (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong)
                       tint) :: nil))
                  (Sset _code (Etempvar _t'5 tint)))
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq (Etempvar _code tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Sset _t'6 (Econst_int (Int.repr 1) tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _code tint)
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 4) tint) tint)
                                     tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'18
                              (Efield
                                (Evar _count__1 (Tstruct _count noattr))
                                _failed tint))
                            (Sset _t'6 (Ecast (Etempvar _t'18 tint) tbool)))
                          (Sset _t'6 (Ecast (Etempvar _t'6 tint) tbool)))
                        (Sset _t'6
                          (Ecast (Econst_int (Int.repr 0) tint) tbool))))
                    (Scall None
                      (Evar _gp_assert (Tfunction (tint :: nil) tvoid
                                         cc_default))
                      ((Etempvar _t'6 tint) :: nil)))
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _code tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                      Sskip)
                    (Ssequence
                      (Sset _w
                        (Ebinop Oand (Etempvar _window_bits tint)
                          (Econst_int (Int.repr 15) tint) tint))
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _window_bits tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Sset _w
                            (Eunop Oneg (Etempvar _window_bits tint) tint))
                          Sskip)
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _w tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Sset _w (Econst_int (Int.repr 15) tint))
                            Sskip)
                          (Ssequence
                            (Sset _read
                              (Ecast (Econst_int (Int.repr 0) tint) tulong))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'8)
                                        (Evar _clip (Tfunction
                                                      (tulong :: nil) tuint
                                                      cc_default))
                                        ((Ebinop Osub
                                           (Etempvar _input_len tulong)
                                           (Etempvar _read tulong) tulong) ::
                                         nil))
                                      (Scall (Some _t'9)
                                        (Evar _upto (Tfunction
                                                      (tulong :: nil) tulong
                                                      cc_default))
                                        ((Etempvar _t'8 tuint) :: nil)))
                                    (Sset _take (Etempvar _t'9 tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'10)
                                        (Evar _nondet_u32 (Tfunction nil
                                                            tuint cc_default))
                                        nil)
                                      (Sset _room
                                        (Ecast (Etempvar _t'10 tuint) tulong)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'11)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Etempvar _room tulong) :: nil))
                                        (Sset _out
                                          (Etempvar _t'11 (tptr tvoid))))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _out (tptr tuchar))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                          Sskip)
                                        (Ssequence
                                          (Scall None
                                            (Evar _set_buffer (Tfunction
                                                                ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                            ((Eaddrof
                                               (Evar _strm (Tstruct _z_stream_s noattr))
                                               (tptr (Tstruct _z_stream_s noattr))) ::
                                             (Ebinop Oadd
                                               (Etempvar _input (tptr tuchar))
                                               (Etempvar _read tulong)
                                               (tptr tuchar)) ::
                                             (Etempvar _take tulong) ::
                                             (Etempvar _out (tptr tuchar)) ::
                                             (Etempvar _room tulong) :: nil))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'12)
                                                  (Evar _nondet_u32 (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                  nil)
                                                (Scall (Some _t'13)
                                                  (Evar _inflate (Tfunction
                                                                   ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tint ::
                                                                    nil) tint
                                                                   cc_default))
                                                  ((Eaddrof
                                                     (Evar _strm (Tstruct _z_stream_s noattr))
                                                     (tptr (Tstruct _z_stream_s noattr))) ::
                                                   (Ecast
                                                     (Etempvar _t'12 tuint)
                                                     tint) :: nil)))
                                              (Sset _code
                                                (Etempvar _t'13 tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sifthenelse (Ebinop One
                                                               (Etempvar _code tint)
                                                               (Eunop Oneg
                                                                 (Econst_int (Int.repr 4) tint)
                                                                 tint) tint)
                                                  (Sset _t'14
                                                    (Econst_int (Int.repr 1) tint))
                                                  (Ssequence
                                                    (Sset _t'17
                                                      (Efield
                                                        (Evar _count__1 (Tstruct _count noattr))
                                                        _failed tint))
                                                    (Sset _t'14
                                                      (Ecast
                                                        (Etempvar _t'17 tint)
                                                        tbool))))
                                                (Scall None
                                                  (Evar _gp_assert (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _t'14 tint) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'16
                                                    (Efield
                                                      (Evar _count__1 (Tstruct _count noattr))
                                                      _peak tulong))
                                                  (Scall None
                                                    (Evar _gp_assert 
                                                    (Tfunction (tint :: nil)
                                                      tvoid cc_default))
                                                    ((Ebinop Ole
                                                       (Etempvar _t'16 tulong)
                                                       (Ebinop Oadd
                                                         (Ebinop Oshl
                                                           (Econst_long (Int64.repr 1) tulong)
                                                           (Etempvar _w tint)
                                                           tulong)
                                                         (Econst_int (Int.repr 7160) tint)
                                                         tulong) tint) ::
                                                     nil)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'15
                                                      (Efield
                                                        (Evar _strm (Tstruct _z_stream_s noattr))
                                                        _avail_in tuint))
                                                    (Sset _read
                                                      (Ebinop Oadd
                                                        (Etempvar _read tulong)
                                                        (Ebinop Osub
                                                          (Etempvar _take tulong)
                                                          (Etempvar _t'15 tuint)
                                                          tulong) tulong)))
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _out (tptr tuchar)) ::
                                                     nil)))))))))))
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _nondet_u8 (Tfunction nil tuchar
                                                       cc_default)) nil)
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _t'7 tuchar)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))
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
 Composite _count Struct
   (Member_plain _now tulong :: Member_plain _peak tulong ::
    Member_plain _failed tint :: nil)
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
     cc_default)) :: (___stringlit_res_memory_inflate_1, Gvar v___stringlit_res_memory_inflate_1) ::
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
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
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
 (_inflateInit2_,
   Gfun(External (EF_external "inflateInit2_"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tint :: (tptr tschar) :: tint ::
      nil) tint cc_default)) :: (_upto, Gfun(Internal f_upto)) ::
 (_clip, Gfun(Internal f_clip)) ::
 (_alloc_any_bytes, Gfun(Internal f_alloc_any_bytes)) ::
 (_set_buffer, Gfun(Internal f_set_buffer)) ::
 (_inflate_window_ok, Gfun(Internal f_inflate_window_ok)) ::
 (_counted_alloc, Gfun(Internal f_counted_alloc)) ::
 (_counted_free, Gfun(Internal f_counted_free)) ::
 (_counted_stream, Gfun(Internal f_counted_stream)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _inflateInit2_ :: _inflate :: _gp_assume :: _gp_assert ::
 _nondet_bytes :: _nondet_size :: _nondet_u32 :: _nondet_u8 ::
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



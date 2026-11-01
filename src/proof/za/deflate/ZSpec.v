(* deflateInit2_ and deflateEnd with a caller-supplied allocator (src/proof/zutil/ZAlloc.v).

   DSpec9's deflateInit2__spec_v9 is for strm->zalloc = zfree = Z_NULL (zlib then installs zcalloc/zcfree) and
   DSpec's deflateEnd_spec for a stream with that default allocator.  Here strm->zalloc, zfree, opaque are the
   caller's allocator [ZA] (non-NULL functions: deflateInit2_ keeps them), and the specifications say what the
   two functions do with it, as the allocator's events:
   - deflateInit2_ on success makes the five allocations [dinit_events s] (the state, then window, prev, head
     and pending_buf, of 2 * w_size, 2 * w_size, 2 * hash_size and 4 * lit_bufsize bytes); on failure every
     block it took is given back (the bytes held are as before the call), and Z_MEM_ERROR comes from an
     allocation that failed (zlib.h: "Z_MEM_ERROR if there was not enough memory"), the event ZFail;
   - deflateEnd gives back the blocks of the stream, [dend_events s p]: the four buffers that are not Z_NULL,
     in the reverse order of their allocation, then the state.
   The rest is as in DSpec9 / DSpec: the model c_deflateInit2_ and the representation dstream_za of the generated
   allocator-generic port (src/proof/za/deflate/DSpec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.za.deflate.DSpec9.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.deflate.code.
Require Export Zlib.proof.zutil.ZAlloc.
#[export] Existing Instance DCS.CS.

(* the bytes deflateInit2_ may allocate at most (windowBits 15, memLevel 9): the state, 2 * 2^15 + 2 * 2^15,
   2 * 2^16 and 4 * 2^15 *)
Definition dinit_max : Z := 5968 + 65536 + 65536 + 131072 + 131072.

Section ZA.
Context {ZA : zallocator}.

(* deflateInit2_'s five allocations of a stream it initialised to s *)
Definition dinit_events (s : dstate) : list zev :=
  [ZAlloc (sizeof t_ds); ZAlloc (2 * d_w_size s); ZAlloc (2 * d_w_size s); ZAlloc (2 * d_hash_size s);
   ZAlloc (4 * tr_lit_bufsize (d_tr s))].

(* deflateEnd's releases: the buffers that are not Z_NULL (pending_buf, head, prev, window), then the state *)
Definition dend_free (q : val) (n : Z) : list zev := if eq_dec q nullval then [] else [ZFree n].
Definition dend_events (s : dstate) (p : dptrs) : list zev :=
  dend_free (p_pbuf p) (4 * tr_lit_bufsize (d_tr s)) ++ dend_free (p_head p) (2 * d_hash_size s) ++
  dend_free (p_prev p) (2 * d_w_size s) ++ dend_free (p_window p) (2 * d_w_size s) ++ [ZFree (sizeof t_ds)].

Definition za_deflateInit2__spec :=
 DECLARE _deflateInit2_
 WITH strmp : val, level : Z, method : Z, wbits : Z, mem : Z, strategy : Z, vp : val, vsh : share,
      vers : list Z, ssize : Z, ni : val, tin : val, tout : val, msgv : val, adler : val,
      dt : val, st0 : val, gv : globals, tr : list zev
 PRE [ tptr t_strm, tint, tint, tint, tint, tint, tptr tschar, tint ]
  PROP (s32_ok level; s32_ok method; s32_ok wbits; s32_ok mem; s32_ok strategy; s32_ok ssize;
        readable_share vsh; 1 <= Zlength vers; -128 <= Znth 0 vers < 128;
        forall a1 a2 a3 a4 a5, exists r,
          c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5 zrst0
            = Some r;
        za_alloc <> nullval; za_free <> nullval; is_pointer_or_null za_opaque; za_now tr + dinit_max <= za_cap)
  PARAMS (strmp; vi level; vi method; vi wbits; vi mem; vi strategy; vp; vi ssize) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp;
       reset_fields strmp tin tout msgv adler;
       @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp;
       @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp;
       @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp;
       @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp;
       @field_at DCS.CS Ews t_strm (DOT _state) st0 strmp;
       @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp;
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       @za_funcs DCS.CS ZA; za_res gv tr; deflate_globals gv)
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : option dstate * strm * Z,
  EX tr' : list zev,
  PROP (c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level method wbits mem strategy a1 a2 a3 a4 a5 zrst0
          = Some r;
        match fst (fst r) with
        | Some s => tr' = tr ++ dinit_events s
        | None => za_now tr' = za_now tr /\ (snd r = Z_MEM_ERROR -> za_failed tr' = true)
        end)
  RETURN (vi (snd r))
  SEP (match fst (fst r) with
       | Some _ => dstream_za 2 (fst (fst r)) strmp nullval gv
       | None => EX st : val, EX dt' : val,
                 !! (snd r = Z_VERSION_ERROR -> st = st0) &&
                 (@za_funcs DCS.CS ZA * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
                  @field_at DCS.CS Ews t_strm (DOT _state) st strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
                  @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
                  @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
                  @field_at DCS.CS Ews t_strm (DOT _data_type) dt' strmp)
       end;
       @field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp;
       EX msgv' : val,
       !! (if snd r =? Z_VERSION_ERROR then msgv' = msgv else msg_ok (z_msg (snd (fst r))) msgv') &&
       reset_fields strmp (rfv (snd r =? Z_OK) (z_total_in (snd (fst r))) tin)
         (rfv (snd r =? Z_OK) (z_total_out (snd (fst r))) tout) msgv'
         (rfv (snd r =? Z_OK) (z_adler (snd (fst r))) adler);
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       za_res gv tr'; deflate_globals gv).

(* What deflateEnd needs, with the pointers [p] of the state exposed: DSpec's dstream_end (allocator-generic)
   for one p, with positive buffer sizes (a generic token does not give the validity of a pointer that
   TRY_FREE tests, the contents of a non-empty buffer do). *)
Definition dend_stream (os : option dstate) (p : dptrs) (strmp : val) (gv : globals) : mpred :=
  match os with
  | Some s =>
      (zfuncs_za gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
       (!! (p_strm p = strmp /\ Int.min_signed <= d_status s <= Int.max_signed /\
            0 < d_w_size s /\ 0 < d_hash_size s /\ 0 < tr_lit_bufsize (d_tr s)) &&
        (dend_at_za s p * ds_pad (p_s p) *
         @field_at DCS.CS Ews t_strm (DOT _state) (p_s p) strmp *
         @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
         @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
         @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
         EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)))%logic
  | None => dstream_end_za None strmp gv
  end.

(* The stream after deflateEnd freed its state: strm->state = Z_NULL, the allocator's fields unchanged. *)
Definition dclosed (strmp : val) (gv : globals) : mpred :=
  (zfuncs_za gv * @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
   @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
   EX dt : val, @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp)%logic.

(* deflateEnd(strm): DSpec's deflateEnd_spec with the allocator's events: a live stream gives its blocks back
   (unless its status is invalid: Z_STREAM_ERROR, nothing freed). *)
Definition za_deflateEnd_spec :=
 DECLARE _deflateEnd
 WITH os : option dstate, p : dptrs, strmp : val, ni : val, z : strm, r : option dstate * strm * Z,
      gv : globals, tr : list zev
 PRE [ tptr t_strm ]
  PROP (match os with Some s => c_deflateEnd s z = Some r | None => r = (None, z, Z_STREAM_ERROR) end;
        is_pointer_or_null za_opaque)
  PARAMS (strmp) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dend_stream os p strmp gv; za_res gv tr)
 POST [ tint ]
  EX tr' : list zev,
  PROP (match os, fst (fst r) with Some s, None => tr' = tr ++ dend_events s p | _, _ => tr' = tr end)
  RETURN (vi (snd r))
  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; match os, fst (fst r) with
       | Some _, None => dclosed strmp gv
       | None, _ => dstream_za 2 None strmp nullval gv
       | Some _, Some _ => dend_stream os p strmp gv
       end;
       za_res gv tr').

(* The callee contexts: ZALLOC / ZFREE go through the function pointers of za_funcs. *)
Definition Gprog_za_deflateEnd : funspecs := [deflateStateCheck_spec_za].
Definition Gprog_za_deflateInit2_ : funspecs := [memset_spec; za_deflateEnd_spec; deflateReset_spec_v9_za].

End ZA.

(* The two bodies, for every allocator. *)
Definition za_deflate_api_stmt : Prop :=
  forall ZA : zallocator,
  @semax_body DSpec.Vprog (@Gprog_za_deflateInit2_ ZA) DCS.CS f_deflateInit2_ (@za_deflateInit2__spec ZA) /\
  @semax_body DSpec.Vprog (@Gprog_za_deflateEnd ZA) DCS.CS f_deflateEnd (@za_deflateEnd_spec ZA).

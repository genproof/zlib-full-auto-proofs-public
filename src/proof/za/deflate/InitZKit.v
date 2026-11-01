(* The body of deflateInit2_ with a caller-supplied allocator (InitZ.v) is proved in three parts, so that no proof
   term is too large to check in one piece: the main part up to the test of the four buffer allocations
   ([if (s->window == Z_NULL || s->prev == Z_NULL || s->head == Z_NULL || s->pending_buf == Z_NULL)]), the branch
   where one of them failed (InitZFail.v: the stream is freed by deflateEnd, Z_MEM_ERROR) and the rest of the
   function where all of them succeeded (InitZOk.v: the state is completed, deflateReset).  This file: the two
   fragments of the body, the state at the test (its precondition) and the function's postcondition. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.ApiKit.
Require Import Zlib.proof.deflate.ZeroBytes Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2.
Require Import Zlib.proof.deflate.InitFacts Zlib.proof.deflate.InitTac.
Require Import Zlib.proof.deflate.InitParts.
Require Import Zlib.proof.za.deflate.InitZParts.

(** The sub-statement of a statement at a path (0/1: the parts of a sequence or a loop, 1/2: the branches of an
    if). *)
Fixpoint iz_ssub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => iz_ssub a path'
    | Ssequence _ b, S O => iz_ssub b path'
    | Sloop a _, O => iz_ssub a path'
    | Sloop _ b, S O => iz_ssub b path'
    | Sifthenelse _ a _, S O => iz_ssub a path'
    | Sifthenelse _ _ b, S (S O) => iz_ssub b path'
    | _, _ => Sskip
    end
  end.

Definition IZ (path : list nat) : statement := iz_ssub (fn_body f_deflateInit2_) path.

(** The test of the four allocations is at [IZ (repeat 1 32 ++ [0; 1])]: its then-branch (Z_MEM_ERROR) and the
    rest of the function. *)
Definition IZ_fail : statement := IZ (repeat 1%nat 32 ++ [0; 1; 1])%nat.
Definition IZ_rest : statement := IZ (repeat 1%nat 33).

Section ZA.
Context {ZA : zallocator}.

Definition Delta_iz : tycontext := func_tycontext f_deflateInit2_ DSpec.Vprog (@Gprog_za_deflateInit2_ ZA) nil.

(** The postcondition of the body (za_deflateInit2__spec's, for the parameters at hand). *)
Definition iz_fpost (strmp : val) (level wbits mem strategy : Z) (vp : val) (vsh : share) (vers : list Z)
    (ssize : Z) (ni tin tout msgv adler st0 : val) (gv : globals) (tr : list zev) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (EX (a1 a2 a3 a4 a5 : bool) (r : option dstate * strm * Z)
        (tr' : list zev),
        PROP (c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level 8
                wbits mem strategy a1 a2 a3 a4 a5 zrst0 = 
              Some r;
        match fst (fst r) with
        | Some s => tr' = tr ++ dinit_events s
        | None =>
            za_now tr' = za_now tr /\
            (snd r = Z_MEM_ERROR -> za_failed tr' = true)
        end)
        RETURN (vi (snd r)) SEP (match fst (fst r) with
                                 | Some _ =>
                                     dstream_za 2 (fst (fst r)) strmp nullval
                                       gv
                                 | None =>
                                     EX st dt' : val,
                                     !! (snd r = Z_VERSION_ERROR -> st = st0) &&
                                     (za_funcs *
                                      field_at_ Ews t_strm 
                                        (DOT _reserved) strmp *
                                      field_at Ews t_strm (DOT _state) st strmp *
                                      field_at Ews t_strm 
                                        (DOT _zalloc) za_alloc strmp *
                                      field_at Ews t_strm 
                                        (DOT _zfree) za_free strmp *
                                      field_at Ews t_strm 
                                        (DOT _opaque) za_opaque strmp *
                                      field_at Ews t_strm 
                                        (DOT _data_type) dt' strmp)
                                 end;
                            field_at Ews t_strm (DOT _next_in) ni strmp;
                            EX msgv' : val,
                            !! (if snd r =? Z_VERSION_ERROR
                                then msgv' = msgv
                                else msg_ok (z_msg (snd (fst r))) msgv') &&
                            reset_fields strmp
                              (rfv (snd r =? Z_OK) (z_total_in (snd (fst r)))
                                 tin)
                              (rfv (snd r =? Z_OK) (z_total_out (snd (fst r)))
                                 tout) msgv'
                              (rfv (snd r =? Z_OK) (z_adler (snd (fst r)))
                                 adler);
                            data_at vsh (tarray tschar (Zlength vers))
                              (map vi vers) vp; za_res gv tr';
                            deflate_globals gv))%argsassert)
    (stackframe_of f_deflateInit2_).

(** The state at the test of the four allocations: the temporaries, the zeroed state with its fields written, the
    four buffers (each Z_NULL or allocated) and the allocator's events so far. *)
Definition iz_pre (strmp : val) (level wbits mem strategy : Z) (vp : val) (vsh : share) (vers : list Z)
    (ni tin tout adler dt : val) (gv : globals) (tr : list zev) (sp pw pp ph pb : val) : environ -> mpred :=

  (PROP ( )
   LOCAL (temp _t'21
            (Val.of_bool
               ((if eq_dec pw nullval then true else false)
                || (if eq_dec pp nullval then true else false)
                || (if eq_dec ph nullval then true else false)
                || (if eq_dec pb nullval then true else false)));
   temp _t'20
     (Val.of_bool
        ((if eq_dec pw nullval then true else false)
         || (if eq_dec pp nullval then true else false)
         || (if eq_dec ph nullval then true else false)));
   temp _t'19
     (Val.of_bool
        ((if eq_dec pw nullval then true else false)
         || (if eq_dec pp nullval then true else false))); 
   temp _t'31 pw; temp _t'33 (Vint (Int.repr (Z.shiftl 1 (mem + 6))));
   temp _t'16 pb; temp _t'36 (Vint (Int.repr (Z.shiftl 1 (mem + 6))));
   temp _t'35 za_opaque; temp _t'34 za_alloc; temp _t'15 ph;
   temp _t'39 (Vint (Int.repr (Z.shiftl 1 (mem + 7)))); 
   temp _t'38 za_opaque; temp _t'37 za_alloc; temp _t'14 pp;
   temp _t'42 (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits))));
   temp _t'41 za_opaque; temp _t'40 za_alloc; temp _t'13 pw;
   temp _t'45 (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits))));
   temp _t'44 za_opaque; temp _t'43 za_alloc;
   temp _t'46 (Vint (Int.repr (mem + 7)));
   temp _t'47 (Vint (Int.repr (Z.shiftl 1 (mem + 7))));
   temp _t'48 (Vint (Int.repr (mem + 7)));
   temp _t'49 (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits))));
   temp _t'50 (Vint (Int.repr (i_wb9 wbits))); temp _s sp; 
   temp _t'12 sp; temp _t'52 za_opaque; temp _t'51 za_alloc;
   temp _windowBits (vi (i_wb9 wbits)); temp _wrap (vi (i_wr wbits));
   gvars gv; temp _strm strmp; temp _level (vi (i_lv level));
   temp _method (vi 8); temp _memLevel (vi mem);
   temp _strategy (vi strategy))
   SEP (za_res gv
          (((((tr ++ [ZAlloc (1 * 5968)]) ++
              zalloc_ev pw (Z.shiftl 1 (i_wb9 wbits) * 2)) ++
             zalloc_ev pp (Z.shiftl 1 (i_wb9 wbits) * 2)) ++
            zalloc_ev ph (Z.shiftl 1 (mem + 7) * 2)) ++
           zalloc_ev pb (Z.shiftl 1 (mem + 6) * 4));
   if eq_dec pb nullval
   then emp
   else
    za_tok (tarray tuchar (4 * Z.shiftl 1 (mem + 6))) pb *
    data_at_ Ews (tarray tuchar (4 * Z.shiftl 1 (mem + 6))) pb;
   if eq_dec ph nullval
   then emp
   else
    za_tok (tarray tushort (Z.shiftl 1 (mem + 7))) ph *
    data_at_ Ews (tarray tushort (Z.shiftl 1 (mem + 7))) ph;
   if eq_dec pp nullval
   then emp
   else
    za_tok (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) pp *
    data_at_ Ews (tarray tushort (Z.shiftl 1 (i_wb9 wbits))) pp;
   if eq_dec pw nullval
   then emp
   else
    za_tok (tarray tuchar (2 * Z.shiftl 1 (i_wb9 wbits))) pw *
    data_at_ Ews (tarray tuchar (2 * Z.shiftl 1 (i_wb9 wbits))) pw; 
   zrest sp; zpad sp; field_at Ews t_strm (DOT _next_in) ni strmp;
   field_at Ews t_strm (DOT _total_in) tin strmp;
   field_at Ews t_strm (DOT _total_out) tout strmp;
   field_at Ews t_strm (DOT _adler) adler strmp;
   field_at Ews t_strm (DOT _data_type) dt strmp;
   field_at_ Ews t_strm (DOT _reserved) strmp;
   data_at vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
   deflate_globals gv; field_at Ews t_ds (DOT _strm) strmp sp;
   field_at Ews t_ds (DOT _status) (Vint (Int.repr 42)) sp;
   field_at Ews t_ds (DOT _wrap) (Vint (Int.repr (i_wr wbits))) sp;
   field_at Ews t_ds (DOT _gzhead)
     (Vlong (Int64.repr (Int.signed (Int.repr 0)))) sp;
   field_at Ews t_ds (DOT _w_bits) (Vint (Int.repr (i_wb9 wbits))) sp;
   field_at Ews t_ds (DOT _w_size)
     (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits)))) sp;
   field_at Ews t_ds (DOT _w_mask)
     (Vint (Int.repr (Z.shiftl 1 (i_wb9 wbits) - 1))) sp;
   field_at Ews t_ds (DOT _hash_bits) (Vint (Int.repr (mem + 7))) sp;
   field_at Ews t_ds (DOT _hash_size)
     (Vint (Int.repr (Z.shiftl 1 (mem + 7)))) sp;
   field_at Ews t_ds (DOT _hash_mask)
     (Vint (Int.repr (Z.shiftl 1 (mem + 7) - 1))) sp;
   field_at Ews t_ds (DOT _hash_shift)
     (Vint (Int.divu (Int.repr (mem + 7 + 3 - 1)) (Int.repr 3))) sp;
   field_at Ews t_ds (DOT _window) pw sp;
   field_at Ews t_ds (DOT _prev) pp sp; field_at Ews t_ds (DOT _head) ph sp;
   field_at Ews t_ds (DOT _high_water)
     (Vlong (Int64.repr (Int.signed (Int.repr 0)))) sp;
   field_at Ews t_ds (DOT _lit_bufsize)
     (Vint (Int.repr (Z.shiftl 1 (mem + 6)))) sp;
   field_at Ews t_ds (DOT _pending_buf) pb sp;
   field_at Ews t_ds (DOT _pending_buf_size)
     (Vlong
        (Int64.mul
           (Int64.repr (Int.unsigned (Int.repr (Z.shiftl 1 (mem + 6)))))
           (Int64.repr (Int.signed (Int.repr 4))))) sp;
   field_at Ews t_ds (DOT _sym_buf) nullval sp;
   field_at Ews t_ds (DOT _sym_end) (vi 0) sp;
   field_at Ews t_ds (DOT _level) (vi 0) sp;
   field_at Ews t_ds (DOT _strategy) (vi 0) sp;
   field_at Ews t_ds (DOT _method) (vi 0) sp; za_tok t_ds sp;
   field_at Ews t_strm (DOT _state) sp strmp; func_ptr' zalloc_spec za_alloc;
   func_ptr' zfree_spec za_free;
   field_at Ews t_strm (DOT _msg) nullval strmp;
   field_at Ews t_strm (DOT _zalloc) za_alloc strmp;
   field_at Ews t_strm (DOT _zfree) za_free strmp;
   field_at Ews t_strm (DOT _opaque) za_opaque strmp)).

End ZA.

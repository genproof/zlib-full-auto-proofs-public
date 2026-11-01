(* The counting allocator of the memory laws (res_free_deflate, res_free_inflate, res_memory_deflate,
   res_memory_inflate): count_alloc, count_free and counted_stream, the same Clight term in the four harness
   units (taken here from res_free_deflate's).

   count_alloc(opaque, items, size) takes a block of sizeof(size_t) + items * size bytes from malloc, writes the
   size items * size in its first word, adds it to count->now (and raises count->peak to count->now), and hands
   out the bytes after the header; when malloc returns NULL it sets count->failed to 1 and returns Z_NULL;
   count_free(opaque, address) reads the size back, subtracts it from count->now and frees the whole block.
   As a caller-supplied allocator of zlib (src/proof/zutil/ZAlloc.v) it is [counted cp za zf]: opaque = cp
   (the struct count), zalloc = za and zfree = zf (the two functions), its state [count_res] the struct count
   holding the counters [cnt tr] of the events, as the C code computes them in size_t (modulo 2^64), and the
   flag [cnt_failed tr] (1 once an allocation failed), and a block's token [count_tok] its size header and the
   malloc token of the whole block. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Export Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Compress.
Require Zlib.harness.res_free_deflate.code.
Module HC := Zlib.harness.res_free_deflate.code.

(* the counters now and peak after the events, in size_t arithmetic *)
Definition cnt_step (np : Z * Z) (e : zev) : Z * Z :=
  match e with
  | ZAlloc n => let now := (fst np + n) mod 2 ^ 64 in (now, if snd np <? now then now else snd np)
  | ZFree n => ((fst np - n) mod 2 ^ 64, snd np)
  | ZFail => np
  end.
Definition cnt (tr : list zev) : Z * Z := fold_left cnt_step tr (0, 0).

(* the flag failed after the events *)
Definition cnt_failed (tr : list zev) : Z := if za_failed tr then 1 else 0.

(* The compspecs of the harness unit: struct z_stream_s and struct count. *)
#[local] Instance CS_count : compspecs. make_compspecs HC.prog. Defined.
Definition t_count : type := Tstruct HC._count noattr.

(* a block of type t handed out at p: its header (the size, one size_t just before p) and the malloc token of
   the block of 8 + sizeof t bytes that starts at the header *)
Definition count_tok {cs : compspecs} (t : type) (p : val) : mpred :=
  (@data_at cs Ews tulong (Vlong (Int64.repr (@sizeof cs t))) (offset_val (-8) p) *
   @malloc_token cs Ews (tarray tuchar (8 + @sizeof cs t)) (offset_val (-8) p))%logic.

(* the struct count at cp with the counters and the flag of the events, and malloc's state *)
Definition count_res (cp : val) (gv : globals) (tr : list zev) : mpred :=
  (mem_mgr gv *
   @data_at CS_count Tsh t_count
     (Vlong (Int64.repr (fst (cnt tr))), (Vlong (Int64.repr (snd (cnt tr))), Vint (Int.repr (cnt_failed tr)))) cp)%logic.

Definition counted (cp za zf : val) : zallocator := {|
  za_alloc := za; za_free := zf; za_opaque := cp;
  za_res := count_res cp;
  za_tok := @count_tok;
  za_cap := Int64.max_unsigned |}.

(* count_alloc and count_free meet zalloc_spec and zfree_spec of [counted cp za zf], for every cp, za, zf
   (WITH: the struct count and the two function pointers are main's). *)
Definition count_alloc_spec :=
  DECLARE HC._counted_alloc
  WITH cp : val, za : val, zf : val, t : type, items : Z, size : Z, gv : globals, tr : list zev
  PRE [ tptr tvoid, tuint, tuint ]
    PROP (0 <= items <= Int.max_unsigned; 0 <= size <= Int.max_unsigned;
          (items * size <= Int.max_unsigned)%Z; sizeof t = (items * size)%Z;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (cp; Vint (Int.repr items); Vint (Int.repr size)) GLOBALS (gv)
    SEP (count_res cp gv tr)
  POST [ tptr tvoid ] EX p : val,
    PROP ()
    RETURN (p)
    SEP (if eq_dec p nullval then count_res cp gv (tr ++ [ZFail])
         else count_res cp gv (tr ++ [ZAlloc (items * size)]) * count_tok t p * data_at_ Ews t p).

Definition count_free_spec :=
  DECLARE HC._counted_free
  WITH cp : val, za : val, zf : val, t : type, p : val, gv : globals, tr : list zev
  PRE [ tptr tvoid, tptr tvoid ]
    PROP ()
    PARAMS (cp; p) GLOBALS (gv)
    SEP (count_res cp gv tr; count_tok t p; data_at_ Ews t p)
  POST [ tvoid ]
    PROP () RETURN () SEP (count_res cp gv (tr ++ [ZFree (sizeof t)])).

(* counted_stream(strm, count): the counters and the flag 0 (the struct count of no events), zalloc / zfree /
   opaque the counting allocator, and set_buffer(strm, Z_NULL, 0, Z_NULL, 0); every other member unchanged *)
Definition counted_stream_spec :=
  DECLARE HC._counted_stream
  WITH sp : val, sh : share, cp : val, gv : globals,
       ni : val, ai : val, ti : val, no : val, ao : val, to : val, msg : val, st : val,
       za : val, zf : val, op : val, dt : val, ad : val, rs : val
  PRE [ tptr t_zs, tptr t_count ]
    PROP (writable_share sh)
    PARAMS (sp; cp) GLOBALS (gv)
    SEP (@data_at Zlib.units.Compress.CS sh t_zs (zs_val ni ai ti no ao to msg st za zf op dt ad rs) sp;
         data_at_ Tsh t_count cp)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (@data_at Zlib.units.Compress.CS sh t_zs
           (zs_val nullval (Vint (Int.repr 0)) ti nullval (Vint (Int.repr 0)) to msg st
                   (gv HC._counted_alloc) (gv HC._counted_free) cp dt ad rs) sp;
         data_at Tsh t_count (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vint (Int.repr 0))) cp).

(* The contexts of the three bodies. *)
Definition Vprog_count : varspecs := [].
Definition Gprog_count_alloc : funspecs := [(_quickproof_malloc, @malloc_spec' CS_count)].
Definition Gprog_count_free : funspecs := [(_quickproof_free, @free_spec' CS_count)].
Definition Gprog_counted_stream : funspecs := [@offer_spec; count_alloc_spec; count_free_spec].

(* The bodies of the three helpers against their specifications, moved into each law with entry_shared. *)
Definition counted_ok : Prop :=
  @semax_body Vprog_count Gprog_count_alloc CS_count HC.f_counted_alloc count_alloc_spec /\
  @semax_body Vprog_count Gprog_count_free CS_count HC.f_counted_free count_free_spec /\
  @semax_body Vprog_count Gprog_counted_stream CS_count HC.f_counted_stream counted_stream_spec.

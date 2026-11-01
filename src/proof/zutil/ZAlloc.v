(* A caller-supplied allocator of a z_stream (zlib.h: "If zalloc and zfree are set to Z_NULL by the application,
   ... the library uses its default allocator; otherwise they are the application's").

   Spec.v specifies zutil.c's default allocator zcalloc/zcfree, and the existing specifications of deflate.c and
   inflate.c fix strm->zalloc = zcalloc, strm->zfree = zcfree, strm->opaque = Z_NULL and malloc tokens for the
   blocks.  This file is the interface of ANY allocator an application may give instead:

   - [za_alloc], [za_free], [za_opaque]: the values of strm->zalloc, strm->zfree and strm->opaque;
   - [za_res gv tr]: the allocator's own state, after the events [tr] (each successful allocation of n bytes,
     each allocation that returned Z_NULL, each release of a block of n bytes, in order); the allocator may
     count them (the memory laws count the bytes and record that an allocation failed);
   - [za_tok t p]: what the allocator hands out with a block of type t at p and takes back when it is freed
     (for zcalloc: malloc_token Ews t p; for the counting allocator of the res_* harnesses, the block's size
     header and the malloc token of the whole block); it may use the compspecs of the specification (the size
     of t);
   - [za_cap]: the allocator can account the bytes it holds up to this bound (the counting allocator keeps
     its counters in size_t variables): zalloc may be called when the bytes held stay within it.

   [zalloc_spec] and [zfree_spec] are what zlib requires of the two functions: zalloc(opaque, items, size)
   returns Z_NULL (event ZFail) or a block of items * size bytes (event ZAlloc), zfree(opaque, p) takes back a
   block zalloc gave (event ZFree).  The block
   is given and taken back at a type t of that size, as zcalloc_spec / zcfree_spec do. *)
Require Import VST.floyd.proofauto.

(* The events an allocator sees: an allocation of n bytes that succeeded, the release of a block of n bytes, an
   allocation that failed (zalloc returned Z_NULL: zlib.h's Z_MEM_ERROR, "not enough memory", comes from one). *)
Inductive zev := ZAlloc (n: Z) | ZFree (n: Z) | ZFail.

(* The bytes held and the most ever held, after the events (both 0 at the start). *)
Definition zev_step (np: Z * Z) (e: zev) : Z * Z :=
  match e with
  | ZAlloc n => (fst np + n, Z.max (snd np) (fst np + n))
  | ZFree n => (fst np - n, snd np)
  | ZFail => np
  end.
Definition za_count (tr: list zev) : Z * Z := fold_left zev_step tr (0, 0).
Definition za_now (tr: list zev) : Z := fst (za_count tr).
Definition za_peak (tr: list zev) : Z := snd (za_count tr).

(* Some allocation of the events failed. *)
Definition za_failed (tr: list zev) : bool := existsb (fun e => match e with ZFail => true | _ => false end) tr.

Class zallocator := ZAllocator {
  za_alloc : val;
  za_free : val;
  za_opaque : val;
  za_res : globals -> list zev -> mpred;
  za_tok : forall {cs: compspecs}, type -> val -> mpred;
  za_cap : Z
}.

Section Specs.
Context {cs: compspecs} {ZA: zallocator}.

(* zalloc(opaque, items, size): Z_NULL (the event ZFail, nothing allocated) or a block of items * size bytes,
   at the type t of that size.  The product is computed in unsigned int by zcalloc: the precondition excludes overflow, as
   zcalloc_spec's does. *)
Definition zalloc_spec : funspec :=
  WITH t: type, items: Z, size: Z, gv: globals, tr: list zev
  PRE [ tptr tvoid, tuint, tuint ]
    PROP (0 <= items <= Int.max_unsigned; 0 <= size <= Int.max_unsigned;
          (items * size <= Int.max_unsigned)%Z; sizeof t = (items * size)%Z;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true;
          za_now tr + items * size <= za_cap)
    PARAMS (za_opaque; Vint (Int.repr items); Vint (Int.repr size)) GLOBALS (gv)
    SEP (za_res gv tr)
  POST [ tptr tvoid ] EX p: val,
    PROP ()
    RETURN (p)
    SEP (if eq_dec p nullval then za_res gv (tr ++ [ZFail])
         else za_res gv (tr ++ [ZAlloc (items * size)]) * za_tok t p * data_at_ Ews t p).

(* zfree(opaque, p): takes back the block p of type t that zalloc gave. *)
Definition zfree_spec : funspec :=
  WITH t: type, p: val, gv: globals, tr: list zev
  PRE [ tptr tvoid, tptr tvoid ]
    PROP ()
    PARAMS (za_opaque; p) GLOBALS (gv)
    SEP (za_res gv tr; za_tok t p; data_at_ Ews t p)
  POST [ tvoid ]
    PROP () RETURN () SEP (za_res gv (tr ++ [ZFree (sizeof t)])).

(* The two functions as the function pointers strm->zalloc and strm->zfree (deflateStateCheck and
   inflateStateCheck compare them with 0; ZALLOC and ZFREE call through them). *)
Definition za_funcs : mpred :=
  (func_ptr' zalloc_spec za_alloc * func_ptr' zfree_spec za_free)%logic.

End Specs.

(* Facts about the counters. *)
Lemma za_count_app: forall tr e, za_count (tr ++ [e]) = zev_step (za_count tr) e.
Proof. intros. unfold za_count. rewrite fold_left_app. reflexivity. Qed.

Lemma za_now_alloc: forall tr n, za_now (tr ++ [ZAlloc n]) = za_now tr + n.
Proof. intros. unfold za_now. rewrite za_count_app. reflexivity. Qed.

Lemma za_now_free: forall tr n, za_now (tr ++ [ZFree n]) = za_now tr - n.
Proof. intros. unfold za_now. rewrite za_count_app. reflexivity. Qed.

Lemma za_peak_alloc: forall tr n, za_peak (tr ++ [ZAlloc n]) = Z.max (za_peak tr) (za_now tr + n).
Proof. intros. unfold za_peak, za_now. rewrite za_count_app. reflexivity. Qed.

Lemma za_peak_free: forall tr n, za_peak (tr ++ [ZFree n]) = za_peak tr.
Proof. intros. unfold za_peak. rewrite za_count_app. reflexivity. Qed.

Lemma za_now_nil: za_now [] = 0.
Proof. reflexivity. Qed.

Lemma za_peak_nil: za_peak [] = 0.
Proof. reflexivity. Qed.

Lemma za_now_fail: forall tr, za_now (tr ++ [ZFail]) = za_now tr.
Proof. intros. unfold za_now. rewrite za_count_app. reflexivity. Qed.

Lemma za_peak_fail: forall tr, za_peak (tr ++ [ZFail]) = za_peak tr.
Proof. intros. unfold za_peak. rewrite za_count_app. reflexivity. Qed.

Lemma za_failed_app: forall tr tr', za_failed (tr ++ tr') = orb (za_failed tr) (za_failed tr').
Proof. intros. unfold za_failed. apply existsb_app. Qed.

Lemma za_failed_fail: forall tr, za_failed (tr ++ [ZFail]) = true.
Proof. intros. rewrite za_failed_app. apply orb_true_r. Qed.

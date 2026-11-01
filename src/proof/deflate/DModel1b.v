(** * The checked model of deflate.c, part 1b: pending output

    put_byte (deflate.h macro, on pending_buf), putShortMSB, flush_pending, the output helper [out_put] (a write
    of bytes at next_out: the output object has [z_avail_out] bytes left), and the FLUSH_BLOCK_ONLY / FLUSH_BLOCK
    macros (with fix F5). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel1.
Require Export Zlib.proof.trees.CModel.
Import ListNotations.
Local Open Scope Z_scope.

(** The trees.c output part of the state, with its mask. *)
Definition d_out (s : dstate) : cout := (tr_out (d_tr s), d_pbm s).
Definition set_d_out (s : dstate) (o : cout) : dstate :=
  set_d_pbm (set_d_tr s (set_out (d_tr s) (fst o))) (snd o).

(** [put_byte(s, c)] *)
Definition c_dput_byte (s : dstate) (c : Z) : option dstate :=
  let* o := c_put_byte (d_out s) c in Some (set_d_out s o).

(** putShortMSB(s, b) *)
Definition c_putShortMSB (s : dstate) (b : Z) : option dstate :=
  let* s := c_dput_byte s (Z.shiftr b 8) in
  c_dput_byte s (Z.land b 255).

(** A write of [bytes] at next_out (zmemcpy into the output object): checks the room; does not change avail_out
    (the C updates next_out / avail_out / total_out itself, see the callers). *)
Definition out_put (z : strm) (bytes : list Z) : option strm :=
  if Zlength bytes <=? z_avail_out z then Some (set_z_out z (z_out z ++ bytes)) else None.

(** flush_pending(strm) *)
Definition c_flush_pending (s : dstate) (z : strm) : option (dstate * strm) :=
  let* o := c_tr_flush_bits (d_out s) in
  let s := set_d_out s o in
  let len := if d_pending s >? z_avail_out z then z_avail_out z else u32 (d_pending s) in
  if len =? 0 then Some (s, z) else
  let* bytes := mb_read (mkMB (o_buf (tr_out (d_tr s))) (d_pbm s)) (d_po s) len in
  let* z := out_put z bytes in
  let s := set_d_po s (d_po s + len) in
  let z := set_z_total_out z (u64 (z_total_out z + len)) in
  let z := set_z_avail_out z (z_avail_out z - len) in
  let o := tr_out (d_tr s) in
  let s := set_d_out s (mkOut (o_buf o) (o_pending o - len) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), d_pbm s) in
  let s := if d_pending s =? 0 then set_d_po s 0 else s in
  Some (s, z).

(** FLUSH_BLOCK_ONLY(s, last): _tr_flush_block with the window bytes [block_start, strstart) (NULL when
    block_start < 0), block_start = strstart, flush_pending. *)
Definition c_flush_block_only (s : dstate) (z : strm) (last : Z) : option (dstate * strm) :=
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let stored_len := u64 (d_strstart s - d_block_start s) in
  let* buf := if d_block_start s >=? 0
              then let* b := mb_read (d_window s) (d_block_start s) stored_len in Some (Some b)
              else Some None in
  let* (t, _) := c_tr_flush_block (d_trm s) buf stored_len last in
  let s := set_d_trm s t in
  let s := set_d_block_start s (d_strstart s) in
  c_flush_pending s z.

(** FLUSH_BLOCK(s, last) (fix F5): [Some (s, z, Some r)] when the macro returns [r] from the compression
    function, [Some (s, z, None)] when it falls through. *)
Definition c_flush_block (s : dstate) (z : strm) (last : Z) : option (dstate * strm * option bstate) :=
  let* (s, z) := c_flush_block_only s z last in
  if (z_avail_out z =? 0) && (negb (last =? 1) || negb (d_pending s =? 0) || negb (d_wrap s =? 0))
  then Some (s, z, Some (if last =? 1 then finish_started else need_more))
  else Some (s, z, None).

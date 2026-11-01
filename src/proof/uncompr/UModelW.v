(* The model of uncompr.c's uncompress2_z for any sizes.

   UModel.unc_loop offers each inflate() call the whole unconsumed source and the whole unfilled destination,
   which is what uncompress2_z does when both are below 2^32 bytes.  For any sizes uncompress2_z gives inflate()
   pieces of at most (uInt)-1 = 2^32-1 bytes: before each call it refills avail_out with the next piece of the
   destination only when the last call left avail_out = 0, and avail_in with the next piece of the source only
   when the last call left avail_in = 0:

       if (stream.avail_out == 0) { stream.avail_out = left > max ? max : left; left -= stream.avail_out; }
       if (stream.avail_in == 0) { stream.avail_in = len > max ? max : len; len -= stream.avail_in; }
       err = inflate(&stream, Z_NO_FLUSH);

   [uncw_loop src cap m used out ai ao err used' out'] follows these calls over the model of inflate()
   (Model2.run2, from the stream m as the previous call left it: UModel.m_next), with `used` bytes of src
   consumed, `out` written into the destination, and ai / ao the avail_in / avail_out the previous call left
   (len = |src| - used - ai and left = cap - |out| - ao are the counters of the code).  [uncompressw_rel] is
   UModel.uncompress_rel with this loop. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.uncompr.UModel.
Require Import Zlib.proof.inflate.Fixed.
Import ListNotations.
Local Open Scope Z_scope.

(* (uInt)-1, the most uncompress2_z offers in one call *)
Definition uw_max : Z := 4294967295.

(* the avail_in / avail_out of the next call: what the previous call left, or the next piece *)
Definition uw_ain (src: list Z) (used ai: Z) : Z :=
  if ai =? 0 then Z.min (Zlength src - used) uw_max else ai.
Definition uw_aout (cap: Z) (out: list Z) (ao: Z) : Z :=
  if ao =? 0 then Z.min (cap - Zlength out) uw_max else ao.

(* the call from the stream m: offered src[used .. used + uw_ain) and uw_aout bytes of space *)
Definition uw_call (src: list Z) (cap: Z) (m: mst) (used: Z) (out: list Z) (ai ao: Z) : mst :=
  m_next m (sublist used (used + uw_ain src used ai) src) (uw_aout cap out ao).

(* the loop, until the first call that does not return Z_OK *)
Inductive uncw_loop (src: list Z) (cap: Z) : mst -> Z -> list Z -> Z -> Z -> Z -> Z -> list Z -> Prop :=
| uwl_stop: forall m used out ai ao res,
    Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list (uw_call src cap m used out ai ao) res ->
    r_ret res <> Z_OK ->
    uncw_loop src cap m used out ai ao (r_ret res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
| uwl_next: forall m used out ai ao res err used' out',
    Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list (uw_call src cap m used out ai ao) res ->
    r_ret res = Z_OK ->
    uncw_loop src cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
      (uw_ain src used ai - m_snx (r_m res)) (uw_aout cap out ao - Zlength (m_ow (r_m res))) err used' out' ->
    uncw_loop src cap m used out ai ao err used' out'.

(* uncompress2(dest, &destLen, source, &sourceLen) with destLen = cap and sourceLen = |src|, for any sizes:
   return value r, *sourceLen = slen, *destLen = dlen, the destination's first bytes `out` (the rest
   unchanged); Z_MEM_ERROR with nothing changed when inflateInit_'s allocation fails *)
Definition uncompressw_rel (src: list Z) (cap: Z) (r slen dlen: Z) (out: list Z) : Prop :=
  (r = Z_MEM_ERROR /\ slen = Zlength src /\ dlen = cap /\ out = []) \/
  (exists err, uncw_loop src cap m_first 0 [] 0 0 err slen out /\ dlen = Zlength out /\
               r = unc_ret err (Zlength src - slen)).

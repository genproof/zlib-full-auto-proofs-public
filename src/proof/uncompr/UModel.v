(* The model of uncompr.c: uncompress2_z's loop of inflate() calls (Z_NO_FLUSH), each offered the
   source bytes not consumed yet and the destination space not filled yet (sizes below 2^31: one chunk
   each), over the model of inflate() (src/proof/inflate/Model2.v run2) and of inflateInit_
   (src/proof/inflate_api/Model.v init_s). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate_api.ApiModel.
Require Export Zlib.proof.inflate.Model2.
Require Import Zlib.proof.inflate.Fixed.
Import ListNotations.
Local Open Scope Z_scope.

(* the machine of the next inflate() call, from the stream as the previous call left it (m: its
   state, header, adler, msg, total_in, total_out), offered inp and aout *)
Definition m_next (m: mst) (inp: list Z) (aout: Z) : mst :=
  let s := m_s m in
  let s := if i_mode s =? TYPE then set_i_mode s TYPEDO else s in
  MS s (m_h m) inp aout 0 [] (i_hold s) (i_bits s) (Zlength inp) aout Z_OK 0
     (m_adler m) (m_msg m) (m_tin m) (m_tout m) 0 0.

Definition default_h : hstate := HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0.

(* the stream after inflateInit_ (windowBits 15: wrap 5, wbits 15; adler = 1, totals 0, msg NULL) *)
Definition m_first : mst :=
  MS (init_s 5 15) default_h [] 0 0 [] 0 0 0 0 Z_OK 0 1 None 0 0 0 0.

(* unc_loop src cap m used out err used' out': from the stream m having consumed `used` bytes of src
   and written `out` into the destination, the calls end with return code err (the first that is not
   Z_OK), having consumed used' bytes and written out' *)
Inductive unc_loop (src: list Z) (cap: Z) : mst -> Z -> list Z -> Z -> Z -> list Z -> Prop :=
| ul_stop: forall m used out res,
    Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list (m_next m (sublist used (Zlength src) src) (cap - Zlength out)) res ->
    r_ret res <> Z_OK ->
    unc_loop src cap m used out (r_ret res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
| ul_next: forall m used out res err used' out',
    Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list (m_next m (sublist used (Zlength src) src) (cap - Zlength out)) res ->
    r_ret res = Z_OK ->
    unc_loop src cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res)) err used' out' ->
    unc_loop src cap m used out err used' out'.

(* uncompress2_z's return value from the last inflate() code and the unconsumed input *)
Definition unc_ret (err rest: Z) : Z :=
  if err =? Z_STREAM_END then Z_OK
  else if err =? Z_NEED_DICT then Z_DATA_ERROR
  else if (err =? Z_BUF_ERROR) && (rest =? 0) then Z_DATA_ERROR
  else err.

(* uncompress2(dest, &destLen, source, &sourceLen) with destLen = cap and sourceLen = |src|:
   return value r, *sourceLen = slen, *destLen = dlen, the destination's first bytes `out` (the rest
   unchanged).  init_ok: inflateInit_'s allocation succeeds. *)
Definition uncompress_rel (src: list Z) (cap: Z) (r slen dlen: Z) (out: list Z) : Prop :=
  (r = Z_MEM_ERROR /\ slen = Zlength src /\ dlen = cap /\ out = []) \/
  (exists err, unc_loop src cap m_first 0 [] err slen out /\ dlen = Zlength out /\
               r = unc_ret err (Zlength src - slen)).

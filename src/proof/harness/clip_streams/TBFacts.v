(* Law rfc_trailing_bytes: THE interface between the inflate part of its main (VST) and the decode theory.

   As IFacts.trl_facts, with the input's length bounded by the size of an object (Ptrofs.max_unsigned) instead
   of PTRDIFF_MAX: the compressed bytes O fill an object of deflateBound_z bytes, which may be longer than
   PTRDIFF_MAX (data of up to PTRDIFF_MAX bytes stored with the stored blocks' overhead); the harness then adds
   no bytes (room = 0) and the input is O itself.

   [tail_facts P]: an invariant P of the call boundaries (IFacts.inv_t) of the inflate loop over the input src =
   O followed by any bytes: it holds after inflateInit2 (tl_init), and a call that does not run out of memory
   returns Z_OK, Z_BUF_ERROR or Z_STREAM_END, and either returns Z_STREAM_END having consumed exactly the bytes
   of O, or keeps it (tl_call). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.clip_streams.IFacts.
Import ListNotations.
Local Open Scope Z_scope.

Record tail_facts (P: inv_t) : Prop := {
  tl_ok : inv_ok P;
  tl_init : forall wbits D O src z sp,
    dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> Int.min_signed <= wbits <= Int.max_signed ->
    init_ok (iwb wbits) z sp ->
    Zlength O <= Zlength src <= Ptrofs.max_unsigned -> sublist 0 (Zlength O) src = O -> bytes_ok src ->
    P wbits D O src 0 [] z (init_live sp (iwb wbits));
  tl_call : forall wbits D O src pos out z L strmp flush ib inp o aout r z' st' ow,
    P wbits D O src pos out z L -> call_pre src pos z L strmp flush ib inp o aout ->
    pos + Zlength inp <= Zlength src ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    r <> Z_MEM_ERROR -> zf_ok z' ->
    exists L', call_post ib inp o aout z' st' ow L' /\
      (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
      (r = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O) /\
      (r <> Z_STREAM_END -> P wbits D O src (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L')
}.

Definition tail_stmt : Prop := exists P, tail_facts P.

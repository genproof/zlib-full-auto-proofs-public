(* The laws rt_dictionary and api_dict_id: THE interface between the inflate part of their mains (VST) and the
   decode theory.

   After the deflate loop (DWFacts.v) ended with Z_STREAM_END, the n bytes D of data were compressed with the
   dictionary dict into the zlib stream O ([DWFacts.dfinal_dict wbits dict D O]).  Both harnesses set up a new
   stream with new_stream() and inflateInit2(windowBits) (8 is given as 9: IFacts.iwb), offer it the first
   clip(|O|) bytes of O and clip(n) bytes of the output object (of n bytes), and call inflate() with any flush:
   - [di_first]: that call returns Z_NEED_DICT after the zlib header and DICTID (6 bytes), with nothing written
     and strm->adler the Adler-32 of the whole dictionary (api_dict_id ends here);
   - [di_set]: inflateSetDictionary(strm, dict, |dict|) then returns Z_OK or Z_MEM_ERROR (the window cannot be
     allocated: the run ends);
   - [di_call]: rt_dictionary then calls inflate(Z_FINISH) in a loop, each call offered the next
     clip(|O| - pos) bytes of O (pos: the bytes consumed) and the next clip(n - |out|) bytes of the output
     object (out: the bytes written), while the call returns Z_BUF_ERROR and was offered less than all the
     rest: a call returns Z_STREAM_END or Z_BUF_ERROR (Z_MEM_ERROR ends the run); Z_BUF_ERROR only from a call
     offered less than the rest of the input or of the output; Z_STREAM_END with all of O consumed and D
     written.
   The theory chooses the invariants [Q wbits dict D O z L] (after the first call) and
   [P wbits dict D O pos out z L] (at the call boundaries of the loop), existential so that the mains and the
   theory are independent.  Everything is over Spec5's relations (inflate_rel over Model2.run2, init_live,
   setdict_f), those of SpecW's wide specifications of inflate() and inflateSetDictionary. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.clip_streams.IFacts.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Import ListNotations.
Local Open Scope Z_scope.

Definition qinv_t : Type := Z -> list Z -> list Z -> list Z -> zfields -> live -> Prop.
Definition dinv_t : Type := Z -> list Z -> list Z -> list Z -> Z -> list Z -> zfields -> live -> Prop.

Record dict_ifacts (Q : qinv_t) (P : dinv_t) : Prop := {
  (** what the loop's invariant says: a zlib stream without gz_header, the position in O, the output a prefix
      of D *)
  di_ok : forall wbits dict D O pos out z L, P wbits dict D O pos out z L ->
    i_head (l_s L) = false /\ i_wrap (l_s L) <> 0 /\ 0 <= pos <= Zlength O /\ exists rest, D = out ++ rest;
  (** the first call, from the stream inflateInit2_ set up, any flush *)
  di_first : forall wbits dict D O z sp strmp flush ib inp o aout r z' st' ow,
    dfinal_dict wbits dict D O -> 1 <= Zlength dict <= dict_max -> Zlength O <= 2 ^ 64 - 1 ->
    init_ok (iwb wbits) z sp ->
    call_pre O 0 z (init_live sp (iwb wbits)) strmp flush ib inp o aout ->
    Zlength inp = clipz (Zlength O) ->
    inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout)
      (Some (init_live sp (iwb wbits))) ib inp (Some o) r z' st' ow ->
    zf_ok z' ->
    r = Z_NEED_DICT /\ zf_adler z' = Zlib.proof.adler32.Model.ref_adler32 1 dict /\
    exists L', call_post ib inp o aout z' st' ow L' /\ Zlength inp - zf_ai z' = 6 /\ ow = [] /\
      i_head (l_s L') = false /\ i_wrap (l_s L') <> 0 /\ Q wbits dict D O z' L';
  (** inflateSetDictionary(strm, dict, |dict|) right after it: Z_OK (the loop starts at position 6, nothing
      written, with the state's wide invariant swfW that SpecW.inflate_specW asks for) or Z_MEM_ERROR *)
  di_set : forall wbits dict D O z L alloc_ok winp,
    Q wbits dict D O z L -> live_ok L ->
    let sd := setdict_f dict alloc_ok winp z L in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> snd3 sd = z /\ swfW (l_s (thd3 sd)) /\ P wbits dict D O 6 [] z (thd3 sd));
  (** a call of the loop: inflate(Z_FINISH) offered the next clip(|O| - pos) bytes of O and the next
      clip(|D| - |out|) bytes of the output object *)
  di_call : forall wbits dict D O pos out z L strmp ib inp o aout r z' st' ow,
    P wbits dict D O pos out z L -> call_pre O pos z L strmp Z_FINISH ib inp o aout ->
    Zlength inp = clipz (Zlength O - pos) -> aout = clipz (Zlength D - Zlength out) ->
    inflate_rel Z_FINISH strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp
      (Some o) r z' st' ow ->
    r <> Z_MEM_ERROR -> zf_ok z' ->
    exists L', call_post ib inp o aout z' st' ow L' /\
      (r = Z_STREAM_END \/ r = Z_BUF_ERROR) /\
      (r = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O /\ out ++ ow = D) /\
      (r = Z_BUF_ERROR ->
         (umax < Zlength O - pos \/ umax < Zlength D - Zlength out) /\
         P wbits dict D O (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L')
}.

Definition dict_ifacts_stmt : Prop := exists Q P, dict_ifacts Q P.

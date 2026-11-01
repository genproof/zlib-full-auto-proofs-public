(* Law uncompress_any, the theory: the statements of its parts.

   The theory (UATheory.v: ua_facts_stmt of UAFacts.v) follows uncompress2_z's loop of inflate() calls
   (UModel.unc_loop over Model2.run2) with, at every call boundary, the stream as Spec5's (z, L) and
   - law inflate_check's invariant (inflate_check/IKTheoryCall.v ikc_I, windowBits 15): inflate_codes' inv
     (return codes, final codes) and IK's Kx (bit buffer, header, check value, trailer); one call by
     ikc_inflate (IK's check_post) and inflate_codes' cl_inflate (inflate_post);
   - live_ok L and zf_ok z, the call's preconditions of those lemmas, kept by a call (ua_live_stmt);
   - ua_fd: no dictionary is ever set (i_havedict = 0) and a header with FDICT never gets past DICT (mode HEAD,
     DICTID, DICT, BAD or MEM), so Z_STREAM_END only for a header without FDICT (ua_fd_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.uncompress_any.UAFacts.
Require Export Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* one inflate() call keeps live_ok and zf_ok (as inflate()'s body does: inflate_api/Body5_inflate.v) *)
Definition ua_live_stmt : Prop :=
  forall flush strmp z L ib inp o r z' st' ow,
    live_ok L -> zf_ok z -> strmp <> nullval -> ib <> InNull ->
    zf_ai z = Zlength inp -> Zlength inp <= Int.max_signed -> bytes_ok inp -> zf_ao z <= Int.max_signed ->
    inflate_rel flush strmp z (Some L) ib inp (Some o) r z' st' ow -> r <> Z_MEM_ERROR ->
    exists L', st' = Some L' /\ live_ok L' /\ zf_ok z'.

(* no dictionary; FDICT stops the stream before the data *)
Definition ua_fd (src: list Z) (s: istate) : Prop :=
  i_havedict s = 0 /\
  (fdict src -> i_mode s = HEAD \/ i_mode s = DICTID \/ i_mode s = DICT \/ i_mode s = BAD \/ i_mode s = MEM).

(* one inflate() call (the hypotheses of inflate_codes' cl_inflate, TheoryCall.v) keeps ua_fd; windowBits 15
   (inflateInit: wrap_of 15 = 5, zlib) *)
Definition ua_fd_stmt : Prop :=
  forall w src pos final indict z L strmp flush ib inp o ain aout r z' st' ow,
    w = 15 -> inv w src pos final indict z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
    0 <= pos -> 0 <= ain -> pos + ain <= Zlength src -> Zlength src <= 2 ^ 24 -> bytes_ok src ->
    0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
    ib <> InNull -> inp = sublist pos (pos + ain) src ->
    ua_fd src (l_s L) ->
    inflate_rel flush strmp (set_zf_call z (in_ptr ib 0) ain (ob_ptr (Some o)) aout) (Some L) ib inp (Some o)
      r z' st' ow ->
    exists L', st' = Some L' /\ ua_fd src (l_s L') /\ (r = Z_STREAM_END -> ~ fdict src).

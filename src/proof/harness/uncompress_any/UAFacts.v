(* Law uncompress_any: THE interface between the main of harness/uncompress_any.c (UAMain.v, VST) and the pure
   theory over the model (UATheory*.v).  Pure Coq over uncompr's model (uncompr/UModel.v uncompress_rel, the
   relation of uncompress2's / uncompress's specifications, uncompr/USpec5.v).

   main draws n <= 2^24 source bytes src (an object of n bytes, malloc'ed) and cap <= 2^20, calls
   uncompress2(dst, &dlen, src, &slen) with dlen = cap, slen = n, and gets (USpec5) r, slen, dlen, out with
   uncompress_rel src cap r slen dlen out, the destination holding out followed by its old bytes from |out| on.
   ua_facts_stmt is what the checks of main need of it; on Z_OK main calls uncompress(d2, &dlen2, src, n) with
   dlen2 = cap, which gives (USpec5) r2, slen2, dlen2, out2 with uncompress_rel src cap r2 slen2 dlen2 out2. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.uncompr.UModel.
Require Export Zlib.proof.harness.inflate_common.HDefs.
Require Export Zlib.proof.adler32.Model.
Require Export Zlib.proof.zutil.Libc.
Import ListNotations.
Local Open Scope Z_scope.

(* the zlib header checks of main (RFC 1950: CM = 8, CINFO <= 7, FCHECK, no FDICT; the bytes exist) *)
Definition ua_hdr (src: list Z) : Prop :=
  2 <= Zlength src /\ Z.land (Znth 0 src) 15 = 8 /\ Z.shiftr (Znth 0 src) 4 <= 7 /\
  (Znth 0 src * 256 + Znth 1 src) mod 31 = 0 /\ Z.land (Znth 1 src) 32 = 0.

(* what main needs of uncompress2's outcome (and, on Z_OK, of uncompress's on the same source) *)
Definition ua_facts_stmt : Prop :=
  forall src cap r slen dlen out,
    bytes_ok src -> Zlength src <= 2 ^ 24 -> 0 <= cap <= 2 ^ 20 ->
    uncompress_rel src cap r slen dlen out ->
    (r = Z_OK \/ r = Z_MEM_ERROR \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\
    0 <= slen <= Zlength src /\ Zlength out <= dlen <= cap /\ bytes_ok out /\
    (r <> Z_MEM_ERROR -> dlen = Zlength out) /\
    (r = Z_OK ->
       6 <= slen /\ ua_hdr src /\ be32 (sublist (slen - 4) slen src) = ref_adler32 1 out /\
       forall r2 slen2 dlen2 out2,
         uncompress_rel src cap r2 slen2 dlen2 out2 -> r2 <> Z_MEM_ERROR ->
         r2 = Z_OK /\ dlen2 = dlen /\ out2 = out).

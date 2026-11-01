(* Law rj_truncated, main: the inflate half (statements 19-25: prefix_len = upto(compressed_len - 1),
   new_stream(&decompressor), window_bits 8 -> 9, inflateInit2_ and its check, next_in, next_out, the while loop of
   inflate() calls with gp_assert(code != Z_STREAM_END)), from the hand-over rt_DH of RTKit.v.  The same shape as
   rt_partial's inflate half (RPKit.v): the facts that do not change during the loop and its invariant. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.harness.rj_truncated.code.
Local Open Scope logic.

(* statement 25: the while loop of inflate() calls (then the final `return 0`) *)
Definition rt_seg25 : statement := ltac:(rt_get_seg 25%nat).

(* the facts of the inflate loop that do not change: those of rt_DH and the prefix length lim < |O| *)
Definition rt_facts (wbits n b lim : Z) (D O : list Z) (dp op cp : val) : Prop :=
  DFacts.dfinal_of wbits D O /\ Zlength D = n /\ 0 <= n <= DFacts.max_size /\ 0 <= Zlength O <= b /\
  b <= Ptrofs.max_unsigned /\ Int.min_signed <= wbits <= Int.max_signed /\
  rbytes D /\ is_bytes D /\ rbytes O /\ isptr dp /\ isptr op /\ isptr cp /\ 0 <= lim < Zlength O.

(* the invariant of the inflate loop, at the head of the while: the bytes of O consumed pos <= lim (next_in =
   compressed + pos), the bytes written out (next_out = out + |out|; the output object holds out, then undefined
   bytes), the stream (z, L) with P wbits D O O pos out z L and the wide state invariant swfW that inflate_specW
   needs (strm->adler of a raw stream undefined) *)
Definition rt_inv (P : inv_t) (wbits n b lim : Z) (D O : list Z) (dp op cp vc vd : val) (gv : globals)
    : environ -> mpred :=
  EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (P wbits D O O pos out z L; swfW (l_s L); 0 <= pos <= lim;
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op; temp _compressed cp;
         temp _prefix_len (Vlong (Int64.repr lim));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); zfuncs gv; mem_mgr gv; R_rt gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; TT).

(* statements 19-24: prefix_len, new_stream, window_bits, inflateInit2_ (any outcome but Z_OK returns), next_in,
   next_out; then the loop (given) *)
Definition rt_setup_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n b D O dp op cp vc vd gv,
  pfx_facts P ->
  (forall lim, rt_facts wbits n b lim D O dp op cp ->
     semax Delta_rt (rt_inv P wbits n b lim D O dp op cp vc vd gv) rt_seg25 POST_B) ->
  semax Delta_rt (rt_DH gv vc vd wbits n b D O dp op cp) rt_seg19 POST_B.

(* statement 25 (the inflate loop) and the final `return 0` *)
Definition rt_loop_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n b lim D O dp op cp vc vd gv,
  pfx_facts P -> rt_facts wbits n b lim D O dp op cp ->
  semax Delta_rt (rt_inv P wbits n b lim D O dp op cp vc vd gv) rt_seg25 POST_B.

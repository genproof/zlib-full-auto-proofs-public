(* Law rt_partial, main (MainRP.v): the kit shared by the segment lemmas of main's body proof.
   - Delta_rp (main's type context), POST_rp (main's postcondition after start_function), POST_B (the
     postcondition of every suffix of main's statement chain: it never ends normally);
   - the segments: main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); rp_seg k is the suffix of the
     chain from its k-th statement (rp_segI: from `prefix_len = upto(compressed_len - 1)` on);
   - rp_DH: the state after the deflate loop (compressed_len = the bytes produced), where the inflate half starts;
   - rp_inv: the invariant of the inflate loop at the head of the while. *)
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
Require Import Zlib.proof.harness.clip_streams.RPDefs.
Require Import Zlib.harness.rt_partial.code.
Local Open Scope logic.

Definition Delta_rp : tycontext := func_tycontext f_main (QPvarspecs p_rp) Gmain_rpc nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_rp : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

Definition POST_B : ret_assert := overridePost FF POST_rp.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint rp_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => rp_drop n' b
  | _, _ => Sskip
  end.

Definition rp_chain (s: statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac rp_get_seg k :=
  let x := eval cbv beta iota zeta delta [rp_drop rp_chain f_main fn_body] in
    (rp_drop k (rp_chain (fn_body f_main))) in
  exact x.

Definition rp_seg0 : statement := ltac:(rp_get_seg 0%nat).

Lemma rp_body_eq : fn_body f_main = Ssequence rp_seg0 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* main's statements (0-based): 0-2 data_len, data and its NULL check, 3 expected = copy_of(data, data_len),
   4-5 out and the NULL check of expected and out, 6-9 the four ints, 10 new_stream, 11 deflateInit2_ and its
   check, 12-14 out_size, compressed and its NULL check, 15-16 next_in, next_out, 17 the deflate loop, 18 its
   check, 19 compressed_len, 20 prefix_len, 21 new_stream, 22 window_bits 8 -> 9, 23 inflateInit2_ and its check,
   24-25 next_in, next_out, 26 the inflate loop, then `return 0` *)
Definition rp_seg20 : statement := ltac:(rp_get_seg 20%nat).
Definition rp_seg26 : statement := ltac:(rp_get_seg 26%nat).

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* the copy of the data made before compression (expected = copy_of(data, data_len)): n bytes holding D at ep;
   main compares the output with it *)
Definition rp_exp (n : Z) (D : list Z) (ep : val) : mpred :=
  malloc_token Ews (tarray tuchar n) ep * data_at Ews (tarray tuchar n) (bytes_rep D) ep.

(* ---------------------------------------------------------------------------------------------- *)
(* The state after the deflate loop: the n bytes D of data (at dp) compressed into the bytes O, the first |O|
   bytes of the object of b bytes at cp; its copy at ep (rp_exp); out (op) an object of n undefined bytes; vc / vd the local streams
   (the compressor's struct given back as plain memory, the rest of its state dropped into TT) *)
Definition rp_DH (wbits n b: Z) (D O: list Z) (dp ep op cp vc vd: val) (gv: globals) : environ -> mpred :=
  PROP (DFacts.dfinal_of wbits D O; Zlength D = n; 0 <= n <= DFacts.max_size; 0 <= Zlength O <= b;
        b <= Ptrofs.max_unsigned; Int.min_signed <= wbits <= Int.max_signed;
        rbytes D; is_bytes D; rbytes O; isptr dp; isptr op; isptr cp; isptr ep)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_rp gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; rp_exp n D ep; TT).

(* the facts of the inflate loop that do not change: those of rp_DH and the prefix length lim < |O| *)
Definition rp_facts (wbits n b lim: Z) (D O: list Z) (dp ep op cp: val) : Prop :=
  DFacts.dfinal_of wbits D O /\ Zlength D = n /\ 0 <= n <= DFacts.max_size /\ 0 <= Zlength O <= b /\
  b <= Ptrofs.max_unsigned /\ Int.min_signed <= wbits <= Int.max_signed /\
  rbytes D /\ is_bytes D /\ rbytes O /\ isptr dp /\ isptr op /\ isptr cp /\ 0 <= lim < Zlength O /\
  isptr ep.

(* the invariant of the inflate loop, at the head of the while: the bytes of O consumed pos <= lim (next_in =
   compressed + pos), the bytes written out (next_out = out + |out|; the output object holds out, then undefined
   bytes), the stream (z, L) with P wbits D O O pos out z L and the wide state invariant swfW that inflate_specW
   needs (strm->adler of a raw stream undefined) *)
Definition rp_inv (P: inv_t) (wbits n b lim: Z) (D O: list Z) (dp ep op cp vc vd: val) (gv: globals)
    : environ -> mpred :=
  EX pos: Z, EX out: list Z, EX z: zfields, EX L: live,
  PROP (P wbits D O O pos out z L; swfW (l_s L); 0 <= pos <= lim;
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _expected ep; temp _out op; temp _compressed cp;
         temp _prefix_len (Vlong (Int64.repr lim));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); zfuncs gv; mem_mgr gv; R_rp gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; rp_exp n D ep; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The two parts of the inflate half                                                             *)

(* statements 20-25: prefix_len, new_stream, window_bits, inflateInit2_ (any outcome but Z_OK returns), next_in,
   next_out; then the loop (given) *)
Definition rp_setup_stmt : Prop :=
  forall {Espec: OracleKind} P wbits n b D O dp ep op cp vc vd gv,
  pfx_facts P ->
  (forall lim, rp_facts wbits n b lim D O dp ep op cp ->
     semax Delta_rp (rp_inv P wbits n b lim D O dp ep op cp vc vd gv) rp_seg26 POST_B) ->
  semax Delta_rp (rp_DH wbits n b D O dp ep op cp vc vd gv) rp_seg20 POST_B.

(* statement 26 (the inflate loop) and the final `return 0` *)
Definition rp_loop_stmt : Prop :=
  forall {Espec: OracleKind} P wbits n b lim D O dp ep op cp vc vd gv,
  pfx_facts P -> rp_facts wbits n b lim D O dp ep op cp ->
  semax Delta_rp (rp_inv P wbits n b lim D O dp ep op cp vc vd gv) rp_seg26 POST_B.

(* Law rfc_trailing_bytes, main (MainTB.v): the kit shared by the segment lemmas of main's body proof.
   - Delta_tb (main's type context), POST_tb (main's postcondition after start_function), POST_B (the
     postcondition of every suffix of main's chain of statements: each ends by a return);
   - the segments: main's body is `chain; return 0`, the chain s0; (s1; (s2; ...)); tb_seg k is the suffix of the
     chain from its k-th statement (0-based);
   - the assertions at the cuts and the CPS statement of each part of the proof.
   Main's statements (0-based): 0-7 the inputs (data_len, data, out and their NULL check, the four ints),
   8 gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy)), 9 new_stream(&compressor),
   10 code = deflateInit2_(...), 11 `if (code == Z_MEM_ERROR) return 0`, 12 gp_assert(code == Z_OK),
   13-20 as in rt_partial's main (RPKit.v: deflateBound_z and malloc, the deflate loop, compressed_len),
   21 room = 0, 22 `if (compressed_len < PTRDIFF_MAX) room = PTRDIFF_MAX - compressed_len`,
   23 after = upto(room), 24 input = any_bytes(compressed_len + after), 25 its NULL check, 26 the loop copying
   compressed[0 .. compressed_len) to input, 27 new_stream(&decompressor), 28 window_bits 8 -> 9,
   29 code = inflateInit2_(...), 30 `if (code == Z_MEM_ERROR) return 0`, 31 gp_assert(code == Z_OK),
   32-33 next_in = input, next_out = out, 34 the do-while of inflate() calls until Z_STREAM_END (with
   gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END) after each call),
   35 gp_assert(next_in == input + compressed_len), then `return 0`. *)
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
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBDefs.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Definition Delta_tb : tycontext := func_tycontext f_main (QPvarspecs p_tb) Gmain_tb4 nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_tb : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF POST_tb.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint tb_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => tb_drop n' b
  | _, _ => Sskip
  end.

Definition tb_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac tb_get_seg k :=
  let x := eval cbv beta iota zeta delta [tb_drop tb_chain f_main fn_body] in
    (tb_drop k (tb_chain (fn_body f_main))) in
  exact x.

Definition tb_seg0 : statement := ltac:(tb_get_seg 0%nat).
Definition tb_seg21 : statement := ltac:(tb_get_seg 21%nat).
Definition tb_seg27 : statement := ltac:(tb_get_seg 27%nat).
Definition tb_seg34 : statement := ltac:(tb_get_seg 34%nat).

Lemma tb_body_eq : fn_body f_main = Ssequence tb_seg0 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

Definition t_zsl : type := Tstruct _z_stream_s noattr.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

(* after start_function *)
Definition tb_A0 (gv : globals) (vc vd : val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_tb gv).

(* after the deflate loop and compressed_len (before statement 21): the n bytes D of data (at dp) compressed
   into the bytes O, the first |O| bytes of the object of b bytes at cp; out (op) an object of n undefined
   bytes; vc / vd the local streams (the compressor's struct given back as plain memory, the rest of its state
   dropped into TT).  As RPKit.rp_DH for this program. *)
Definition tb_DH (wbits n b : Z) (D O : list Z) (dp op cp vc vd : val) (gv : globals) : environ -> mpred :=
  PROP (DFacts.dfinal_of wbits D O; Zlength D = n; 0 <= n <= DFacts.max_size; 0 <= Zlength O <= b;
        b <= Ptrofs.max_unsigned; Int.min_signed <= wbits <= Int.max_signed;
        rbytes D; is_bytes D; rbytes O; isptr dp; isptr op; isptr cp)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_tb gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

(* the facts of the inflate half that do not change: those of tb_DH, and the input src (at ip): the bytes O
   followed by any bytes, an object of at most Ptrofs.max_unsigned bytes *)
Definition tb_facts (wbits n : Z) (D O src : list Z) (dp op ip : val) : Prop :=
  DFacts.dfinal_of wbits D O /\ Zlength D = n /\ 0 <= n <= DFacts.max_size /\
  Zlength O <= Zlength src <= Ptrofs.max_unsigned /\ sublist 0 (Zlength O) src = O /\ bytes_ok src /\
  Int.min_signed <= wbits <= Int.max_signed /\
  rbytes D /\ is_bytes D /\ rbytes O /\ isptr dp /\ isptr op /\ isptr ip.

(* after the copy loop (before statement 27): the input object ip holds src (after = |src| - |O|); the
   compressed object is no longer needed (dropped into TT) *)
Definition tb_TH (wbits n : Z) (D O src : list Z) (dp op ip vc vd : val) (gv : globals) : environ -> mpred :=
  PROP (tb_facts wbits n D O src dp op ip)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _window_bits (Vint (Int.repr wbits));
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _after (Vlong (Int64.repr (Zlength src - Zlength O))); temp _input ip;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_tb gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at_ Ews (tarray tuchar n) op; malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ip;
       malloc_token Ews (tarray tuchar (Zlength src)) ip;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

(* the invariant of the inflate loop (statement 34), at the head of the do-while's body: the bytes of src
   consumed pos (next_in = input + pos), the bytes written out (next_out = out + |out|; the output object holds
   out, then undefined bytes), the stream (z, L) with P wbits D O src pos out z L and the wide state invariant
   swfW that inflate_specW needs *)
Definition tb_inv (P : inv_t) (wbits n : Z) (D O src : list Z) (dp op ip vc vd : val) (gv : globals)
    : environ -> mpred :=
  EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (P wbits D O src pos out z L; swfW (l_s L);
        zf_ni z = offset_val pos ip; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _after (Vlong (Int64.repr (Zlength src - Zlength O))); temp _input ip;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); Zlib.proof.inflate.Callees.zfuncs gv; mem_mgr gv; R_tb gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ip;
       malloc_token Ews (tarray tuchar (Zlength src)) ip;
       data_at_ Tsh t_zsl vc; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The parts of main's body proof (CPS: each proves its segment from the proof of the next one)  *)

(* statements 0-20: the deflate half, up to compressed_len *)
Definition tb_deflate_stmt : Prop :=
  forall {Espec : OracleKind} J0 J gv vc vd,
  clip_dfacts J0 J ->
  (forall wbits n b D O dp op cp, semax Delta_tb (tb_DH wbits n b D O dp op cp vc vd gv) tb_seg21 POST_B) ->
  semax Delta_tb (tb_A0 gv vc vd) tb_seg0 POST_B.

(* statements 21-26: room, after, input = any_bytes(compressed_len + after) and its NULL check, the copy loop *)
Definition tb_input_stmt : Prop :=
  forall {Espec : OracleKind} wbits n b D O dp op cp vc vd gv,
  (forall src ip, tb_facts wbits n D O src dp op ip ->
     semax Delta_tb (tb_TH wbits n D O src dp op ip vc vd gv) tb_seg27 POST_B) ->
  semax Delta_tb (tb_DH wbits n b D O dp op cp vc vd gv) tb_seg21 POST_B.

(* statements 27-33: new_stream, window_bits 8 -> 9, inflateInit2_ (Z_MEM_ERROR returns, gp_assert of Z_OK), next_in,
   next_out; the loop's invariant then holds at pos 0 with no output (TBFacts.tl_init) *)
Definition tb_setup_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n D O src dp op ip vc vd gv,
  tail_facts P -> tb_facts wbits n D O src dp op ip ->
  semax Delta_tb (tb_inv P wbits n D O src dp op ip vc vd gv) tb_seg34 POST_B ->
  semax Delta_tb (tb_TH wbits n D O src dp op ip vc vd gv) tb_seg27 POST_B.

(* statement 34 (the inflate loop), the gp_assert and the final `return 0` (TBFacts.tl_call) *)
Definition tb_loop_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n D O src dp op ip vc vd gv,
  tail_facts P -> tb_facts wbits n D O src dp op ip ->
  semax Delta_tb (tb_inv P wbits n D O src dp op ip vc vd gv) tb_seg34 POST_B.

(* main's body against main_core_spec R_tb, for any invariants of the deflate loop and of the inflate loop *)
Definition main_tb_tail_stmt : Prop :=
  forall J0 J P, clip_dfacts J0 J -> tail_facts P ->
  semax_body (QPvarspecs p_tb) Gmain_tb4 f_main (_main, main_core_spec R_tb).

(* The mains of harness/rt_dictionary.c and harness/api_dict_id.c (data of any length, a dictionary of
   1 .. 2^32 - 1 bytes; round 3: the copies made with copy_of before compression): the kit shared by the proofs
   of their bodies (DWMains.v).

   main's body is [Ssequence b0 (return 0)], b0 a right-nested sequence of statements.  The statements of b0 of
   rt_dictionary, 0-based (api_dict_id's are the same without statement 6 and with one test less in 12: from 6
   on, api_dict_id's statement k is rt_dictionary's k + 1):
     0-3   dict_len = 1 + upto(UINT_MAX - 1), data_len = upto(PTRDIFF_MAX), dict = alloc_any_bytes(dict_len),
           data = alloc_any_bytes(data_len),
     4     `return 0` if dict or data is NULL,
     5     dict_copy = copy_of(dict, dict_len),   6  expected = copy_of(data, data_len) (rt_dictionary only),
     7-11  out = malloc(data_len), level, window_bits = 8 + upto(7), mem_level, strategy,
     12    `return 0` if dict_copy, expected (rt_dictionary only) or out is NULL,
     13    new_stream(&compressor),          14  deflateInit2 and its test,
     15    deflateSetDictionary(&compressor, dict, (uInt) dict_len) and its test,
     16    out_size = deflateBound_z(&compressor, data_len),  17  compressed = malloc(out_size),  18  its NULL test,
     19    compressor.next_in = data,         20  compressor.next_out = compressed,
     21    the do-while of deflate() calls,   22  `if (code != Z_STREAM_END) return 0`,  23  compressed_len,
     24    new_stream(&decompressor),         25  window_bits 8 -> 9,  26  inflateInit2 and its test,
     27    set_buffer(&decompressor, compressed, clip(compressed_len), out, clip(data_len)),
     28    (flush draw; inflate(&decompressor, flush)) followed by rt_dictionary's gp_assert(... == Z_NEED_DICT) /
           api_dict_id's `code = ...`,
     29... the rest of each law: api_dict_id's check of strm->adler against adler32_z(1, dict_copy, dict_len);
           rt_dictionary's inflateSetDictionary(&decompressor, dict_copy, ...) (29 the call, 30 `return 0` on
           Z_MEM_ERROR, 31 gp_assert Z_OK), 32 the do-while of inflate(Z_FINISH) calls, 33-34 the final checks
           (against expected) and `return 0`.
   From statement 6 on, the numbers of main's temporaries differ between the two programs, so every segment is
   proved in each program's own context.
   The segments, Hoare triples from one assertion to the next (a `return` inside a segment goes to main's
   postcondition), with rt_dictionary's statement numbers:
     seg_in    (0-12)  PRE0 -> A10 * F    seg_init  (13-14) A10 -> A12      seg_dict  (15)    A12 -> A13
     seg_bnd   (16-20) A13  -> LI         seg_loop  (21)    LI  -> LB       seg_end   (22-23) LB  -> DH
     seg_setup (24-27) DH   -> A25        seg_first (28, first half) A25 -> A26
     tail_api  (28, second half, 29...) A26 * F -> main's postcondition
     trt_set   (28, second half, 29-31) A26 * F -> RI * F   trt_loop (32) RI -> RB   trt_end (33-34) RB * F -> post.
   F (F_drt, F_dai) holds the copies (their temporaries and objects): the segments from seg_init to seg_first and
   trt_loop do not touch them and are proved without F; DWMains.v frames F around them ([dw_frame]).

   Everything is at clip_streams' compspecs CS.CS (DWCS.dw_comps: the same composites), so that clip_streams'
   moves and helper lemmas (RTKit, RTMem, RTSegLoop, RTLoop, RTSetup: law-independent up to CS.CS) apply. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require VST.veric.expr_lemmas.
Require VST.veric.semax_prog.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Zlib.harness.rt_dictionary.code.
Require Zlib.harness.api_dict_id.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Module DRT := Zlib.harness.rt_dictionary.code.
Module DAI := Zlib.harness.api_dict_id.code.

(* ---------------------------------------------------------------------------------------------- *)
(** ** Cutting main's body into segments *)

(* b0: main's body without the final return *)
Definition body0 (f : function) : statement :=
  match fn_body f with Ssequence b _ => b | s => s end.

(* the statements of a right-nested sequence from position k on, and its first k statements *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

Fixpoint take (k : nat) (s : statement) : statement :=
  match k, s with
  | S (S k'), Ssequence a b => Ssequence a (take (S k') b)
  | S O, Ssequence a _ => a
  | _, _ => Sskip
  end.

(* the first inflate() statement (28 in rt_dictionary, 27 in api_dict_id) = Ssequence x y: x the flush draw and
   inflate(), y each law's own use of its result *)
Definition st_inf (k : nat) (f : function) : statement * statement :=
  match suf k (body0 f) with Ssequence (Ssequence x y) _ => (x, y) | _ => (Sskip, Sskip) end.

Ltac get_stmt e :=
  let x := eval cbv beta iota zeta delta [take suf body0 st_inf fst snd DRT.f_main DAI.f_main fn_body] in e in
  exact x.

Definition seg_in_drt : statement := ltac:(get_stmt (take 13 (body0 DRT.f_main))).
Definition seg_in_dai : statement := ltac:(get_stmt (take 12 (body0 DAI.f_main))).
Definition seg_init_drt : statement := ltac:(get_stmt (take 2 (suf 13 (body0 DRT.f_main)))).
Definition seg_init_dai : statement := ltac:(get_stmt (take 2 (suf 12 (body0 DAI.f_main)))).
Definition seg_dict_drt : statement := ltac:(get_stmt (take 1 (suf 15 (body0 DRT.f_main)))).
Definition seg_dict_dai : statement := ltac:(get_stmt (take 1 (suf 14 (body0 DAI.f_main)))).
Definition seg_bnd_drt : statement := ltac:(get_stmt (take 5 (suf 16 (body0 DRT.f_main)))).
Definition seg_bnd_dai : statement := ltac:(get_stmt (take 5 (suf 15 (body0 DAI.f_main)))).
Definition seg_loop_drt : statement := ltac:(get_stmt (take 1 (suf 21 (body0 DRT.f_main)))).
Definition seg_loop_dai : statement := ltac:(get_stmt (take 1 (suf 20 (body0 DAI.f_main)))).
Definition seg_end_drt : statement := ltac:(get_stmt (take 2 (suf 22 (body0 DRT.f_main)))).
Definition seg_end_dai : statement := ltac:(get_stmt (take 2 (suf 21 (body0 DAI.f_main)))).
Definition seg_setup_drt : statement := ltac:(get_stmt (take 4 (suf 24 (body0 DRT.f_main)))).
Definition seg_setup_dai : statement := ltac:(get_stmt (take 4 (suf 23 (body0 DAI.f_main)))).
Definition seg_first_drt : statement := ltac:(get_stmt (fst (st_inf 28 DRT.f_main))).
Definition seg_first_dai : statement := ltac:(get_stmt (fst (st_inf 27 DAI.f_main))).
(* api_dict_id's own part: the second half of statement 27, then statements 28... (they end by `return 0`) *)
Definition tail_api : statement :=
  ltac:(get_stmt (Ssequence (snd (st_inf 27 DAI.f_main)) (suf 28 (body0 DAI.f_main)))).
(* rt_dictionary's own part: gp_assert(... == Z_NEED_DICT) and inflateSetDictionary (statements 29-31), the
   do-while of inflate(Z_FINISH) calls (32), the final checks and `return 0` (33-34) *)
Definition trt_set : statement :=
  ltac:(get_stmt (Ssequence (snd (st_inf 28 DRT.f_main)) (take 3 (suf 29 (body0 DRT.f_main))))).
Definition trt_loop : statement := ltac:(get_stmt (take 1 (suf 32 (body0 DRT.f_main)))).
Definition trt_end : statement := ltac:(get_stmt (suf 33 (body0 DRT.f_main))).

(* the temporaries that receive the first inflate()'s result *)
Definition tinf_drt : ident := DRT._t'26.
Definition tinf_dai : ident := DAI._t'24.

(* ---------------------------------------------------------------------------------------------- *)
(** ** Type contexts and postconditions *)

Definition Delta_drt : tycontext := func_tycontext DRT.f_main (QPvarspecs p_drt) Gmain_drt nil.
Definition Delta_dai : tycontext := func_tycontext DAI.f_main (QPvarspecs p_dai) Gmain_dai nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_of (f : function) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f).
Definition POST_drt : ret_assert := POST_of DRT.f_main.
Definition POST_dai : ret_assert := POST_of DAI.f_main.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The assertions *)

Import DRT.

(* the inputs: data_len n, the data object dp holding D (n bytes), the output object op (n bytes), the
   dictionary object ddp holding dict, window_bits wbits *)
Definition dw_cf (n : Z) (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits : Z) : Prop :=
  0 <= n <= max_size /\ Zlength D = n /\ is_bytes D /\ isptr dp /\ isptr op /\
  1 <= Zlength dict <= dict_max /\ is_bytes dict /\ isptr ddp /\ 8 <= wbits <= 15.

(* the facts of the inflate half: the deflate run ended with Z_STREAM_END, O is the zlib stream of the data D
   with the dictionary, at the start of the object cp of b bytes *)
Definition dw_hf (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) : Prop :=
  dfinal_dict wbits dict D O /\ dw_cf n D dp op dict ddp wbits /\ 0 <= Zlength O <= b /\
  b <= Ptrofs.max_unsigned /\ rbytes D /\ rbytes O /\ isptr cp.

Section Assertions.
Context (vlit : ident) (gv : globals) (vc vd : val).

(* after start_function *)
Definition PRE0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv).

(* before statement 13 (new_stream(&compressor)): the inputs drawn, the three objects made *)
Definition A10 (n : Z) (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (level wbits mem strategy : Z)
    : environ -> mpred :=
  PROP (dw_cf n D dp op dict ddp wbits; rs32 level; rs32 mem; rs32 strategy)
  LOCAL (temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op;
         temp _level (Vint (Int.repr level)); temp _window_bits (Vint (Int.repr wbits));
         temp _mem_level (Vint (Int.repr mem)); temp _strategy (Vint (Int.repr strategy));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op).

(* before statement 15 (deflateSetDictionary): deflateInit2 returned Z_OK, the state s and the fields (tin,
   tout, adler, msg) satisfy J0 *)
Definition A12 (J0 : Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z) (dp op : val) (dict : list Z)
    (ddp : val) (wbits : Z) (s : dstate) (tin tout adler : Z) (msg : option Z) (msgv : val)
    : environ -> mpred :=
  PROP (dw_cf n D dp op dict ddp wbits; J0 wbits s tin tout adler; msg_ok msg msgv)
  LOCAL (temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv; api_fields vc nullval 0 tin nullval 0 tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op).

(* before statement 16 (out_size = deflateBound_z): deflateSetDictionary returned Z_OK, J1 holds; avail_in /
   avail_out as deflateSetDictionary left them (ai, ao) *)
Definition A13 (J1 : Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z) (D : list Z) (dp op : val)
    (dict : list Z) (ddp : val) (wbits : Z) (s : dstate) (tin tout adler ai ao : Z) (msg : option Z)
    (msgv : val) : environ -> mpred :=
  PROP (dw_cf n D dp op dict ddp wbits; J1 wbits dict s tin tout adler; msg_ok msg msgv)
  LOCAL (temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv; api_fields vc nullval ai tin nullval ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op).

(* the invariant of the do-while of deflate() calls (statement 21) at the head of its body: pos bytes of the
   data consumed (next_in = data + pos), O produced (next_out = compressed + |O|), avail_in / avail_out as the
   previous call left them (ai, ao), J of the state and the fields (RTKit.rt_LI with the dictionary) *)
Definition LI (J : Z -> list Z -> list Z -> Z -> Z -> list Z -> dstate -> Z -> Z -> Z -> Prop) (n : Z)
    (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits b : Z) (cp : val) : environ -> mpred :=
  EX pos : Z, EX O : list Z, EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX ai : Z, EX ao : Z,
  EX msg : option Z, EX msgv : val,
  PROP (dw_cf n D dp op dict ddp wbits; isptr cp; J wbits dict D b pos O s tin tout adler; msg_ok msg msgv)
  LOCAL (temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _out_size (Vlong (Int64.repr b)); temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       api_fields vc (offset_val pos dp) ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rt_comp b O cp).

(* after the do-while (before statement 22): the last call's code; on Z_STREAM_END (1), O is the zlib stream of
   the data with the dictionary (RTKit.rt_LB with the dictionary) *)
Definition LB (n : Z) (D : list Z) (dp op : val) (dict : list Z) (ddp : val) (wbits b : Z) (cp : val)
    : environ -> mpred :=
  EX code : Z, EX O : list Z, EX os : option dstate, EX nin : val, EX ai : Z, EX tin : Z, EX ao : Z, EX tout : Z,
  EX adler : Z, EX msgv : val,
  PROP (dw_cf n D dp op dict ddp wbits; isptr cp; 0 <= Zlength O <= b; b <= max_u64; rbytes O; rs32 code;
        code = 1 -> dfinal_dict wbits dict D O)
  LOCAL (temp _code (Vint (Int.repr code));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (dstream 2 os vc nullval gv;
       api_fields vc nin ai tin (offset_val (Zlength O) cp) ao tout msgv adler; rt_srest vc;
       data_at_ Tsh t_zsl vd; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rt_comp b O cp; TT).

(* the hand-over to the inflate half (before statement 24): the compressor given back as the local's memory
   (its state's allocations are left in TT) *)
Definition DH (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) : environ -> mpred :=
  PROP (dw_hf wbits n b D O dict dp op ddp cp)
  LOCAL (temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _window_bits (Vint (Int.repr wbits));
         temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

(* before statement 28 (the first inflate()): inflateInit2(iwb wbits) returned Z_OK with the fields z
   (IFacts.init_ok) and the live state init_live sp (iwb wbits); set_buffer gave the stream the first clip(|O|)
   bytes of the compressed object and clip(n) bytes of the output object *)
Definition A25 (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) (z : zfields) (sp : val)
    : environ -> mpred :=
  PROP (dw_hf wbits n b D O dict dp op ddp cp; init_ok (iwb wbits) z sp;
        swfW (l_s (init_live sp (iwb wbits))))
  LOCAL (temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd
         (offer_z z cp (IFacts.clipz (Zlength O)) op (IFacts.clipz n)) Vundef (Some (init_live sp (iwb wbits)));
       zfuncs gv; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

(* after the first inflate() (its result in the temporary tq): Z_NEED_DICT, the 6 bytes of the zlib header and
   DICTID read, nothing written, strm->adler the Adler-32 of the dictionary, the decode theory's Q
   (DWIFacts.di_first) *)
Definition A26 (tq : ident) (Q : qinv_t) (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) (z : zfields)
    (L : live) : environ -> mpred :=
  PROP (dw_hf wbits n b D O dict dp op ddp cp; Q wbits dict D O z L;
        zf_adler z = Zlib.proof.adler32.Model.ref_adler32 1 dict;
        zf_ni z = offset_val 6 cp; zf_no z = op; swfW (l_s L); i_head (l_s L) = false; i_wrap (l_s L) <> 0)
  LOCAL (temp tq (Vint (Int.repr Z_NEED_DICT));
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _data_len (Vlong (Int64.repr n));
         temp _dict ddp; temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L);
       zfuncs gv; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

(* rt_dictionary: the invariant of the do-while of inflate(Z_FINISH) calls (statement 32) at the head of its
   body: the bytes of O consumed pos (next_in = compressed + pos), the bytes written out (next_out = out + |out|;
   the output object holds out, then undefined bytes), the stream (z, L) with the theory's P and the wide state
   invariant swfW that inflate_specW needs *)
Definition RI (P : dinv_t) (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) : environ -> mpred :=
  EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (dw_hf wbits n b D O dict dp op ddp cp; 6 <= Zlength O; P wbits dict D O pos out z L; swfW (l_s L);
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _data_len (Vlong (Int64.repr n));
         temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L);
       zfuncs gv; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

(* rt_dictionary, after the do-while: the last call returned Z_STREAM_END having read all of O
   (next_in = compressed + |O|) and written exactly D (next_out = out + n); the theory says nothing of the state
   after that call, so the gz_header memory of its live state (Spec5.head_mem, emp without a gz_header) is kept *)
Definition RB (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) : environ -> mpred :=
  EX z : zfields, EX L : live,
  PROP (dw_hf wbits n b D O dict dp op ddp cp; 6 <= Zlength O;
        zf_ni z = offset_val (Zlength O) cp; zf_no z = offset_val n op)
  LOCAL (temp _code (Vint (Int.repr Z_STREAM_END));
         temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _data_len (Vlong (Int64.repr n));
         temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); head_mem L;
       zfuncs gv; mem_mgr gv; R_of vlit gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op; data_at Ews (tarray tuchar n) (bytes_rep D) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

End Assertions.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The copies *)

(* rt_dictionary: dict_copy holds the dictionary, expected the data (copy_of, statements 5 and 6) *)
Definition F_drt (n : Z) (D dict : list Z) (dcp ep : val) : environ -> mpred :=
  PROP (isptr dcp; isptr ep)
  LOCAL (temp _dict_copy dcp; temp _expected ep)
  SEP (malloc_token Ews (tarray tuchar (Zlength dict)) dcp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) dcp;
       malloc_token Ews (tarray tuchar n) ep; data_at Ews (tarray tuchar n) (bytes_rep D) ep).

(* api_dict_id: dict_copy holds the dictionary *)
Definition F_dai (dict : list Z) (dcp : val) : environ -> mpred :=
  PROP (isptr dcp)
  LOCAL (temp _dict_copy dcp)
  SEP (malloc_token Ews (tarray tuchar (Zlength dict)) dcp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) dcp).

(* a segment that does not touch the frame F (none of its temporaries is assigned) keeps it; a `return` inside
   the segment drops it into main's postcondition (its TT) *)
Lemma dw_frame {Espec : OracleKind} (Delta : tycontext) (f : function) (P B F : environ -> mpred)
    (c : statement) :
  closed_wrt_modvars c F ->
  semax Delta P c (overridePost B (POST_of f)) ->
  semax Delta (P * F) c (overridePost (B * F) (POST_of f)).
Proof.
  intros HC HS.
  pose proof (semax_frame _ _ _ _ _ HC HS) as H.
  eapply semax_post; [ | | | | exact H];
    unfold POST_of, function_body_ret_assert, frame_ret_assert, overridePost; simpl.
  { intros x; apply andp_left2; apply derives_refl. }
  { intros x; apply andp_left2; normalize. }
  { intros x; apply andp_left2; normalize. }
  intros vl x; apply andp_left2.
  rewrite sepcon_assoc, (sepcon_comm (stackframe_of f x)), <- sepcon_assoc.
  apply sepcon_derives; [ | apply derives_refl].
  destruct vl; unfold bind_ret; simpl; normalize.
  unfold liftx, lift; simpl. normalize.
  apply exp_right with x0.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl. normalize.
Qed.

(* a test of the closedness of the frames (checked here, used by DWMains.v) *)
Goal forall n D dict dcp ep dcp', closed_wrt_modvars seg_init_drt (F_drt n D dict dcp ep) /\
                               closed_wrt_modvars trt_loop (F_drt n D dict dcp ep) /\
                               closed_wrt_modvars seg_loop_dai (F_dai dict dcp').
Proof. intros. unfold F_drt, F_dai. split; [|split]; auto 50 with closed. Qed.

(* the closedness side goal of [dw_frame] for the frames above *)
Ltac dw_closed := unfold F_drt, F_dai; auto 50 with closed.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The segment statements *)

(* the draws, the copies and the NULL tests: each program's own statements *)
Definition seg_in_drt_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd,
  semax Delta_drt (PRE0 lit_drt gv vc vd) seg_in_drt
    (overridePost (EX n : Z, EX D : list Z, EX dp : val, EX op : val, EX dict : list Z, EX ddp : val,
                   EX level : Z, EX wbits : Z, EX mem : Z, EX strategy : Z, EX dcp : val, EX ep : val,
                   A10 lit_drt gv vc vd n D dp op dict ddp level wbits mem strategy * F_drt n D dict dcp ep)
       POST_drt).

Definition seg_in_dai_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd,
  semax Delta_dai (PRE0 lit_dai gv vc vd) seg_in_dai
    (overridePost (EX n : Z, EX D : list Z, EX dp : val, EX op : val, EX dict : list Z, EX ddp : val,
                   EX level : Z, EX wbits : Z, EX mem : Z, EX strategy : Z, EX dcp : val,
                   A10 lit_dai gv vc vd n D dp op dict ddp level wbits mem strategy * F_dai dict dcp)
       POST_dai).

(* the segments without the copies, for a program's context Delta, its statement c, its version literal vlit
   and main's postcondition Post *)
Definition seg_init_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} J0 J1 J gv vc vd n D dp op dict ddp level wbits mem strategy,
  dict_dfacts J0 J1 J ->
  semax Delta (A10 vlit gv vc vd n D dp op dict ddp level wbits mem strategy) c
    (overridePost (EX s : dstate, EX tin : Z, EX tout : Z, EX adler : Z, EX msg : option Z, EX msgv : val,
                   A12 vlit gv vc vd J0 n D dp op dict ddp wbits s tin tout adler msg msgv) Post).

Definition seg_dict_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler msg msgv,
  dict_dfacts J0 J1 J ->
  semax Delta (A12 vlit gv vc vd J0 n D dp op dict ddp wbits s tin tout adler msg msgv) c
    (overridePost (EX s' : dstate, EX tin' : Z, EX tout' : Z, EX adler' : Z, EX ai : Z, EX ao : Z,
                   EX msg' : option Z, EX msgv' : val,
                   A13 vlit gv vc vd J1 n D dp op dict ddp wbits s' tin' tout' adler' ai ao msg' msgv') Post).

Definition seg_bnd_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} J0 J1 J gv vc vd n D dp op dict ddp wbits s tin tout adler ai ao msg msgv,
  dict_dfacts J0 J1 J ->
  semax Delta (A13 vlit gv vc vd J1 n D dp op dict ddp wbits s tin tout adler ai ao msg msgv) c
    (overridePost (EX b : Z, EX cp : val, LI vlit gv vc vd J n D dp op dict ddp wbits b cp) Post).

Definition seg_loop_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} J0 J1 J gv vc vd n D dp op dict ddp wbits b cp,
  dict_dfacts J0 J1 J ->
  semax Delta (LI vlit gv vc vd J n D dp op dict ddp wbits b cp) c
    (overridePost (LB vlit gv vc vd n D dp op dict ddp wbits b cp) Post).

Definition seg_end_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} gv vc vd n D dp op dict ddp wbits b cp,
  semax Delta (LB vlit gv vc vd n D dp op dict ddp wbits b cp) c
    (overridePost (EX O : list Z, DH vlit gv vc vd wbits n b D O dict dp op ddp cp) Post).

Definition seg_setup_stmt (Delta : tycontext) (c : statement) (vlit : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} gv vc vd wbits n b D O dict dp op ddp cp,
  semax Delta (DH vlit gv vc vd wbits n b D O dict dp op ddp cp) c
    (overridePost (EX z : zfields, EX sp : val, A25 vlit gv vc vd wbits n b D O dict dp op ddp cp z sp) Post).

(* tq: the temporary of the first inflate()'s result *)
Definition seg_first_stmt (Delta : tycontext) (c : statement) (vlit tq : ident) (Post : ret_assert) : Prop :=
  forall {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp z sp,
  dict_ifacts Q P ->
  semax Delta (A25 vlit gv vc vd wbits n b D O dict dp op ddp cp z sp) c
    (overridePost (EX z' : zfields, EX L : live, A26 vlit gv vc vd tq Q wbits n b D O dict dp op ddp cp z' L)
       Post).

(* the segments of each program *)
Definition seg_init_drt_stmt : Prop := seg_init_stmt Delta_drt seg_init_drt lit_drt POST_drt.
Definition seg_init_dai_stmt : Prop := seg_init_stmt Delta_dai seg_init_dai lit_dai POST_dai.
Definition seg_dict_drt_stmt : Prop := seg_dict_stmt Delta_drt seg_dict_drt lit_drt POST_drt.
Definition seg_dict_dai_stmt : Prop := seg_dict_stmt Delta_dai seg_dict_dai lit_dai POST_dai.
Definition seg_bnd_drt_stmt : Prop := seg_bnd_stmt Delta_drt seg_bnd_drt lit_drt POST_drt.
Definition seg_bnd_dai_stmt : Prop := seg_bnd_stmt Delta_dai seg_bnd_dai lit_dai POST_dai.
Definition seg_loop_drt_stmt : Prop := seg_loop_stmt Delta_drt seg_loop_drt lit_drt POST_drt.
Definition seg_loop_dai_stmt : Prop := seg_loop_stmt Delta_dai seg_loop_dai lit_dai POST_dai.
Definition seg_end_drt_stmt : Prop := seg_end_stmt Delta_drt seg_end_drt lit_drt POST_drt.
Definition seg_end_dai_stmt : Prop := seg_end_stmt Delta_dai seg_end_dai lit_dai POST_dai.
Definition seg_setup_drt_stmt : Prop := seg_setup_stmt Delta_drt seg_setup_drt lit_drt POST_drt.
Definition seg_setup_dai_stmt : Prop := seg_setup_stmt Delta_dai seg_setup_dai lit_dai POST_dai.
Definition seg_first_drt_stmt : Prop := seg_first_stmt Delta_drt seg_first_drt lit_drt tinf_drt POST_drt.
Definition seg_first_dai_stmt : Prop := seg_first_stmt Delta_dai seg_first_dai lit_dai tinf_dai POST_dai.

(* api_dict_id's own part, with the dictionary's copy: it ends by `return 0` *)
Definition tail_api_stmt : Prop :=
  forall {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp z L dcp,
  dict_ifacts Q P ->
  semax Delta_dai (A26 lit_dai gv vc vd tinf_dai Q wbits n b D O dict dp op ddp cp z L * F_dai dict dcp)
    tail_api POST_dai.

(* rt_dictionary's own part: inflateSetDictionary with the dictionary's copy, the loop (without the copies), the
   final checks against the data's copy *)
Definition trt_set_stmt : Prop :=
  forall {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp z L dcp ep,
  dict_ifacts Q P ->
  semax Delta_drt
    (A26 lit_drt gv vc vd tinf_drt Q wbits n b D O dict dp op ddp cp z L * F_drt n D dict dcp ep) trt_set
    (overridePost (RI lit_drt gv vc vd P wbits n b D O dict dp op ddp cp * F_drt n D dict dcp ep) POST_drt).

Definition trt_loop_stmt : Prop :=
  forall {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp,
  dict_ifacts Q P ->
  semax Delta_drt (RI lit_drt gv vc vd P wbits n b D O dict dp op ddp cp) trt_loop
    (overridePost (RB lit_drt gv vc vd wbits n b D O dict dp op ddp cp) POST_drt).

Definition trt_end_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd wbits n b D O dict dp op ddp cp dcp ep,
  semax Delta_drt (RB lit_drt gv vc vd wbits n b D O dict dp op ddp cp * F_drt n D dict dcp ep) trt_end
    POST_drt.

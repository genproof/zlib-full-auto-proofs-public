(* Law rt_stream_trailing (harness/rt_stream_trailing.c): the kit of main's body proof.

   The harness is rt_stream's with three changes: after each deflate() and each inflate() call
   gp_assert(accounted(&strm, &at)) (laws_session.h: the call moved next_in and next_out exactly as far as it
   lowered avail_in and avail_out); after the deflate loop main copies the compressed bytes O to the start of a new
   object [input] of |O| + after bytes (after = upto(PTRDIFF_MAX - compressed_len), the other bytes any bytes:
   alloc_any_bytes); inflate() is fed that object, and at Z_STREAM_END next_in must be input + |O|.  So this kit
   reuses rt_stream's (UMainKit.v: the drawn values [setup], the objects [dobj] / [cobj] / [oobj], the compressor
   [cstream] and the deflate loop's state [dls] / [dl_ok], the decompressor's state [ils]) with this program's
   main, its resources [Rm_t], its context [Gmain_t] and the input object [iobj].

   main's body is [Ssequence b0 (return 0)]; b0 is a right-nested sequence of statements, 0-based:
     0-20  as rt_stream: the draws, gp_assume(deflate_params_ok(...)), the objects data, expected, compressed,
           out, new_stream(&compressor), deflateInit2_ (Z_MEM_ERROR: return; gp_assert(code == Z_OK)), next_in,
           next_out, offered, flush;
     21    the deflate loop (rt_stream's, with gp_assert(accounted(&compressor, &at)) after deflate());
     22    compressed_len,  23  after = upto(PTRDIFF_MAX - compressed_len),
     24    input = alloc_any_bytes(compressed_len + after),  25  the NULL test of input,
     26    the copy loop (for (i = 0; i < compressed_len; i++) input[i] = compressed[i]);
     27    new_stream(&decompressor),  28  window_bits 8 -> 9,  29  code = inflateInit2_(...),
     30    Z_MEM_ERROR: return,  31  gp_assert(code == Z_OK),  32-33  next_in = input, next_out = out;
     34    the inflate loop (rt_stream's on input, with gp_assert(accounted(&decompressor, &at)) after the test of
           the codes);
     35... the final checks (next_in == input + compressed_len; next_out and the bytes) and return 0.
   The parts, as Hoare triples between the assertions below (a return inside a part goes to main's
   postcondition POST_t):
     segA_t  (0-20)                  PRE0_t -> DI_t
     loopD_t (21, the deflate loop)  DI_t (its invariant) -> DE_t (after deflate returned Z_STREAM_END)
     segB_t  (22-26)                 DE_t -> DB_t (the input object holds O, then any bytes)
     segC_t  (27-33)                 DB_t -> II_t
     loopI_t (34, the inflate loop)  II_t (its invariant) -> IE_t (after inflate returned Z_STREAM_END)
     segE_t  (35...)                 IE_t -> return
   DI_t and DE_t are rt_stream's DI and DE with Rm_t.  From DB_t on, the input object [iobj src ip] is the LAST
   item of SEP and the new facts are the last items of PROP, so that rt_stream's scripts keep their indices. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TIFacts.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(** ** Cutting main's body into its parts *)

(* b0: main's body without the final return *)
Definition body0_t : statement := match fn_body f_main with Ssequence b _ => b | s => s end.

Ltac get_stmt_t e :=
  let x := eval cbv beta iota zeta delta [take suf first body0_t f_main fn_body] in e in
  exact x.

Definition segA_t : statement := ltac:(get_stmt_t (take 21 body0_t)).
Definition loopD_t : statement := ltac:(get_stmt_t (first (suf 21 body0_t))).
Definition segB_t : statement := ltac:(get_stmt_t (take 5 (suf 22 body0_t))).
Definition segC_t : statement := ltac:(get_stmt_t (take 7 (suf 27 body0_t))).
Definition loopI_t : statement := ltac:(get_stmt_t (first (suf 34 body0_t))).
Definition segE_t : statement := ltac:(get_stmt_t (suf 35 body0_t)).

(* main's body and its parts in sequence are the same statements up to the association of the sequences *)
Definition body_of_parts_t : statement :=
  Ssequence
    (Ssequence segA_t (Ssequence loopD_t (Ssequence segB_t (Ssequence segC_t (Ssequence loopI_t segE_t)))))
    (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Lemma body_parts_t : unfold_Ssequence body_of_parts_t = unfold_Ssequence (fn_body f_main).
Proof. reflexivity. Qed.

(** ** Type context and postcondition of main's body *)
Definition Delta_t : tycontext := func_tycontext f_main (QPvarspecs p_t) Gmain_t nil.

Definition POST_t : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** The input object of inflate: O, then any bytes *)
Definition iobj (src : list Z) (ip : val) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength src)) ip * data_at Ews (tarray tuchar (Zlength src)) (map vi src) ip.

(* src: the compressed bytes O at its start, at most PTRDIFF_MAX bytes, bytes *)
Definition src_ok (O src : list Z) : Prop :=
  Zlength O <= Zlength src <= max_size /\ sublist 0 (Zlength O) src = O /\ Zlib.proof.zutil.Libc.bytes_ok src.

(** ** The decompressor between inflate() calls *)
(* the bytes of src consumed (next_in = input + pos), the bytes produced (next_out = out + |out|), the live
   state and the fields of the stream *)
Definition il_ok_t (P : trl_iinv) (u : setup) (O src : list Z) (ip : val) (l : ils) : Prop :=
  P (su_data u) O src (il_pos l) (il_out l) (l_s (il_L l)) (zf_tout (il_z l)) /\ swfW (l_s (il_L l)) /\
  0 <= il_pos l <= Zlength src /\ (exists rest, su_data u = il_out l ++ rest) /\
  zf_ni (il_z l) = offset_val (il_pos l) ip /\
  zf_no (il_z l) = offset_val (Zlength (il_out l)) (su_op u).

(** ** The assertions *)
Section Assertions.
Context (gv : globals) (vc vd va : val).

(* after start_function *)
Definition PRE0_t : environ -> mpred :=
  PROPx [] (LOCALx (lv_locals gv vc vd va)
  (SEPx [data_at_ Tsh t_z vd; data_at_ Tsh t_p va; data_at_ Tsh t_z vc; mem_mgr gv; Rm_t gv])).

(* DI_t: the deflate loop's head (rt_stream's DI) *)
Definition DI_t (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
          su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
        dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* DE_t: deflate returned Z_STREAM_END: O is a finished stream of the data (rt_stream's DE) *)
Definition DE_t (u : setup) (O : list Z) (c : cst) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
        dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) O;
        Zlength O <= su_cap u; rbytes O; cs_no c = offset_val (Zlength O) (su_cp u)]
  (LOCALx (su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc c; data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv; dobj u; cobj u O; oobj u [];
        data_at_ Tsh t_p va])).

(* DB_t: the input object [ip] holds src = O followed by any bytes *)
Definition DB_t (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
        dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) O;
        Zlength O <= su_cap u; rbytes O; cs_no c = offset_val (Zlength O) (su_cp u);
        src_ok O src; isptr ip]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc c; data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv; dobj u; cobj u O; oobj u [];
        data_at_ Tsh t_p va; iobj src ip])).

(* II_t: the inflate loop's head *)
Definition II_t (P : trl_iinv) (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (l : ils)
    : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u; rbytes O; il_ok_t P u O src ip l; src_ok O src; isptr ip]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd (il_z l) Vundef (Some (il_L l)); head_opt (Some (il_L l));
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u (il_out l);
        data_at_ Tsh t_p va; iobj src ip])).

(* IE_t: inflate returned Z_STREAM_END having read exactly O (none of the bytes after it) and produced exactly
   the data *)
Definition IE_t (u : setup) (O : list Z) (c : cst) (src : list Z) (ip : val) (z : zfields) (L : live)
    : environ -> mpred :=
  PROPx [su_ok u; Zlength O <= su_cap u;
        zf_ni z = offset_val (Zlength O) ip;
        zf_no z = offset_val (Zlength (su_data u)) (su_op u);
        src_ok O src; isptr ip]
  (LOCALx (temp _compressed_len (vl (Zlength O)) :: temp _after (vl (Zlength src - Zlength O)) ::
           temp _input ip :: su_locals u (rts_iw (su_wbits u)) ++ lv_locals gv vc vd va)
  (SEPx [istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L);
        cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv; dobj u; cobj u O; oobj u (su_data u);
        data_at_ Tsh t_p va; iobj src ip])).

End Assertions.

(** ** The parts *)

Definition segA_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va, urts_dfacts J ->
  semax Delta_t (PRE0_t gv vc vd va) segA_t
    (overridePost (EX u : setup, EX l : dls, DI_t gv vc vd va J u l) POST_t).

(* the do-while loop (Clight: Sloop body (if (code != Z_STREAM_END) skip else break)) from its invariant *)
Definition loopD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u, urts_dfacts J ->
  semax Delta_t (EX l : dls, DI_t gv vc vd va J u l) loopD_t
    (overridePost (EX O : list Z, EX c : cst, DE_t gv vc vd va u O c) POST_t).

Definition segB_t_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd va u O c,
  semax Delta_t (DE_t gv vc vd va u O c) segB_t
    (overridePost (EX src : list Z, EX ip : val, DB_t gv vc vd va u O c src ip) POST_t).

Definition segC_t_stmt : Prop :=
  forall {Espec : OracleKind} P gv vc vd va u O c src ip, trl_ifacts P ->
  semax Delta_t (DB_t gv vc vd va u O c src ip) segC_t
    (overridePost (EX l : ils, II_t gv vc vd va P u O c src ip l) POST_t).

Definition loopI_t_stmt : Prop :=
  forall {Espec : OracleKind} P gv vc vd va u O c src ip, trl_ifacts P ->
  semax Delta_t (EX l : ils, II_t gv vc vd va P u O c src ip l) loopI_t
    (overridePost (EX z : zfields, EX L : live, IE_t gv vc vd va u O c src ip z L) POST_t).

Definition segE_t_stmt : Prop :=
  forall {Espec : OracleKind} gv vc vd va u O c src ip z L,
  semax Delta_t (IE_t gv vc vd va u O c src ip z L) segE_t POST_t.

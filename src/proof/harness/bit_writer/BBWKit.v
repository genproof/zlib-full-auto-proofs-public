(* Law rj_bad_block, main (harness/rj_bad_block.c): the kit shared by the segment lemmas of main's body proof.
   - Gmain_bbW: the specifications main calls (BBMain.Gmain_bb is the same list); bbw_Delta, bbw_POST (main's
     postcondition after start_function), POST_B (that of every suffix of main's chain of statements: each ends
     by a return);
   - the segments: main's body is `chain; return 0`, the chain s1; (s2; (s3; ...)); bbw_seg k is the suffix of
     the chain from its k-th statement (1-based);
   - the assertions at the two cuts: bbw_inv (the head of the do-while of inflate() calls) and bbw_AT (after it);
   - the statements of the three segments (setup, loop, tail), in continuation-passing style.
   Main's statements: 1 window_bits, 2 kind, 3 which, 4 literals = 0, 5 `if (kind == 2 || kind == 3) literals =
   ...`, 6 stream_len, 7 room, 8 stream = any_bytes, 9 literal = any_bytes, 10 out = malloc, 11 their NULL
   check, 12 bit = 1, 13-17 btype[0..4], 18 put_bits(BTYPE), 19 kind 0's gp_assume, 20 the loop of
   put_literal, 21-23 the bad element of kinds 2, 3, 4, 24 new_stream, 25 inflateInit2 and its check,
   26-27 next_in, next_out, 28 flush, 29 the do-while of inflate() calls, 30 the call after it with Z_TREES,
   31 gp_assert and `return 0`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Zlib.harness.rj_bad_block.code.
Module BBC := Zlib.harness.rj_bad_block.code.
#[export] Existing Instance BB.CS.
Local Open Scope logic.

(* the specifications main calls *)
Definition Gmain_bbW : funspecs :=
  [inflateInit2__spec; inflate_specW; zcalloc_i; zcfree_i;
   upto_spec; clip_spec; any_bytes_spec; offer_spec; new_stream_spec;
   put_bits_spec; put_literal_spec;
   (_quickproof_malloc, @malloc_spec' BB.CS); nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition bbw_Delta : tycontext := func_tycontext BBC.f_main (QPvarspecs BB.p) Gmain_bbW nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition bbw_POST : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of BBC.f_main).

(* the postcondition of every suffix of the chain: it never ends normally *)
Definition POST_B : ret_assert := overridePost FF bbw_POST.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint bbw_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => bbw_drop n' b
  | _, _ => Sskip
  end.

Definition bbw_chain (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.

Ltac bbw_get_seg k :=
  let n := eval compute in (k - 1)%nat in
  let x := eval cbv beta iota zeta delta [bbw_drop bbw_chain BBC.f_main fn_body] in
    (bbw_drop n (bbw_chain (fn_body BBC.f_main))) in
  exact x.

Definition bbw_seg1 : statement := ltac:(bbw_get_seg 1%nat).
Definition bbw_seg29 : statement := ltac:(bbw_get_seg 29%nat).
Definition bbw_seg30 : statement := ltac:(bbw_get_seg 30%nat).

Lemma bbw_body_eq : fn_body BBC.f_main = Ssequence bbw_seg1 (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

Definition t_zsb : type := Tstruct BBC._z_stream_s noattr.

(* after start_function: the three local variables, the allocator, the globals main needs *)
Definition bbw_A0 (gv: globals) (vs vbt vbit: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit;
       mem_mgr gv; R_bb gv).

(* the facts on main's inputs that do not change after the writes: the stream S0 and the block written into it
   (BBWDefs.bbw_ok), room >= |lits| bytes of output space, flush an int; the stream (strp, |S0| bytes) and the
   output space (outp, room bytes) are objects *)
Definition bbw_args (S0: list Z) (kind which: Z) (lits: list Z) (room flush: Z) (strp outp: val) : Prop :=
  bbw_ok S0 kind which lits /\ Zlength lits <= room <= Int64.max_signed /\
  Int.min_signed <= flush <= Int.max_signed /\ isptr strp /\ isptr outp.

(* the head of the do-while: pos bytes of the stream consumed (next_in = stream + pos), the output so far ob
   (next_out = out + |ob|; the output object holds any room values), the stream (z, L) with the theory's
   invariant J and the wide state invariant swfW that inflate_specW needs (strm->adler of a raw stream
   undefined); the literal object and the harness's version literal are dropped into TT *)
Definition bbw_inv (J: bbw_J) (gv: globals) (vs vbt vbit strp outp: val) (S0: list Z) (kind which: Z)
    (lits: list Z) (room flush: Z) : environ -> mpred :=
  EX pos: Z, EX ob: list Z, EX z: zfields, EX L: live, EX oc: list val,
  PROP (J S0 kind which lits pos ob (l_s L); swfW (l_s L); i_head (l_s L) = false;
        0 <= pos <= Zlength S0; Zlength ob <= room; Zlength oc = room;
        zf_ni z = offset_val pos strp; zf_no z = offset_val (Zlength ob) outp)
  LOCAL (temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._out outp; temp BBC._flush (Vint (Int.repr flush));
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); zfuncs gv; mem_mgr gv; tables_rep Ers gv; crc_table_at Ers gv;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (bb_bytes S0 kind which lits)) strp;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at Ews (tarray tuchar room) oc outp; malloc_token Ews (tarray tuchar room) outp;
       data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT).

(* after the do-while: the code is Z_DATA_ERROR, or Z_OK with flush = Z_TREES from a call that was offered all
   the rest of the stream (avail_in = |S0| - pos) and of the room (avail_out = room - |ob|), after which the
   next call returns Z_DATA_ERROR (BBWDefs.bbw_extra) *)
Definition bbw_AT (gv: globals) (vs vbt vbit strp outp: val) (S0: list Z) (kind which: Z) (lits: list Z)
    (room flush: Z) : environ -> mpred :=
  EX code: Z, EX pos: Z, EX ob: list Z, EX z: zfields, EX L: live, EX oc: list val,
  PROP (code = Z_DATA_ERROR \/
        (code = Z_OK /\ flush = Z_TREES /\ swfW (l_s L) /\ i_head (l_s L) = false /\
         0 <= pos <= Zlength S0 /\ Zlength ob <= room /\
         zf_ni z = offset_val pos strp /\ zf_ai z = Zlength S0 - pos /\
         zf_no z = offset_val (Zlength ob) outp /\ zf_ao z = room - Zlength ob /\
         bbw_extra S0 kind which lits pos ob (l_s L) flush);
        Zlength oc = room)
  LOCAL (temp BBC._code (Vint (Int.repr code)); temp BBC._flush (Vint (Int.repr flush));
         temp BBC._stream strp; temp BBC._out outp;
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (istreamA gv Tsh vs z Vundef (Some L); zfuncs gv; mem_mgr gv; tables_rep Ers gv; crc_table_at Ers gv;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (bb_bytes S0 kind which lits)) strp;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at Ews (tarray tuchar room) oc outp; malloc_token Ews (tarray tuchar room) outp;
       data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The three segments                                                                            *)

(* statements 1-28: the inputs, the writes, new_stream, inflateInit2_ (any outcome but Z_OK returns), next_in,
   next_out, flush; then the loop (given) from its invariant at pos = 0, ob = [] *)
Definition bbw_setup_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit,
  bbw_facts J ->
  (forall S0 kind which lits room flush strp outp,
     bbw_args S0 kind which lits room flush strp outp ->
     semax bbw_Delta (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush) bbw_seg29 POST_B) ->
  semax bbw_Delta (bbw_A0 gv vs vbt vbit) bbw_seg1 POST_B.

(* statement 29: the do-while of inflate() calls (a call returning Z_MEM_ERROR returns 0); then the rest (given)
   from bbw_AT *)
Definition bbw_loop_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_facts J -> bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbw_AT gv vs vbt vbit strp outp S0 kind which lits room flush) bbw_seg30 POST_B ->
  semax bbw_Delta (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush) bbw_seg29 POST_B.

(* statements 30-31: the call after the loop when the code is Z_OK and flush Z_TREES, gp_assert(code ==
   Z_DATA_ERROR), return 0 *)
Definition bbw_tail_stmt : Prop :=
  forall {Espec: OracleKind} gv vs vbt vbit S0 kind which lits room flush strp outp,
  bbw_args S0 kind which lits room flush strp outp ->
  semax bbw_Delta (bbw_AT gv vs vbt vbit strp outp S0 kind which lits room flush) bbw_seg30 POST_B.

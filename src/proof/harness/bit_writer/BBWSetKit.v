(* Law rj_bad_block, main: the cuts inside the setup segment (statements 1-28, BBWKit.bbw_setup_stmt), so that
   its proof is split into four files: BBWSet1.v (statements 1-10: the inputs and the objects), BBWSetNull.v
   (statement 11: the NULL check), BBWSet2.v (statements 12-23: the writes of the block) and BBWSet3.v
   (statements 24-28: new_stream, inflateInit2_, next_in, next_out, flush).  bbs_A10 holds after statement 10,
   bbs_A1 after statement 11, bbs_A2 after statement 23.  The writes keep the bit position in a size_t; the
   harness's bound on the literals ((PTRDIFF_MAX - 5) / 9) keeps it below 2^64 (9 * |lits| + 15 bits at most,
   carried by bbs_A10 and bbs_A1 to bbs_set2_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Local Open Scope logic.

Definition bbw_seg11 : statement := ltac:(bbw_get_seg 11%nat).
Definition bbw_seg12 : statement := ltac:(bbw_get_seg 12%nat).
Definition bbw_seg24 : statement := ltac:(bbw_get_seg 24%nat).

(* after out = malloc(room) (statement 10): as bbs_A1, but each of the three objects may be NULL *)
Definition bbs_A10 (gv: globals) (vs vbt vbit: val) (w kind which: Z) (lits S0: list Z) (room: Z)
    (strp litp outp: val) : environ -> mpred :=
  PROP (-15 <= w <= -8; 0 <= kind <= 4; 0 <= which <= 1; (kind = 2 \/ kind = 3) \/ lits = [];
        is_bytes lits; is_bytes S0; 5 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed;
        Zlength lits <= room <= Int64.max_signed;
        is_pointer_or_null strp; is_pointer_or_null litp; is_pointer_or_null outp;
        9 * Zlength lits + 15 <= Int64.max_unsigned)
  LOCAL (temp BBC._window_bits (Vint (Int.repr w)); temp BBC._kind (Vint (Int.repr kind));
         temp BBC._which (Vint (Int.repr which)); temp BBC._literals (Vlong (Int64.repr (Zlength lits)));
         temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._literal litp; temp BBC._out outp;
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit;
       mem_mgr gv; R_bb gv;
       if eq_dec strp nullval then emp
       else (malloc_token Ews (tarray tuchar (Zlength S0)) strp *
             data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep S0) strp);
       if eq_dec litp nullval then emp
       else (malloc_token Ews (tarray tuchar (Zlength lits)) litp *
             data_at Ews (tarray tuchar (Zlength lits)) (bytes_rep lits) litp);
       if eq_dec outp nullval then emp
       else (malloc_token Ews (tarray tuchar room) outp * data_at_ Ews (tarray tuchar room) outp)).

(* after the NULL check (statement 11): the inputs drawn (windowBits w, kind, which, the literals lits, the
   stream's bytes S0 before the writes, room) and the three objects: the stream (strp), the literals (litp) and
   the output space (outp, room undefined bytes) *)
Definition bbs_A1 (gv: globals) (vs vbt vbit: val) (w kind which: Z) (lits S0: list Z) (room: Z)
    (strp litp outp: val) : environ -> mpred :=
  PROP (-15 <= w <= -8; 0 <= kind <= 4; 0 <= which <= 1; (kind = 2 \/ kind = 3) \/ lits = [];
        is_bytes lits; is_bytes S0; 5 + 2 * Zlength lits <= Zlength S0 <= Int64.max_signed;
        Zlength lits <= room <= Int64.max_signed; isptr strp; isptr litp; isptr outp;
        9 * Zlength lits + 15 <= Int64.max_unsigned)
  LOCAL (temp BBC._window_bits (Vint (Int.repr w)); temp BBC._kind (Vint (Int.repr kind));
         temp BBC._which (Vint (Int.repr which)); temp BBC._literals (Vlong (Int64.repr (Zlength lits)));
         temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._literal litp; temp BBC._out outp;
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit;
       mem_mgr gv; R_bb gv;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep S0) strp;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at Ews (tarray tuchar (Zlength lits)) (bytes_rep lits) litp;
       malloc_token Ews (tarray tuchar (Zlength lits)) litp;
       data_at_ Ews (tarray tuchar room) outp; malloc_token Ews (tarray tuchar room) outp).

(* after the writes (statement 23): the stream holds the broken block (BBFacts.bb_bytes), the inputs satisfy
   BBWDefs.bbw_ok; the literal object is no longer needed (TT) *)
Definition bbs_A2 (gv: globals) (vs vbt vbit: val) (w kind which: Z) (lits S0: list Z) (room: Z)
    (strp outp: val) : environ -> mpred :=
  PROP (-15 <= w <= -8; bbw_ok S0 kind which lits; Zlength lits <= room <= Int64.max_signed;
        isptr strp; isptr outp)
  LOCAL (temp BBC._window_bits (Vint (Int.repr w));
         temp BBC._stream_len (Vlong (Int64.repr (Zlength S0))); temp BBC._room (Vlong (Int64.repr room));
         temp BBC._stream strp; temp BBC._out outp;
         lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt; lvar BBC._bit tulong vbit; gvars gv)
  SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit;
       mem_mgr gv; R_bb gv;
       data_at Ews (tarray tuchar (Zlength S0)) (bytes_rep (bb_bytes S0 kind which lits)) strp;
       malloc_token Ews (tarray tuchar (Zlength S0)) strp;
       data_at_ Ews (tarray tuchar room) outp; malloc_token Ews (tarray tuchar room) outp; TT).

(* statements 1-10, then the rest (given) from bbs_A10 *)
Definition bbs_set1_stmt : Prop :=
  forall {Espec: OracleKind} gv vs vbt vbit,
  (forall w kind which lits S0 room strp litp outp,
     semax bbw_Delta (bbs_A10 gv vs vbt vbit w kind which lits S0 room strp litp outp) bbw_seg11 POST_B) ->
  semax bbw_Delta (bbw_A0 gv vs vbt vbit) bbw_seg1 POST_B.

(* statement 11 (the NULL check), then the rest (given) from bbs_A1 *)
Definition bbs_null_stmt : Prop :=
  forall {Espec: OracleKind} gv vs vbt vbit w kind which lits S0 room strp litp outp,
  semax bbw_Delta (bbs_A1 gv vs vbt vbit w kind which lits S0 room strp litp outp) bbw_seg12 POST_B ->
  semax bbw_Delta (bbs_A10 gv vs vbt vbit w kind which lits S0 room strp litp outp) bbw_seg11 POST_B.

(* statements 12-23, then the rest (given) from bbs_A2, when the bit position of the writes stays below 2^64:
   main keeps it in a size_t, from 3 up to 3 + (at most 9 bits per literal) + 12 bits of the bad element; the
   harness's bound (PTRDIFF_MAX - 5) / 9 on the literals ensures it (with more literals the position could wrap
   and the writes would overwrite the block header) *)
Definition bbs_set2_stmt : Prop :=
  forall {Espec: OracleKind} gv vs vbt vbit w kind which lits S0 room strp litp outp,
  9 * Zlength lits + 15 <= Int64.max_unsigned ->
  semax bbw_Delta (bbs_A2 gv vs vbt vbit w kind which lits S0 room strp outp) bbw_seg24 POST_B ->
  semax bbw_Delta (bbs_A1 gv vs vbt vbit w kind which lits S0 room strp litp outp) bbw_seg12 POST_B.

(* statements 24-28, then the loop (given) from its invariant at pos = 0, ob = [] *)
Definition bbs_set3_stmt : Prop :=
  forall {Espec: OracleKind} (J: bbw_J) gv vs vbt vbit w kind which lits S0 room strp outp,
  bbw_facts J ->
  (forall flush, bbw_args S0 kind which lits room flush strp outp ->
     semax bbw_Delta (bbw_inv J gv vs vbt vbit strp outp S0 kind which lits room flush) bbw_seg29 POST_B) ->
  semax bbw_Delta (bbs_A2 gv vs vbt vbit w kind which lits S0 room strp outp) bbw_seg24 POST_B.

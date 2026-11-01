(* Law inflate_reset, main, the loop body (IRMainLoop.v): its segments and the statement of its tail.
   - seg_call: from `a.next_in = ia;` (after the NULL checks of the four objects) to the end of the body;
   - seg_after: from `pos += ain - a.avail_in;` (after `if (phase == 2) {...}`) to the end of the body: the six
     free()s and `if (stop == 0) { if (phase == 2) break; <reset> }` (IRMainKit.seg_rst, rst_stmt);
   - tail_pre / tail_facts / tail_stmt: the tail from either phase (the stream b as IRMainKit.bmem), with the
     loop body's postcondition. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts Zlib.proof.harness.inflate_reset.IRMainKit.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

(* the statement after the first n commands of a right-nested sequence *)
Fixpoint seg_from (n: nat) (s: statement) : statement :=
  match n, s with O, _ => s | S k, Ssequence _ b => seg_from k b | _, _ => Sskip end.

Definition seg_call : statement := ltac:(let x := eval cbv [seg_from seg_loop] in (seg_from 14 seg_loop) in exact x).
Definition seg_after : statement := ltac:(let x := eval cbv [seg_from seg_loop] in (seg_from 21 seg_loop) in exact x).

(* the loop body's postcondition *)
Definition loop_post (I1: I1T) (I2: I2T) (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z)
    (rb: rawf) : ret_assert :=
  loop_nocontinue_ret_assert (loop_inv I1 I2 gv va vb vsa vsb w srcp src rb)
    (overridePost (brk_inv I1 I2 gv va vb vsa vsb w srcp src rb) POST_m).

(* after `if (phase == 2) {...}`: stream a after its call (za, La) at the old pos (pos is updated by the tail),
   stream b (bmem: before its init in phase 1, after its call in phase 2); the four objects (any contents) and
   the two snapshot objects qa, qb in sa, sb *)
Definition tail_pre (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z) (rb: rawf)
    (ph pos w2 aout wsel stop how ain: Z) (iap ibp oap obp qa qb: val)
    (cia cib ca cb da db: list val) (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr ph)); temp _w2 (Vint (Int.repr w2)); temp _pos (Vint (Int.repr pos));
         temp _wsel (Vint (Int.repr wsel)); temp _stop (Vint (Int.repr stop)); temp _how (Vint (Int.repr how));
         temp _ain (Vint (Int.repr ain)); temp _ia iap; temp _ib ibp; temp _oa oap; temp _ob obp;
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za (Some La); bmem gv vb ph rb zb Lb; mem_mgr gv; zfuncs gv; tables_rep Ers gv;
       crc_table_at Ers gv; version_lit gv; ir_hversion_lit gv; ir_msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at Ews (tarray tuchar ain) cia iap; malloc_token Ews (tarray tuchar ain) iap;
       data_at Ews (tarray tuchar ain) cib ibp; malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar aout) ca oap; malloc_token Ews (tarray tuchar aout) oap;
       data_at Ews (tarray tuchar aout) cb obp; malloc_token Ews (tarray tuchar aout) obp;
       data_at Tsh (tptr tuchar) qa vsa; data_at Tsh (tptr tuchar) qb vsb;
       data_at Ews (tarray tuchar aout) da qa; malloc_token Ews (tarray tuchar aout) qa;
       data_at Ews (tarray tuchar aout) db qb; malloc_token Ews (tarray tuchar aout) qb).

(* the invariant holds at the new position pos + (ain - avail_in) *)
Definition tail_facts (I1: I1T) (I2: I2T) (w: Z) (srcp: val) (src: list Z) (rb: rawf) (va vb: val)
    (ph pos w2 aout wsel stop how ain: Z) (iap ibp oap obp qa qb: val)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts I1 I2 w srcp src rb /\
  ph_inv I1 I2 w src ph (pos + (ain - zf_ai za)) w2 za La zb Lb /\ 0 <= zf_ai za <= ain /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ 0 <= aout <= 2 ^ 20 /\
  Int.min_signed <= w2 <= Int.max_signed /\ Int.min_signed <= wsel <= Int.max_signed /\
  0 <= stop <= 255 /\ 0 <= how <= 255 /\
  isptr va /\ isptr vb /\ isptr iap /\ isptr ibp /\ isptr oap /\ isptr obp /\ isptr qa /\ isptr qb.

(* IRMainLoopTail.v *)
Definition tail_stmt : Prop :=
  forall {Espec: OracleKind} I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 aout wsel stop how ain
         iap ibp oap obp qa qb cia cib ca cb da db za La zb Lb,
  tail_facts I1 I2 w srcp src rb va vb ph pos w2 aout wsel stop how ain iap ibp oap obp qa qb za La zb Lb ->
  semax Delta_m
    (tail_pre gv va vb vsa vsb w srcp src rb ph pos w2 aout wsel stop how ain iap ibp oap obp qa qb
       cia cib ca cb da db za La zb Lb)
    seg_after
    (loop_post I1 I2 gv va vb vsa vsb w srcp src rb).

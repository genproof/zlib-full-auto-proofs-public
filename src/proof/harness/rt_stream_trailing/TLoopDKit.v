(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's deflate loop (TMainKit.loopD_t): the cut of its body
   and the assertions between the pieces.  The loop is rt_stream's (rt_stream/ULoopDKit.v) with one statement more:

     0  read = next_in - data;
     1  if (flush != Z_FINISH) { offered += upto(data_len - offered); flush = upto(Z_BLOCK); ... }
     2  avail_in = clip(offered - read);
     3  avail_out = clip(upto(capacity - (next_out - compressed)));
     4  [posD_t] = `position_of(&compressor, &at)`;
     5  [callD_t] = `code = deflate(&compressor, flush)`;
     6  [accD_t] = `gp_assert(accounted(&compressor, &at))`;
     7  [assertD_t] = `if (at.avail_out == 0) gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at))`;
     8  the out-of-room test (return 0 when deflate did not finish and compressed is full).
   The assertions are rt_stream's with this program's resources Rm_t; [DA_t], the state after the call, also says
   that the call accounted for what it moved ([acc_ok]: next_in + avail_in and next_out + avail_out are those
   position_of recorded, within or one past the end of the objects data and compressed), which statement 6 checks
   and keeps.  TLoopDDraw proves statements 0-1, TLoopDPrep 2-3, TLoopDPosOf 4, TLoopDCall 5, TLoopDAcc 6,
   TLoopDAssert 7, TLoopDTest 8; TLoopD.v composes them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Zlib.proof.harness.rt_stream.ULoopDKit.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* the six members of the compressor that position_of records (rt_stream's) *)
Notation cpos := Zlib.proof.harness.rt_stream.ULoopDKit.cpos.

(* the loop's body and its pieces: the whole body; from its third statement on; from its fifth (position_of, the
   call, the accounted assert, the unmoved assert, the out-of-room test); and each of these *)
Definition loop_body_t (s : statement) : statement := match s with Sloop b _ => b | _ => s end.
Definition bodyD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loop_body_t loopD_t] in (loop_body_t loopD_t) in exact x).
Definition prepD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_t loopD_t] in (suf 2 (loop_body_t loopD_t)) in
        exact x).
Definition callTestD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_t loopD_t] in (suf 4 (loop_body_t loopD_t)) in
        exact x).
Definition posD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_t loopD_t] in
          (first (suf 4 (loop_body_t loopD_t))) in exact x).
Definition callD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_t loopD_t] in
          (first (suf 5 (loop_body_t loopD_t))) in exact x).
Definition accD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_t loopD_t] in
          (first (suf 6 (loop_body_t loopD_t))) in exact x).
Definition assertD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_t loopD_t] in
          (first (suf 7 (loop_body_t loopD_t))) in exact x).
Definition testD_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_t loopD_t] in (suf 8 (loop_body_t loopD_t)) in
        exact x).

Lemma callTestD_t_eq :
  callTestD_t = Ssequence posD_t (Ssequence callD_t (Ssequence accD_t (Ssequence assertD_t testD_t))).
Proof. reflexivity. Qed.

(* the call accounted for what it moved: with [c] the compressor after the call and [a] its six members before
   it, accounted(&compressor, &at) holds, the four next_* are pointers, and the sums
   next_in + avail_in and next_out + avail_out (the same before and after) point into or one past the end of the
   objects data and compressed *)
Definition acc_ok (u : setup) (c : cst) (a : LS.posz) : Prop :=
  LS.accounted_b (cpos c) a = true /\
  isptr (cs_ni c) /\ isptr (cs_no c) /\ isptr (LS.pz_next_in a) /\ isptr (LS.pz_next_out a) /\
  exists ki ko, 0 <= ki <= Zlength (su_data u) /\ 0 <= ko <= su_cap u /\
    offset_val (cs_ain c) (cs_ni c) = offset_val ki (su_dp u) /\
    offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki (su_dp u) /\
    offset_val (cs_aout c) (cs_no c) = offset_val ko (su_cp u) /\
    offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_cp u).

Section Assertions.
Context (gv : globals) (vc vd va : val).

(* after read = next_in - data and the draws: DI_t for the new offered and flush, read = |D| *)
Definition DR_t (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l]
  (LOCALx (temp _read (vl (Zlength (dl_D l))) :: temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
          su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
        dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* before position_of: avail_in is clip(offered - |D|), avail_out at most clip(capacity - |O|) *)
Definition DC_t (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* after position_of: at holds the compressor's six members (at laws_session's compspecs) *)
Definition DP_t (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
         dobj u; cobj u (dl_O l); oobj u [];
         @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of (cpos (dl_c l))) va])).

(* after the call, its result [code] in _code; [l]: the new state, with the offered bytes [off] and the flush
   [flush] of the call; at holds the members [a] before the call: the call accounted for what it moved, and when no
   output space was offered, it returned Z_BUF_ERROR and moved nothing *)
Definition DA_t (J : urts_dinv) (u : setup) (off flush code : Z) (l : dls) (a : LS.posz) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
         Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) (dl_O l)
         else dl_ok J u l;
         LS.posz_ok a; LS.pz_avail_out a = 0 -> code = Z_BUF_ERROR /\ cpos (dl_c l) = a;
         acc_ok u (dl_c l) a]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
         dobj u; cobj u (dl_O l); oobj u []; @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va])).

(* after the asserts: at any bytes again *)
Definition DK_t (J : urts_dinv) (u : setup) (off flush code : Z) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
         Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) (dl_O l)
         else dl_ok J u l]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm_t gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

End Assertions.

(* the postcondition of the loop body, as forward_loop states it: falling through or `continue` reach the
   loop's test with DK_t, `break` leaves with DE_t, `return` is main's return *)
Definition loopD_post_t (J : urts_dinv) (gv : globals) (vc vd va : val) (u : setup) : ret_assert :=
  loop1_ret_assert (EX code : Z, EX l : dls, DK_t gv vc vd va J u (dl_off l) (dl_flush l) code l)
    (overridePost (EX O : list Z, EX c : cst, DE_t gv vc vd va u O c)
       (overridePost (EX O : list Z, EX c : cst, DE_t gv vc vd va u O c) POST_t)).

(** ** The pieces *)

(* statements 0-1: from DI_t to DR_t, for some new offered and flush (stated for any proof of the rest) *)
Definition drawD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  (forall l1, semax Delta_t (DR_t gv vc vd va J u l1) prepD_t (loopD_post_t J gv vc vd va u)) ->
  semax Delta_t (DI_t gv vc vd va J u l) bodyD_t (loopD_post_t J gv vc vd va u).

(* statements 2-3: from DR_t to DC_t *)
Definition prepD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  (forall l2, semax Delta_t (DC_t gv vc vd va J u l2) callTestD_t (loopD_post_t J gv vc vd va u)) ->
  semax Delta_t (DR_t gv vc vd va J u l) prepD_t (loopD_post_t J gv vc vd va u).

(* statement 4: position_of *)
Definition posD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  semax Delta_t (DC_t gv vc vd va J u l) posD_t (overridePost (DP_t gv vc vd va J u l) POST_t).

(* statement 5: the call *)
Definition callD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l, urts_dfacts J ->
  semax Delta_t (DP_t gv vc vd va J u l) callD_t
    (overridePost
       (EX code : Z, EX l' : dls, DA_t gv vc vd va J u (dl_off l) (dl_flush l) code l' (cpos (dl_c l)))
       POST_t).

(* statement 6: the accounted assert *)
Definition accD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u off flush code l a,
  semax Delta_t (DA_t gv vc vd va J u off flush code l a) accD_t
    (overridePost (DA_t gv vc vd va J u off flush code l a) POST_t).

(* statement 7: the unmoved assert *)
Definition assertD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u off flush code l a,
  semax Delta_t (DA_t gv vc vd va J u off flush code l a) assertD_t
    (overridePost (DK_t gv vc vd va J u off flush code l) POST_t).

(* statement 8: the out-of-room test *)
Definition testD_t_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u off flush code l,
  semax Delta_t (DK_t gv vc vd va J u off flush code l) testD_t (loopD_post_t J gv vc vd va u).

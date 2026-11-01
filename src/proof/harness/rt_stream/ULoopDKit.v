(* Law rt_stream (data of any length), main's deflate loop (UMainKit.loopD): the cut of its body and the
   assertions between the pieces.

   The loop body is, statement by statement:
     0  read = next_in - data;
     1  if (flush != Z_FINISH) { offered += upto(data_len - offered); flush = upto(Z_BLOCK);
                                 Z_FINISH only when the rest data_len - read fits in one call; then offered = data_len }
     2  avail_in = clip(offered - read);
     3  avail_out = clip(upto(capacity - (next_out - compressed)));
     4  [posD] = `position_of(&compressor, &at)`;
     5  [callD] = `code = deflate(&compressor, flush)`;
     6  [assertD] = `if (at.avail_out == 0) gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at))`;
     7  the out-of-room test (return 0 when deflate did not finish and compressed is full).
   [DR] is the state after statements 0-1 (DI for the new offered and flush, with read = |D|), [DC] the state right
   before position_of (avail_in = clip(offered - |D|), avail_out at most clip(capacity - |O|)), [DP] the state right
   after it (at holds the six members of the compressor, [cpos]), [DA] the state right after the call: either
   deflate returned Z_STREAM_END and O is a finished stream of the data, or the loop invariant holds again for the
   same offered and flush; and a call offered no output space returned Z_BUF_ERROR and moved nothing (the six
   members are at's).  [DK] is the state after the assert (at is any bytes again).  ULoopDDraw proves statements
   0-1 (DI to DR), ULoopDPrep 2-3 (DR to DC), ULoopDPosOf position_of (DC to DP), ULoopDCall the call (DP to DA),
   ULoopDAssert the assert (DA to DK), ULoopDTest the test (DK to the loop's test); ULoopD.v composes them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.harness.rt_stream.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* the loop's body and its pieces: the whole body; from its third statement on (after read and the draws); from
   its fifth (position_of, the deflate() call, the assert, the out-of-room test); position_of; the call; the
   assert; the test *)
Definition loop_body (s : statement) : statement := match s with Sloop b _ => b | _ => s end.
Definition bodyD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loop_body loopD] in (loop_body loopD) in exact x).
Definition prepD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body loopD] in (suf 2 (loop_body loopD)) in exact x).
Definition callTestD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body loopD] in (suf 4 (loop_body loopD)) in exact x).
Definition posD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body loopD] in (first (suf 4 (loop_body loopD))) in
        exact x).
Definition callD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body loopD] in (first (suf 5 (loop_body loopD))) in
        exact x).
Definition assertD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body loopD] in (first (suf 6 (loop_body loopD))) in
        exact x).
Definition testD : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body loopD] in (suf 7 (loop_body loopD)) in exact x).

Lemma callTestD_eq : callTestD = Ssequence posD (Ssequence callD (Ssequence assertD testD)).
Proof. reflexivity. Qed.

(* the six members of the compressor that position_of records and unmoved compares *)
Definition cpos (c : cst) : LS.posz :=
  LS.mk_posz (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c).

Section Assertions.
Context (gv : globals) (vc vd va : val).

(* after read = next_in - data and the draws: DI for the new offered and flush, read = |D| *)
Definition DR (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l]
  (LOCALx (temp _read (vl (Zlength (dl_D l))) :: temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
          su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
        dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* before the call: avail_in is clip(offered - |D|), avail_out at most clip(capacity - |O|) *)
Definition DC (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

(* after position_of: at holds the compressor's six members (at laws_session's compspecs, as position_of and
   unmoved take it) *)
Definition DP (J : urts_dinv) (u : setup) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true; dl_ok J u l;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u [];
         @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of (cpos (dl_c l))) va])).

(* after the call, its result [code] in _code; [l]: the new state, with the offered bytes [off] and the flush
   [flush] of the call; at holds the members [a] before the call: when no output space was offered, the call
   returned Z_BUF_ERROR and moved nothing *)
Definition DA (J : urts_dinv) (u : setup) (off flush code : Z) (l : dls) (a : LS.posz) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
         Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) (dl_O l)
         else dl_ok J u l;
         LS.posz_ok a; LS.pz_avail_out a = 0 -> code = Z_BUF_ERROR /\ cpos (dl_c l) = a]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va])).

(* after the assert: as DA, at any bytes again *)
Definition DK (J : urts_dinv) (u : setup) (off flush code : Z) (l : dls) : environ -> mpred :=
  PROPx [su_ok u; rparams_ok (su_level u) 8 (su_wbits u) (su_mem u) (su_strategy u) = true;
         Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal [] (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) None (su_data u) (dl_O l)
         else dl_ok J u l]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           su_locals u (su_wbits u) ++ lv_locals gv vc vd va)
  (SEPx [cstream gv vc (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va])).

End Assertions.

(* the postcondition of the loop body, as forward_loop states it: falling through or `continue` reach the
   loop's test with DK, `break` leaves with DE, `return` is main's return *)
Definition loopD_post (J : urts_dinv) (gv : globals) (vc vd va : val) (u : setup) : ret_assert :=
  loop1_ret_assert (EX code : Z, EX l : dls, DK gv vc vd va J u (dl_off l) (dl_flush l) code l)
    (overridePost (EX O : list Z, EX c : cst, DE gv vc vd va u O c)
       (overridePost (EX O : list Z, EX c : cst, DE gv vc vd va u O c) POST_m)).

(** ** The pieces *)

(* statements 0-1: from DI to DR, for some new offered and flush (stated for any proof of the rest) *)
Definition drawD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  (forall l1, semax Delta_m (DR gv vc vd va J u l1) prepD (loopD_post J gv vc vd va u)) ->
  semax Delta_m (DI gv vc vd va J u l) bodyD (loopD_post J gv vc vd va u).

(* statements 2-3: from DR to DC *)
Definition prepD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  (forall l2, semax Delta_m (DC gv vc vd va J u l2) callTestD (loopD_post J gv vc vd va u)) ->
  semax Delta_m (DR gv vc vd va J u l) prepD (loopD_post J gv vc vd va u).

(* statement 4: position_of *)
Definition posD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l,
  semax Delta_m (DC gv vc vd va J u l) posD (overridePost (DP gv vc vd va J u l) POST_m).

(* statement 5: the call *)
Definition callD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u l, urts_dfacts J ->
  semax Delta_m (DP gv vc vd va J u l) callD
    (overridePost (EX code : Z, EX l' : dls, DA gv vc vd va J u (dl_off l) (dl_flush l) code l' (cpos (dl_c l)))
       POST_m).

(* statement 6: the assert *)
Definition assertD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u off flush code l a,
  semax Delta_m (DA gv vc vd va J u off flush code l a) assertD
    (overridePost (DK gv vc vd va J u off flush code l) POST_m).

(* statement 7: the out-of-room test *)
Definition testD_stmt : Prop :=
  forall {Espec : OracleKind} J gv vc vd va u off flush code l,
  semax Delta_m (DK gv vc vd va J u off flush code l) testD (loopD_post J gv vc vd va u).

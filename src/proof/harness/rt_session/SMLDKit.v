(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD, statement 57): the cut of its body and
   the assertions between the pieces.  The loop is rt_stream_trailing's:

     0  read = next_in - data;
     1  if (flush != Z_FINISH) { offered += upto(data_len - offered); flush = upto(Z_BLOCK); ... }
     2  avail_in = clip(offered - read);
     3  avail_out = clip(upto(out_size - (next_out - compressed)));
     4  [posD_s] = `position_of(&compressor, &at)`;
     5  [callD_s] = `code = deflate(&compressor, flush)`;
     6  [accD_s] = `gp_assert(accounted(&compressor, &at))`;
     7  [assertD_s] = `if (at.avail_out == 0) gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at))`;
     8  the out-of-room test (return 0 when deflate did not finish and compressed is full).

   The assertions are SMKit's DI with the invariant J of the session (SDFacts.ses_dfacts over the dictionary
   [sdict u] and the header [sgh u]); the compressor's gzhead pointer is [ghp u] and the header part of its state
   [hdr_at (Some s) (ghp u) hx] and the rest [Hr] are framed through every piece; only the call changes the state,
   and it keeps the state's gzhead (SDFacts.sd_deflate, sd_range), so [hdr_at] of the new state is the same
   predicate and [hclose] still holds (SMLDLib.hdr_at_gz, hclose_gz).  [DA_s], the state after the call, also
   says that the call accounted for what it moved ([acc_ok_s]: next_in + avail_in and next_out + avail_out are
   those position_of recorded, within or one past the end of the objects data and compressed), which statement 6
   checks and keeps.  SMLDDraw proves statements 0-1, SMLDPrep 2-3, SMLDPosOf 4, SMLDCall 5, SMLDAcc 6,
   SMLDAssert 7, SMLDTest 8; SMLoopD.v composes them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMLDLib.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* the loop's body and its pieces: the whole body; from its third statement on; from its fifth (position_of, the
   call, the accounted assert, the unmoved assert, the out-of-room test); and each of these *)
Definition loop_body_s (s : statement) : statement := match s with Sloop b _ => b | _ => s end.
Definition bodyD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [loop_body_s loopD] in (loop_body_s loopD) in exact x).
Definition prepD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_s loopD] in (suf 2 (loop_body_s loopD)) in
        exact x).
Definition callTestD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_s loopD] in (suf 4 (loop_body_s loopD)) in
        exact x).
Definition posD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_s loopD] in
          (first (suf 4 (loop_body_s loopD))) in exact x).
Definition callD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_s loopD] in
          (first (suf 5 (loop_body_s loopD))) in exact x).
Definition accD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_s loopD] in
          (first (suf 6 (loop_body_s loopD))) in exact x).
Definition assertD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [first suf loop_body_s loopD] in
          (first (suf 7 (loop_body_s loopD))) in exact x).
Definition testD_s : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf loop_body_s loopD] in (suf 8 (loop_body_s loopD)) in
        exact x).

Lemma callTestD_s_eq :
  callTestD_s = Ssequence posD_s (Ssequence callD_s (Ssequence accD_s (Ssequence assertD_s testD_s))).
Proof. reflexivity. Qed.

(* the call accounted for what it moved: with [c] the compressor after the call and [a] its six members before
   it, accounted(&compressor, &at) holds, the four next_* are pointers, and the sums
   next_in + avail_in and next_out + avail_out (the same before and after) point into or one past the end of the
   objects data and compressed *)
Definition acc_ok_s (u : setup) (c : cst) (a : LS.posz) : Prop :=
  LS.accounted_b (cpos_s c) a = true /\
  isptr (cs_ni c) /\ isptr (cs_no c) /\ isptr (LS.pz_next_in a) /\ isptr (LS.pz_next_out a) /\
  exists ki ko, 0 <= ki <= Zlength (su_data u) /\ 0 <= ko <= su_cap u /\
    offset_val (cs_ain c) (cs_ni c) = offset_val ki (su_dp u) /\
    offset_val (LS.pz_avail_in a) (LS.pz_next_in a) = offset_val ki (su_dp u) /\
    offset_val (cs_aout c) (cs_no c) = offset_val ko (su_cp u) /\
    offset_val (LS.pz_avail_out a) (LS.pz_next_out a) = offset_val ko (su_cp u).

Section Assertions.
Context (gv : globals) (vh vg vc va vd : val).

(* after read = next_in - data and the draws: DI for the new offered and flush, read = |D| *)
Definition DR_s (J : ses_dinv) (u : setup) (l : dls) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [su_ok u; dl_ok J u l; hclose vh u (cs_s (dl_c l)) hx Hr]
  (LOCALx (temp _read (vl (Zlength (dl_D l))) :: temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx [cstream gv vc (ghp vh u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va;
         hdr_at (Some (cs_s (dl_c l))) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u])).

(* before position_of: avail_in is clip(offered - |D|), avail_out at most clip(capacity - |O|) *)
Definition DC_s (J : ses_dinv) (u : setup) (l : dls) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [su_ok u; dl_ok J u l; hclose vh u (cs_s (dl_c l)) hx Hr;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx [cstream gv vc (ghp vh u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va;
         hdr_at (Some (cs_s (dl_c l))) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u])).

(* after position_of: at holds the compressor's six members (at laws_session's compspecs) *)
Definition DP_s (J : ses_dinv) (u : setup) (l : dls) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [su_ok u; dl_ok J u l; hclose vh u (cs_s (dl_c l)) hx Hr;
         cs_ain (dl_c l) = Z.min (dl_off l - Zlength (dl_D l)) Int.max_unsigned;
         0 <= cs_aout (dl_c l) <= Z.min (su_cap u - Zlength (dl_O l)) Int.max_unsigned]
  (LOCALx (temp _offered (vl (dl_off l)) :: temp _flush (vi (dl_flush l)) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx [cstream gv vc (ghp vh u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u [];
         @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of (cpos_s (dl_c l))) va;
         hdr_at (Some (cs_s (dl_c l))) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u])).

(* after the call, its result [code] in _code; [l]: the new state, with the offered bytes [off] and the flush
   [flush] of the call; at holds the members [a] before the call: the call accounted for what it moved, and when no
   output space was offered, it returned Z_BUF_ERROR and moved nothing *)
Definition DA_s (J : ses_dinv) (u : setup) (off flush code : Z) (l : dls) (a : LS.posz)
    (hx : share * val * val * val) (Hr : mpred) : environ -> mpred :=
  PROPx [su_ok u; Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal (sdict u) (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) (sgh u) (su_data u) (dl_O l)
         else dl_ok J u l;
         LS.posz_ok a; LS.pz_avail_out a = 0 -> code = Z_BUF_ERROR /\ cpos_s (dl_c l) = a;
         acc_ok_s u (dl_c l) a; hclose vh u (cs_s (dl_c l)) hx Hr]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx [cstream gv vc (ghp vh u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va;
         hdr_at (Some (cs_s (dl_c l))) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u])).

(* after the asserts: at any bytes again *)
Definition DK_s (J : ses_dinv) (u : setup) (off flush code : Z) (l : dls)
    (hx : share * val * val * val) (Hr : mpred) : environ -> mpred :=
  PROPx [su_ok u; Int.min_signed <= code <= Int.max_signed; dl_off l = off; dl_flush l = flush;
         Zlength (dl_O l) <= su_cap u; rbytes (dl_O l);
         cs_no (dl_c l) = offset_val (Zlength (dl_O l)) (su_cp u);
         if code =? Z_STREAM_END
         then dfinal (sdict u) (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) (sgh u) (su_data u) (dl_O l)
         else dl_ok J u l;
         hclose vh u (cs_s (dl_c l)) hx Hr]
  (LOCALx (temp _code (vi code) :: temp _offered (vl off) :: temp _flush (vi flush) ::
           c_locals u ++ d_locals u (su_wbits u) ++ lvs gv vh vg vc va vd)
  (SEPx [cstream gv vc (ghp vh u) (dl_c l); data_at_ Tsh t_z vd; mem_mgr gv; Rm gv;
         dobj u; cobj u (dl_O l); oobj u []; data_at_ Tsh t_p va;
         hdr_at (Some (cs_s (dl_c l))) (ghp vh u) hx; Hr; graw vg u; dictobj u; dcopy u])).

End Assertions.

(* the postcondition of the loop body, as forward_loop states it: falling through or `continue` reach the
   loop's test with DK_s, `break` leaves with DE, `return` is main's return *)
Definition loopD_post_s (J : ses_dinv) (gv : globals) (vh vg vc va vd : val) (u : setup)
    (hx : share * val * val * val) (Hr : mpred) : ret_assert :=
  loop1_ret_assert (EX code : Z, EX l : dls, DK_s gv vh vg vc va vd J u (dl_off l) (dl_flush l) code l hx Hr)
    (overridePost (EX O : list Z, EX c : cst, DE gv vh vg vc va vd u O c)
       (overridePost (EX O : list Z, EX c : cst, DE gv vh vg vc va vd u O c) POST_s)).

(** ** The pieces *)

(* statements 0-1: from DI to DR_s, for some new offered and flush (stated for any proof of the rest) *)
Definition drawD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u hx Hr l,
  (forall l1, semax Delta_s (DR_s gv vh vg vc va vd J u l1 hx Hr) prepD_s
                (loopD_post_s J gv vh vg vc va vd u hx Hr)) ->
  semax Delta_s (DI gv vh vg vc va vd J u l hx Hr) bodyD_s (loopD_post_s J gv vh vg vc va vd u hx Hr).

(* statements 2-3: from DR_s to DC_s *)
Definition prepD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u hx Hr l,
  (forall l2, semax Delta_s (DC_s gv vh vg vc va vd J u l2 hx Hr) callTestD_s
                (loopD_post_s J gv vh vg vc va vd u hx Hr)) ->
  semax Delta_s (DR_s gv vh vg vc va vd J u l hx Hr) prepD_s (loopD_post_s J gv vh vg vc va vd u hx Hr).

(* statement 4: position_of *)
Definition posD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u hx Hr l,
  semax Delta_s (DC_s gv vh vg vc va vd J u l hx Hr) posD_s
    (overridePost (DP_s gv vh vg vc va vd J u l hx Hr) POST_s).

(* statement 5: the call *)
Definition callD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u hx Hr l, ses_dfacts J ->
  semax Delta_s (DP_s gv vh vg vc va vd J u l hx Hr) callD_s
    (overridePost
       (EX code : Z, EX l' : dls,
          DA_s gv vh vg vc va vd J u (dl_off l) (dl_flush l) code l' (cpos_s (dl_c l)) hx Hr)
       POST_s).

(* statement 6: the accounted assert *)
Definition accD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u off flush code l a hx Hr,
  semax Delta_s (DA_s gv vh vg vc va vd J u off flush code l a hx Hr) accD_s
    (overridePost (DA_s gv vh vg vc va vd J u off flush code l a hx Hr) POST_s).

(* statement 7: the unmoved assert *)
Definition assertD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u off flush code l a hx Hr,
  semax Delta_s (DA_s gv vh vg vc va vd J u off flush code l a hx Hr) assertD_s
    (overridePost (DK_s gv vh vg vc va vd J u off flush code l hx Hr) POST_s).

(* statement 8: the out-of-room test *)
Definition testD_s_stmt : Prop :=
  forall {Espec : OracleKind} J gv vh vg vc va vd u off flush code l hx Hr,
  semax Delta_s (DK_s gv vh vg vc va vd J u off flush code l hx Hr) testD_s
    (loopD_post_s J gv vh vg vc va vd u hx Hr).

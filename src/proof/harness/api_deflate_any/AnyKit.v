(* Law api_deflate_any: the kit of main's body proof (AnyMain.v).  main's type context and postcondition, its body
   cut into suffixes, the assertions at the cuts and the statements of the parts.

   main of harness/api_deflate_any.c drives one stream: deflateInit2 with any parameters in zlib.h's ranges
   (gp_assume(deflate_params_ok(...)); it must return Z_OK unless Z_MEM_ERROR), then a loop whose
   iteration offers the next piece of the data (a copy of [take] bytes from [read] on, [take] any value up to
   clip(data_len - read); once Z_FINISH was given, the [left] bytes the last call did not consume), an output
   space of any [out_size] bytes holding any bytes [bs] (and a copy [before] of them), maybe deflateParams with any
   level and strategy (only before the first Z_FINISH), then records the stream's position in its local [at]
   (position_of) and calls deflate with any flush (Z_FINISH once given), and checks the codes, that a call with no
   output space and a valid flush returned Z_BUF_ERROR and left the position as it was (unmoved), and that the
   output space past what deflate wrote still holds [bs].  The model facts are
   [any_facts J] (AnyFacts.v) for main's loop invariant [J]: [J fin s tin adler] of the state [s] ([fin = Some R]
   once Z_FINISH was given, [R] the data not consumed since; [tin], [adler] the fields total_in and strm->adler).

   The stream's memory is that of law api_deterministic's main (DetKit2.strm_at, shead, out_at; their lemmas:
   DetKit2, DetMem2, DetMem2b, used qualified).  The local [at] (struct position, address [ap]) is held as
   laws_session/Spec.v's [data_at_ Tsh t_pos ap] at its compspecs CS_session, holding [pos_of (c_pos ...)] from
   position_of to the end of the checks.

   main's body is proved at the law's compspecs AnyCS.CS (main's local struct position is not a composite of
   deflate.c's DCS.CS, and VST lifts only whole function bodies from one compspecs to another); the assertions keep
   the shared specifications' predicates at DCS.CS (calls are compspecs-independent); main's own loads of the
   stream's members use any_field_cs below; the postcondition [POST_m] frees main's two locals at AnyCS.CS.

   Each part lemma is in continuation-passing style: it proves the suffix at its first cut from the hypothesis
   that the suffix at its next cut is proved from the assertion there.
     any_prefix (AnyPrefix.v): main_body (PRE0)        -> msuf15 (the loop), J_at
   and in the loop body (lsuf k: statement k of the body's sequence):
     any_pre    (AnyPre.v):    lbody (J_at)            -> lsuf9 (the deflateParams if), C_at with c0 (set_buffer done)
     any_params (AnyParams.v): lsuf9 (C_at, c0)        -> lsuf10 (position_of, deflate), C_at (maybe after deflateParams)
     any_call   (AnyCall.v):   lsuf10 (C_at)           -> lsuf12 (the checks), D_at
     any_check  (AnyCheck.v):  lsuf12 (D_at)           -> end of the body, T_at (the loop test's precondition)
   AnyMain.v assembles them (the loop, its test, return 0 after the loop). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.deflate.ApiKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Zlib.contracts.api_deflate_any.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.
Module DK := Zlib.proof.harness.api_deterministic.DetKit2.
Module LS := Zlib.proof.harness.laws_session.Spec.

(** ** Suffixes of main's body *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

(* main's body is Ssequence main_body (return 0); main_body's statements: the four nondet_u32 (0-3),
   gp_assume(deflate_params_ok(...)) (4), data_len (5), data (6), its NULL test (7), new_stream (8),
   code = deflateInit2(...) (9), the Z_MEM_ERROR test (10), gp_assert(code == Z_OK) (11), read, left, finishing
   (12-14), then msuf15 = the loop; return 0 *)
Definition main_body : statement := ltac:(let x := eval cbv beta iota zeta delta [f_main fn_body] in
  (match fn_body f_main with Ssequence b _ => b | _ => Sskip end) in exact x).
Ltac get_msuf k := let x := eval cbv beta iota zeta delta [suf main_body] in (suf k main_body) in exact x.
Definition msuf15 : statement := ltac:(get_msuf 15%nat).

(* the do-while loop is Sloop lbody ltest *)
Definition lbody : statement := ltac:(let x := eval cbv beta iota zeta delta [suf main_body] in
  (match suf 15 main_body with Ssequence (Sloop b _) _ => b | _ => Sskip end) in exact x).
Definition ltest : statement := ltac:(let x := eval cbv beta iota zeta delta [suf main_body] in
  (match suf 15 main_body with Ssequence (Sloop _ t) _ => t | _ => Sskip end) in exact x).

Lemma msuf15_eq : msuf15 = Ssequence (Sloop lbody ltest) (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* the loop body's statements: take (0), out_size (1), flush (2), piece = copy_of (3), out = alloc_any_bytes (4),
   their NULL test (5), before = copy_of (6), its NULL test (7), set_buffer (8), the deflateParams if (9),
   position_of (10), deflate (11), bad_flush (12), the three gp_asserts on the code (13-15), the unmoved check
   when out_size == 0 && !bad_flush (16), wrote (17), the gp_assert on the output space (18), read, left,
   finishing (19-21), free x3 (22-24) *)
Ltac get_lsuf k := let x := eval cbv beta iota zeta delta [suf lbody] in (suf k lbody) in exact x.
Definition lsuf9 : statement := ltac:(get_lsuf 9%nat).
Definition lsuf10 : statement := ltac:(get_lsuf 10%nat).
Definition lsuf12 : statement := ltac:(get_lsuf 12%nat).
Definition lsuf16 : statement := ltac:(get_lsuf 16%nat).
Definition lsuf17 : statement := ltac:(get_lsuf 17%nat).
Definition lsuf19 : statement := ltac:(get_lsuf 19%nat).

(** ** Type context and postcondition of main's body *)
Definition Delta_m : tycontext :=
  func_tycontext f_main (QPvarspecs Zlib.contracts.api_deflate_any.whole_prog) Gmain nil.

(* the frame: main's two locals at the law's compspecs (AnyMainStmt.any_main_stmt) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (@stackframe_of AnyCS.CS f_main).

(** ** The assertions *)

(* main's [finishing]: 1 once Z_FINISH was given *)
Definition fin_flag (fin : option (list Z)) : Z := match fin with Some _ => 1 | None => 0 end.

(* the output space after [O] was written at its start: the rest still holds the bytes [bs] it was made with *)
Definition ovals (bs O : list Z) : list Z := O ++ sublist (Zlength O) (Zlength bs) bs.

(* the loop head: the state [s], [read] bytes of the data consumed, [left] the avail_in the last call left (the
   rest of the data to give with Z_FINISH once [fin] is [Some _]); total_in = read *)
Record lstate := mkLS {
  ls_s : dstate; ls_fin : option (list Z); ls_read : Z; ls_left : Z;
  ls_tout : Z; ls_adler : Z; ls_msg : option Z; ls_msgv : val }.

(* one iteration's choices: the piece's length, the output space's size and bytes, the flush, the three objects *)
Record citer := mkCI {
  ci_take : Z; ci_room : Z; ci_bs : list Z; ci_flush : Z; ci_piece : val; ci_out : val; ci_before : val }.

(* the stream before deflate: the state, next_in at [nin] in the piece, [out] written into the output space
   (deflateParams may consume input and write output) *)
Record cstate := mkCS {
  cs_s : dstate; cs_nin : Z; cs_out : list Z; cs_tout : Z; cs_adler : Z; cs_msg : option Z; cs_msgv : val }.

(* deflate's result: the model's [c_deflate s z flush = Some (dr_s, dr_z, dr_code)] *)
Record dres := mkDR { dr_s : dstate; dr_z : strm; dr_code : Z; dr_msgv : val }.

Section Kit.
Context (J : det_inv) (n : Z) (data : list Z) (datap : val).
Context (v sp : val) (gv : globals) (ap : val).

(* what main drew before the loop *)
Definition setup_ok : Prop :=
  any_facts J /\ 0 <= n <= 9223372036854775807 /\ Zlength data = n /\ bytes data /\ isptr datap.

Definition J_ok (ls : lstate) : Prop :=
  setup_ok /\ J (ls_fin ls) (ls_s ls) (ls_read ls) (ls_adler ls) /\
  0 <= ls_read ls <= n /\ 0 <= ls_left ls <= 4294967295 /\
  match ls_fin ls with
  | None => True
  | Some R => ls_read ls + ls_left ls <= n /\ R = sublist (ls_read ls) (ls_read ls + ls_left ls) data
  end /\
  u64r (ls_tout ls) /\ msg_ok (ls_msg ls) (ls_msgv ls).

Definition J_loc (ls : lstate) : list localdef :=
  [temp _data datap; temp _data_len (vl n); temp _read (vl (ls_read ls)); temp _left (vl (ls_left ls));
   temp _finishing (vi (fin_flag (ls_fin ls))); lvar _strm t_strm v; lvar _at LS.t_pos ap; gvars gv].

(* main's local [at] when it holds no position main reads *)
Definition at_free : mpred := @data_at_ LS.CS_session Tsh LS.t_pos ap.

Definition J_sep (ls : lstate) : list mpred :=
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   DK.shead v (ls_s ls) sp (ls_read ls) (ls_tout ls) (ls_msgv ls) (ls_adler ls) gv; at_free; TT].

Definition J_at (ls : lstate) : environ -> mpred :=
  PROPx [J_ok ls] (LOCALx (J_loc ls) (SEPx (J_sep ls))).

Definition J_inv : environ -> mpred := EX ls : lstate, J_at ls.

(* after the body (before the loop test): the code of deflate; the invariant again unless it was
   Z_STREAM_END *)
Definition T_at (code : Z) (ls : lstate) : environ -> mpred :=
  PROPx [setup_ok; code <> Z_STREAM_END -> J_ok ls]
    (LOCALx (temp _code (vi code) :: J_loc ls) (SEPx (J_sep ls))).

Definition T_inv : environ -> mpred := EX code : Z, EX ls : lstate, T_at code ls.

(* after the loop *)
Definition E_inv : environ -> mpred :=
  EX ls : lstate, PROPx [] (LOCALx [lvar _strm t_strm v; lvar _at LS.t_pos ap; gvars gv] (SEPx (J_sep ls))).

(* the loop body's postcondition *)
Definition Rbody : ret_assert := loop1_ret_assert T_inv (overridePost E_inv POST_m).

(* the piece: [take] bytes of the data from [read] on *)
Definition ci_inb (ls : lstate) (ci : citer) : list Z := sublist (ls_read ls) (ls_read ls + ci_take ci) data.

Definition ci_ok (ls : lstate) (ci : citer) : Prop :=
  0 <= ci_take ci <= 4294967295 /\ ls_read ls + ci_take ci <= n /\
  Int.min_signed <= ci_flush ci <= Int.max_signed /\
  (ls_fin ls <> None -> ci_flush ci = Z_FINISH /\ ci_take ci = ls_left ls) /\
  0 <= ci_room ci <= 4294967295 /\ Zlength (ci_bs ci) = ci_room ci /\ bytes (ci_bs ci) /\
  isptr (ci_piece ci) /\ isptr (ci_out ci) /\ isptr (ci_before ci).

Definition B_loc (ls : lstate) (ci : citer) : list localdef :=
  [temp _data datap; temp _data_len (vl n); temp _read (vl (ls_read ls)); temp _left (vl (ls_left ls));
   temp _finishing (vi (fin_flag (ls_fin ls))); temp _take (vl (ci_take ci)); temp _out_size (vl (ci_room ci));
   temp _flush (vi (ci_flush ci)); temp _piece (ci_piece ci); temp _out (ci_out ci);
   temp _before (ci_before ci); lvar _strm t_strm v; lvar _at LS.t_pos ap; gvars gv].

(* before deflate: deflateParams was called only before Z_FINISH (once Z_FINISH was given, the state is the
   loop head's and next_in the piece's start) *)
Definition cs_ok (ls : lstate) (ci : citer) (c : cstate) : Prop :=
  J (ls_fin ls) (cs_s c) (ls_read ls + cs_nin c) (cs_adler c) /\
  0 <= cs_nin c <= ci_take ci /\ Zlength (cs_out c) <= ci_room ci /\ bytes (cs_out c) /\
  (ls_fin ls <> None -> cs_nin c = 0) /\
  u64r (cs_tout c) /\ msg_ok (cs_msg c) (cs_msgv c).

(* the configuration right after set_buffer *)
Definition c0 (ls : lstate) : cstate :=
  mkCS (ls_s ls) 0 [] (ls_tout ls) (ls_adler ls) (ls_msg ls) (ls_msgv ls).

Definition C_sep (ls : lstate) (ci : citer) (c : cstate) : list mpred :=
  let take := ci_take ci in let room := ci_room ci in let o := cs_out c in
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   BoundKit.obj (ci_piece ci) (ci_inb ls ci);
   DK.out_at (ci_out ci) room (map vi (ovals (ci_bs ci) o));
   BoundKit.obj (ci_before ci) (ci_bs ci);
   DK.strm_at v (cs_s c) sp (offset_val (cs_nin c) (ci_piece ci)) (take - cs_nin c) (ls_read ls + cs_nin c)
     (offset_val (Zlength o) (ci_out ci)) (room - Zlength o) (cs_tout c) (cs_msgv c) (cs_adler c) gv;
   at_free; TT].

Definition C_at (ls : lstate) (ci : citer) (c : cstate) : environ -> mpred :=
  PROPx [J_ok ls; ci_ok ls ci; cs_ok ls ci c] (LOCALx (B_loc ls ci) (SEPx (C_sep ls ci c))).

(* the stream's position before deflate (what position_of records in [at]): next_in, avail_in, total_in,
   next_out, avail_out, total_out of C_sep's strm_at *)
Definition c_pos (ls : lstate) (ci : citer) (c : cstate) : LS.posz :=
  LS.mk_posz (offset_val (cs_nin c) (ci_piece ci)) (ci_take ci - cs_nin c) (ls_read ls + cs_nin c)
    (offset_val (Zlength (cs_out c)) (ci_out ci)) (ci_room ci - Zlength (cs_out c)) (cs_tout c).

(* the model call of deflate *)
Definition d_call (ls : lstate) (ci : citer) (c : cstate) : strm :=
  zcall (ci_inb ls ci) (cs_nin c) (ci_take ci - cs_nin c) (ls_read ls + cs_nin c)
    (ci_room ci - Zlength (cs_out c)) (cs_tout c) (cs_adler c) (cs_msg c).

(* deflate's run and what main checks of it *)
Definition dr_ok (ls : lstate) (ci : citer) (c : cstate) (d : dres) : Prop :=
  c_deflate (cs_s c) (d_call ls ci c) (ci_flush ci) = Some (dr_s d, dr_z d, dr_code d) /\
  call_okw (ci_inb ls ci) (cs_nin c) (ci_room ci - Zlength (cs_out c)) (ls_read ls + cs_nin c) (cs_tout c)
    (dr_z d) /\
  (dr_code d <> Z_STREAM_END ->
   J (if ci_flush ci =? Z_FINISH then Some (sublist (z_next_in (dr_z d)) (ci_take ci) (ci_inb ls ci))
      else None)
     (dr_s d) (z_total_in (dr_z d)) (z_adler (dr_z d))) /\
  (dr_code d = Z_STREAM_ERROR <-> ci_flush ci < 0 \/ 5 < ci_flush ci) /\
  (dr_code d = Z_OK \/ dr_code d = Z_BUF_ERROR \/ dr_code d = Z_STREAM_ERROR \/ dr_code d = Z_STREAM_END) /\
  (dr_code d = Z_STREAM_END -> ci_flush ci = Z_FINISH) /\
  (* no output space and a valid flush: Z_BUF_ERROR, nothing moved (AnyCodes.deflate_no_room) *)
  (ci_room ci = 0 -> 0 <= ci_flush ci <= 5 ->
   dr_code d = Z_BUF_ERROR /\ z_next_in (dr_z d) = cs_nin c /\ z_avail_in (dr_z d) = ci_take ci - cs_nin c /\
   z_total_in (dr_z d) = ls_read ls + cs_nin c /\ z_out (dr_z d) = [] /\ z_avail_out (dr_z d) = 0 /\
   z_total_out (dr_z d) = cs_tout c) /\
  msg_ok (z_msg (dr_z d)) (dr_msgv d).

Definition D_sep (ls : lstate) (ci : citer) (c : cstate) (d : dres) : list mpred :=
  let room := ci_room ci in let o := cs_out c ++ z_out (dr_z d) in let z := dr_z d in
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   BoundKit.obj (ci_piece ci) (ci_inb ls ci);
   DK.out_at (ci_out ci) room (map vi (ovals (ci_bs ci) o));
   BoundKit.obj (ci_before ci) (ci_bs ci);
   DK.strm_at v (dr_s d) sp (offset_val (z_next_in z) (ci_piece ci)) (z_avail_in z) (z_total_in z)
     (offset_val (Zlength o) (ci_out ci)) (z_avail_out z) (z_total_out z) (dr_msgv d) (z_adler z) gv;
   @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of (c_pos ls ci c)) ap; TT].

Definition D_at (ls : lstate) (ci : citer) (c : cstate) (d : dres) : environ -> mpred :=
  PROPx [J_ok ls; ci_ok ls ci; cs_ok ls ci c; dr_ok ls ci c d]
    (LOCALx (temp _code (vi (dr_code d)) :: B_loc ls ci) (SEPx (D_sep ls ci c d))).

(* bad_flush = flush < Z_NO_FLUSH || flush > Z_BLOCK *)
Definition bad_b (fl : Z) : bool := (fl <? 0) || (5 <? fl).

(* after the three checks of the code (before the unmoved check): D_at with main's [bad_flush] *)
Definition Dq_at (ls : lstate) (ci : citer) (c : cstate) (d : dres) : environ -> mpred :=
  PROPx [J_ok ls; ci_ok ls ci; cs_ok ls ci c; dr_ok ls ci c d]
    (LOCALx (temp _bad_flush (Val.of_bool (bad_b (ci_flush ci))) :: temp _code (vi (dr_code d)) :: B_loc ls ci)
     (SEPx (D_sep ls ci c d))).

End Kit.

(** ** main's entry (after start_function) *)
Definition PRE0 (v : val) (gv : globals) (ap : val) : environ -> mpred :=
  PROP () LOCAL (lvar _strm t_strm v; lvar _at LS.t_pos ap; gvars gv)
  SEP (data_at_ Tsh t_strm v; mem_mgr gv; deflate_globals gv; version_at gv vlit; at_free ap).

(** ** main's loads of the stream's members, at the law's compspecs *)
Lemma any_field_cs_avail_in (sh : share) (x p : val) :
  @field_at DCS.CS sh t_strm (DOT _avail_in) x p = @field_at AnyCS.CS sh t_strm (DOT _avail_in) x p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma any_field_cs_avail_out (sh : share) (x p : val) :
  @field_at DCS.CS sh t_strm (DOT _avail_out) x p = @field_at AnyCS.CS sh t_strm (DOT _avail_out) x p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(** ** The parts' statements (at the law's compspecs) *)
Definition any_prefix_stmt : Prop := forall {Espec : OracleKind} v gv ap,
  any_theory_stmt ->
  (forall J n data datap sp ls, @semax AnyCS.CS _ Delta_m (J_at J n data datap v sp gv ap ls) msuf15 POST_m) ->
  @semax AnyCS.CS _ Delta_m (PRE0 v gv ap) main_body POST_m.

Definition any_pre_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls,
  (forall ci, @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci (c0 ls)) lsuf9
     (Rbody J n data datap v sp gv ap)) ->
  @semax AnyCS.CS _ Delta_m (J_at J n data datap v sp gv ap ls) lbody (Rbody J n data datap v sp gv ap).

Definition any_params_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci,
  (forall c, @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci c) lsuf10 (Rbody J n data datap v sp gv ap)) ->
  @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci (c0 ls)) lsuf9 (Rbody J n data datap v sp gv ap).

Definition any_call_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c,
  (forall d, @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf12 (Rbody J n data datap v sp gv ap)) ->
  @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci c) lsuf10 (Rbody J n data datap v sp gv ap).

(* the checks after deflate, in four parts (AnyCheck.v composes them):
     any_check_code    (AnyCheckCode.v):    lsuf12 (D_at)  -> lsuf16 (the unmoved check), Dq_at
     any_check_unmoved (AnyCheckUnmoved.v): lsuf16 (Dq_at) -> lsuf17 (wrote), D_at
     any_check_bytes   (AnyCheckBytes.v):   lsuf17 (D_at)  -> lsuf19 (read, left, finishing, the frees), D_at
     any_check_tail    (AnyCheck.v):        lsuf19 (D_at)  -> end of the body *)
Definition any_check_code_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c d,
  @semax AnyCS.CS _ Delta_m (Dq_at J n data datap v sp gv ap ls ci c d) lsuf16 (Rbody J n data datap v sp gv ap) ->
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf12 (Rbody J n data datap v sp gv ap).

Definition any_check_unmoved_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c d,
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf17 (Rbody J n data datap v sp gv ap) ->
  @semax AnyCS.CS _ Delta_m (Dq_at J n data datap v sp gv ap ls ci c d) lsuf16 (Rbody J n data datap v sp gv ap).

Definition any_check_bytes_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c d,
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf19 (Rbody J n data datap v sp gv ap) ->
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf17 (Rbody J n data datap v sp gv ap).

Definition any_check_tail_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c d,
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf19 (Rbody J n data datap v sp gv ap).

Definition any_check_stmt : Prop := forall {Espec : OracleKind} J n data datap v sp gv ap ls ci c d,
  @semax AnyCS.CS _ Delta_m (D_at J n data datap v sp gv ap ls ci c d) lsuf12 (Rbody J n data datap v sp gv ap).

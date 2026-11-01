(* Law api_deterministic (data of any length): the kit of main's body proof (DetMain2.v).  main's type context and postcondition, its
   body cut into suffixes, the assertions at the cuts, and the memory lemmas the parts share.

   main of harness/api_deterministic.c drives two streams [first] and [second] by the same calls.  Its proof
   keeps the two streams' abstract states EQUAL: every call runs the same model function on the same arguments
   (DSpec's specifications are functional), so both calls of a pair return the same state, stream fields, code
   and output.  The facts about the model are [det_facts2 J] (DetFacts2.v, for main's loop invariant [J]).
   The data have any length below 2^63; each iteration offers the next [take = clip(offered - read)] bytes (at
   most 2^32 - 1), and Z_FINISH is chosen only when the rest of the data fits in one call.

   Each part lemma is in continuation-passing style: it proves the suffix at its first cut from the hypothesis
   that the suffix at its next cut is proved from the assertion there.
     det_prefix (DetPrefix2.v): main_body (PRE0)       -> msuf17 (the loop), J_at
   and in the loop body (lsuf k: statement k of the body's sequence):
     det_pre    (DetPre2.v):     lsuf 0  (J_at)         -> lsuf 10 (nondet_u8), C_at with c0 (offer done on both)
     det_params (DetParams2.v): lsuf 10 (C_at, c0)     -> lsuf 11 (deflate), C_at (maybe after deflateParams x2)
     det_call   (DetCall2.v):    lsuf 11 (C_at)         -> lsuf 13 (the checks), D_at (deflate x2)
     det_check  (DetCheck2.v):   lsuf 13 (D_at)         -> end of the body, T_at (the loop test's precondition)
   DetMain2.v assembles them (the loop, its test, return 0 after Z_STREAM_END). *)
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
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.ApiKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Export Zlib.proof.harness.api_deterministic.DetMem2.
Require Export Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.rj_deflate_params.RJPMain.
Require Zlib.contracts.api_deterministic.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module DC := Zlib.deflate.code.

(** ** Suffixes of main's body *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

(* main's body is Ssequence main_body (return 0); main_body's statements: the four nondet_u32 (0-3),
   gp_assume(deflate_params_ok(...)) (4), data_len (5), data (6), its NULL test (7), new_stream x2 (8, 9),
   deflateInit2 x2 (10, 11), the Z_MEM_ERROR test (12), gp_assert of both Z_OK (13), offered, read, flush (14-16),
   then msuf17 = the loop; return 0 *)
Definition main_body : statement := ltac:(let x := eval cbv beta iota zeta delta [f_main fn_body] in
  (match fn_body f_main with Ssequence b _ => b | _ => Sskip end) in exact x).
Ltac get_msuf k := let x := eval cbv beta iota zeta delta [suf main_body] in (suf k main_body) in exact x.
Definition msuf17 : statement := ltac:(get_msuf 17%nat).

(* the do-while loop is Sloop lbody ltest *)
Definition lbody : statement := ltac:(let x := eval cbv beta iota zeta delta [suf main_body] in
  (match suf 17 main_body with Ssequence (Sloop b _) _ => b | _ => Sskip end) in exact x).
Definition ltest : statement := ltac:(let x := eval cbv beta iota zeta delta [suf main_body] in
  (match suf 17 main_body with Ssequence (Sloop _ t) _ => t | _ => Sskip end) in exact x).

Lemma msuf17_eq : msuf17 = Ssequence (Sloop lbody ltest) (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* the loop body's statements: if (flush != Z_FINISH) {...} (0), take = clip(offered - read) (1), room (2), copy_of x2 (3, 4),
   malloc x2 (5, 6), the NULL test (7), offer x2 (8, 9), nondet_u8 and maybe deflateParams x2 (10),
   deflate x2 (11, 12), the three gp_asserts (13-15), read (16), free x4 (17-20) *)
Ltac get_lsuf k := let x := eval cbv beta iota zeta delta [suf lbody] in (suf k lbody) in exact x.
Definition lsuf10 : statement := ltac:(get_lsuf 10%nat).
Definition lsuf11 : statement := ltac:(get_lsuf 11%nat).
Definition lsuf13 : statement := ltac:(get_lsuf 13%nat).

(** ** Type context and postcondition of main's body *)
Definition Delta_m : tycontext :=
  func_tycontext f_main (QPvarspecs Zlib.contracts.api_deterministic.whole_prog) Gmain nil.

Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** The memory of a stream *)

(* A live stream at main's local [p]: the state (dstream_sp, the deflate_state at [sp]), the caller's fields,
   the padding of the Ews half of the local, and the other half [BoundKit.Ecomp] (main keeps it until return). *)
Definition strm_at (p : val) (s : dstate) (sp : val) (nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) : mpred :=
  dstream_sp 2 (Some s) p nullval sp gv * api_fields p nin ain tin nout aout tout msgv adler *
  BoundKit.strm_pad p * data_at_ BoundKit.Ecomp t_strm p.

(* between iterations: next_in, avail_in, next_out, avail_out hold the last call's values (dangling) *)
Definition shead (p : val) (s : dstate) (sp : val) (tin tout : Z) (msgv : val) (adler : Z) (gv : globals)
    : mpred :=
  EX nin : val, EX ain : Z, EX nout : val, EX aout : Z, strm_at p s sp nin ain tin nout aout tout msgv adler gv.

(* an object of malloc: the input copies hold bytes (BoundKit.obj), the output spaces [room] bytes with
   contents [l] *)
Definition out_at (q : val) (room : Z) (l : list val) : mpred :=
  malloc_token Ews (tarray tuchar room) q * data_at Ews (tarray tuchar room) l q.

(* the output space after [o] bytes were written into it *)
Definition out_vals (room : Z) (o : list Z) : list val := map vi o ++ Zrepeat Vundef (room - Zlength o).


(* new_stream's postcondition as deflateInit2__spec_v9's precondition pieces, the three fields the spec does not
   mention (avail_in, next_out, avail_out) and the padding *)
Lemma det_new_stream_split (p : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p
  |-- field_at Ews t_strm (DOT DC._next_in) nullval p * reset_fields p Vundef Vundef Vundef Vundef *
      (field_at Ews t_strm (DOT DC._avail_in) (vi 0) p * field_at Ews t_strm (DOT DC._next_out) nullval p *
       field_at Ews t_strm (DOT DC._avail_out) (vi 0) p) *
      field_at Ews t_strm (DOT DC._zalloc) nullval p * field_at Ews t_strm (DOT DC._zfree) nullval p *
      field_at Ews t_strm (DOT DC._opaque) nullval p * field_at Ews t_strm (DOT DC._data_type) Vundef p *
      field_at Ews t_strm (DOT DC._state) Vundef p * field_at_ Ews t_strm (DOT DC._reserved) p *
      BoundKit.strm_pad p.
Proof.
  exact (Zlib.proof.harness.rj_deflate_params.RJPMain.rjp_new_stream_split p).
Qed.

Definition det_dt (s : dstate) : val := vi (tr_data_type (fst (d_trm s))).

Definition strm_own_live (p sp : val) (gv : globals) (s : dstate) : mpred :=
  strm_own p sp (gv DC._zcalloc) (gv DC._zcfree) nullval (det_dt s).

(* The z_stream fields of a live stream out of dstream_sp, the rest kept as a wand (offer writes the whole
   struct; the six fields come back unchanged). *)
Lemma det_dstream_open (s : dstate) (p ghp sp : val) (gv : globals) :
  dstream_sp 2 (Some s) p ghp sp gv |--
  strm_own_live p sp gv s * (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p ghp sp gv).
Proof.
  unfold dstream_sp at 1. Intros pp. rewrite ApiKit.dstate_at'_2.
  unfold dstate_at, trees_at, dtype_at. Intros.
  unfold strm_own_live, strm_own, det_dt. subst.
  cancel.
  rewrite <- wand_sepcon_adjoint.
  unfold dstream_sp. Exists pp. rewrite ApiKit.dstate_at'_2.
  unfold dstate_at, trees_at, dtype_at. entailer!.
Qed.

Lemma det_dstream_close (s : dstate) (p ghp sp : val) (gv : globals) :
  strm_own_live p sp gv s * (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p ghp sp gv)
  |-- dstream_sp 2 (Some s) p ghp sp gv.
Proof. apply modus_ponens_wand. Qed.



(* the stream's fields, whatever their values, back to the local's Ews half *)
Lemma det_fields_back (p nin tin tout msgv adler ai no ao sp za zf op dt : val) :
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  strm_own p sp za zf op dt * BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p.
Proof.
  sep_apply (det_offer_pre p nin ai tin no ao tout msgv adler sp za zf op dt).
  rewrite det_strm_cs. apply data_at_data_at_.
Qed.

(* deflateInit2__spec_v9's postcondition, whatever the outcome, back to the local's Ews half (the state and its
   allocations are dropped) *)
Lemma det_init_back (os : option dstate) (code : Z) (p : val) (gv : globals)
    (nin tin tout msgv adler ai no ao : val) :
  match os with
  | Some _ => dstream 2 os p nullval gv
  | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
            !! (code = Z_VERSION_ERROR -> st = Vundef) &&
            (zfuncs gv * field_at_ Ews t_strm (DOT DC._reserved) p *
             field_at Ews t_strm (DOT DC._state) st p * field_at Ews t_strm (DOT DC._zalloc) za p *
             field_at Ews t_strm (DOT DC._zfree) zf p * field_at Ews t_strm (DOT DC._opaque) op' p *
             field_at Ews t_strm (DOT DC._data_type) dt' p)
  end *
  field_at Ews t_strm (DOT DC._next_in) nin p * reset_fields p tin tout msgv adler *
  (field_at Ews t_strm (DOT DC._avail_in) ai p * field_at Ews t_strm (DOT DC._next_out) no p *
   field_at Ews t_strm (DOT DC._avail_out) ao p) *
  BoundKit.strm_pad p
  |-- data_at_ Ews t_strm p * TT.
Proof.
  destruct os as [s|].
  - rewrite dstream_sp_eq. Intros sp. sep_apply (det_dstream_open s p nullval sp gv).
    unfold strm_own_live.
    sep_apply (det_fields_back p nin tin tout msgv adler ai no ao sp (gv DC._zcalloc) (gv DC._zcfree) nullval
                 (det_dt s)). cancel.
  - Intros st za zf op' dt'.
    eapply derives_trans;
      [| apply sepcon_derives; [apply (det_fields_back p nin tin tout msgv adler ai no ao st za zf op' dt') |
                                apply TT_right]].
    unfold strm_own. cancel. apply derives_refl.
Qed.

(* a live stream back to the local's memory (both halves) *)
Lemma det_strm_back (p : val) (s : dstate) (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) :
  strm_at p s sp nin ain tin nout aout tout msgv adler gv |-- data_at_ Tsh t_strm p * TT.
Proof.
  unfold strm_at. sep_apply (det_dstream_open s p nullval sp gv). unfold strm_own_live, api_fields. Intros.
  rewrite (BoundKit.data_at__Tsh_split t_strm p).
  eapply derives_trans;
    [| apply sepcon_derives;
       [apply sepcon_derives;
          [apply (det_fields_back p nin (vl tin) (vl tout) msgv (vl adler) (vi ain) nout (vi aout) sp
                    (gv DC._zcalloc) (gv DC._zcfree) nullval (det_dt s)) | apply derives_refl] | apply TT_right]].
  unfold reset_fields. cancel. apply derives_refl.
Qed.

Lemma det_shead_back (p : val) (s : dstate) (sp : val) (tin tout : Z) (msgv : val) (adler : Z) (gv : globals) :
  shead p s sp tin tout msgv adler gv |-- data_at_ Tsh t_strm p * TT.
Proof. unfold shead. Intros nin ain nout aout. apply det_strm_back. Qed.

(** ** The assertions *)

(* the loop head: the common state [s], the data [read] bytes of which were consumed, [offered] of which were
   offered, the last flush; total_in = read on both streams, the same total_out, adler and model message.  Once
   Z_FINISH was given, the rest of the data fits in one call (so every later piece is the whole rest). *)
Record lstate := mkLS {
  ls_s : dstate; ls_fin : option (list Z); ls_offered : Z; ls_read : Z; ls_flush : Z;
  ls_tout : Z; ls_adler : Z; ls_msg : option Z; ls_msgv1 : val; ls_msgv2 : val }.

(* one iteration's choices: the new [offered] and flush, the output space, the four objects *)
Record citer := mkCI {
  ci_offered : Z; ci_flush : Z; ci_room : Z; ci_in1 : val; ci_in2 : val; ci_out1 : val; ci_out2 : val }.

(* the stream before deflate: the state, next_in at [nin] in the input copy, [out] written into the output
   space (deflateParams may consume input and write output) *)
Record cstate := mkCS {
  cs_s : dstate; cs_fin : option (list Z); cs_nin : Z; cs_out : list Z;
  cs_tout : Z; cs_adler : Z; cs_msg : option Z; cs_msgv1 : val; cs_msgv2 : val }.

(* deflate's result on both streams: the model's [c_deflate s z flush = Some (dr_s, dr_z, dr_code)] *)
Record dres := mkDR { dr_s : dstate; dr_z : strm; dr_code : Z; dr_msgv1 : val; dr_msgv2 : val }.

Section Kit.
Context (J : det_inv) (n : Z) (data : list Z) (datap : val).
Context (v1 v2 sp1 sp2 : val) (gv : globals).

(* what main drew before the loop *)
Definition setup_ok : Prop :=
  det_facts2 J /\ 0 <= n <= 9223372036854775807 /\ Zlength data = n /\ bytes data /\ isptr datap.

Definition J_ok (ls : lstate) : Prop :=
  setup_ok /\ J (ls_fin ls) (ls_s ls) (ls_read ls) (ls_adler ls) /\ d_gzhead (ls_s ls) = None /\
  0 <= ls_read ls <= ls_offered ls /\ ls_offered ls <= n /\ 0 <= ls_flush ls <= 5 /\
  match ls_fin ls with
  | None => ls_flush ls <> 4
  | Some R => ls_flush ls = 4 /\ ls_offered ls = n /\ R = sublist (ls_read ls) n data /\
              n - ls_read ls <= 4294967295
  end /\
  u64r (ls_tout ls) /\ msg_ok (ls_msg ls) (ls_msgv1 ls) /\ msg_ok (ls_msg ls) (ls_msgv2 ls).

Definition J_loc (ls : lstate) : list localdef :=
  [temp _data datap; temp _data_len (vl n); temp _offered (vl (ls_offered ls)); temp _read (vl (ls_read ls));
   temp _flush (vi (ls_flush ls)); lvar _first t_strm v1; lvar _second t_strm v2; gvars gv].

Definition J_sep (ls : lstate) : list mpred :=
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   shead v1 (ls_s ls) sp1 (ls_read ls) (ls_tout ls) (ls_msgv1 ls) (ls_adler ls) gv;
   shead v2 (ls_s ls) sp2 (ls_read ls) (ls_tout ls) (ls_msgv2 ls) (ls_adler ls) gv; TT].

Definition J_at (ls : lstate) : environ -> mpred :=
  PROPx [J_ok ls] (LOCALx (J_loc ls) (SEPx (J_sep ls))).

Definition J_inv : environ -> mpred := EX ls : lstate, J_at ls.

(* after the body (before the loop test): code_first; the invariant again unless deflate returned
   Z_STREAM_END *)
Definition T_at (code : Z) (ls : lstate) : environ -> mpred :=
  PROPx [setup_ok; code <> Z_STREAM_END -> J_ok ls]
    (LOCALx (temp _code_first (vi code) :: J_loc ls) (SEPx (J_sep ls))).

Definition T_inv : environ -> mpred := EX code : Z, EX ls : lstate, T_at code ls.

(* after the loop (break: Z_STREAM_END) *)
Definition E_inv : environ -> mpred :=
  EX ls : lstate, PROPx [] (LOCALx [lvar _first t_strm v1; lvar _second t_strm v2; gvars gv] (SEPx (J_sep ls))).

(* the loop body's postcondition *)
Definition Rbody : ret_assert := loop1_ret_assert T_inv (overridePost E_inv POST_m).

(* one iteration: the piece offered is clip(offered - read) bytes of the data from [read] on *)
Definition ci_take (ls : lstate) (ci : citer) : Z := Z.min (ci_offered ci - ls_read ls) 4294967295.
Definition ci_inb (ls : lstate) (ci : citer) : list Z := sublist (ls_read ls) (ls_read ls + ci_take ls ci) data.

Definition ci_ok (ls : lstate) (ci : citer) : Prop :=
  ls_read ls <= ci_offered ci <= n /\ 0 <= ci_flush ci <= 5 /\
  (ci_flush ci = 4 -> ci_offered ci = n /\ n - ls_read ls <= 4294967295) /\
  (ls_fin ls <> None -> ci_flush ci = 4) /\ 0 <= ci_room ci <= 4294967295 /\
  isptr (ci_in1 ci) /\ isptr (ci_in2 ci) /\ isptr (ci_out1 ci) /\ isptr (ci_out2 ci).

Definition B_loc (ls : lstate) (ci : citer) : list localdef :=
  [temp _data datap; temp _data_len (vl n); temp _offered (vl (ci_offered ci)); temp _read (vl (ls_read ls));
   temp _flush (vi (ci_flush ci)); temp _take (vl (ci_take ls ci)); temp _room (vl (ci_room ci));
   temp _in_first (ci_in1 ci); temp _in_second (ci_in2 ci);
   temp _out_first (ci_out1 ci); temp _out_second (ci_out2 ci);
   lvar _first t_strm v1; lvar _second t_strm v2; gvars gv].

Definition cs_ok (ls : lstate) (ci : citer) (c : cstate) : Prop :=
  J (cs_fin c) (cs_s c) (ls_read ls + cs_nin c) (cs_adler c) /\ d_gzhead (cs_s c) = None /\
  0 <= cs_nin c <= ci_take ls ci /\ Zlength (cs_out c) <= ci_room ci /\ bytes (cs_out c) /\
  (forall R, cs_fin c = Some R -> ci_flush ci = 4 /\ R = sublist (cs_nin c) (ci_take ls ci) (ci_inb ls ci)) /\
  u64r (cs_tout c) /\ msg_ok (cs_msg c) (cs_msgv1 c) /\ msg_ok (cs_msg c) (cs_msgv2 c).

(* the configuration right after the two offers *)
Definition c0 (ls : lstate) : cstate :=
  mkCS (ls_s ls) (ls_fin ls) 0 [] (ls_tout ls) (ls_adler ls) (ls_msg ls) (ls_msgv1 ls) (ls_msgv2 ls).

Definition C_sep (ls : lstate) (ci : citer) (c : cstate) : list mpred :=
  let take := ci_take ls ci in let room := ci_room ci in let o := cs_out c in
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   BoundKit.obj (ci_in1 ci) (ci_inb ls ci); BoundKit.obj (ci_in2 ci) (ci_inb ls ci);
   out_at (ci_out1 ci) room (out_vals room o); out_at (ci_out2 ci) room (out_vals room o);
   strm_at v1 (cs_s c) sp1 (offset_val (cs_nin c) (ci_in1 ci)) (take - cs_nin c) (ls_read ls + cs_nin c)
     (offset_val (Zlength o) (ci_out1 ci)) (room - Zlength o) (cs_tout c) (cs_msgv1 c) (cs_adler c) gv;
   strm_at v2 (cs_s c) sp2 (offset_val (cs_nin c) (ci_in2 ci)) (take - cs_nin c) (ls_read ls + cs_nin c)
     (offset_val (Zlength o) (ci_out2 ci)) (room - Zlength o) (cs_tout c) (cs_msgv2 c) (cs_adler c) gv; TT].

Definition C_at (ls : lstate) (ci : citer) (c : cstate) : environ -> mpred :=
  PROPx [J_ok ls; ci_ok ls ci; cs_ok ls ci c] (LOCALx (B_loc ls ci) (SEPx (C_sep ls ci c))).

(* the model call of deflate *)
Definition d_call (ls : lstate) (ci : citer) (c : cstate) : strm :=
  zcall (ci_inb ls ci) (cs_nin c) (ci_take ls ci - cs_nin c) (ls_read ls + cs_nin c)
    (ci_room ci - Zlength (cs_out c)) (cs_tout c) (cs_adler c) (cs_msg c).

Definition dr_ok (ls : lstate) (ci : citer) (c : cstate) (d : dres) : Prop :=
  c_deflate (cs_s c) (d_call ls ci c) (ci_flush ci) = Some (dr_s d, dr_z d, dr_code d) /\
  call_okw (ci_inb ls ci) (cs_nin c) (ci_room ci - Zlength (cs_out c)) (ls_read ls + cs_nin c) (cs_tout c)
    (dr_z d) /\
  (dr_code d <> Z_STREAM_END ->
   J (if ci_flush ci =? Z_FINISH then Some (sublist (z_next_in (dr_z d)) (ci_take ls ci) (ci_inb ls ci))
      else None)
     (dr_s d) (z_total_in (dr_z d)) (z_adler (dr_z d))) /\
  msg_ok (z_msg (dr_z d)) (dr_msgv1 d) /\ msg_ok (z_msg (dr_z d)) (dr_msgv2 d).

Definition D_sep (ls : lstate) (ci : citer) (c : cstate) (d : dres) : list mpred :=
  let room := ci_room ci in let o := cs_out c ++ z_out (dr_z d) in let z := dr_z d in
  [mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
   BoundKit.obj (ci_in1 ci) (ci_inb ls ci); BoundKit.obj (ci_in2 ci) (ci_inb ls ci);
   out_at (ci_out1 ci) room (out_vals room o); out_at (ci_out2 ci) room (out_vals room o);
   strm_at v1 (dr_s d) sp1 (offset_val (z_next_in z) (ci_in1 ci)) (z_avail_in z) (z_total_in z)
     (offset_val (Zlength o) (ci_out1 ci)) (z_avail_out z) (z_total_out z) (dr_msgv1 d) (z_adler z) gv;
   strm_at v2 (dr_s d) sp2 (offset_val (z_next_in z) (ci_in2 ci)) (z_avail_in z) (z_total_in z)
     (offset_val (Zlength o) (ci_out2 ci)) (z_avail_out z) (z_total_out z) (dr_msgv2 d) (z_adler z) gv; TT].

Definition D_at (ls : lstate) (ci : citer) (c : cstate) (d : dres) : environ -> mpred :=
  PROPx [J_ok ls; ci_ok ls ci; cs_ok ls ci c; dr_ok ls ci c d]
    (LOCALx (temp _code_first (vi (dr_code d)) :: temp _code_second (vi (dr_code d)) :: B_loc ls ci)
       (SEPx (D_sep ls ci c d))).

End Kit.

(** ** main's entry (after start_function) *)
Definition PRE0 (v1 v2 : val) (gv : globals) : environ -> mpred :=
  PROP () LOCAL (lvar _first t_strm v1; lvar _second t_strm v2; gvars gv)
  SEP (data_at_ Tsh t_strm v1; data_at_ Tsh t_strm v2; mem_mgr gv; deflate_globals gv; version_at gv vlit).

(** ** The parts' statements *)
Definition det_prefix_stmt : Prop := forall {Espec : OracleKind} v1 v2 gv,
  det_theory2_stmt ->
  (forall J n data datap sp1 sp2 ls,
     semax Delta_m (J_at J n data datap v1 v2 sp1 sp2 gv ls) msuf17 POST_m) ->
  semax Delta_m (PRE0 v1 v2 gv) main_body POST_m.

Definition det_pre_stmt : Prop := forall {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls,
  (forall ci, semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci (c0 ls)) lsuf10
                (Rbody J n data datap v1 v2 sp1 sp2 gv)) ->
  semax Delta_m (J_at J n data datap v1 v2 sp1 sp2 gv ls) lbody (Rbody J n data datap v1 v2 sp1 sp2 gv).

Definition det_params_stmt : Prop := forall {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci,
  (forall c, semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci c) lsuf11
               (Rbody J n data datap v1 v2 sp1 sp2 gv)) ->
  semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci (c0 ls)) lsuf10
    (Rbody J n data datap v1 v2 sp1 sp2 gv).

Definition det_call_stmt : Prop := forall {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci c,
  (forall d, semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf13
               (Rbody J n data datap v1 v2 sp1 sp2 gv)) ->
  semax Delta_m (C_at J n data datap v1 v2 sp1 sp2 gv ls ci c) lsuf11 (Rbody J n data datap v1 v2 sp1 sp2 gv).

Definition det_check_stmt : Prop := forall {Espec : OracleKind} J n data datap v1 v2 sp1 sp2 gv ls ci c d,
  semax Delta_m (D_at J n data datap v1 v2 sp1 sp2 gv ls ci c d) lsuf13 (Rbody J n data datap v1 v2 sp1 sp2 gv).

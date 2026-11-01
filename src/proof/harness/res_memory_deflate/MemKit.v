(* Law res_memory_deflate: the kit of main's body proof (Main.v): main's type context and postcondition, its body
   cut at the loop, the loop invariant, and the statements of the two parts.

   main of harness/res_memory_deflate.c draws deflateInit2's parameters and the data, makes the stream count
   through the harness's allocator (counted_stream), calls deflateInit2_ and then loops: each iteration offers
   the piece take = upto(clip(data_len - read)) at data + read and a fresh output space of nondet_u32() bytes,
   calls deflate() with any flush, checks count.peak and frees the output space.  The proof:
     prefix_stmt: main's body (PRE0) up to the loop (main_body; its suffix msuf17 is the loop and return 0),
                  continued at the loop invariant J_at;
     body_stmt:   one iteration (lbody) from J_at, back to the invariant J_inv (or main's return when malloc
                  fails);
   Main.v assembles them (the loop, its test nondet_u8() != 0, return 0).

   The invariant [J_at K ... L] at the loop head: the deflate state [ms_s L] meets the invariant [K] of
   deflate/AnyCalls.v with total_in = read (the bytes of the data consumed so far) and strm->adler; the stream's
   next_in, avail_in, next_out, avail_out hold the last call's (dangling) values; the allocator's events [tr]
   (deflateInit2_'s five allocations: deflate() allocates nothing) and their peak within the harness's bound. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Import Zlib.proof.harness.res_alloc_deflate.Specs.
Require Import Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_alloc_deflate.MainKit.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
Require Import Zlib.proof.harness.res_memory_deflate.PeakExact.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.

Definition vlit : ident := ___stringlit_res_memory_deflate_1.

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which runs away on main's LOCAL
   list (the identifiers _data and _data_len); the same list built syntactically, comparing the identifiers by
   vm_compute.  Each proof file installs it with
     Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt. *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
Ltac mem_simplify_rlt :=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(** ** Suffixes of main's body *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

(* main's body is Ssequence main_body (return 0); main_body's statements: the four nondet_u32 (0-3),
   gp_assume(deflate_params_ok(...)) (4), data_len (5), data (6), its NULL test (7), counted_stream (8),
   deflateInit2 (9), the check of its code (10), the Z_OK test (11), w and its three adjustments (12-15),
   read = 0 (16), then msuf17 = the loop; return 0 *)
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
Proof.
  reflexivity.
Qed.

(** ** Type context and postcondition of main's body *)
Definition Delta_m : tycontext :=
  func_tycontext f_main (QPvarspecs Zlib.contracts.res_memory_deflate.whole_prog) Gmain_mem nil.

Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (@stackframe_of CSa f_main).

(* main's entry (after start_function) *)
Definition PRE0 (cp p : val) (gv : globals) : environ -> mpred :=
  PROP () LOCAL (lvar _count__1 (Tstruct _count noattr) cp; lvar _strm (Tstruct _z_stream_s noattr) p; gvars gv)
  SEP (@data_at_ CSa Tsh (Tstruct _count noattr) cp; @data_at_ CSa Tsh (Tstruct _z_stream_s noattr) p;
       mem_mgr gv; Ra vlit gv).

(** ** The loop invariant *)

(* what changes from one iteration to the next: the deflate state, read (= total_in), total_out, strm->adler,
   the model's message and strm->msg *)
Record mstate := mkMS {
  ms_s : dstate; ms_read : Z; ms_tout : Z; ms_adler : Z; ms_msg : option Z; ms_msgv : val }.

Section Kit.
Context (K : dstate -> Z -> Z -> Prop).
(* main's two locals (struct count at cp, the z_stream at p), the data (dp, bytes bs), mem_level, the harness's
   w, the allocator's events and the deflate_state's address *)
Context (gv : globals) (cp p dp : val) (bs : list Z) (mem W : Z) (tr : list zev) (spp : val).

(* the counting allocator main hands to deflateInit2_ *)
Definition mc : KC := (cp, gv HC._counted_alloc, gv HC._counted_free).

(* what main drew and computed before the loop *)
Definition setup_ok : Prop :=
  Zlength bs <= 9223372036854775807 /\ bytes bs /\ isptr dp /\
  9 <= W <= 15 /\ 1 <= mem <= 9 /\ 0 <= snd (cnt tr) <= 2 ^ (W + 2) + 2 ^ (mem + 9) + 5968.

Definition J_ok (L : mstate) : Prop :=
  setup_ok /\ K (ms_s L) (ms_read L) (ms_adler L) /\ 0 <= ms_read L <= Zlength bs /\ u64r (ms_tout L) /\
  msg_ok (ms_msg L) (ms_msgv L).

Definition J_loc (L : mstate) : list localdef :=
  [temp _data dp; temp _data_len (Vlong (Int64.repr (Zlength bs))); temp _read (Vlong (Int64.repr (ms_read L)));
   temp _w (Vint (Int.repr W)); temp _mem_level (Vint (Int.repr mem));
   lvar _count__1 (Tstruct _count noattr) cp; lvar _strm (Tstruct _z_stream_s noattr) p; gvars gv].

(* the live stream between two calls: the state, the application's fields (next_in, avail_in, next_out,
   avail_out as the last call left them), the padding of the Ews half of the local and its other half *)
Definition strm_head (s : dstate) (tin tout : Z) (msgv : val) (adler : Z) : mpred :=
  EX nin : val, EX ain : Z, EX nout : val, EX aout : Z,
    @dstream_sp_za (kc mc) 2 (Some s) p nullval spp gv * api_fields p nin ain tin nout aout tout msgv adler *
    strm_pad p * @data_at_ Zlib.units.Compress.CS Ecomp t_zs p.

(* struct count with the counters and the flag of the events, as main reads it *)
Definition count_at : mpred :=
  @data_at CSa Tsh (Tstruct _count noattr)
    (Vlong (Int64.repr (fst (cnt tr))), (Vlong (Int64.repr (snd (cnt tr))), Vint (Int.repr (cnt_failed tr)))) cp.

Definition J_sep (L : mstate) : list mpred :=
  [mem_mgr gv; deflate_globals gv; @data_at DCS.CS Ews (tarray tuchar (Zlength bs)) (map vi bs) dp;
   strm_head (ms_s L) (ms_read L) (ms_tout L) (ms_msgv L) (ms_adler L); count_at; TT].

Definition J_at (L : mstate) : environ -> mpred :=
  PROPx [J_ok L] (LOCALx (J_loc L) (SEPx (J_sep L))).

Definition J_inv : environ -> mpred := EX L : mstate, J_at L.

(* the loop body's postcondition: the invariant again (no break in the body; return when malloc fails) *)
Definition Rbody : ret_assert := loop1_ret_assert J_inv (overridePost J_inv POST_m).

(* after set_buffer (the cut lsuf5 of the body): the piece of [take] bytes at data + read and the output space
   of [room] bytes at [out] (malloc's object, any contents) offered to the stream *)
Record citer := mkCI { ci_take : Z; ci_room : Z; ci_out : val }.

Definition C_ok (L : mstate) (ci : citer) : Prop :=
  J_ok L /\ 0 <= ci_take ci <= Z.min (Zlength bs - ms_read L) 4294967295 /\ 0 <= ci_room ci <= 4294967295 /\
  isptr (ci_out ci).

Definition C_loc (L : mstate) (ci : citer) : list localdef :=
  temp _take (Vlong (Int64.repr (ci_take ci))) :: temp _room (Vlong (Int64.repr (ci_room ci))) ::
  temp _out (ci_out ci) :: J_loc L.

(* the live stream with the piece and the output space offered (deflate()'s precondition, the members) *)
Definition strm_offered (L : mstate) (ci : citer) : mpred :=
  @dstream_sp_za (kc mc) 2 (Some (ms_s L)) p nullval spp gv *
  api_fields p (offset_val (ms_read L) dp) (ci_take ci) (ms_read L) (ci_out ci) (ci_room ci) (ms_tout L)
    (ms_msgv L) (ms_adler L) *
  strm_pad p * @data_at_ Zlib.units.Compress.CS Ecomp t_zs p.

(* the output space as malloc gave it *)
Definition out_obj (ci : citer) : mpred :=
  @malloc_token CSa Ews (tarray tuchar (ci_room ci)) (ci_out ci) *
  @data_at_ CSa Ews (tarray tuchar (ci_room ci)) (ci_out ci).

Definition C_sep (L : mstate) (ci : citer) : list mpred :=
  [mem_mgr gv; deflate_globals gv; @data_at DCS.CS Ews (tarray tuchar (Zlength bs)) (map vi bs) dp;
   strm_offered L ci; count_at; out_obj ci; TT].

Definition C_at (L : mstate) (ci : citer) : environ -> mpred :=
  PROPx [C_ok L ci] (LOCALx (C_loc L ci) (SEPx (C_sep L ci))).

End Kit.

(* the loop body's statements: take = upto(clip(data_len - read)) (0), room (1), out = malloc(room) (2), its
   NULL test (3), set_buffer (4), deflate (5), the check of count.peak (6), read += take - avail_in; free(out)
   (lsuf 7) *)
Ltac get_lsuf k := let x := eval cbv beta iota zeta delta [suf lbody] in (suf k lbody) in exact x.
Definition lsuf5 : statement := ltac:(get_lsuf 5%nat).

(** ** The parts' statements *)
Definition prefix_stmt : Prop := forall {Espec : OracleKind} K cp p gv,
  any_calls K ->
  (forall dp bs mem W tr spp L,
     @semax CSa Espec Delta_m (J_at K gv cp p dp bs mem W tr spp L) msuf17 POST_m) ->
  @semax CSa Espec Delta_m (PRE0 cp p gv) main_body POST_m.

(* one iteration up to set_buffer (draws, malloc and its NULL test, set_buffer), continued at C_at *)
Definition body_pre_stmt : Prop := forall {Espec : OracleKind} K gv cp p dp bs mem W tr spp L,
  any_calls K -> (forall ZA : zallocator, @ob_dstream_to_end_za ZA) ->
  (forall ci, @semax CSa Espec Delta_m (C_at K gv cp p dp bs mem W tr spp L ci) lsuf5
                (Rbody K gv cp p dp bs mem W tr spp)) ->
  @semax CSa Espec Delta_m (J_at K gv cp p dp bs mem W tr spp L) lbody (Rbody K gv cp p dp bs mem W tr spp).

(* the rest of the iteration: deflate(), the check of count.peak, read, free(out), back to the invariant *)
Definition body_call_stmt : Prop := forall {Espec : OracleKind} K gv cp p dp bs mem W tr spp L ci,
  any_calls K ->
  @semax CSa Espec Delta_m (C_at K gv cp p dp bs mem W tr spp L ci) lsuf5 (Rbody K gv cp p dp bs mem W tr spp).

Definition body_stmt : Prop := forall {Espec : OracleKind} K gv cp p dp bs mem W tr spp L,
  any_calls K -> (forall ZA : zallocator, @ob_dstream_to_end_za ZA) ->
  @semax CSa Espec Delta_m (J_at K gv cp p dp bs mem W tr spp L) lbody (Rbody K gv cp p dp bs mem W tr spp).

Lemma body_of_parts : body_pre_stmt -> body_call_stmt -> body_stmt.
Proof.
  intros Hpre Hcall Espec K gv cp p dp bs mem W tr spp L AC TE.
  apply (Hpre Espec K gv cp p dp bs mem W tr spp L AC TE). intros ci. apply (Hcall Espec K gv cp p dp bs mem W tr spp L ci AC).
Qed.

(** ** Memory lemmas the parts share *)

(* A live stream (from deflate()'s postcondition) lends set_buffer the members it holds (state, zalloc, zfree,
   opaque, data_type, reserved) and gets them back unchanged: as StrmKit.dstream_za_open, from dstream_sp_za. *)
Lemma dstream_sp_open {ZA : zallocator} (s : dstate) (sp ghp spp' : val) (gv : globals) :
  dstream_sp_za 2 (Some s) sp ghp spp' gv |--
  strm_live sp spp' (vi (tr_data_type (d_tr s))) *
    (strm_live sp spp' (vi (tr_data_type (d_tr s))) -* dstream_sp_za 2 (Some s) sp ghp spp' gv).
Proof.
  unfold dstream_sp_za at 1. Intros pp.
  apply (wand_lend _ _ _ (!! (p_strm pp = sp /\ p_gzhead pp = ghp /\ p_s pp = spp') && dlive_rest s pp gv)).
  - unfold dstate_at', dstate_at, trees_at, dtype_at, strm_live, dlive_rest. simpl. Intros.
    rewrite !prop_true_andp by auto. subst. cancel.
  - unfold dstream_sp_za, strm_live, dlive_rest. Intros. Exists pp.
    unfold dstate_at', dstate_at, trees_at, dtype_at. simpl.
    rewrite !prop_true_andp by auto. subst. cancel.
Qed.

(* main's return: the stream (live, whatever its fields) and struct count back to the uninitialised locals *)
Lemma strm_head_back (K' : dstate -> Z -> Z -> Prop) (gv : globals) (cp p spp : val) (s : dstate)
    (tin tout : Z) (msgv : val) (adler : Z) :
  (forall ZA : zallocator, @ob_dstream_to_end_za ZA) ->
  strm_head gv cp p spp s tin tout msgv adler |-- @data_at_ CSa Tsh (Tstruct _z_stream_s noattr) p * TT.
Proof.
  intros TE. unfold strm_head. Intros nin ain nout aout.
  sep_apply (@dstream_sp_back (kc (mc gv cp)) (Some s) p nullval spp gv nin ain tin nout aout tout msgv adler
               (TE (kc (mc gv cp)))).
  sep_apply (strm_back p). cancel.
Qed.

Lemma count_at_back (gv : globals) (cp : val) (tr : list zev) :
  count_at cp tr |-- @data_at_ CSa Tsh (Tstruct _count noattr) cp.
Proof. unfold count_at. apply data_at_data_at_. Qed.

Lemma lsuf5_shape : exists a b, lsuf5 = Ssequence (Ssequence a b) (suf 6 lbody).
Proof.
  do 2 eexists. reflexivity.
Qed.

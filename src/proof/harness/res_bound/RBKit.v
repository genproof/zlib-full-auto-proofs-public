(* Law res_bound, main (harness/res_bound.c): the kit of main's body proof, under DCS.CS (deflate.c + trees.c's
   composites, which include z_stream_s and gz_header_s; the body moves to the law's compspecs by entry_shared).

   main's body is [Ssequence b0 (return 0)], b0 a sequence of 43 statements; [msuf k] is statement k of b0 and
   everything after it (then the return).  The statements: the four nondet_u32 parameters (0-3),
   gp_assume(deflate_params_ok(...)) (4), data_len (5), data (6), choice (7), dict_len, extra_len, name_len,
   comment_len (8-11), dict, extra (12, 13), name, comment (14, 15), the NULL test (16), the eight stores into head
   (17-24), new_stream (25), code = deflateInit2 (26), its Z_MEM_ERROR test (27), gp_assert(code == Z_OK) (28), the
   deflateSetHeader branch (29), the deflateSetDictionary branch (30), deflateBound (31), gp_assume (32), malloc
   (33), its NULL test (34), set_buffer (35), total_in = strm.total_in (36), code = deflate (37), gp_assert(code ==
   Z_STREAM_END) (38), wrote (39), the asserts on wrote, avail_in, next_in (40) and on total_in, total_out (41),
   return 0 (42).

   The part lemmas (RBPre, RBStores, RBInit, RBHead, RBDict, RBBnd, RBRun) are in continuation-passing
   style: each proves the suffix at its first cut from the hypothesis that the suffix at its next cut is proved
   from the assertion there:
     part_pre    msuf 0  (PRE0)  -> msuf 17 (A1: everything drawn and allocated, none NULL)
     part_stores msuf 17 (A1)    -> msuf 25 (A2: head's eight fields stored)
     part_init   msuf 25 (A2)    -> msuf 29 (A3: deflateInit2 returned Z_OK)
     part_head   msuf 29 (A3)    -> msuf 30 (A4: the header set when choice & 1 and windowBits > 15)
     part_dict   msuf 30 (A4)    -> msuf 31 (A5: the dictionary set when choice & 1 and windowBits <= 15)
     part_bound  msuf 31 (A5)    -> msuf 35 (A6: bound = deflateBound, at most UINT_MAX, compressed allocated)
     part_run    msuf 35 (A6)    -> the end
   RBMain.v assembles them (body_main). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.deflate.LTWBOnce.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString.
Require Zlib.contracts.res_bound.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** main's callees and the resources of the globals *)
Definition Gmain : funspecs :=
  [Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec;
   upto_spec; any_bytes_spec; any_string_spec; offer_spec; new_stream_spec;
   deflateInit2__spec_v9; deflateSetHeader_spec; deflateSetDictionary_spec; deflateBound_spec; deflate_spec;
   (_quickproof_malloc, @malloc_spec' DCS.CS); nondet_u32_spec; nondet_u8_spec; gp_assert_spec; gp_assume_spec].

Definition vlit : ident := ___stringlit_res_bound_1.

(* the globals main gets (RBGlobals.globals_rb) *)
Definition R (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs Zlib.contracts.res_bound.whole_prog) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(** ** Suffixes of main's body *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

Ltac get_msuf k :=
  let x := eval cbv beta iota zeta delta [suf f_main fn_body] in
    (match fn_body f_main with Ssequence b r => Ssequence (suf k b) r | s => s end) in exact x.

Definition msuf0 : statement := ltac:(get_msuf 0%nat).
Definition msuf17 : statement := ltac:(get_msuf 17%nat).
Definition msuf25 : statement := ltac:(get_msuf 25%nat).
Definition msuf29 : statement := ltac:(get_msuf 29%nat).
Definition msuf30 : statement := ltac:(get_msuf 30%nat).
Definition msuf31 : statement := ltac:(get_msuf 31%nat).
Definition msuf35 : statement := ltac:(get_msuf 35%nat).

Lemma msuf0_body : msuf0 = fn_body f_main.
Proof. reflexivity. Qed.

(** ** The values main draws, and its objects *)
Record rsetup := mkRS {
  r_level : Z; r_wbits : Z; r_mem : Z; r_strategy : Z;
  r_n : Z; r_choice : Z; r_dlen : Z; r_xlen : Z; r_nl : Z; r_cl : Z;
  r_datap : val; r_dictp : val; r_xp : val; r_np : val; r_cp : val;
  (* the contents: data (n bytes), dictionary (dlen), extra field (xlen), name and comment (nl, cl non-zero
     bytes; their objects hold them and a zero byte) *)
  r_data : list Z; r_dict : list Z; r_xf : list Z; r_nm : list Z; r_cm : list Z }.

(* The limit of name_len and comment_len in the harness (upto(...) in main).  The header theory takes names and
   comments of at most 2^32-2 bytes (LawFactsW.cstr_ok_w); within that limit deflateBound's count of the header
   in 64 bits does not wrap. *)
Definition str_max : Z := 4294967294.

Lemma str_max_range : 0 <= str_max <= 4294967294.
Proof. unfold str_max; lia. Qed.

Definition nzbytes (l : list Z) : Prop := Forall (fun b => 0 < b < 256) l.

Definition rs_ok (rs : rsetup) : Prop :=
  s32 (r_level rs) /\ s32 (r_wbits rs) /\ s32 (r_mem rs) /\ s32 (r_strategy rs) /\
  0 <= r_n rs <= 4294967295 /\ 0 <= r_choice rs < 256 /\ 0 <= r_dlen rs <= 4294967295 /\
  0 <= r_xlen rs <= 65535 /\ 0 <= r_nl rs <= str_max /\ 0 <= r_cl rs <= str_max /\
  Zlength (r_data rs) = r_n rs /\ bytes (r_data rs) /\ Zlength (r_dict rs) = r_dlen rs /\ bytes (r_dict rs) /\
  Zlength (r_xf rs) = r_xlen rs /\ bytes (r_xf rs) /\ Zlength (r_nm rs) = r_nl rs /\ nzbytes (r_nm rs) /\
  Zlength (r_cm rs) = r_cl rs /\ nzbytes (r_cm rs) /\
  isptr (r_datap rs) /\ isptr (r_dictp rs) /\ isptr (r_xp rs) /\ isptr (r_np rs) /\ isptr (r_cp rs) /\
  params_ok (r_level rs) 8 (r_wbits rs) (r_mem rs) (r_strategy rs) = true.

(* an object of main: malloc'ed, exactly its bytes *)
Definition obj (p : val) (l : list Z) : mpred := BoundKit.obj p l.

Definition objs (rs : rsetup) : mpred :=
  obj (r_datap rs) (r_data rs) * obj (r_dictp rs) (r_dict rs) * obj (r_xp rs) (r_xf rs) *
  obj (r_np rs) (r_nm rs ++ [0]) * obj (r_cp rs) (r_cm rs ++ [0]).

(* the temps of the drawn values and the objects *)
Definition rs_locals (rs : rsetup) : list localdef :=
  [temp _level (vi (r_level rs)); temp _window_bits (vi (r_wbits rs)); temp _mem_level (vi (r_mem rs));
   temp _strategy (vi (r_strategy rs)); temp _data_len (vl (r_n rs)); temp _data (r_datap rs);
   temp _choice (vi (r_choice rs)); temp _dict_len (vl (r_dlen rs)); temp _extra_len (vl (r_xlen rs));
   temp _name_len (vl (r_nl rs)); temp _comment_len (vl (r_cl rs)); temp _dict (r_dictp rs);
   temp _extra (r_xp rs); temp _name (r_np rs); temp _comment (r_cp rs)].

(* bit [m] of choice is set: choice & m != 0 *)
Definition has (rs : rsetup) (m : Z) : bool := negb (Z.land (r_choice rs) m =? 0).

(* a header is set: (choice & 1) && window_bits > 15; a dictionary is set: (choice & 1) && window_bits <= 15 *)
Definition hs_of (rs : rsetup) : bool := has rs 1 && (15 <? r_wbits rs).
Definition ds_of (rs : rsetup) : bool := has rs 1 && (r_wbits rs <=? 15).

(** ** The gzip header head *)

(* the four values main draws for it: text, time, os, hcrc *)
Record hvals := mkHV { h_text : Z; h_time : Z; h_os : Z; h_hcrc : Z }.

Definition hv_ok (hv : hvals) : Prop :=
  s32 (h_text hv) /\ u32r (h_time hv) /\ s32 (h_os hv) /\ s32 (h_hcrc hv).

(* head.extra, head.name, head.comment: the object when its bit of choice is set, else Z_NULL *)
Definition selp (rs : rsetup) (m : Z) (q : val) : val := if has rs m then q else nullval.
Definition selo (rs : rsetup) (m : Z) (l : list Z) : option (list Z) := if has rs m then Some l else None.

(* head after its eight stores; xflags, extra_max, name_max, comm_max and done are never written *)
Definition hval (rs : rsetup) (hv : hvals) : reptype t_gzh :=
  (vi (h_text hv), (vl (h_time hv), (Vundef, (vi (h_os hv), (selp rs 2 (r_xp rs), (vi (r_xlen rs),
   (Vundef, (selp rs 4 (r_np rs), (Vundef, (selp rs 8 (r_cp rs), (Vundef, (vi (h_hcrc hv), Vundef)))))))))))).

(* the header deflateSetHeader is given *)
Definition hdr_of (rs : rsetup) (hv : hvals) : gzh :=
  mkGZ (h_text hv) (h_time hv) (h_os hv) (selo rs 2 (r_xf rs)) (r_xlen rs) (selo rs 4 (r_nm rs ++ [0]))
    (selo rs 8 (r_cm rs ++ [0])) (h_hcrc hv).

(** ** The stream between the calls (MainKit.bstrm: the state and the caller's z_stream fields; next_in and
    next_out are Z_NULL until offer); srest: the complement of Ews in the local strm and the padding *)
Notation bstrm := MainKit.bstrm.
Notation st_s := MainKit.st_s.
Notation st_tin := MainKit.st_tin.
Notation st_tout := MainKit.st_tout.
Notation st_adler := MainKit.st_adler.
Notation st_msg := MainKit.st_msg.
Notation st_msgv := MainKit.st_msgv.
Notation st_fields := MainKit.st_fields.
Notation srest := MainKit.srest.

Section Kit.
Context (Bpre : bpre_inv) (Brun : brun_inv).
Context (gv : globals) (vh vs : val).

(* the header's memory at the end: whatever the state's gzhead [hdr_at] and the rest [Hr] hold, with the
   state's gzhead unchanged they give back head's memory (MainKit.hclose) *)
Definition hclose (s : dstate) (ghp : val) (hx : share * val * val * val) (Hr : mpred) : Prop :=
  MainKit.hclose vh s ghp hx Hr.

(* the entry (after start_function) *)
Definition PRE0 : environ -> mpred :=
  PROP ()
  LOCAL (lvar _strm t_strm vs; lvar _head t_gzh vh; gvars gv)
  SEP (data_at_ Tsh t_strm vs; data_at_ Tsh t_gzh vh; mem_mgr gv; R gv).

(* A1 (msuf 17, after the NULL test): everything drawn and allocated *)
Definition A1 (rs : rsetup) : environ -> mpred :=
  PROPx [rs_ok rs]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [data_at_ Tsh t_gzh vh; data_at_ Tsh t_strm vs; mem_mgr gv; deflate_globals gv; version_at gv vlit;
         objs rs])).

(* A2 (msuf 25, before new_stream): head's eight fields stored *)
Definition A2 (rs : rsetup) (hv : hvals) : environ -> mpred :=
  PROPx [rs_ok rs; hv_ok hv]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [data_at Tsh t_gzh (hval rs hv) vh; data_at_ Tsh t_strm vs; mem_mgr gv; deflate_globals gv;
         version_at gv vlit; objs rs])).

(* A3 (msuf 29, before the deflateSetHeader branch): deflateInit2 returned Z_OK *)
Definition A3 (rs : rsetup) (hv : hvals) (st : bstrm) : environ -> mpred :=
  PROPx [rs_ok rs; hv_ok hv;
         Bpre (r_level rs) (r_wbits rs) (r_mem rs) (r_strategy rs) false (st_s st) (st_tin st) (st_tout st)
           (st_adler st);
         d_gzhead (st_s st) = None; msg_ok (st_msg st) (st_msgv st)]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs nullval gv; st_fields vs st; srest vs;
         data_at Tsh t_gzh (hval rs hv) vh; mem_mgr gv; deflate_globals gv; objs rs; TT])).

(* A4 (msuf 30, before the deflateSetDictionary branch): the header set when hs_of rs; the dictionary's
   object is kept *)
Definition A4 (rs : rsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [rs_ok rs;
         Bpre (r_level rs) (r_wbits rs) (r_mem rs) (r_strategy rs) false (st_s st) (st_tin st) (st_tout st)
           (st_adler st);
         msg_ok (st_msg st) (st_msgv st); hclose (st_s st) ghp hx Hr]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs ghp gv; st_fields vs st; srest vs; hdr_at (Some (st_s st)) ghp hx; Hr;
         mem_mgr gv; deflate_globals gv; obj (r_datap rs) (r_data rs); obj (r_dictp rs) (r_dict rs); TT])).

(* A5 (msuf 31, before deflateBound): the dictionary set when ds_of rs *)
Definition A5 (rs : rsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred)
    : environ -> mpred :=
  PROPx [rs_ok rs;
         Bpre (r_level rs) (r_wbits rs) (r_mem rs) (r_strategy rs) (ds_of rs) (st_s st) (st_tin st)
           (st_tout st) (st_adler st);
         msg_ok (st_msg st) (st_msgv st); hclose (st_s st) ghp hx Hr]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [dstream 2 (Some (st_s st)) vs ghp gv; st_fields vs st; srest vs; hdr_at (Some (st_s st)) ghp hx; Hr;
         mem_mgr gv; deflate_globals gv; obj (r_datap rs) (r_data rs); TT])).

(* A6 (msuf 35, before set_buffer): b = deflateBound(&strm, data_len) <= UINT_MAX, compressed = malloc(b) not
   NULL; total_out is still 0 *)
Definition A6 (rs : rsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred) (b : Z)
    (obp : val) : environ -> mpred :=
  PROPx [rs_ok rs; Brun (r_n rs) b 0 false (st_s st) (st_tin st) (st_tout st) (st_adler st);
         0 <= b <= 4294967295; isptr obp; st_tout st = 0; msg_ok (st_msg st) (st_msgv st); hclose (st_s st) ghp hx Hr]
  (LOCALx [temp _bound (vl b); temp _compressed obp; temp _data (r_datap rs); temp _data_len (vl (r_n rs));
           lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv]
  (SEPx [dstream 2 (Some (st_s st)) vs ghp gv; st_fields vs st; srest vs; hdr_at (Some (st_s st)) ghp hx; Hr;
         mem_mgr gv; deflate_globals gv; obj (r_datap rs) (r_data rs);
         @malloc_token DCS.CS Ews (tarray tuchar b) obp; @data_at_ DCS.CS Ews (tarray tuchar b) obp; TT])).

End Kit.

(** ** The statements of the parts (each proved in its own file) *)

Definition part_pre_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val),
  (forall rs, semax Delta_m (A1 gv vh vs rs) msuf17 POST_m) ->
  semax Delta_m (PRE0 gv vh vs) msuf0 POST_m.

Definition part_stores_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup),
  (forall hv, semax Delta_m (A2 gv vh vs rs hv) msuf25 POST_m) ->
  semax Delta_m (A1 gv vh vs rs) msuf17 POST_m.

Definition part_init_stmt : Prop :=
  forall {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (I : api_inv) (Iend : dstate -> Prop)
    (gv : globals) (vh vs : val) (rs : rsetup) (hv : hvals),
  bound_facts_w Bpre Brun -> api_facts I Iend -> ob_dstream_to_end ->
  (forall st, semax Delta_m (A3 Bpre gv vh vs rs hv st) msuf29 POST_m) ->
  semax Delta_m (A2 gv vh vs rs hv) msuf25 POST_m.

Definition part_head_stmt : Prop :=
  forall {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vh vs : val) (rs : rsetup)
    (hv : hvals) (st : bstrm),
  bound_facts_w Bpre Brun ->
  (forall st' ghp hx Hr, semax Delta_m (A4 Bpre gv vh vs rs st' ghp hx Hr) msuf30 POST_m) ->
  semax Delta_m (A3 Bpre gv vh vs rs hv st) msuf29 POST_m.

Definition part_dict_stmt : Prop :=
  forall {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vh vs : val) (rs : rsetup)
    (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred),
  bound_facts_w Bpre Brun ->
  (forall st', semax Delta_m (A5 Bpre gv vh vs rs st' ghp hx Hr) msuf31 POST_m) ->
  semax Delta_m (A4 Bpre gv vh vs rs st ghp hx Hr) msuf30 POST_m.

Definition part_bound_stmt : Prop :=
  forall {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vh vs : val) (rs : rsetup)
    (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred),
  bound_facts_w Bpre Brun -> Zlib.proof.deflate.LTWBOnce.once_acct_w Bpre Brun -> ob_dstream_to_end ->
  (forall b obp, semax Delta_m (A6 Brun gv vh vs rs st ghp hx Hr b obp) msuf35 POST_m) ->
  semax Delta_m (A5 Bpre gv vh vs rs st ghp hx Hr) msuf31 POST_m.

Definition part_run_stmt : Prop :=
  forall {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vh vs : val) (rs : rsetup)
    (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred) (b : Z) (obp : val),
  bound_facts_w Bpre Brun -> Zlib.proof.deflate.LTWBOnce.once_acct_w Bpre Brun -> ob_dstream_to_end ->
  semax Delta_m (A6 Brun gv vh vs rs st ghp hx Hr b obp) msuf35 POST_m.

(** ** The statement of main's body (RBMain.v) *)
Definition body_main_stmt : Prop :=
  forall (Bpre : bpre_inv) (Brun : brun_inv) (I : api_inv) (Iend : dstate -> Prop),
  bound_facts_w Bpre Brun -> Zlib.proof.deflate.LTWBOnce.once_acct_w Bpre Brun -> api_facts I Iend -> ob_dstream_to_end ->
  semax_body (QPvarspecs Zlib.contracts.res_bound.whole_prog) Gmain f_main (_main, main_core_spec R).

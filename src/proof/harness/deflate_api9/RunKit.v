(* Law deflate_api: the kit of deflate_run's body proof (Run.v): its type context and postcondition, its body
   cut into suffixes (statement k of the body's sequence and everything after it), and the assertions at the
   cuts.  Each part lemma (Run*.v) is in continuation-passing style: it proves the suffix at its first cut from
   the hypothesis that the suffix at its last cut is proved from the assertion there:
     run_prefix  (RunPrefix.v):  suffix 0  (entry)        -> suffix 45 (stream_defaults), A1
     run_init    (RunInit.v):    suffix 45 (A1)           -> suffix 51 (if (tsel == 0)), A2
     run_opts    (RunOpts.v):    suffix 51 (A2)           -> suffix 57 (the loop), J_at
   and in the loop body (lsuf k: statement k of the body's sequence, 0 = the leading skip of for(;;)):
     loop_pre    (LoopPre.v):    lsuf 0  (J_at)           -> lsuf 21 (the call), B1
     loop_call   (LoopCall.v):   lsuf 21 (B1)             -> lsuf 22 (used = ...), B2
     loop_check  (LoopCheck.v):  lsuf 22 (B2)             -> lsuf 25 (bytes_copy), B3
     loop_post   (LoopPost.v):   lsuf 25 (B3)             -> end of the body (J_inv again, or break with E)
   Run.v assembles them (the loop, R->ended = 1; return 1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

(** ** Suffixes of a statement sequence *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

Ltac get_suf k s :=
  let x := eval cbv beta iota zeta delta [suf] in (suf k s) in exact x.

Definition run_body : statement := ltac:(let x := eval cbv beta iota zeta delta [f_deflate_run fn_body] in
                                         (fn_body f_deflate_run) in exact x).
Ltac get_rsuf k := let x := eval cbv beta iota zeta delta [suf run_body] in (suf k run_body) in exact x.
Definition rsuf45 : statement := ltac:(get_rsuf 45%nat).
Definition rsuf51 : statement := ltac:(get_rsuf 51%nat).
Definition rsuf57 : statement := ltac:(get_rsuf 57%nat).
Definition rsuf58 : statement := ltac:(get_rsuf 58%nat).

(* the loop: for(;;) is Sloop lbody Sskip *)
Definition run_lbody : statement := ltac:(let x := eval cbv beta iota zeta delta [suf run_body] in
  (match suf 57 run_body with Ssequence (Sloop b _) _ => b | _ => Sskip end) in exact x).
Ltac get_lsuf k := let x := eval cbv beta iota zeta delta [suf run_lbody] in (suf k run_lbody) in exact x.
Definition lsuf21 : statement := ltac:(get_lsuf 21%nat).
Definition lsuf22 : statement := ltac:(get_lsuf 22%nat).
Definition lsuf25 : statement := ltac:(get_lsuf 25%nat).

Lemma rsuf57_eq : rsuf57 = Ssequence (Sloop run_lbody Sskip) rsuf58.
Proof. reflexivity. Qed.

(** ** Type context and postcondition of deflate_run's body *)
Definition Delta_r : tycontext := func_tycontext f_deflate_run (QPvarspecs p) Grun nil.

Definition POST_r (Iend : dstate -> Prop) (Rp sp : val) (gv : globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (EX ret : Z, PROP (ret = 0 \/ ret = 1) RETURN (vi ret)
                    SEP (mem_mgr gv; deflate_globals gv; run_post Iend ret Rp sp gv))%argsassert)
    (stackframe_of f_deflate_run).

(** ** The objects drawn by the run, before the loop *)
Definition allobjs (rs : rsetup) : mpred :=
  obj (rs_datap rs) (rs_data rs) * obj (rs_dictp rs) (rs_dict rs) * obj (rs_xfp rs) (rs_xf rs) *
  obj (rs_nfp rs) (rs_nm rs ++ [0]) * obj (rs_cfp rs) (rs_cm rs ++ [0]) * comp_at [] (rs_compp rs).

Section Kit.
Context (I : api_inv) (Iend : dstate -> Prop).
Context (Rp sp : val) (api : Z) (vosn : val) (gv : globals).

(* the entry (after start_function) *)
Definition PRE0 : environ -> mpred :=
  PROP (api_facts I Iend; s32 api)
  LOCAL (temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (data_at_ Ews t_drun Rp; data_at_ Ews t_strmL sp; mem_mgr gv; deflate_globals gv; version_at gv vlit;
       data_at_ Tsh (tptr tuchar) vosn).

(* A1 (before stream_defaults(s)): everything drawn, R's fields set but init, wrap, wb, h *)
Definition A1 (rs : rsetup) : environ -> mpred :=
  PROP (rs_ok rs; api_facts I Iend; s32 api)
  LOCAL (temp _t1 (vi (rs_t1 rs)); temp _t2 (vi (rs_t2 rs)); temp _t3 (vi (rs_t3 rs)); temp _t4 (vi (rs_t4 rs));
         temp _mtime (vl (rs_mtime rs)); temp _tsel (vi (rs_tsel rs)); temp _dsel (vi (rs_dsel rs));
         temp _hsel (vi (rs_hsel rs)); temp _text (vi (rs_text rs)); temp _os (vi (rs_os rs));
         temp _hcrc (vi (rs_hcrc rs));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest rs Vundef Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 Rp; field_at_ Ews t_drun (DOT _h) Rp;
       data_at_ Ews t_strmL sp; allobjs rs; mem_mgr gv; deflate_globals gv; version_at gv vlit;
       data_at_ Tsh (tptr tuchar) vosn).

(* A2 (before if (tsel == 0)): deflateInit2 returned Z_OK, R->init, wrap, wb set *)
Definition A2 (rs : rsetup) (s : dstate) (tin tout adler : Z) (nin : val) (ain : Z) (nout : val) (aout : Z)
    (msg : option Z) (msgv : val) : environ -> mpred :=
  PROP (rs_ok rs; api_facts I Iend; s32 api;
        I [] (wrap_of (rs_wbits rs)) [] [] None s tin tout adler; d_gzhead s = None; msg_ok msg msgv)
  LOCAL (temp _t1 (vi (rs_t1 rs)); temp _t2 (vi (rs_t2 rs)); temp _t3 (vi (rs_t3 rs)); temp _t4 (vi (rs_t4 rs));
         temp _mtime (vl (rs_mtime rs)); temp _tsel (vi (rs_tsel rs)); temp _dsel (vi (rs_dsel rs));
         temp _hsel (vi (rs_hsel rs)); temp _text (vi (rs_text rs)); temp _os (vi (rs_os rs));
         temp _hcrc (vi (rs_hcrc rs));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (Zlength (rs_data rs)) 0 0 0 0 Rp;
       field_at_ Ews t_drun (DOT _h) Rp;
       dstream 2 (Some s) sp nullval gv; api_fields sp nin ain tin nout aout tout msgv adler; strm_pad sp;
       allobjs rs; mem_mgr gv; deflate_globals gv; data_at_ Tsh (tptr tuchar) vosn; TT).

(** ** The loop *)

(* the state at the loop head: [ls_pos] bytes of the data consumed, [ls_O] the output so far (comp[0..clen)),
   [ls_fin] Z_FINISH given (Some of the rest of the data to consume), the stream (state, the caller's fields),
   R->nf, R->dict_set, R->head_set, the state's gzhead pointer. *)
Record lstate := mkLS {
  ls_dict : list Z; ls_pos : Z; ls_O : list Z; ls_fin : option (list Z); ls_s : dstate;
  ls_tin : Z; ls_tout : Z; ls_adler : Z; ls_nin : val; ls_ain : Z; ls_nout : val; ls_aout : Z;
  ls_msg : option Z; ls_msgv : val; ls_nf : Z; ls_dset : Z; ls_hset : Z; ls_ghp : val }.

Definition fin_flag (fin : option (list Z)) : Z := match fin with None => 0 | Some _ => 1 end.

Definition J_ok (rs : rsetup) (ls : lstate) : Prop :=
  let data := rs_data rs in
  rs_ok rs /\ api_facts I Iend /\ s32 api /\
  I (ls_dict ls) (wrap_of (rs_wbits rs)) (sublist 0 (ls_pos ls) data) (ls_O ls) (ls_fin ls) (ls_s ls)
    (ls_tin ls) (ls_tout ls) (ls_adler ls) /\
  0 <= ls_pos ls <= ls_nf ls /\ ls_nf ls <= Zlength data /\ Zlength (ls_O ls) <= COMP_MAX /\ bytes (ls_O ls) /\
  ((ls_fin ls = None /\ ls_nf ls = Zlength data) \/ ls_fin ls = Some (sublist (ls_pos ls) (ls_nf ls) data)) /\
  ((ls_dset ls = 1 /\ ls_dict ls = rs_dict rs /\ rs_dict rs <> []) \/ (ls_dset ls = 0 /\ ls_dict ls = [])) /\
  ((ls_hset ls = 1 /\ ls_ghp ls = hp_of Rp /\ d_gzhead (ls_s ls) = Some (hdr_of rs)) \/
   (ls_hset ls = 0 /\ d_gzhead (ls_s ls) = None)) /\
  msg_ok (ls_msg ls) (ls_msgv ls).

(* the memory at the loop head, but R->nf, the fields of the stream and osnap's contents (B1, B2, B3 change
   them) *)
Definition lsep (rs : rsetup) (ls : lstate) : mpred :=
  hpart (ls_hset ls) Rp * dstream 2 (Some (ls_s ls)) sp (ls_ghp ls) gv * strm_pad sp *
  hdr_at (Some (ls_s ls)) (ls_ghp ls) (hx_of rs) *
  obj (rs_datap rs) (rs_data rs) * obj (rs_dictp rs) (rs_dict rs) * comp_at (ls_O ls) (rs_compp rs) *
  mem_mgr gv * deflate_globals gv * TT.

Definition J_at (rs : rsetup) (ls : lstate) : environ -> mpred :=
  PROP (J_ok rs ls)
  LOCAL (temp _pos (vi (ls_pos ls)); temp _finishing (vi (fin_flag (ls_fin ls)));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (ls_nf ls) (ls_dset ls)
         (ls_hset ls) (Zlength (ls_O ls)) 0 Rp;
       api_fields sp (ls_nin ls) (ls_ain ls) (ls_tin ls) (ls_nout ls) (ls_aout ls) (ls_tout ls) (ls_msgv ls)
         (ls_adler ls);
       data_at_ Tsh (tptr tuchar) vosn; lsep rs ls).

Definition J_inv (rs : rsetup) : environ -> mpred := EX ls : lstate, J_at rs ls.

(* after the loop (break: deflate returned Z_STREAM_END) *)
Definition E_at (rf : rfinal) : environ -> mpred :=
  PROP (rf_ok Iend Rp rf)
  LOCAL (temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest (rf_rs rf) (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits (rf_rs rf)))) (rf_nf rf) (rf_dset rf)
         (rf_hset rf) (Zlength (rf_O rf)) 0 Rp;
       hpart (rf_hset rf) Rp; dstream 2 (Some (rf_s rf)) sp (rf_ghp rf) gv;
       api_fields sp (rf_nin rf) (rf_ain rf) (rf_tin rf) (rf_nout rf) (rf_aout rf) (rf_tout rf) (rf_msgv rf)
         (rf_adler rf); strm_pad sp;
       hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of (rf_rs rf));
       obj (rs_datap (rf_rs rf)) (rs_data (rf_rs rf)) * obj (rs_dictp (rf_rs rf)) (rs_dict (rf_rs rf)) *
       comp_at (rf_O rf) (rs_compp (rf_rs rf));
       mem_mgr gv; deflate_globals gv; data_at_ Tsh (tptr tuchar) vosn; TT).

Definition E_inv (rs : rsetup) : environ -> mpred := EX rf : rfinal, !! (rf_rs rf = rs) && E_at rf.

(* the loop body's postcondition *)
Definition Rbody (rs : rsetup) : ret_assert :=
  loop1_ret_assert (J_inv rs) (overridePost (E_inv rs) (POST_r Iend Rp sp gv)).

(* one iteration's choices: the input object ib holds data[pos..lim) (lim - pos = ain), aout bytes of output
   space at ob with arbitrary bytes bs (osnap's object q holds the same), the flush value, params (deflateParams
   with plev, pstrat instead of deflate) *)
Record citer := mkCI {
  ci_lim : Z; ci_aout : Z; ci_flush : Z; ci_params : bool; ci_plev : Z; ci_pstrat : Z;
  ci_ib : val; ci_ob : val; ci_q : val; ci_bs : list Z }.

Definition ci_inb (rs : rsetup) (ls : lstate) (ci : citer) : list Z := sublist (ls_pos ls) (ci_lim ci) (rs_data rs).
(* R->nf and finishing after the iteration's choices *)
Definition ci_nf (ls : lstate) (ci : citer) : Z := if ci_flush ci =? Z_FINISH then ci_lim ci else ls_nf ls.
Definition ci_fin (ci : citer) : Z := if ci_flush ci =? Z_FINISH then 1 else 0.

Definition ci_ok (rs : rsetup) (ls : lstate) (ci : citer) : Prop :=
  J_ok rs ls /\
  ls_pos ls <= ci_lim ci <= Zlength (rs_data rs) /\
  (forall R, ls_fin ls = Some R -> ci_flush ci = Z_FINISH /\ ci_lim ci = ls_nf ls) /\
  0 <= ci_flush ci <= 5 /\
  0 <= ci_aout ci <= 1048576 /\ Zlength (ls_O ls) + ci_aout ci <= COMP_MAX /\
  (ci_params ci = true -> ls_fin ls = None /\ ci_flush ci <> Z_FINISH) /\
  s32 (ci_plev ci) /\ s32 (ci_pstrat ci) /\
  Zlength (ci_bs ci) = ci_aout ci /\ bytes (ci_bs ci) /\
  isptr (ci_ib ci) /\ isptr (ci_ob ci) /\ isptr (ci_q ci).

Definition B_loc (ls : lstate) (ci : citer) : list localdef :=
  [temp _pos (vi (ls_pos ls)); temp _lim (vi (ci_lim ci)); temp _finishing (vi (ci_fin ci));
   temp _flush (vi (ci_flush ci)); temp _ain (vi (ci_lim ci - ls_pos ls)); temp _aout (vi (ci_aout ci));
   temp _ib (ci_ib ci); temp _ob (ci_ob ci); temp _tin (vl (ls_tin ls)); temp _tout (vl (ls_tout ls));
   temp _params (vi (if ci_params ci then 1 else 0)); temp _plev (vi (ci_plev ci));
   temp _pstrat (vi (ci_pstrat ci));
   temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv].

(* B1 (before the call): the stream's caller fields set for the call, ib and ob, osnap holds q *)
Definition B1 (rs : rsetup) (ls : lstate) (ci : citer) : environ -> mpred :=
  PROPx [ci_ok rs ls ci]
  (LOCALx (B_loc ls ci)
  (SEPx [drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (ci_nf ls ci) (ls_dset ls)
          (ls_hset ls) (Zlength (ls_O ls)) 0 Rp;
        api_fields sp (ci_ib ci) (ci_lim ci - ls_pos ls) (ls_tin ls) (ci_ob ci) (ci_aout ci) (ls_tout ls)
          (ls_msgv ls) (ls_adler ls);
        data_at Tsh (tptr tuchar) (ci_q ci) vosn;
        obj (ci_ib ci) (ci_inb rs ls ci); obj (ci_ob ci) (ci_bs ci); obj (ci_q ci) (ci_bs ci);
        lsep rs ls])).

(* what the call did (af_deflate / af_params of LawFacts): [code] its result, [s'] [z'] the stream after it *)
Definition step_ok (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (code : Z) : Prop :=
  let inb := ci_inb rs ls ci in
  let used := Zlength inb - z_avail_in z' in
  let wrap := wrap_of (rs_wbits rs) in
  let D' := sublist 0 (ls_pos ls) (rs_data rs) ++ sublist 0 used inb in
  let O' := ls_O ls ++ z_out z' in
  d_gzhead s' = d_gzhead (ls_s ls) /\ call_ok inb (ci_aout ci) (ls_tin ls) (ls_tout ls) z' /\
  if ci_params ci then
    (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_ERROR) /\
    (code = Z_STREAM_ERROR <-> ~ (-1 <= ci_plev ci <= 9 /\ 0 <= ci_pstrat ci <= 4)) /\
    I (ls_dict ls) wrap D' O' None s' (z_total_in z') (z_total_out z') (z_adler z')
  else
    (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
    (code = Z_STREAM_END -> ci_flush ci = Z_FINISH /\ z_avail_in z' = 0) /\
    (code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = ci_aout ci) /\
    (if code =? Z_STREAM_END then Iend s' /\ final_ok (ls_dict ls) wrap D' O' (z_adler z')
     else I (ls_dict ls) wrap D' O'
            (if ci_flush ci =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z')).

(* the memory after the call *)
Definition B_sep (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (msgv' : val) : list mpred :=
  [drun_rest rs (vi 0) (vi (wrap_of (rs_wbits rs))) (vi (wb_of (rs_wbits rs))) (ci_nf ls ci) (ls_dset ls)
     (ls_hset ls) (Zlength (ls_O ls)) 0 Rp;
   api_fields sp (offset_val (z_next_in z') (ci_ib ci)) (z_avail_in z') (z_total_in z')
     (offset_val (Zlength (z_out z')) (ci_ob ci)) (z_avail_out z') (z_total_out z') msgv' (z_adler z');
   data_at Tsh (tptr tuchar) (ci_q ci) vosn;
   obj (ci_ib ci) (ci_inb rs ls ci);
   malloc_token Ews (tarray tuchar (ci_aout ci)) (ci_ob ci) *
   data_at Ews (tarray tuchar (ci_aout ci))
     (map vi (z_out z') ++ sublist (Zlength (z_out z')) (ci_aout ci) (map vi (ci_bs ci))) (ci_ob ci);
   obj (ci_q ci) (ci_bs ci);
   lsep rs (mkLS (ls_dict ls) (ls_pos ls) (ls_O ls) (ls_fin ls) s' (ls_tin ls) (ls_tout ls) (ls_adler ls)
              (ls_nin ls) (ls_ain ls) (ls_nout ls) (ls_aout ls) (ls_msg ls) (ls_msgv ls) (ls_nf ls) (ls_dset ls)
              (ls_hset ls) (ls_ghp ls))].

(* B2 (after the call, r its result) *)
Definition B2 (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (code : Z) (msgv' : val)
    : environ -> mpred :=
  PROPx [ci_ok rs ls ci; step_ok rs ls ci s' z' code; msg_ok (z_msg z') msgv']
  (LOCALx (temp _r (vi code) :: B_loc ls ci)
  (SEPx (B_sep rs ls ci s' z' msgv'))).

(* B3 (after the API checks: used and made computed) *)
Definition B3 (rs : rsetup) (ls : lstate) (ci : citer) (s' : dstate) (z' : strm) (code : Z) (msgv' : val)
    : environ -> mpred :=
  PROPx [ci_ok rs ls ci; step_ok rs ls ci s' z' code; msg_ok (z_msg z') msgv']
  (LOCALx (temp _used (vi (Zlength (ci_inb rs ls ci) - z_avail_in z')) ::
          temp _made (vi (ci_aout ci - z_avail_out z')) :: temp _r (vi code) :: B_loc ls ci)
  (SEPx (B_sep rs ls ci s' z' msgv'))).

End Kit.

(** ** Memory lemmas (proved in RunMem.v; parts that need them take [run_mem_ok] as a hypothesis) *)
Definition run_mem_ok : Prop :=
  (* a live or ended stream and the caller's fields are the z_stream's memory *)
  (forall (os : option dstate) (sp ghp : val) (gv : globals) (nin : val) (ain tin : Z) (nout : val)
          (aout tout : Z) (msgv : val) (adler : Z),
     dstream 2 os sp ghp gv * api_fields sp nin ain tin nout aout tout msgv adler * strm_pad sp
     |-- data_at_ Ews t_strmL sp * TT) /\
  (* struct drun with R->h held by the stream's header (hset = 1) or by hpart (hset = 0) *)
  (forall (rs : rsetup) (init wrap wb : val) (nf dset hset clen ended : Z) (Rp : val) (s : dstate) (ghp : val),
     ((hset = 1 /\ ghp = hp_of Rp /\ d_gzhead s = Some (hdr_of rs)) \/ (hset = 0 /\ d_gzhead s = None)) ->
     drun_rest rs init wrap wb nf dset hset clen ended Rp * hpart hset Rp * hdr_at (Some s) ghp (hx_of rs)
     |-- data_at_ Ews t_drun Rp * TT) /\
  (* struct drun with R->h a field *)
  (forall (rs : rsetup) (init wrap wb : val) (nf dset hset clen ended : Z) (Rp : val),
     drun_rest rs init wrap wb nf dset hset clen ended Rp * field_at_ Ews t_drun (DOT _h) Rp
     |-- data_at_ Ews t_drun Rp).

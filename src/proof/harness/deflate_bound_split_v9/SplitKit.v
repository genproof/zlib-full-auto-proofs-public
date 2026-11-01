(* Law deflate_bound_split: the kit of main's body proof (SplitBody.v).  main is proved under DCS.CS (SplitMain.v);
   its body (after start_function: [Ssequence mbody (return 0)]) is cut into suffixes of the statement sequence
   [mbody] ([msuf k]: statement k and everything after it) and, in the loop, of the loop body [lbody]
   ([lsuf k]).  Each part lemma (Split*.v) is in continuation-passing style: it proves the suffix at its first
   cut from the hypothesis that the suffix at its next cut is proved from the assertion there:
     part_draws  (SplitDraws.v):  mbody   (PRE0)        -> msuf 27 (nondet_bytes(data, n)), A1 bd
     part_fill   (SplitFill.v):   msuf 27 (A1 bd)       -> msuf 35 (deflateInit2), A2 bs f
     part_init   (SplitInit.v):   msuf 35 (A2 bs f)     -> msuf 37 (if dsel == 0 ..), SA bs false false s f
     part_dict   (SplitDict.v):   msuf 37 (SA .. false false) -> msuf 38 (if hsel == 0 ..), SA bs (dset bs) false
     part_head   (SplitHead.v):   msuf 38 (SA .. false) -> msuf 39 (deflateBound), SA bs (dset bs) true s f
     part_bound  (SplitBound.v):  msuf 39 (SA .. true)  -> msuf 42 (the loop), J bs b 0 false s f
   the loop body (for(;;): Sloop lbody Sskip; lbody = Ssequence Sskip ..; postcondition Rbody):
     part_l1     (SplitL1.v):     lbody (J ..)          -> lsuf 11 (s.next_in = ib), B1 bs b st ci
     part_l2     (SplitL2.v):     lsuf 11 (B1 ..)       -> lsuf 16 (the asserts), B2 bs b st ci s' z' code msgv'
     part_l3     (SplitL3.v):     lsuf 16 (B2 ..)       -> end of the body (J again, or break with E)
   after the loop:
     part_end    (SplitEnd.v):    msuf 43 (E bs s f)    -> return 0.
   SplitBody.v assembles them.  Every part's postcondition is [Rm_ret] (main's, normal exit impossible).

   Representation: main's locals s, h, osnap are Tsh; the API specifications are on Ews.  Right after
   stream_defaults (part_fill) the stream is split into its Ews part (the API's pieces: api_fields, the other
   fields, [strm_pad]) and [data_at_ Ecomp t_strm sp], kept until the return (BoundKit.v).  The header h is
   [data_at_ Tsh t_gzh hp] until part_head; when deflateSetHeader is called (hset bs) it is split the same way,
   its Ews fields become the stream's [hdr_at] (gzh_at Ews (hdr_of bs) ..). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(** ** Suffixes of a statement sequence *)
Fixpoint suf (k : nat) (s : statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ b => suf k' b
  | _, _ => Sskip
  end.

(* main's body: Ssequence mbody (return 0) *)
Definition mbody : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [f_main fn_body] in
        (match fn_body f_main with Ssequence b _ => b | _ => Sskip end) in exact x).
Ltac get_msuf k := let x := eval cbv beta iota zeta delta [suf mbody] in (suf k mbody) in exact x.
Definition msuf27 : statement := ltac:(get_msuf 27%nat).
Definition msuf35 : statement := ltac:(get_msuf 35%nat).
Definition msuf37 : statement := ltac:(get_msuf 37%nat).
Definition msuf38 : statement := ltac:(get_msuf 38%nat).
Definition msuf39 : statement := ltac:(get_msuf 39%nat).
Definition msuf42 : statement := ltac:(get_msuf 42%nat).
Definition msuf43 : statement := ltac:(get_msuf 43%nat).

Lemma fn_body_main : fn_body f_main = Ssequence mbody (Sreturn (Some (Econst_int (Int.repr 0) tint))).
Proof. reflexivity. Qed.

(* the loop: for(;;) is Sloop lbody Sskip *)
Definition lbody : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf mbody] in
        (match suf 42 mbody with Ssequence (Sloop b _) _ => b | _ => Sskip end) in exact x).
Ltac get_lsuf k := let x := eval cbv beta iota zeta delta [suf lbody] in (suf k lbody) in exact x.
Definition lsuf11 : statement := ltac:(get_lsuf 11%nat).
Definition lsuf16 : statement := ltac:(get_lsuf 16%nat).

Lemma msuf42_eq : msuf42 = Ssequence (Sloop lbody Sskip) msuf43.
Proof. reflexivity. Qed.

(** ** Type context and postcondition of main's body *)
Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

Definition POST_m : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* every part's postcondition: main's, with no normal exit (each path of mbody returns) *)
Definition Rm_ret : ret_assert := overridePost FF POST_m.

(** ** What main drew *)
(* the scalar draws and the five allocations (before their contents are drawn) *)
Record bdraw := mkBD {
  bd_level : Z; bd_wbits : Z; bd_mem : Z; bd_strategy : Z;
  bd_n : Z; bd_dlen : Z; bd_xlen : Z; bd_nl : Z; bd_cl : Z; bd_mtime : Z;
  bd_dsel : Z; bd_hsel : Z; bd_text : Z; bd_os : Z; bd_hcrc : Z; bd_xsel : Z; bd_nsel : Z; bd_csel : Z;
  bd_datap : val; bd_dictp : val; bd_xfp : val; bd_nfp : val; bd_cfp : val }.

Definition bd_ok (bd : bdraw) : Prop :=
  s32 (bd_level bd) /\ s32 (bd_wbits bd) /\ s32 (bd_mem bd) /\ s32 (bd_strategy bd) /\
  params_ok (bd_level bd) 8 (bd_wbits bd) (bd_mem bd) (bd_strategy bd) = true /\
  0 <= bd_n bd <= 1048576 /\ 0 <= bd_dlen bd <= 32768 /\
  0 <= bd_xlen bd <= 4096 /\ 0 <= bd_nl bd <= 4096 /\ 0 <= bd_cl bd <= 4096 /\ u32r (bd_mtime bd) /\
  0 <= bd_dsel bd < 256 /\ 0 <= bd_hsel bd < 256 /\ 0 <= bd_text bd < 256 /\ 0 <= bd_os bd < 256 /\
  0 <= bd_hcrc bd < 256 /\ 0 <= bd_xsel bd < 256 /\ 0 <= bd_nsel bd < 256 /\ 0 <= bd_csel bd < 256 /\
  isptr (bd_datap bd) /\ isptr (bd_dictp bd) /\ isptr (bd_xfp bd) /\ isptr (bd_nfp bd) /\ isptr (bd_cfp bd).

(* and the contents: the data, the dictionary, the extra field, the name and the comment (without their 0) *)
Record bsetup := mkBS {
  bs_d : bdraw; bs_data : list Z; bs_dict : list Z; bs_xf : list Z; bs_nm : list Z; bs_cm : list Z }.

Definition bs_ok (bs : bsetup) : Prop :=
  let bd := bs_d bs in
  bd_ok bd /\
  Zlength (bs_data bs) = bd_n bd /\ Zlength (bs_dict bs) = bd_dlen bd /\ Zlength (bs_xf bs) = bd_xlen bd /\
  Zlength (bs_nm bs) = bd_nl bd /\ Zlength (bs_cm bs) = bd_cl bd /\
  bytes (bs_data bs) /\ bytes (bs_dict bs) /\ bytes (bs_xf bs) /\
  Forall (fun b => 0 < b < 256) (bs_nm bs) /\ Forall (fun b => 0 < b < 256) (bs_cm bs).

(* a dictionary is set / a header is set (both calls are asserted to succeed) *)
Definition dset (bs : bsetup) : bool := andb (bd_dsel (bs_d bs) =? 0) (bd_wbits (bs_d bs) <=? 15).
Definition hset (bs : bsetup) : bool := andb (bd_hsel (bs_d bs) =? 0) (bd_wbits (bs_d bs) >? 15).

(* the header given to deflateSetHeader *)
Definition hdr_of (bs : bsetup) : gzh :=
  let bd := bs_d bs in
  mkGZ (Z.land (bd_text bd) 1) (bd_mtime bd) (bd_os bd)
       (if bd_xsel bd =? 0 then None else Some (bs_xf bs)) (bd_xlen bd)
       (if bd_nsel bd =? 0 then None else Some (bs_nm bs ++ [0]))
       (if bd_csel bd =? 0 then None else Some (bs_cm bs ++ [0]))
       (Z.land (bd_hcrc bd) 1).

(* the header's extra, name, comment pointers *)
Definition hx_of (bs : bsetup) : share * val * val * val :=
  let bd := bs_d bs in
  (Ews, if bd_xsel bd =? 0 then nullval else bd_xfp bd, if bd_nsel bd =? 0 then nullval else bd_nfp bd,
   if bd_csel bd =? 0 then nullval else bd_cfp bd).

Section Kit.
Context (Bpre : bpre_inv) (Brun : brun_inv).
Context (sp hp vosn : val) (gv : globals).

(** ** Memory *)
(* the memory of h and of the objects xf, nf, cf outside the stream; [hd]: the header part was executed (and
   a header set when [hset bs]) *)
Definition hmem (bs : bsetup) (hd : bool) : mpred :=
  let bd := bs_d bs in
  if andb hd (hset bs) then
    data_at_ Ecomp t_gzh hp * gzh_pad hp *
    (if bd_xsel bd =? 0 then obj (bd_xfp bd) (bs_xf bs) else obj_rest (bd_xfp bd) (bs_xf bs)) *
    (if bd_nsel bd =? 0 then obj (bd_nfp bd) (bs_nm bs ++ [0]) else obj_rest (bd_nfp bd) (bs_nm bs ++ [0])) *
    (if bd_csel bd =? 0 then obj (bd_cfp bd) (bs_cm bs ++ [0]) else obj_rest (bd_cfp bd) (bs_cm bs ++ [0]))
  else
    data_at_ Tsh t_gzh hp * obj (bd_xfp bd) (bs_xf bs) * obj (bd_nfp bd) (bs_nm bs ++ [0]) *
    obj (bd_cfp bd) (bs_cm bs ++ [0]).

(* the state's gzhead pointer *)
Definition ghp_of (bs : bsetup) (hd : bool) : val := if andb hd (hset bs) then hp else nullval.

(* the caller's fields of the z_stream *)
Record sfields := mkSF {
  sf_nin : val; sf_ain : Z; sf_tin : Z; sf_nout : val; sf_aout : Z; sf_tout : Z; sf_msg : option Z;
  sf_msgv : val; sf_adler : Z }.
Definition sf_at (f : sfields) : mpred :=
  api_fields sp (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f).

(* a live stream with state s, its caller's fields f, the split-off rest of the locals s and h *)
Definition live (bs : bsetup) (hd : bool) (s : dstate) (f : sfields) : mpred :=
  dstream 2 (Some s) sp (ghp_of bs hd) gv * sf_at f * strm_pad sp * data_at_ Ecomp t_strm sp *
  hdr_at (Some s) (ghp_of bs hd) (hx_of bs) * hmem bs hd.

(* the temps of the draws *)
Definition draw_locals (bd : bdraw) : list localdef :=
  [temp _level (vi (bd_level bd)); temp _wbits (vi (bd_wbits bd)); temp _mem (vi (bd_mem bd));
   temp _strategy (vi (bd_strategy bd)); temp _n (vi (bd_n bd)); temp _dlen (vi (bd_dlen bd));
   temp _xlen (vi (bd_xlen bd)); temp _nl (vi (bd_nl bd)); temp _cl (vi (bd_cl bd));
   temp _mtime (vl (bd_mtime bd)); temp _dsel (vi (bd_dsel bd)); temp _hsel (vi (bd_hsel bd));
   temp _text (vi (bd_text bd)); temp _os (vi (bd_os bd)); temp _hcrc (vi (bd_hcrc bd));
   temp _xsel (vi (bd_xsel bd)); temp _nsel (vi (bd_nsel bd)); temp _csel (vi (bd_csel bd));
   temp _data (bd_datap bd); temp _dict (bd_dictp bd); temp _xf (bd_xfp bd); temp _nf (bd_nfp bd);
   temp _cf (bd_cfp bd);
   lvar _osnap (tptr tuchar) vosn; lvar _h t_gzh hp; lvar _s t_strm sp; gvars gv].

(** ** The assertions at the cuts *)
(* the entry, after start_function *)
Definition PRE0 : environ -> mpred :=
  PROP (bound_facts Bpre Brun; Obligations.ob_dstream_to_end)
  LOCAL (lvar _osnap (tptr tuchar) vosn; lvar _h t_gzh hp; lvar _s t_strm sp; gvars gv)
  SEP (data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh t_gzh hp; data_at_ Tsh t_strm sp; mem_mgr gv; Rm gv).

(* A1 (msuf 27, before nondet_bytes(data, n)): the draws, the five objects allocated, contents undefined *)
Definition A1 (bd : bdraw) : environ -> mpred :=
  PROPx [bd_ok bd; bound_facts Bpre Brun; Obligations.ob_dstream_to_end]
  (LOCALx (draw_locals bd)
  (SEPx [malloc_token Ews (tarray tuchar (bd_n bd)) (bd_datap bd);
         data_at_ Ews (tarray tuchar (bd_n bd)) (bd_datap bd);
         malloc_token Ews (tarray tuchar (bd_dlen bd)) (bd_dictp bd);
         data_at_ Ews (tarray tuchar (bd_dlen bd)) (bd_dictp bd);
         malloc_token Ews (tarray tuchar (bd_xlen bd)) (bd_xfp bd);
         data_at_ Ews (tarray tuchar (bd_xlen bd)) (bd_xfp bd);
         malloc_token Ews (tarray tuchar (bd_nl bd + 1)) (bd_nfp bd);
         data_at_ Ews (tarray tuchar (bd_nl bd + 1)) (bd_nfp bd);
         malloc_token Ews (tarray tuchar (bd_cl bd + 1)) (bd_cfp bd);
         data_at_ Ews (tarray tuchar (bd_cl bd + 1)) (bd_cfp bd);
         data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh t_gzh hp; data_at_ Tsh t_strm sp; mem_mgr gv;
         deflate_globals gv; version_at gv vlit])).

(* A2 (msuf 35, before deflateInit2): the contents drawn; stream_defaults done, the stream split ([f]: its
   caller's fields, next_in = next_out = Z_NULL, avail_in = avail_out = 0, msg undefined (Vundef, None)) *)
Definition A2 (bs : bsetup) (f : sfields) (dt : Z) : environ -> mpred :=
  let bd := bs_d bs in
  PROPx [bs_ok bs; bound_facts Bpre Brun; Obligations.ob_dstream_to_end;
         sf_nin f = nullval; sf_ain f = 0; sf_nout f = nullval; sf_aout f = 0; sf_msg f = None]
  (LOCALx (draw_locals bd)
  (SEPx [sf_at f;
         field_at Ews t_strm (DOT _zalloc) nullval sp; field_at Ews t_strm (DOT _zfree) nullval sp;
         field_at Ews t_strm (DOT _opaque) nullval sp; field_at Ews t_strm (DOT _data_type) (vi dt) sp;
         field_at Ews t_strm (DOT _state) Vundef sp; field_at_ Ews t_strm (DOT _reserved) sp;
         strm_pad sp; data_at_ Ecomp t_strm sp;
         obj (bd_datap bd) (bs_data bs); obj (bd_dictp bd) (bs_dict bs);
         hmem bs false;
         data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; deflate_globals gv; version_at gv vlit])).

(* SA (msuf 37, 38, 39): a live stream after deflateInit2 returned Z_OK; [ds]: a dictionary was set (false
   before part_dict, dset bs after it); [hd]: part_head done *)
Definition SA (bs : bsetup) (ds hd : bool) (s : dstate) (f : sfields) : environ -> mpred :=
  let bd := bs_d bs in
  PROPx [bs_ok bs; bound_facts Bpre Brun; Obligations.ob_dstream_to_end;
         Bpre (bd_level bd) (bd_wbits bd) (bd_mem bd) (bd_strategy bd) ds s (sf_tin f) (sf_tout f) (sf_adler f);
         d_gzhead s = (if andb hd (hset bs) then Some (hdr_of bs) else None);
         msg_ok (sf_msg f) (sf_msgv f); is_pointer_or_null (sf_nin f)]
  (LOCALx (draw_locals bd)
  (SEPx [live bs hd s f; obj (bd_datap bd) (bs_data bs); obj (bd_dictp bd) (bs_dict bs);
         data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; deflate_globals gv; TT])).

(** ** The loop *)
Definition fin_flag (fin : bool) : Z := if fin then 1 else 0.

Definition loop_locals (bs : bsetup) (b pos : Z) (fin : bool) : list localdef :=
  [temp _data (bd_datap (bs_d bs)); temp _n (vi (bd_n (bs_d bs))); temp _bound (vl b);
   temp _pos (vi pos); temp _finishing (vi (fin_flag fin));
   lvar _osnap (tptr tuchar) vosn; lvar _h t_gzh hp; lvar _s t_strm sp; gvars gv].

Definition J_ok (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate) (f : sfields) : Prop :=
  bs_ok bs /\ bound_facts Bpre Brun /\ Obligations.ob_dstream_to_end /\
  Brun (bd_n (bs_d bs)) b pos fin s (sf_tin f) (sf_tout f) (sf_adler f) /\
  d_gzhead s = (if hset bs then Some (hdr_of bs) else None) /\ msg_ok (sf_msg f) (sf_msgv f) /\
  0 <= pos <= bd_n (bs_d bs) /\ 0 <= b <= 4294967295.

(* J (msuf 42, the loop head): [pos] bytes consumed, [fin]: Z_FINISH given, bound b *)
Definition J (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate) (f : sfields) : environ -> mpred :=
  PROPx [J_ok bs b pos fin s f]
  (LOCALx (loop_locals bs b pos fin)
  (SEPx [live bs true s f; obj (bd_datap (bs_d bs)) (bs_data bs);
         data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; deflate_globals gv; TT])).

Definition J_inv (bs : bsetup) (b : Z) : environ -> mpred :=
  EX pos : Z, EX fin : bool, EX s : dstate, EX f : sfields, J bs b pos fin s f.

(* E (msuf 43, after the loop: deflate returned Z_STREAM_END) *)
Definition E (bs : bsetup) (s : dstate) (f : sfields) : environ -> mpred :=
  PROPx [bs_ok bs; Obligations.ob_dstream_to_end;
         d_gzhead s = (if hset bs then Some (hdr_of bs) else None)]
  (LOCALx [lvar _osnap (tptr tuchar) vosn; lvar _h t_gzh hp; lvar _s t_strm sp; gvars gv]
  (SEPx [live bs true s f; data_at_ Tsh (tptr tuchar) vosn; mem_mgr gv; TT])).

Definition E_inv (bs : bsetup) : environ -> mpred := EX s : dstate, EX f : sfields, E bs s f.

(* the loop body's postcondition *)
Definition Rbody (bs : bsetup) (b : Z) : ret_assert :=
  loop1_ret_assert (J_inv bs b) (overridePost (E_inv bs) Rm_ret).

(* one iteration's choices: the input object ib holds data[pos..lim), the output space ob of aout bytes holds
   the arbitrary bytes obs (osnap's object q the same), [fin']: Z_FINISH given after this iteration's choice *)
Record citer := mkCI {
  ci_lim : Z; ci_aout : Z; ci_fin : bool; ci_ib : val; ci_ob : val; ci_q : val; ci_obs : list Z }.

Definition ci_inb (bs : bsetup) (pos : Z) (ci : citer) : list Z := sublist pos (ci_lim ci) (bs_data bs).
Definition ci_flush (ci : citer) : Z := if ci_fin ci then Z_FINISH else Z_NO_FLUSH.

Definition ci_ok (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate) (f : sfields) (ci : citer) : Prop :=
  J_ok bs b pos fin s f /\
  pos <= ci_lim ci <= bd_n (bs_d bs) /\ (fin = true -> ci_fin ci = true) /\
  (ci_fin ci = true -> ci_lim ci = bd_n (bs_d bs)) /\
  0 <= ci_aout ci <= 1048576 /\ Zlength (ci_obs ci) = ci_aout ci /\ bytes (ci_obs ci) /\
  isptr (ci_ib ci) /\ isptr (ci_ob ci) /\ isptr (ci_q ci).

Definition B_locals (bs : bsetup) (b pos : Z) (ci : citer) : list localdef :=
  [temp _lim (vi (ci_lim ci)); temp _ain (vi (ci_lim ci - pos)); temp _aout (vi (ci_aout ci));
   temp _ib (ci_ib ci); temp _ob (ci_ob ci)] ++ loop_locals bs b pos (ci_fin ci).

(* the iteration's three objects *)
Definition iobjs (bs : bsetup) (pos : Z) (ci : citer) : mpred :=
  obj (ci_ib ci) (ci_inb bs pos ci) * obj (ci_ob ci) (ci_obs ci) * obj (ci_q ci) (ci_obs ci).

(* B1 (lsuf 11, before s.next_in = ib) *)
Definition B1 (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate) (f : sfields) (ci : citer) : environ -> mpred :=
  PROPx [ci_ok bs b pos fin s f ci]
  (LOCALx (B_locals bs b pos ci)
  (SEPx [live bs true s f; iobjs bs pos ci; obj (bd_datap (bs_d bs)) (bs_data bs);
         data_at Tsh (tptr tuchar) (ci_q ci) vosn; mem_mgr gv; deflate_globals gv; TT])).

(* what the call did (bf_split of LawFacts): its result [code], the state [s'] and stream [z'] after it *)
Definition step_ok (bs : bsetup) (b pos : Z) (s : dstate) (f : sfields) (ci : citer)
    (s' : dstate) (z' : strm) (code : Z) : Prop :=
  let inb := ci_inb bs pos ci in
  c_deflate s (zcall inb 0 (Zlength inb) (sf_tin f) (ci_aout ci) (sf_tout f) (sf_adler f) (sf_msg f))
    (ci_flush ci) = Some (s', z', code) /\
  d_gzhead s' = d_gzhead s /\ (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
  0 <= z_avail_in z' <= Zlength inb /\ z_total_out z' <= b /\
  (code <> Z_STREAM_END ->
   Brun (bd_n (bs_d bs)) b (pos + Zlength inb - z_avail_in z') (ci_flush ci =? Z_FINISH) s'
        (z_total_in z') (z_total_out z') (z_adler z')).

(* the caller's fields after the call *)
Definition sf_after (ci : citer) (z' : strm) (msgv' : val) : sfields :=
  mkSF (offset_val (z_next_in z') (ci_ib ci)) (z_avail_in z') (z_total_in z')
       (offset_val (Zlength (z_out z')) (ci_ob ci)) (z_avail_out z') (z_total_out z') (z_msg z') msgv'
       (z_adler z').

(* B2 (lsuf 16, after r = deflate(..)) *)
Definition B2 (bs : bsetup) (b pos : Z) (fin : bool) (s : dstate) (f : sfields) (ci : citer)
    (s' : dstate) (z' : strm) (code : Z) (msgv' : val) : environ -> mpred :=
  PROPx [ci_ok bs b pos fin s f ci; step_ok bs b pos s f ci s' z' code; msg_ok (z_msg z') msgv']
  (LOCALx (temp _r (vi code) :: B_locals bs b pos ci)
  (SEPx [live bs true s' (sf_after ci z' msgv');
         obj (ci_ib ci) (ci_inb bs pos ci);
         malloc_token Ews (tarray tuchar (ci_aout ci)) (ci_ob ci) *
         data_at Ews (tarray tuchar (ci_aout ci))
           (map vi (z_out z') ++ sublist (Zlength (z_out z')) (ci_aout ci) (map vi (ci_obs ci))) (ci_ob ci);
         obj (ci_q ci) (ci_obs ci); obj (bd_datap (bs_d bs)) (bs_data bs);
         data_at Tsh (tptr tuchar) (ci_q ci) vosn; mem_mgr gv; deflate_globals gv; TT])).

End Kit.

(** ** Memory lemmas for the returns (proved in SplitMem.v) *)
Definition split_mem_ok : Prop :=
  (* a live stream, at a return: the locals s and h back (TT takes the rest) *)
  (forall (sp hp : val) (gv : globals) (bs : bsetup) (hd : bool) (s : dstate) (f : sfields),
     Obligations.ob_dstream_to_end ->
     d_gzhead s = (if andb hd (hset bs) then Some (hdr_of bs) else None) ->
     live sp hp gv bs hd s f |-- data_at_ Tsh t_strm sp * data_at_ Tsh t_gzh hp * TT).

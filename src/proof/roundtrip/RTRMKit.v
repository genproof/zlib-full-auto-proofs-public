(* Law deflate_roundtrip: the kit of main's body proof (RTRMain.v), continuation-passing as
   deflate_api9/MainKit.v.

   - Delta_m (main's type context), POST_m (main's postcondition after start_function), POST_b (the postcondition
     of b0 = main's body without its final `return 0`: every suffix of b0 ends by a return, so its normal
     postcondition is FF);
   - the segments of b0 (0-based positions of its 24 statements: 0 deflate_run and its test, 1 deflateEnd,
     2 stream_defaults(&t), 3 iw, 4 inflateInit2, 5 `if (r != Z_OK) return 0`, 6 the inflateGetHeader block,
     7 the raw dictionary block, 8 exact_copy, 9 malloc(nf), 10 their null test, 11-14 the stores into t,
     15 inflate(&t, Z_FINISH), 16 the zlib dictionary block, 17 `if (r == Z_MEM_ERROR) return 0`, 18 r == END,
     19 avail_in/avail_out, 20 bytes_same(ob, data, nf), 21 the header checks, 22 inflateEnd, 23 return 0);
     seg k is b0 from position k on;
   - the assertions at the segments' boundaries (A1: after a successful run; A6: after a successful
     inflateInit2; A8: before exact_copy, with the live part L the call starts from; A16: after the first
     inflate(); A17: after the zlib dictionary block) and the pure facts between them (first_ok: what the
     inflate() call from L gives, by RTIIface.ifacts; call1_ok, fin_ok);
   - the memory of main's locals at a return (rm_dside_ret, rm_istream_ret).

   The gzip run with a header (R.head_set = 1) is ONE separate part (RTRSHdr.rms_hset1: from A6 to
   the end), since its inflateGetHeader call needs a header specification that accepts the harness's partly
   uninitialized gz_header (Spec5.head_rep needs defined fields and buffer bytes) and RTIIface.if_gzhead does
   not give h_xp/h_np/h_cp; the other segments are for head_set = 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Zlib.proof.roundtrip.RTRRunMem.
Require Zlib.proof.inflate_api.Spec5 Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Definition t_gzhL := Tstruct _gz_header_s noattr.

(** ** Type context and postconditions *)
(* the functions main calls with the specifications the segments are proved against (= RTRMainSpec.Gmain with
   Spec5's inflate_spec / inflateGetHeader_spec; fixed here so that a law using other specifications of these
   two functions (header-relaxed v6) moves the segments by subsumption: semax_body_subsumption / funspec_sub) *)
Definition Gm5 (I : api_inv) (Iend : dstate -> Prop) : funspecs :=
  [deflate_run_spec I Iend; deflateEnd_spec; stream_defaults_spec; exact_copy_spec;
   Zlib.proof.inflate_api.Spec5.inflateInit2__spec; Zlib.proof.inflate_api.Spec5.inflateGetHeader_spec;
   Zlib.proof.inflate_api.Spec5.inflateSetDictionary_spec; Zlib.proof.inflate_api.Spec5.inflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateEnd_spec;
   ref_adler32_spec; bytes_same_spec;
   Zlib.proof.inflate_api.Bodies5.zcalloc_i; Zlib.proof.inflate_api.Bodies5.zcfree_i;
   (_quickproof_malloc, malloc_spec'); gp_assert_spec].

Lemma Gm5_Gmain I Iend : Gm5 I Iend = Gmain I Iend.
Proof. reflexivity. Qed.

Definition Delta_m (I : api_inv) (Iend : dstate -> Prop) : tycontext :=
  func_tycontext f_main (QPvarspecs p) (Gm5 I Iend) nil.

Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

Definition POST_b : ret_assert := overridePost FF POST_m.

(** ** The segments *)
Fixpoint rm_drop (n : nat) (s : statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => rm_drop n' b
  | _, _ => Sskip
  end.
Definition rm_first (s : statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.
Definition rm_second (s : statement) : statement := match s with Ssequence _ b => b | _ => Sskip end.
Ltac rm_seg t := let x := eval cbv beta iota zeta delta [rm_drop rm_first rm_second f_main fn_body] in t in exact x.

Definition b0 : statement := ltac:(rm_seg (rm_first (fn_body f_main))).
Definition b0_ret : statement := ltac:(rm_seg (rm_second (fn_body f_main))).
Definition seg1 : statement := ltac:(rm_seg (rm_drop 1 (rm_first (fn_body f_main)))).
Definition seg6 : statement := ltac:(rm_seg (rm_drop 6 (rm_first (fn_body f_main)))).
Definition seg8 : statement := ltac:(rm_seg (rm_drop 8 (rm_first (fn_body f_main)))).
Definition seg16 : statement := ltac:(rm_seg (rm_drop 16 (rm_first (fn_body f_main)))).
Definition seg17 : statement := ltac:(rm_seg (rm_drop 17 (rm_first (fn_body f_main)))).

Lemma rm_body_eq : fn_body f_main = Ssequence b0 b0_ret.
Proof. reflexivity. Qed.
Lemma rm_b0_eq : exists x, b0 = Ssequence x seg1.
Proof. eexists. reflexivity. Qed.

(** ** The run's values *)
Definition rm_D (rf : rfinal) : list Z := sublist 0 (rf_nf rf) (rs_data (rf_rs rf)).
(* inflateInit2's windowBits as main computes it from R.wrap and R.wb *)
Definition rm_iw (rf : rfinal) : Z := iw_of (rf_wrap rf) (wb_of (rs_wbits (rf_rs rf))).
(* a zlib stream with a dictionary: the first inflate() stops at Z_NEED_DICT *)
Definition rm_zd (rf : rfinal) : bool := (rf_wrap rf =? 1) && (rf_dset rf =? 1).

(* struct drun, the run's objects and main's half of R after deflateEnd *)
Definition rm_dside (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in
  drun_rest rs (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits rs))) (rf_nf rf) (rf_dset rf) (rf_hset rf)
    (Zlength (rf_O rf)) 1 vR *
  hpart (rf_hset rf) vR * hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of rs) *
  obj (rs_datap rs) (rs_data rs) * obj (rs_dictp rs) (rs_dict rs) * comp_at (rf_O rf) (rs_compp rs) *
  data_at_ (Share.comp Ews) t_drun vR.

(* the stream fields after stream_defaults and a successful inflateInit2 *)
Definition rm_zinit (z : zfields) : Prop :=
  zf_ok z /\ zf_ni z = nullval /\ zf_ai z = 0 /\ zf_no z = nullval /\ zf_ao z = 0 /\ zf_tout z = 0 /\
  zf_msg z = None.

(** ** The pure facts of the inflate() calls *)

(* the zlib dictionary: inflateSetDictionary from L1 (the stream after Z_NEED_DICT) and the second call *)
Definition zd_cont (rf : rfinal) (L1 : live) : Prop :=
  let O := rf_O rf in let O6 := sublist 6 (Zlength O) O in
  forall alloc_ok winp z1, live_ok L1 ->
    let sd := setdict_f (rf_dict rf) alloc_ok winp z1 L1 in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> forall z2 res2,
       live_ok (thd3 sd) -> zcall_ok z2 O6 (rm_D rf) ->
       Zlib.proof.inflate.Model2.run2 4 lenfix_list distfix_list (m_init z2 (thd3 sd) O6) res2 ->
       rdone O6 (rm_D rf) res2).

(* the model's result of the first inflate() call *)
Definition res_ok (rf : rfinal) (res : result) : Prop :=
  if rm_zd rf then
    (* no Z_MEM_ERROR here: main asserts r == Z_NEED_DICT (inflate returns Z_NEED_DICT before any window
       allocation; RTIIface.if_zdict's conclusion still allows Z_MEM_ERROR) *)
    r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
    m_aout (r_m res) = Zlength (rm_D rf) /\ m_tout (r_m res) = 0 /\
    m_adler (r_m res) = Zlib.proof.adler32.Model.ref_adler32 1 (rf_dict rf) /\
    (forall L1, l_s L1 = m_s (r_m res) -> l_h L1 = m_h (r_m res) -> zd_cont rf L1)
  else rdone (rf_O rf) (rm_D rf) res.

(* the first inflate() call from the live part L, offered all of O and |D| bytes of space *)
Definition first_ok (rf : rfinal) (L : live) : Prop :=
  forall z res, live_ok L -> zcall_ok z (rf_O rf) (rm_D rf) ->
    Zlib.proof.inflate.Model2.run2 4 lenfix_list distfix_list (m_init z L (rf_O rf)) res -> res_ok rf res.

(* the first inflate() call on a zlib stream with a dictionary does not fail to allocate (it stops at Z_NEED_DICT
   after the 6 header bytes, before any window allocation): what RTIIface.if_zdict's conclusion lacks *)
Definition zd_nomem : Prop :=
  forall wb dict D O sp z res,
    Zlib.proof.roundtrip.RTFinal.dfinal dict 1 wb None D O -> dict <> [] -> Zlength dict <= 32768 ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 -> live_ok (init_live sp 0) -> zcall_ok z O D ->
    Zlib.proof.inflate.Model2.run2 4 lenfix_list distfix_list (m_init z (init_live sp 0) O) res ->
    r_ret res <> Z_MEM_ERROR.

(* RTIIface.ifacts for the run (without a gzip header): the stream inflateInit2 left (sp: its state) and, for a
   raw dictionary, the stream after inflateSetDictionary *)
Definition first_facts (rf : rfinal) : Prop :=
  forall sp,
  (~ (rf_wrap rf = 0 /\ rf_dset rf = 1) -> first_ok rf (init_live sp (rm_iw rf))) /\
  (rf_wrap rf = 0 -> rf_dset rf = 1 -> live_ok (init_live sp (rm_iw rf)) ->
   forall alloc_ok winp z,
     let sd := setdict_f (rf_dict rf) alloc_ok winp z (init_live sp (rm_iw rf)) in
     (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\ (fst3 sd = Z_OK -> first_ok rf (thd3 sd))).

(* the end of the inflation: Z_MEM_ERROR, or Z_STREAM_END with all input consumed and the space filled with D *)
Definition fin_ok (rf : rfinal) (r : Z) (z1 : zfields) (ow : list Z) : Prop :=
  r = Z_MEM_ERROR \/ (r = Z_STREAM_END /\ zf_ai z1 = 0 /\ zf_ao z1 = 0 /\ ow = rm_D rf).

(* after the first inflate() call (ibp: the copy of O, obp: the output space), in main's terms *)
Definition call1_ok (rf : rfinal) (ibp obp : val) (r : Z) (z1 : zfields) (L1 : live) (ow : list Z) : Prop :=
  if rm_zd rf then
    r = Z_NEED_DICT /\ zf_ni z1 = offset_val 6 ibp /\ zf_ai z1 = Zlength (rf_O rf) - 6 /\
    zf_no z1 = offset_val 0 obp /\ zf_ao z1 = Zlength (rm_D rf) /\ zf_tout z1 = 0 /\
    zf_adler z1 = Zlib.proof.adler32.Model.ref_adler32 1 (rf_dict rf) /\ ow = [] /\ zd_cont rf L1
  else fin_ok rf r z1 ow.

(* the copy of O (exact_copy) and the output space (malloc(nf)) as inflate() takes them *)
Definition rm_ib (rf : rfinal) (ibp : val) : inbuf :=
  InBuf Ews ibp 0 (Zlength (rf_O rf)) (byte_vals (rf_O rf)).
Definition rm_ob (rf : rfinal) (obp : val) (cont : list val) : outbuf := OutBuf Ews obp 0 (rf_nf rf) cont.

(** ** The assertions *)

(* after deflate_run returned 1 with R.init = Z_OK (main's halves comp Ews of R and s) *)
Definition A1 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) : environ -> mpred :=
  PROP (rf_ok Iend vR rf)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (run_ok_at rf vR vs gv; data_at_ (Share.comp Ews) t_drun vR; data_at_ (Share.comp Ews) t_strmL vs;
       data_at_ Tsh t_strmL vt; data_at_ Tsh t_gzhL vih; mem_mgr gv; Rm gv; zfuncs gv).

(* after deflateEnd and a successful inflateInit2(&t, iw) (sp: the inflate state) *)
Definition A6 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields)
    (sp : val) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rm_zinit z)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z (Some (init_live sp (rm_iw rf))); data_at_ Tsh t_gzhL vih;
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* before exact_copy (no gzip header): the live part L the inflate() call starts from *)
Definition A8 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields)
    (L : live) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 0; rm_zinit z; first_ok rf L)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z (Some L); head_mem L; data_at_ Tsh t_gzhL vih;
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* after the first inflate() call (r = its result, z1/L1 the stream, ow the bytes written into the space whose
   contents before were cont) *)
Definition A16 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (ibp obp : val)
    (r : Z) (z1 : zfields) (L1 : live) (ow : list Z) (cont : list val) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 0; call1_ok rf ibp obp r z1 L1 ow; Zlength cont = rf_nf rf)
  LOCAL (temp _r (vi r); temp _ib ibp; temp _ob obp;
         lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z1 (Some L1); head_mem L1; data_at_ Tsh t_gzhL vih;
       in_rep (rm_ib rf ibp); in_tok true (rm_ib rf ibp);
       out_rep (rm_ob rf obp cont) ow; out_tok true (Some (rm_ob rf obp cont));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* after the zlib dictionary block: the last inflate() call's result *)
Definition A17 (Iend : dstate -> Prop) (rf : rfinal) (vR vs vt vih : val) (gv : globals) (ibp obp : val)
    (r : Z) (z1 : zfields) (L1 : live) (ow : list Z) (cont : list val) : environ -> mpred :=
  PROP (rf_ok Iend vR rf; rf_hset rf = 0; fin_ok rf r z1 ow; Zlength cont = rf_nf rf)
  LOCAL (temp _r (vi r); temp _ib ibp; temp _ob obp;
         lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z1 (Some L1); head_mem L1; data_at_ Tsh t_gzhL vih;
       in_rep (rm_ib rf ibp); in_tok true (rm_ib rf ibp);
       out_rep (rm_ob rf obp cont) ow; out_tok true (Some (rm_ob rf obp cont));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(** ** The memory of main's locals at a return *)

Lemma rm_dside_ret Iend vR rf :
  rf_ok Iend vR rf -> rm_dside rf vR |-- data_at_ Tsh t_drun vR * TT.
Proof.
  intros OK. destruct OK as (_ & _ & _ & _ & _ & _ & _ & HH & _).
  pose proof RTRRunMem.run_mem as (_ & M2 & _).
  unfold rm_dside.
  sep_apply (M2 (rf_rs rf) (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits (rf_rs rf)))) (rf_nf rf) (rf_dset rf)
               (rf_hset rf) (Zlength (rf_O rf)) 1 vR (rf_s rf) (rf_ghp rf) HH).
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  cancel.
Qed.

Definition rm_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma rm_strm_cs sh (v : rm_strm_tuple) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v q = @data_at CS sh t_strmL v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition rm_strm_undef : rm_strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma rm_strm_undef_cs sh q :
  @data_at_ CS sh t_strmL q = @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm rm_strm_undef q.
Proof. unfold data_at_. rewrite rm_strm_cs. reflexivity. Qed.

(* a struct z_stream at the inflate unit's compspecs (any fields) is the local's memory *)
Lemma rm_strm_to_undef sh (v : rm_strm_tuple) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v q |-- @data_at_ CS sh t_strmL q.
Proof. rewrite rm_strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

Lemma rm_istream_ret gv vt z st :
  istream gv Tsh vt z st |-- data_at_ Tsh t_strmL vt * TT.
Proof.
  unfold istream, zstrm_at, Zlib.proof.inflate.Rep.strm_rep. destruct st as [L | ]; Intros.
  - sep_apply rm_strm_to_undef. cancel.
  - sep_apply rm_strm_to_undef. cancel.
Qed.

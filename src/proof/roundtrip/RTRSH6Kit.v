(* Law deflate_roundtrip (gzip header, part H6): the kit of positions 6-7 with a gzip header (R.head_set = 1):
   the memory lemmas of the inflateGetHeader block (rmh_raw: main's gz_header as hraw6 of RTRSKit.rm_h0; rmh_toks:
   the buffers' malloc tokens as hdr_btoks and rm_htoks), rm_dside opened at the four fields the block reads
   (rmh_split / rmh_join), the block's statements (hs_then = the body of `if (R.head_set)`, hs_tail = from the NULL
   test on, hs_nt, hs_call) and the assertions between the parts (rmh_P0 before the block's body, rmh_PA after the
   stores, rmh_PN after the NULL test, rmh_Q6 after the block). *)
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
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.roundtrip.RTRMSeg6.
Require Zlib.proof.roundtrip.RTRMSeg8.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* ih after the stores *)
Definition rmh_ih (rf : rfinal) (xb nb cb : val) : rm_head_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (xb, (Vundef, (Vint (Int.repr (Zlength (rs_xf (rf_rs rf)))),
   (nb, (Vint (Int.repr (Zlength (rs_nm (rf_rs rf)) + 1)),
   (cb, (Vint (Int.repr (Zlength (rs_cm (rf_rs rf)) + 1)), (Vundef, Vundef)))))))))))).

(* the gz_header main hands to inflateGetHeader: its stores, the other fields undefined, the fresh buffers *)
Lemma rmh_raw rf vih xb nb cb :
  xb <> nullval -> nb <> nullval -> cb <> nullval ->
  data_at Tsh t_gzhL (rmh_ih rf xb nb cb) vih *
  data_at_ Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb *
  data_at_ Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb *
  data_at_ Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb
  |-- hraw6 Tsh vih xb nb cb (rm_h0 rf).
Proof.
  intros Nx Nn Nc. unfold hraw6, rm_h0, hbuf6, rm_x, rm_nm, rm_cm, rmh_ih.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. simpl h_xp. simpl h_np. simpl h_cp.
  simpl h_extra_max. simpl h_name_max. simpl h_comm_max.
  Exists Vundef Vundef Vundef Vundef Vundef Vundef Vundef.
  Exists (Zrepeat Vundef (Zlength (rs_xf (rf_rs rf)))) (Zrepeat Vundef (Zlength (rs_nm (rf_rs rf)) + 1))
         (Zrepeat Vundef (Zlength (rs_cm (rf_rs rf)) + 1)).
  destruct (eq_dec xb nullval); [contradiction | ]. destruct (eq_dec nb nullval); [contradiction | ].
  destruct (eq_dec cb nullval); [contradiction | ].
  rewrite !(bytes_cs Zlib.units.Inflate.CS CS).
  rewrite rm_head_cs.
  pose proof (Zlength_nonneg (rs_xf (rf_rs rf))). pose proof (Zlength_nonneg (rs_nm (rf_rs rf))).
  pose proof (Zlength_nonneg (rs_cm (rf_rs rf))).
  rewrite !Zlength_Zrepeat by lia.
  entailer!.
Qed.

Lemma rmh_tok xb n : xb <> nullval -> @malloc_token CS Ews (tarray tuchar n) xb |-- btok xb n * nbtok xb n.
Proof.
  intros Nx. unfold btok, nbtok. destruct (eq_dec xb nullval); [contradiction | ].
  destruct (zeq n 0).
  - subst. rewrite RTRMSeg8.rm8_tok_cs. cancel.
  - cancel.
Qed.

Lemma rmh_toks rf xb nb cb : xb <> nullval -> nb <> nullval -> cb <> nullval ->
  @malloc_token CS Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb *
  @malloc_token CS Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb *
  @malloc_token CS Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb
  |-- hdr_btoks xb nb cb (rm_h0 rf) * rm_htoks rf xb nb cb.
Proof.
  intros Nx Nn Nc. unfold hdr_btoks, rm_htoks, rm_h0, rm_x, rm_nm, rm_cm.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. simpl h_extra_max. simpl h_name_max. simpl h_comm_max.
  sep_apply (rmh_tok xb (Zlength (rs_xf (rf_rs rf))) Nx). sep_apply (rmh_tok nb (Zlength (rs_nm (rf_rs rf)) + 1) Nn).
  sep_apply (rmh_tok cb (Zlength (rs_cm (rf_rs rf)) + 1) Nc). cancel.
Qed.

Lemma rmh_hwf rf : rs_ok (rf_rs rf) -> hwf (rm_h0 rf).
Proof.
  intros RS. assert (Lx: Zlength (rs_xf (rf_rs rf)) <= 4096 /\ Zlength (rs_nm (rf_rs rf)) <= 4096 /\
              Zlength (rs_cm (rf_rs rf)) <= 4096) by (unfold rs_ok in RS; tauto).
  pose proof (Zlength_nonneg (rs_xf (rf_rs rf))). pose proof (Zlength_nonneg (rs_nm (rf_rs rf))).
  pose proof (Zlength_nonneg (rs_cm (rf_rs rf))).
  unfold rm_h0, rm_x, rm_nm, rm_cm. rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  constructor; simpl; unfold srange, lrange, urange, bytes_ok; try rep_lia;
    (split; [rewrite Zlength_Zrepeat by lia; reflexivity | unfold Zrepeat; apply Forall_repeat; rep_lia]).
Qed.

Lemma rmh_iw rf : rf_wrap rf = 2 -> rm_iw rf = 32.
Proof. intros W. unfold rm_iw, iw_of. rewrite W. reflexivity. Qed.

Lemma rmh_attach vt sp : isptr vt -> hattach_ok vt (Some (init_live sp 32)).
Proof.
  intros P. unfold hattach_ok, is_live. destruct (eq_dec vt nullval); [subst; contradiction | ].
  vm_compute. intros _. left. reflexivity.
Qed.

Lemma rmh_ret_ok vt sp : isptr vt ->
  (match is_live vt (Some (init_live sp 32)) with
   | Some L => if Z.land (i_wrap (l_s L)) 2 =? 0 then Z_STREAM_ERROR else Z_OK
   | None => Z_STREAM_ERROR end) = Z_OK.
Proof. intros P. unfold is_live. destruct (eq_dec vt nullval); [subst; contradiction | ]. reflexivity. Qed.

(* rm_dside without the four fields the inflateGetHeader block reads *)
Definition rmh_drest (rf : rfinal) (vR : val) : mpred :=
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  malloc_token Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (rs_dictp (rf_rs rf)) *
  data_at Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (map vi (rs_dict (rf_rs rf))) (rs_dictp (rf_rs rf)) *
  field_at Ews t_drun (DOT _level) (vi (rs_level (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _method) (vi (rs_method (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy (rf_rs rf))) vR *
  field_at Ews t_drun (DOT _init) (vi 0) vR *
  field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _data) (rs_datap (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _nf) (vi (rf_nf rf)) vR *
  field_at Ews t_drun (DOT _xf) (rs_xfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _nf_) (rs_nfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _cf) (rs_cfp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _comp) (rs_compp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _clen) (vl (Zlength (rf_O rf))) vR *
  field_at Ews t_drun (DOT _ended) (vi 1) vR *
  field_at Ews t_drun (DOT _api_ok) (vi 1) vR *
  drun_pad vR *
  hpart (rf_hset rf) vR * hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of (rf_rs rf)) *
  obj (rs_datap (rf_rs rf)) (rs_data (rf_rs rf)) * comp_at (rf_O rf) (rs_compp (rf_rs rf)) *
  data_at_ (Share.comp Ews) t_drun vR.

Lemma rmh_split rf vR :
  rm_dside rf vR = field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm (rf_rs rf)))) vR * rmh_drest rf vR.
Proof. rewrite rm6_open_eq. unfold rm6_open, rm6_rest, rmh_drest. apply pred_ext; cancel. Qed.

Lemma rmh_join rf vR :
  field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm (rf_rs rf)))) vR * rmh_drest rf vR |-- rm_dside rf vR.
Proof. rewrite rmh_split. apply derives_refl. Qed.

Lemma rmh_ih0 vih :
  data_at_ Tsh t_gzhL vih =
  data_at Tsh t_gzhL ((Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
                        (Vundef, (Vundef, Vundef)))))))))))) : rm_head_tuple) vih.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.


(** ** The statements *)
Definition hs_then : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [seg6] in
          (match seg6 with Ssequence (Ssequence _ (Sifthenelse _ t _)) _ => t | _ => Sskip end) in exact x).
Ltac rmh_seg t := let x := eval cbv beta iota zeta delta [rm_drop rm_first rm_second hs_then] in t in exact x.
Definition hs_tail : statement := ltac:(rmh_seg (rm_drop 6 hs_then)).
Definition hs_nt : statement := ltac:(rmh_seg (rm_first (rm_drop 6 hs_then))).
Definition hs_call : statement := ltac:(rmh_seg (rm_second (rm_drop 6 hs_then))).
(* the NULL test: the two conditional expressions (hs_t, setting _t'10) and `if (_t'10) return 0;` (hs_ret) *)
Definition hs_t : statement := ltac:(rmh_seg (rm_first (rm_first (rm_drop 6 hs_then)))).
Definition hs_ret : statement := ltac:(rmh_seg (rm_second (rm_first (rm_drop 6 hs_then)))).
Lemma hs_tail_eq : hs_tail = Ssequence (Ssequence hs_t hs_ret) hs_call.
Proof. reflexivity. Qed.

(** ** The assertions *)
(* the body of `if (R.head_set)` starts *)
Definition rmh_P0 (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields) (sp : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'72 (vi (rf_hset rf)); lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt;
         lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z (Some (init_live sp (rm_iw rf))); data_at_ Tsh t_gzhL vih;
       field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR;
       field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf (rf_rs rf)))) vR;
       field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm (rf_rs rf)))) vR;
       field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm (rf_rs rf)))) vR;
       rmh_drest rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT).

(* after the three mallocs and the stores into ih *)
Definition rmh_PA (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields) (sp xb nb cb : val) :
    environ -> mpred :=
  PROP ()
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec xb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb *
         data_at_ Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb;
       if eq_dec nb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb *
         data_at_ Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb;
       if eq_dec cb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb *
         data_at_ Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb;
       data_at Tsh t_gzhL (rmh_ih rf xb nb cb) vih;
       istream gv Tsh vt z (Some (init_live sp (rm_iw rf)));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; Rm gv; zfuncs gv; TT).

(* the value of `ih.extra == NULL || ih.name == NULL || ih.comment == NULL` *)
Definition rmh_any (xb nb cb : val) : int :=
  if eq_dec xb nullval then Int.one else if eq_dec nb nullval then Int.one else
  if eq_dec cb nullval then Int.one else Int.zero.

(* after the conditional expressions of the NULL test *)
Definition rmh_PT (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields) (sp xb nb cb : val) :
    environ -> mpred :=
  PROP ()
  LOCAL (temp _t'10 (Vint (rmh_any xb nb cb));
         lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec xb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb *
         data_at_ Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb;
       if eq_dec nb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb *
         data_at_ Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb;
       if eq_dec cb nullval then emp else
         malloc_token Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb *
         data_at_ Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb;
       data_at Tsh t_gzhL (rmh_ih rf xb nb cb) vih;
       istream gv Tsh vt z (Some (init_live sp (rm_iw rf)));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; Rm gv; zfuncs gv; TT).

(* after the NULL test: the three buffers allocated *)
Definition rmh_PN (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields) (sp xb nb cb : val) :
    environ -> mpred :=
  PROP (xb <> nullval; nb <> nullval; cb <> nullval)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (mem_mgr gv;
       malloc_token Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb;
       data_at_ Ews (tarray tuchar (Zlength (rs_xf (rf_rs rf)))) xb;
       malloc_token Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb;
       data_at_ Ews (tarray tuchar (Zlength (rs_nm (rf_rs rf)) + 1)) nb;
       malloc_token Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb;
       data_at_ Ews (tarray tuchar (Zlength (rs_cm (rf_rs rf)) + 1)) cb;
       data_at Tsh t_gzhL (rmh_ih rf xb nb cb) vih;
       istream gv Tsh vt z (Some (init_live sp (rm_iw rf)));
       rm_dside rf vR; data_at_ Tsh t_strmL vs; Rm gv; zfuncs gv; TT).

(* after the inflateGetHeader block *)
Definition rmh_Q6 (rf : rfinal) (vR vs vt vih : val) (gv : globals) (z : zfields) (sp : val) : environ -> mpred :=
  (EX xb : val, EX nb : val, EX cb : val,
    PROP ()
    LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
    SEP (istream gv Tsh vt z (Some (rm_hL rf sp vih xb nb cb)); head_mem6 (rm_hL rf sp vih xb nb cb);
         rm_htoks rf xb nb cb; rm_dside rf vR; data_at_ Tsh t_strmL vs; mem_mgr gv; Rm gv; zfuncs gv; TT))%assert.

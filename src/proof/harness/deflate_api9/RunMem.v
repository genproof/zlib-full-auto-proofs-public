(* Law deflate_api: the memory lemmas of RunKit.run_mem_ok (the z_stream and struct drun given back). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.


(** ** struct drun, field by field (VST's unfold_data_at diverges on the law's compspecs) *)
(* struct drun, field by field, with its two padding holes: after head_set (68..72) and after cl (188..192)
   (= RunSpec v2's drun_pad); (unfold_data_at diverges on the law's compspecs) *)
Lemma drun_split_raw Rp :
  data_at_ Ews (Tstruct _drun noattr) Rp =
  field_at_ Ews (Tstruct _drun noattr) (DOT _level) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _method) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _wbits) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _mem) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _strategy) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _init) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _wrap) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _wb) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _data) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _n) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _nf) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _dict) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _dlen) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _dict_set) Rp *
  ((field_at_ Ews (Tstruct _drun noattr) (DOT _head_set) Rp * spacer Ews 68 72 Rp) *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _h) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _xf) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _nf_) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _cf) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _xlen) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _nl) Rp *
  ((field_at_ Ews (Tstruct _drun noattr) (DOT _cl) Rp * spacer Ews 188 192 Rp) *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _comp) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _clen) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _ended) Rp *
  (field_at_ Ews (Tstruct _drun noattr) (DOT _api_ok) Rp))))))))))))))))))))))))).
Proof.
  set (V := default_val (nested_field_type (Tstruct _drun noattr) [])).
  change (data_at_ Ews (Tstruct _drun noattr) Rp) with (field_at Ews (Tstruct _drun noattr) [] V Rp).
  rewrite (@field_at_Tstruct CS Ews (Tstruct _drun noattr) [] _drun noattr V V Rp eq_refl (JMeq_refl _)).
  unfold nested_sfieldlist_at.
  let L := eval vm_compute in (co_members (get_co _drun)) in
  change (co_members (get_co _drun)) with L; set (M := L).
  unfold M at 1 2.
  lazy beta iota zeta delta [aggregate_pred.struct_pred aggregate_pred.aggregate_pred.struct_pred
    list_rect withspacer].
  do 7 (match goal with |- context [Z.eq_dec ?a 0] => first [rewrite (if_true _ (Z.eq_dec a 0)) by (unfold M; vm_compute; reflexivity) | rewrite (if_false _ (Z.eq_dec a 0)) by (unfold M; vm_compute; discriminate)] end).
  do 7 (match goal with |- context [Z.eq_dec ?a 0] => first [rewrite (if_true _ (Z.eq_dec a 0)) by (unfold M; vm_compute; reflexivity) | rewrite (if_false _ (Z.eq_dec a 0)) by (unfold M; vm_compute; discriminate)] end).
  do 7 (match goal with |- context [Z.eq_dec ?a 0] => first [rewrite (if_true _ (Z.eq_dec a 0)) by (unfold M; vm_compute; reflexivity) | rewrite (if_false _ (Z.eq_dec a 0)) by (unfold M; vm_compute; discriminate)] end).
  repeat (match goal with |- context [Z.eq_dec ?a 0] => first [rewrite (if_true _ (Z.eq_dec a 0)) by (unfold M; vm_compute; reflexivity) | rewrite (if_false _ (Z.eq_dec a 0)) by (unfold M; vm_compute; discriminate)] end).
  repeat match goal with |- context [spacer Ews ?a ?b Rp] =>
    lazymatch a with 68 => fail | 188 => fail | _ =>
    let a0 := eval cbv delta [M] in a in let b0 := eval cbv delta [M] in b in
    let a' := eval vm_compute in a0 in let b' := eval vm_compute in b0 in
    change (spacer Ews a b Rp) with (spacer Ews a' b' Rp) end end.
  subst V.
  reflexivity.
Qed.

Lemma drun_split Rp :
  data_at_ Ews t_drun Rp =
  field_at_ Ews t_drun (DOT _level) Rp *
  field_at_ Ews t_drun (DOT _method) Rp *
  field_at_ Ews t_drun (DOT _wbits) Rp *
  field_at_ Ews t_drun (DOT _mem) Rp *
  field_at_ Ews t_drun (DOT _strategy) Rp *
  field_at_ Ews t_drun (DOT _init) Rp *
  field_at_ Ews t_drun (DOT _wrap) Rp *
  field_at_ Ews t_drun (DOT _wb) Rp *
  field_at_ Ews t_drun (DOT _data) Rp *
  field_at_ Ews t_drun (DOT _n) Rp *
  field_at_ Ews t_drun (DOT _nf) Rp *
  field_at_ Ews t_drun (DOT _dict) Rp *
  field_at_ Ews t_drun (DOT _dlen) Rp *
  field_at_ Ews t_drun (DOT _dict_set) Rp *
  field_at_ Ews t_drun (DOT _head_set) Rp *
  field_at_ Ews t_drun (DOT _h) Rp *
  field_at_ Ews t_drun (DOT _xf) Rp *
  field_at_ Ews t_drun (DOT _nf_) Rp *
  field_at_ Ews t_drun (DOT _cf) Rp *
  field_at_ Ews t_drun (DOT _xlen) Rp *
  field_at_ Ews t_drun (DOT _nl) Rp *
  field_at_ Ews t_drun (DOT _cl) Rp *
  field_at_ Ews t_drun (DOT _comp) Rp *
  field_at_ Ews t_drun (DOT _clen) Rp *
  field_at_ Ews t_drun (DOT _ended) Rp *
  field_at_ Ews t_drun (DOT _api_ok) Rp *
  (spacer Ews 68 72 Rp * spacer Ews 188 192 Rp).
Proof.
  unfold t_drun. rewrite drun_split_raw.
  apply pred_ext; cancel.
Qed.



(** ** z_stream: its 14 fields and its padding (at DCS.CS) *)
Lemma strm_fields_pad (sp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_in) a1 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_in) a2 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._total_in) a3 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._next_out) a4 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._avail_out) a5 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._total_out) a6 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._msg) a7 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._adler) a8 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._state) a9 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zalloc) a10 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._zfree) a11 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._opaque) a12 sp *
  @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) a13 sp *
  @field_at_ DCS.CS Ews t_strm (DOT deflate.code._reserved) sp * strm_pad sp
  |-- @data_at_ DCS.CS Ews t_strm sp.
Proof.
  unfold_data_at (@data_at_ DCS.CS Ews t_strm sp).
  unfold strm_pad.
  cancel.
  unfold field_at_; apply derives_refl.
Qed.

(** ** gz_header: its 13 fields and its padding (at DCS.CS) *)
Lemma gzh_fields_pad (hp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._text) a1 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._time) a2 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._os) a3 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._extra) a4 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._extra_len) a5 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._name) a6 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._comment) a7 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._hcrc) a8 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._xflags) a9 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._extra_max) a10 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._name_max) a11 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._comm_max) a12 hp *
  @field_at DCS.CS Ews t_gzh (DOT deflate.code._done) a13 hp * gzh_pad hp
  |-- @data_at_ DCS.CS Ews t_gzh hp.
Proof.
  unfold_data_at (@data_at_ DCS.CS Ews t_gzh hp).
  unfold gzh_pad.
  cancel.
Qed.

Lemma gzh_data_at__cs (q : val) :
  @data_at_ DCS.CS Ews t_gzh q = @data_at_ CS Ews (Tstruct _gz_header_s noattr) q.
Proof.
  unfold data_at_. apply equal_f.
  apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma drun_h_of_gzh (Rp : val) :
  @data_at_ DCS.CS Ews t_gzh (hp_of Rp) |-- field_at_ Ews t_drun (DOT _h) Rp.
Proof.
  rewrite gzh_data_at__cs. unfold field_at_, hp_of. rewrite field_at_data_at.
  apply derives_refl.
Qed.

(* the data_type field of the z_stream, inside the state *)
Lemma dstate_dtype (s : dstate) (p : dptrs) (gv : globals) :
  dstate_at s p gv |-- (EX v : val, @field_at DCS.CS Ews t_strm (DOT deflate.code._data_type) v (p_strm p)) * TT.
Proof.
  unfold dstate_at, trees_at, dtype_at. Intros. Exists (vi (tr_data_type (fst (d_trm s)))). cancel.
Qed.

Lemma drun_fields rs init wrap wb nf dset hset clen ended Rp :
  drun_rest rs init wrap wb nf dset hset clen ended Rp * field_at_ Ews t_drun (DOT _h) Rp
  |-- data_at_ Ews t_drun Rp.
Proof.
  unfold drun_rest, drun_pad. rewrite drun_split. cancel.
Qed.

Lemma run_mem : run_mem_ok.
Proof.
  split; [|split].
  - intros os sp ghp gv nin ain tin nout aout tout msgv adler.
    rewrite <- strm_data_at__cs.
    unfold dstream, api_fields. destruct os as [s|].
    + Intros p. change (dstate_at' 2 s p gv) with (dstate_at s p gv).
      sep_apply dstate_dtype. Intros v. subst sp ghp.
      sep_apply (strm_fields_pad (p_strm p) nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv (vl adler)
                   (p_s p) (gv deflate.code._zcalloc) (gv deflate.code._zcfree) nullval v).
      cancel.
    + Intros za zf op dt.
      sep_apply (strm_fields_pad sp nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv (vl adler)
                   nullval za zf op dt).
      cancel.
  - intros rs init wrap wb nf dset hset clen ended Rp s ghp [[-> [-> Hg]] | [-> Hg]].
    + change (hpart 1 Rp) with (gzh_pad (hp_of Rp)).
      unfold hdr_at, hx_of. rewrite Hg. unfold gzh_at. Intros v1 v2 v3 v4 v5.
      sep_apply (gzh_fields_pad (hp_of Rp) (vi (gz_text (hdr_of rs))) (vl (gz_time (hdr_of rs)))
                   (vi (gz_os (hdr_of rs))) (rs_xfp rs) (vi (gz_extra_len (hdr_of rs))) (rs_nfp rs) (rs_cfp rs)
                   (vi (gz_hcrc (hdr_of rs))) v5 v4 v3 v2 v1).
      sep_apply drun_h_of_gzh. sep_apply drun_fields. cancel.
    + change (hpart 0 Rp) with (field_at_ Ews t_drun (DOT _h) Rp).
      unfold hdr_at. rewrite Hg. Intros. sep_apply drun_fields. cancel.
  - intros. apply drun_fields.
Qed.

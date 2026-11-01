(* Law deflate_api: struct drun field by field, with its two padding holes (VST's unfold_data_at diverges on
   the law's compspecs; this split takes ~4 min: keep it in its own file). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

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


(* inflate()'s prologue from LOAD() to the loop head. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Pro.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.roundtrip.RTH9ProKit.
Require Import Zlib.proof.roundtrip.RTH9ProP.
Require Import Zlib.proof.roundtrip.RTH9ProT2a.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.

Lemma pro9_load : forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (Rn Rb Rc: environ -> mpred) (Rr: option val -> environ -> mpred),
  pro9_ctx gv shs strmp z L ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd Rr ->
  ~ (ib = InNull /\ zf_ai z <> 0) ->
  semax Delta_inflate5 (PROP () LOCAL (temp _t'444 (Vint (Int.repr (i_mode (l_s L)))); temp _state (let (l_sp, _, _, _, _, _, _, _, _) := L in l_sp);
         temp _t'445 (l_sp L); temp _t'3 (Vint (Int.repr 0)); temp _t'2 (Vint (Int.repr 0)); temp _t'1 (Vint (Int.repr 0)); temp _leave (Vint (Int.repr 0));
         lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv;
         temp _strm strmp; temp _flush (Vint (Int.repr flush)))
    SEP (data_at shs t_strm (zf_ni z,
         (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), ((offset_val olo op),
         (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
         (gv _zcalloc, (gv _zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
         (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))) strmp;
       field_at Ews t_state (DOT _strm) strmp (l_sp L);
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode (s_typedo (l_s L))))) (l_sp L); zfuncs gv;
       data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
       malloc_token Ews t_state (l_sp L);
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold (l_s L)))) (l_sp L);
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits (l_s L)))) (l_sp L);
       state_rest gv (l_sp L) (l_headp L) (l_winp L) (l_s L);
       win_rep (l_winp L) (l_s L); state_pad (l_sp L); Hd; htok6 (Some L); in_rep ib;
       data_at osh (tarray tuchar on) (sublist 0 olo oc ++ sublist (olo + Zlength (@nil Z)) on oc) op;
       in_tok itok ib; if otok then malloc_token Ews (tarray tuchar on) op else emp;
       tables_rep gsh gv; Zlib.proof.crc32.Spec.crc_table_at tsh gv; mem_mgr gv))
    pro9_s4
    (overridePost (pro_post6 gv shs strmp z (Some L) ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd)
      {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |}).
Proof.
intros Espec gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb Hd Rn Rb Rc Rr HC GOODI.
pro9_prelude HC.
destruct HOB as [HNO HOO]. pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
cbv beta iota zeta delta [pro9_s1 pro9_s2 pro9_s4 pro9_rest sq1 sq2 inflate_pre f_inflate fn_body].
assert (TNI: is_pointer_or_null (zf_ni z)).
{ rewrite HNI. destruct ib as [|ish ip ilo ilen ic]; simpl; auto.
  destruct HIB as [(_ & IP & _) _]. destruct ip; try contradiction. exact I. }
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_loop (PROPx P (LOCALx Q (SEPx R)))
    continue: (PROPx P (LOCALx (temp _put (offset_val olo op) :: temp _left (Vint (Int.repr (zf_ao z))) ::
        temp _next (zf_ni z) :: temp _have (Vint (Int.repr (zf_ai z))) ::
        temp _hold (Vlong (Int64.repr (i_hold (l_s L)))) :: temp _bits (Vint (Int.repr (i_bits (l_s L)))) :: Q) (SEPx R)))
    break: (PROPx P (LOCALx (temp _put (offset_val olo op) :: temp _left (Vint (Int.repr (zf_ao z))) ::
        temp _next (zf_ni z) :: temp _have (Vint (Int.repr (zf_ai z))) ::
        temp _hold (Vlong (Int64.repr (i_hold (l_s L)))) :: temp _bits (Vint (Int.repr (i_bits (l_s L)))) :: Q) (SEPx R)))
end.
{ apply ENTAIL_refl. }
{ subst zca zcf. eapply semax_post; [ | | | | eapply pro9_loadbody with (inp := inp) (Rr := Rr); pro9_ctx_ok ].
  all: unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  { apply andp_left2, derives_refl. }
  all: try match goal with |- forall _ : option val, _ => intro end; apply andp_left2, FF_left. }
{ forward. apply ENTAIL_refl. }
forward. forward. forward.
subst zca zcf. eapply pro9_post with (Rr := Rr); [pro9_ctx_ok | exact GOODI].
Qed.

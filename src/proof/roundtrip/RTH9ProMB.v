(* inflate()'s prologue, the argument checks with an input object. *)
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
Require Import Zlib.proof.roundtrip.RTH9ProT1.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.

Lemma pro9_bufin : forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ish: share) (ip: val) (ilo ilen: Z) (ic: list val) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (Rn Rb Rc: environ -> mpred) (Rr: option val -> environ -> mpred),
  pro9_ctx gv shs strmp z L (InBuf ish ip ilo ilen ic) inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd Rr ->
  ~ ((InBuf ish ip ilo ilen ic) = InNull /\ zf_ai z <> 0) ->
  semax Delta_inflate5 (PROP () LOCAL (temp _t'2 (Vint (Int.repr 0)); temp _t'1 (Vint (Int.repr 0)); temp _leave (Vint (Int.repr 0));
         lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv;
         temp _strm strmp; temp _flush (Vint (Int.repr flush)))
    SEP (data_at shs t_strm (zf_ni z,
         (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), ((offset_val olo op),
         (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
         (gv _zcalloc, (gv _zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
         (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))) strmp;
       field_at Ews t_state (DOT _strm) strmp (l_sp L);
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode (l_s L)))) (l_sp L); zfuncs gv;
       data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
       malloc_token Ews t_state (l_sp L);
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold (l_s L)))) (l_sp L);
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits (l_s L)))) (l_sp L);
       state_rest gv (l_sp L) (l_headp L) (l_winp L) (l_s L);
       win_rep (l_winp L) (l_s L); state_pad (l_sp L); Hd; htok6 (Some L); in_rep (InBuf ish ip ilo ilen ic);
       data_at osh (tarray tuchar on) (sublist 0 olo oc ++ sublist (olo + Zlength (@nil Z)) on oc) op;
       in_tok itok (InBuf ish ip ilo ilen ic); if otok then malloc_token Ews (tarray tuchar on) op else emp;
       tables_rep gsh gv; Zlib.proof.crc32.Spec.crc_table_at tsh gv; mem_mgr gv))
    pro9_s2
    (overridePost (pro_post6 gv shs strmp z (Some L) (InBuf ish ip ilo ilen ic) inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd)
      {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |}).
Proof.
intros Espec gv shs strmp z L ish ip ilo ilen ic inp osh op olo on oc flush gsh tsh itok otok vh vl vb Hd Rn Rb Rc Rr HC GOODI.
pro9_prelude HC.
destruct HOB as [HNO HOO]. pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
cbv beta iota zeta delta [pro9_s1 pro9_s2 pro9_s4 pro9_rest sq1 sq2 inflate_pre f_inflate fn_body].
forward_if (temp _t'3 (Vint (Int.repr 0))).
{ dead_branch. }
{ destruct HIB as [HIO HIA]. pose proof HIO as (IR & IP & IL & ILN & IC & IM & IB & IBO).
pose proof (Zlength_nonneg inp).
simpl in HNI. rewrite HNI, Z.add_0_r.
forward.
forward_if.
{ simpl in_rep. simpl in_tok. entailer!. apply tc_test_eq_null; [destruct ip; try contradiction; exact I | ].
  sep_apply (bytes_wvp ish ip ilo (Zlength ic) ic itok); [rep_lia | ].
  apply sepcon_weak_valid_pointer1, derives_refl. }
{ exfalso. destruct ip; try contradiction. match goal with H: offset_val _ _ = nullval |- _ => inv H end. }
{ forward. rewrite HNI, Z.add_0_r. entailer!. apply derives_refl. } }
forward_if.
{ dead_branch. }
subst zca zcf. eapply pro9_state; [pro9_ctx_ok | exact GOODI].
Qed.

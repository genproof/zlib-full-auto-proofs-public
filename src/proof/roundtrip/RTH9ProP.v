(* inflate()'s prologue, its last step: the state after LOAD() is the loop state at m_init. *)
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
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.

Lemma pro9_post : forall (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (Rr: option val -> environ -> mpred),
  pro9_ctx gv shs strmp z L ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd Rr ->
  ~ (ib = InNull /\ zf_ai z <> 0) ->
  ENTAIL Delta_inflate5, PROP () LOCAL (temp _ret (Vint (Int.repr 0)); temp _out (Vint (Int.repr (zf_ao z)));
         temp _in (Vint (Int.repr (zf_ai z))); temp _put (offset_val olo op);
         temp _left (Vint (Int.repr (zf_ao z))); temp _next (zf_ni z);
         temp _have (Vint (Int.repr (zf_ai z))); temp _hold (Vlong (Int64.repr (i_hold (l_s L))));
         temp _bits (Vint (Int.repr (i_bits (l_s L))));
         temp _t'444 (Vint (Int.repr (i_mode (l_s L)))); temp _state (let (l_sp, _, _, _, _, _, _, _, _) := L in l_sp);
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
       tables_rep gsh gv; Zlib.proof.crc32.Spec.crc_table_at tsh gv; mem_mgr gv)
  |-- pro_post6 gv shs strmp z (Some L) ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh itok otok vh vl vb Hd.
Proof.
intros gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb Hd Rr HC GOODI.
pro9_prelude HC.
destruct HOB as [HNO HOO]. pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
assert (NB: ~ inflate_bad strmp z (Some L) ib (Some (OutBuf osh op olo on oc))).
{ unfold inflate_bad. rewrite ISL. intros [E | [E | E]]; [discriminate | discriminate | contradiction]. }
assert (AIL: zf_ai z = Zlength inp /\ in_ok ib inp).
{ destruct ib as [|ish ip ilo ilen ic].
  - subst inp. split; [ | reflexivity]. rewrite Zlength_nil.
    destruct (Z.eq_dec (zf_ai z) 0); auto. contradiction GOODI; auto.
  - destruct HIB as [HIO HIA]. auto. }
destruct AIL as [AIL INOK].
pose proof (typedo_fields (l_s L)) as (TH & TB & THD).
unfold pro_post6. Exists L (OutBuf osh op olo on oc).
unfold lstateH, mem_repH, locals_rep, hdr_tok, head_partH, hnoneH, xfr, mkF. rewrite m_init_eq.
cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres
     f_vhere f_vlast f_vhbuf f_flush m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
     m_adler m_msg m_tin m_tout m_snx m_sow].
rewrite state_rep_split, state_rest_typedo, win_rep_typedo, TH, TB, THD.
unfold m_have, m_left. cbn [m_inp m_nx m_aout m_ow].
unfold strm_rep. rewrite <- Hzca, <- Hzcf.
rewrite <- HNI, Zlength_nil, !Z.sub_0_r, <- AIL. simpl out_ptr. rewrite Z.add_0_r.
unfold out_rep, out_tok. rewrite Zlength_nil, Z.add_0_r.
unfold htok6, hdr_btoks.
change (let (l_sp, _, _, _, _, _, _, _, _) := L in l_sp) with (l_sp L).
destruct (i_head (l_s L)); entailer!.
Qed.

(* inflate()'s prologue, the branch where next_out is Z_NULL: inflate() returns Z_STREAM_ERROR. *)
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

Lemma pro9_outnull : forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (Rn Rb Rc: environ -> mpred) (Rr: option val -> environ -> mpred),
  pro9_ctx gv shs strmp z L ib inp None flush gsh tsh itok otok vh vl vb Hd Rr ->
  semax Delta_inflate5 (PROP () LOCAL (temp _t'1 (Vint (Int.repr 0)); temp _leave (Vint (Int.repr 0));
         lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv;
         temp _strm strmp; temp _flush (Vint (Int.repr flush)))
    SEP (data_at shs t_strm (zf_ni z,
         (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), ((zf_no z),
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
       win_rep (l_winp L) (l_s L); state_pad (l_sp L); Hd; htok6 (Some L); bufs_opt (Some L) ib None [] itok otok;
       tables_rep gsh gv; Zlib.proof.crc32.Spec.crc_table_at tsh gv; mem_mgr gv))
    pro9_s1
    (overridePost (pro_post6 gv shs strmp z (Some L) ib inp None flush gsh tsh itok otok vh vl vb Hd)
      {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |}).
Proof.
intros Espec gv shs strmp z L ib inp flush gsh tsh itok otok vh vl vb Hd Rn Rb Rc Rr HC.
pro9_prelude HC.
cbv beta iota zeta delta [pro9_s1 pro9_s2 pro9_s4 pro9_rest sq1 sq2 inflate_pre f_inflate fn_body].
rewrite HOB.
forward_if (temp _t'2 (Vint (Int.repr 1))).
{ dead_branch. }
{ forward. forward. entailer!. }
forward_if (temp _t'3 (Vint (Int.repr 1))).
{ forward. entailer!. }
{ dead_branch. }
forward_if (PROP (False) LOCAL () SEP ()).
2:{ dead_branch. }
eapply semax_pre; [ | apply semax_return].
apply andp_right. { entailer!. }
eapply derives_trans; [ | apply (HBAD (or_intror (or_introl eq_refl)))].
apply andp_right; [apply andp_left1; apply derives_refl | ].
unfold istream_opt. rewrite if_false by auto. unfold istream, state_mem.
rewrite zstrm_at_eq, state_rep_split. unfold zsv. rewrite <- Hzca, <- Hzcf, HOB.
entailer!.
Qed.

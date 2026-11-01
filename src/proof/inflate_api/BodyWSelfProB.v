(* A part of inflate()'s prologue in the allocator-generic port, after the tests of inflateStateCheck() and of
   next_out == Z_NULL: next_in == Z_NULL with avail_in != 0, the return of Z_STREAM_ERROR (inflate_bad).  It
   holds for any output object.  The script is a branch of za/inflate_api/Body5Pro.v's pro_part5_za;
   BodyWSelfProM.v uses it (the prologue is cut in parts so that each file checks quickly). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate_api.Body5Parts.
Require Import Zlib.proof.za.inflate_api.Body5Conv.
Require Import Zlib.proof.za.inflate_api.Body5Pro.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.za.inflate.ZTac.
Require Zlib.proof.inflate.InvW.
Require Import Zlib.proof.inflate_api.BodyWSelfProL.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.
Section ZAlloc.
Context {ZA : Zlib.proof.zutil.ZAlloc.zallocator} {ZAV : Zlib.proof.za.inflate.ZAV.adler_cell}.

(* the stream checks from the test of t'2 on: if (t'2) ... ; if (t'3) return; then inflate_pre_rest *)
Definition inflate_chk_mid : statement :=
  match fn_body f_inflate with
  | Ssequence _ (Ssequence (Ssequence (Ssequence _ if2) if3) _) => Ssequence if2 (Ssequence if3 inflate_pre_rest)
  | _ => Sskip
  end.

(* the state after the tests of inflateStateCheck() and of next_out, on a live stream with an output object *)
Definition pro_chk_za (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live) (ib: inbuf)
    (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (tr: list zev) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'2 (Vint (Int.repr 0)); temp _t'1 (Vint (Int.repr 0)); temp _leave (Vint (Int.repr 0));
         lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl;
         lvar _here t_code vh; gvars gv; temp _strm strmp;
         temp _flush (Vint (Int.repr flush)))
  SEP (data_at shs t_strm
         (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (offset_val olo op,
          (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
          (za_alloc, (za_free, (za_opaque, (Vint (Int.repr (zf_dt z)),
          (adler_val (zf_adler z), zf_res z))))))))))))) strmp;
       field_at Ews t_state (DOT _strm) strmp (l_sp L);
       field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode (l_s L)))) (l_sp L); zfuncs_za gv;
       data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
       za_tok t_state (l_sp L);
       field_at Ews t_state (DOT _hold) (Vlong (Int64.repr (i_hold (l_s L)))) (l_sp L);
       field_at Ews t_state (DOT _bits) (Vint (Int.repr (i_bits (l_s L)))) (l_sp L);
       state_rest gv (l_sp L) (l_headp L) (l_winp L) (l_s L);
       win_rep_za (l_winp L) (l_s L); state_pad (l_sp L); head_opt (Some L); in_rep ib;
       data_at osh (tarray tuchar on) (sublist 0 olo oc ++ sublist (olo + Zlength (@nil Z)) on oc) op;
       in_tok itok ib;
       if otok then malloc_token Ews (tarray tuchar on) op else emp;
       tables_rep gsh gv; crc_table_at tsh gv; za_res gv tr).

Definition pro_chk_bad_za_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share)
    (itok otok: bool) (vh vl vb: val) (tr: list zev) (R: ret_assert),
  in_tok_ok itok ib -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  zf_no z = out_ptr (OutBuf osh op olo on oc) 0 ->
  out_ok (OutBuf osh op olo on oc) (zf_ao z) ->
  strmp <> nullval -> zf_ok z -> writable_share shs -> live_ok L -> ib = InNull /\ zf_ai z <> 0 ->
  (inflate_bad strmp z (Some L) ib (Some (OutBuf osh op olo on oc)) ->
   ENTAIL Delta_inflate5_za,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt_za gv shs strmp z (Some L); head_opt (Some L);
              bufs_opt (Some L) ib (Some (OutBuf osh op olo on oc)) [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; za_res gv tr; zfuncs_za gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5_za (pro_chk_za gv shs strmp z L ib osh op olo on oc flush gsh tsh itok otok vh vl vb tr)
    inflate_chk_mid
    (overridePost (pro_post_za gv shs strmp z (Some L) ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh
       itok otok vh vl vb tr) R).

Lemma pro_chk_bad_za : pro_chk_bad_za_stmt.
Proof.
intros Espec gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr R
  HIT HNI HIB HNO HOO NN ZOK WS LOK BADI HBAD.
destruct R as [Rn Rb Rc Rr]. simpl RA_return in HBAD.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (ISL: is_live strmp (Some L) = Some L).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
unfold pro_chk_za.
remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf.
cbv beta iota zeta delta [inflate_chk_mid f_inflate fn_body].
(* next_in = Z_NULL, avail_in > 0 *)
destruct BADI as [EI AIN]. subst ib. simpl in HNI. rewrite HNI.
forward_if (temp _t'3 (Vint (Int.repr 1))).
{ dead_branch. }
{ forward. forward_if.
  { forward. forward. forward. entailer!.
    unfold Int.eq. rewrite if_false; [reflexivity | ].
    pose proof ZOK as (ZAI & _). rewrite !Int.unsigned_repr by rep_lia. auto. }
  { dead_branch. } }
forward_if (PROP (False) LOCAL () SEP ()).
2:{ dead_branch. }
eapply semax_pre; [ | apply semax_return].
apply andp_right. { entailer!. }
eapply derives_trans; [ | apply (HBAD (or_intror (or_intror (conj eq_refl AIN))))].
apply andp_right; [apply andp_left1; apply derives_refl | ].
unfold istream_opt_za. rewrite if_false by auto. unfold istream_za, state_mem_za.
rewrite zstrm_at_eq_za, state_rep_split. unfold zsv_za. rewrite <- Hzca, <- Hzcf, HNI, HNO.
simpl out_ptr. rewrite Z.add_0_r. unfold bufs_opt. simpl out_opt. simpl out_tok.
rewrite !Z.add_0_r. go_lower.
apply andp_right; [apply prop_right; repeat split; auto | ]. cancel.
apply andp_right; [apply prop_right; auto | ]. apply andp_right; [apply prop_right; auto | ]. cancel.
Qed.

End ZAlloc.

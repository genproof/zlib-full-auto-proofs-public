(* The second half of inflate()'s prologue in the allocator-generic port, after the stream checks passed:
   state = strm->state; TYPE -> TYPEDO; LOAD(); in = have; out = left; ret = Z_OK, up to the loop head
   (za/inflate_api/Body5Parts.v pro_post_za).  It holds for any output object (the output's malloc token is not
   used); BodyWSelfPro.v's pro_self_za ends with it.  The script is the end of za/inflate_api/Body5Pro.v's
   pro_part5_za up to LOAD() (BodyWSelfProL.v from there: the prologue is cut in parts so that each file checks
   quickly). *)
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

(* the state after the stream checks on a live stream with an output object *)
Definition pro_mid_za (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live) (ib: inbuf)
    (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (tr: list zev) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'3 (Vint (Int.repr 0)); temp _t'2 (Vint (Int.repr 0));
         temp _t'1 (Vint (Int.repr 0)); temp _leave (Vint (Int.repr 0));
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

Definition pro_tail_za_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share)
    (itok otok: bool) (vh vl vb: val) (tr: list zev) (R: ret_assert),
  zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  out_ok (OutBuf osh op olo on oc) (zf_ao z) ->
  strmp <> nullval -> zf_ok z -> writable_share shs -> live_ok L -> ~ (ib = InNull /\ zf_ai z <> 0) ->
  semax Delta_inflate5_za (pro_mid_za gv shs strmp z L ib osh op olo on oc flush gsh tsh itok otok vh vl vb tr)
    inflate_pre_rest
    (overridePost (pro_post_za gv shs strmp z (Some L) ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh
       itok otok vh vl vb tr) R).

Lemma pro_tail_za : pro_tail_za_stmt.
Proof.
intros Espec gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr R
  HNI HIB HOO NN ZOK WS LOK GOODI.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (ISL: is_live strmp (Some L) = Some L).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
unfold pro_mid_za.
remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf.
destruct R as [Rn Rb Rc Rr].
rewrite inflate_pre_rest_eq.
cbv beta iota zeta delta [inflate_pre_st inflate_pre_ty f_inflate fn_body].
forward. forward. forward.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx (replace_nth 2 R
     (field_at Ews t_state (DOT _mode) (Vint (Int.repr (i_mode (s_typedo (l_s L))))) (l_sp L))))))
end.
{ forward.
  assert (TYM: i_mode (l_s L) = Zlib.proof.inflate.Model.TYPE).
  { pose proof (sw_mode _ LS). unfold HEAD, SYNC, Zlib.proof.inflate.Model.TYPE in *.
    apply repr_inj_signed; [rep_lia | rep_lia | auto]. }
  unfold s_typedo. rewrite TYM, Z.eqb_refl.
  cbn [replace_nth i_mode set_i_mode]. entailer!. }
{ forward.
  assert (TYM: i_mode (l_s L) <> Zlib.proof.inflate.Model.TYPE).
  { intro E. rewrite E in *. contradiction. }
  unfold s_typedo. rewrite (proj2 (Z.eqb_neq _ _) TYM).
  cbn [replace_nth]. entailer!. }
cbn [replace_nth].
(* LOAD() and the rest *)
subst zca zcf.
apply (@pro_load_za ZA ZAV _ gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr
         (Build_ret_assert Rn Rb Rc Rr)); auto.
Qed.

End ZAlloc.

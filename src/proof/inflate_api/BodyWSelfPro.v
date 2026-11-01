(* inflate()'s prologue in the allocator-generic port (za/inflate_api/Body5Parts.v pro_part5_stmt_za) when the
   output object is the empty one at the stream's own member `reserved` (SpecSelf.self_out): no malloc token is
   needed for the comparison of next_out with Z_NULL, since the pointer is valid as an address inside the
   z_stream (BodySelfPro.strm_res_wvp).  The script is za/inflate_api/Body5Pro.v's pro_part5_za with the output
   case of BodySelfPro.v's pro_self, up to the test of next_out; the rest holds for any output object
   (BodyWSelfProM.v). *)
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
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.inflate_api.SpecSelf.
Require Import Zlib.proof.inflate_api.BodySelfPro.
Require Import Zlib.proof.inflate_api.BodyWSelfProB.
Require Import Zlib.proof.inflate_api.BodyWSelfProM.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.
Section ZAlloc.
Context {ZA : Zlib.proof.zutil.ZAlloc.zallocator} {ZAV : Zlib.proof.za.inflate.ZAV.adler_cell}.

(* pro_part5_stmt_za with the self output instead of out_tok_ok *)
Definition pro_self_za_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live)
    (ib: inbuf) (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (tr: list zev) (R: ret_assert),
  Int.min_signed <= flush <= Int.max_signed -> readable_share gsh -> readable_share tsh ->
  in_tok_ok itok ib -> self_out strmp otok ob (zf_ao z) -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end ->
  (inflate_bad strmp z st ib ob ->
   ENTAIL Delta_inflate5_za,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt_za gv shs strmp z st; head_opt (is_live strmp st);
              bufs_opt (is_live strmp st) ib ob [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; za_res gv tr; zfuncs_za gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5_za (pro_pre_za gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb tr)
    (Ssequence inflate_leave0 inflate_pre)
    (overridePost (pro_post_za gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb tr) R).

Lemma pro_self_za : pro_self_za_stmt.
Proof.
intros Espec gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb tr R
  HF HG HT HIT HOT HNI HIB HOB HBAD.
destruct R as [Rn Rb Rc Rr]. simpl RA_return in HBAD.
unfold pro_pre_za.
cbv beta iota zeta delta [inflate_pre inflate_leave0 f_inflate fn_body].
forward.
destruct (eq_dec strmp nullval) as [EN|NN].
{ (* Z_NULL stream *)
  subst strmp.
  replace (is_live nullval st) with (@None live) by reflexivity.
  forward_call (nullval, shs, default_val t_strm, nullval, 0, false, gv).
  { rewrite if_true by auto. cancel. }
  rewrite !if_true by auto.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H. }
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H. }
  forward_if (PROP (False) LOCAL () SEP ()).
  2:{ exfalso. inv H. }
  eapply semax_pre; [ | apply semax_return].
  apply andp_right. { entailer!. }
  eapply derives_trans; [ | apply (HBAD (or_introl eq_refl))].
  apply andp_right; [apply andp_left1; apply derives_refl | ].
  unfold istream_opt_za. rewrite if_true by auto. simpl head_opt. simpl bufs_opt.
  entailer!. }
assert (ISL: is_live strmp st = st) by (unfold is_live; rewrite if_false by auto; reflexivity).
rewrite ISL in HBAD |- *.
unfold istream_opt_za at 1. rewrite if_false by auto. unfold istream_za at 1.
destruct st as [L|].
2:{ (* ended stream *)
  rewrite zstrm_at_eq_za. Intros.
  forward_call (strmp, shs, zsv_za gv z nullval, nullval, 0, false, gv).
  { rewrite if_false by auto. cancel. }
  { right. split; [auto | unfold stream_ok_val_za, zsv_za; simpl; auto]. }
  rewrite !if_false by auto. Intros.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H1. }
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. inv H1. }
  forward_if (PROP (False) LOCAL () SEP ()).
  2:{ exfalso. inv H1. }
  eapply semax_pre; [ | apply semax_return].
  apply andp_right. { entailer!. }
  eapply derives_trans; [ | apply (HBAD (or_introl ISL))].
  apply andp_right; [apply andp_left1; apply derives_refl | ].
  unfold istream_opt_za. rewrite if_false by auto. unfold istream_za. rewrite zstrm_at_eq_za.
  simpl head_opt. simpl bufs_opt.
  entailer!. }
Intros. rename H into ZOK, H0 into WS, H1 into LOK.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (MC: ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool = true).
{ pose proof (sw_mode _ LS). apply andb_true_intro; split; apply Z.leb_le; lia. }
unfold state_mem_za. rewrite zstrm_at_eq_za, state_rep_split. Intros.
forward_call (strmp, shs, zsv_za gv z (l_sp L), l_sp L, i_mode (l_s L), true, gv).
{ rewrite if_false by auto. cancel. }
{ pose proof (sw_mode _ LS). unfold HEAD, SYNC in *.
  split3; [right; split; [auto | unfold stream_ok_val_za, zsv_za; simpl; auto] | | ]; rep_lia. }
rewrite !if_false by auto. rewrite MC. Intros. unfold zsv_za.
remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf.
destruct ob as [o|]; [ | destruct HOT as (_ & _ & ? & _ & E); discriminate].
destruct HOT as (OT & _ & ssh & _ & EO).
destruct HOB as [HNO HOO].
destruct o as [osh op olo on oc].
pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
rewrite HNO. simpl out_ptr. rewrite Z.add_0_r.
unfold bufs_opt at 1. Intros. simpl out_opt. simpl out_tok.
forward_if (temp _t'2 (Vint (Int.repr 0))).
{ dead_branch. }
{ forward. forward.
  { entailer!. apply tc_test_eq_null; [destruct op; try contradiction; exact I | ].
    inv EO. unfold strm_res_ptr. rewrite offset_offset_val, Z.add_0_r.
    match goal with |- context [data_at shs t_strm ?v strmp] => sep_apply (strm_res_wvp shs v strmp) end;
      [auto | ].
    wvp_close. }
  destruct op; try contradiction. entailer!. }
(* the rest: any output object *)
subst zca zcf.
apply (@pro_chk_mid_za ZA ZAV _ gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr
         (Build_ret_assert Rn Rb Rc Rr)); auto.
Qed.

End ZAlloc.

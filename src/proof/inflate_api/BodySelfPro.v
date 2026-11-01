(* inflate()'s prologue (Body5Parts.v pro_part5_stmt) when the output object is the empty one at the stream's own
   member `reserved` (SpecSelf.self_out): no malloc token is needed for the comparison of next_out with Z_NULL,
   since the pointer is valid as an address inside the z_stream.  The script follows Body5Pro.v's pro_part5. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.inflate_api.Body5Pro.
Require Import Zlib.proof.inflate_api.SpecSelf.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* pro_part5_stmt with the self output instead of out_tok_ok *)
Definition pro_self_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live)
    (ib: inbuf) (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (R: ret_assert),
  Int.min_signed <= flush <= Int.max_signed -> readable_share gsh -> readable_share tsh ->
  in_tok_ok itok ib -> self_out strmp otok ob (zf_ao z) -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end ->
  zf_ai z <= Int.max_signed -> zf_ao z <= Int.max_signed ->
  (inflate_bad strmp z st ib ob ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt gv shs strmp z st; head_opt (is_live strmp st);
              bufs_opt (is_live strmp st) ib ob [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5 (pro_pre gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb)
    (Ssequence inflate_leave0 inflate_pre)
    (overridePost (pro_post gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb) R).

(* a pointer into the z_stream at p, at the member `reserved`, is (weakly) valid *)
Lemma strm_res_wvp: forall sh v p, readable_share sh ->
  data_at sh t_strm v p |-- weak_valid_pointer (offset_val 104 p).
Proof.
  intros sh v p RS.
  eapply derives_trans; [apply data_at_memory_block | ].
  apply memory_block_weak_valid_pointer; [simpl; lia | simpl; lia | apply readable_nonidentity; auto].
Qed.

Lemma pro_self : pro_self_stmt.
Proof.
intros Espec gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb R
  HF HG HT HIT HOT HNI HIB HOB HAI HAO HBAD.
destruct R as [Rn Rb Rc Rr]. simpl RA_return in HBAD.
unfold pro_pre.
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
  unfold istream_opt. rewrite if_true by auto. simpl head_opt. simpl bufs_opt.
  entailer!. }
assert (ISL: is_live strmp st = st) by (unfold is_live; rewrite if_false by auto; reflexivity).
rewrite ISL in HBAD |- *.
unfold istream_opt at 1. rewrite if_false by auto. unfold istream at 1.
destruct st as [L|].
2:{ (* ended stream *)
  rewrite zstrm_at_eq. Intros.
  forward_call (strmp, shs, zsv gv z nullval, nullval, 0, false, gv).
  { rewrite if_false by auto. cancel. }
  { right. split; [auto | unfold stream_ok_val, zsv; simpl; auto]. }
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
  unfold istream_opt. rewrite if_false by auto. unfold istream. rewrite zstrm_at_eq.
  simpl head_opt. simpl bufs_opt.
  entailer!. }
Intros. rename H into ZOK, H0 into WS, H1 into LOK.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (MC: ((HEAD <=? i_mode (l_s L)) && (i_mode (l_s L) <=? SYNC))%bool = true).
{ pose proof (sw_mode _ LS). apply andb_true_intro; split; apply Z.leb_le; lia. }
unfold state_mem. rewrite zstrm_at_eq, state_rep_split. Intros.
forward_call (strmp, shs, zsv gv z (l_sp L), l_sp L, i_mode (l_s L), true, gv).
{ rewrite if_false by auto. cancel. }
{ pose proof (sw_mode _ LS). unfold HEAD, SYNC in *.
  split3; [right; split; [auto | unfold stream_ok_val, zsv; simpl; auto] | | ]; rep_lia. }
rewrite !if_false by auto. rewrite MC. Intros. unfold zsv.
remember (gv _zcalloc) as zca eqn:Hzca. remember (gv _zcfree) as zcf eqn:Hzcf.
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
assert (DEC: (ib = InNull /\ zf_ai z <> 0) \/ ~ (ib = InNull /\ zf_ai z <> 0)).
{ destruct ib; [destruct (Z.eq_dec (zf_ai z) 0); [right; intros [_ ?]; auto | left; auto]
              | right; intros [? _]; discriminate]. }
destruct DEC as [BADI | GOODI].
{ (* next_in = Z_NULL, avail_in > 0 *)
  destruct BADI as [EI AIN]. subst ib. simpl in HNI. rewrite HNI.
  forward_if (temp _t'3 (Vint (Int.repr 1))).
  { dead_branch. }
  { forward. forward_if.
    { forward. forward. forward. entailer!.
      unfold Int.eq. rewrite if_false; [reflexivity | ].
      pose proof ZOK as (ZA & _). rewrite !Int.unsigned_repr by rep_lia. auto. }
    { dead_branch. } }
  forward_if (PROP (False) LOCAL () SEP ()).
  2:{ dead_branch. }
  eapply semax_pre; [ | apply semax_return].
  apply andp_right. { entailer!. }
  eapply derives_trans; [ | apply (HBAD (or_intror (or_intror (conj eq_refl AIN))))].
  apply andp_right; [apply andp_left1; apply derives_refl | ].
  unfold istream_opt. rewrite if_false by auto. unfold istream, state_mem.
  rewrite zstrm_at_eq, state_rep_split. unfold zsv. rewrite <- Hzca, <- Hzcf, HNI, HNO.
  simpl out_ptr. rewrite Z.add_0_r. unfold bufs_opt. simpl out_opt. simpl out_tok.
  entailer!. apply derives_refl. }
forward_if (temp _t'3 (Vint (Int.repr 0))).
{ dead_branch. }
{ destruct ib as [|ish ip ilo ilen ic].
  - (* next_in = Z_NULL, avail_in = 0 *)
    assert (AI0: zf_ai z = 0) by (destruct (Z.eq_dec (zf_ai z) 0); auto; contradiction GOODI; auto).
    simpl in HNI. rewrite HNI, AI0.
    forward.
    forward_if.
    { forward. forward. forward. rewrite HNI, AI0. entailer!. }
    { dead_branch. }
  - (* an input object *)
    destruct HIB as [HIO HIA]. pose proof HIO as (IR & IP & IL & ILN & IC & IM & IB & IBO).
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
(* state = strm->state; the TYPE test *)
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
(* LOAD() *)
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
{ forward. forward. forward. forward. forward. forward. entailer!. }
{ forward. apply ENTAIL_refl. }
forward. forward. forward.
assert (NB: ~ inflate_bad strmp z (Some L) ib (Some (OutBuf osh op olo on oc))).
{ unfold inflate_bad. rewrite ISL. intros [E | [E | E]]; [discriminate | discriminate | contradiction]. }
assert (AIL: zf_ai z = Zlength inp /\ in_ok ib inp).
{ destruct ib as [|ish ip ilo ilen ic].
  - subst inp. split; [ | reflexivity]. rewrite Zlength_nil.
    destruct (Z.eq_dec (zf_ai z) 0); auto. contradiction GOODI; auto.
  - destruct HIB as [HIO HIA]. auto. }
destruct AIL as [AIL INOK].
pose proof (typedo_fields (l_s L)) as (TH & TB & THD).
unfold pro_post. Exists L (OutBuf osh op olo on oc).
unfold lstate, mem_rep, locals_rep, hdr_tok, head_part, xfr, mkF. rewrite m_init_eq.
cbn [f_gv f_shs f_strmp f_sp f_headp f_winp f_hsh f_xb f_nb f_cb f_ib f_ob f_gsh f_tsh f_dt f_vres
     f_vhere f_vlast f_vhbuf f_flush m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
     m_adler m_msg m_tin m_tout m_snx m_sow].
rewrite state_rep_split, state_rest_typedo, win_rep_typedo, TH, TB, THD.
unfold m_have, m_left. cbn [m_inp m_nx m_aout m_ow].
unfold strm_rep. rewrite <- Hzca, <- Hzcf.
rewrite <- HNI, Zlength_nil, !Z.sub_0_r, <- AIL. simpl out_ptr. rewrite Z.add_0_r.
unfold out_rep, out_tok. rewrite Zlength_nil, Z.add_0_r.
unfold head_opt, head_mem.
change (let (l_sp, _, _, _, _, _, _, _, _) := L in l_sp) with (l_sp L).
destruct (i_head (l_s L)); entailer!.
Qed.

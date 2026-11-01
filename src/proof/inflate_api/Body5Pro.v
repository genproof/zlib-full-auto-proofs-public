(* inflate()'s prologue (Body5Parts.v pro_part5_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.Body5Conv.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the z_stream value of zstrm_at *)
Definition zsv (gv: globals) (z: zfields) (sp: val) : reptype t_strm :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (lv (zf_tin z), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (lv (zf_tout z), (msg_val gv (zf_msg z), (sp, (gv _zcalloc, (gv _zcfree,
   (nullval, (zv (zf_dt z), (lv (zf_adler z), zf_res z))))))))))))).

Lemma zstrm_at_eq: forall gv shs strmp z sp,
  zstrm_at gv shs strmp z sp = data_at shs t_strm (zsv gv z sp) strmp.
Proof. reflexivity. Qed.

(* struct inflate_state without the members the prologue touches (strm, mode, hold, bits) *)
Definition state_rest (gv: globals) (sp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma state_rep_split: forall gv sp strmp headp winp s,
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _strm) strmp sp * field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp * field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  state_rest gv sp headp winp s.
Proof.
  intros. unfold state_rep, state_rest. apply pred_ext; cancel.
Qed.

Lemma state_rest_typedo: forall gv sp headp winp s,
  state_rest gv sp headp winp (s_typedo s) = state_rest gv sp headp winp s.
Proof.
  intros. unfold s_typedo. destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); reflexivity.
Qed.

Lemma win_rep_typedo: forall winp s, win_rep winp (s_typedo s) = win_rep winp s.
Proof.
  intros. unfold s_typedo. destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); reflexivity.
Qed.

Ltac dead_branch :=
  exfalso;
  match goal with
  | H: Int.repr _ = Int.zero |- _ => solve [inv H]
  | H: Int.repr _ <> Int.zero |- _ => solve [apply H; reflexivity]
  | H: Int64.repr _ <> Int64.repr _ |- _ => solve [apply H; reflexivity]
  | H: Int64.repr _ = Int64.zero |- _ => solve [inv H]
  end.

(* the pointers next_out / next_in compared with Z_NULL *)
Lemma bytes_wvp: forall sh p lo n (c: list val) (tok: bool),
  readable_share sh -> isptr p -> 0 <= lo <= n -> (tok = false -> 0 < n) ->
  data_at sh (tarray tuchar n) c p * (if tok then malloc_token Ews (tarray tuchar n) p else emp)
  |-- weak_valid_pointer (offset_val lo p).
Proof.
  intros sh p lo n c tok RS P L T.
  destruct (zlt 0 n) as [N | N].
  - apply sepcon_weak_valid_pointer1.
    eapply derives_trans; [apply data_at_memory_block | ].
    simpl sizeof. rewrite Z.max_r by lia.
    apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
  - destruct tok; [ | specialize (T eq_refl); lia].
    assert (lo = 0) by lia. subst lo.
    apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
    destruct p; try contradiction. rewrite offset_val_zero_Vptr. apply valid_pointer_weak.
Qed.

Lemma tc_test_eq_null: forall P p, isptr p -> P |-- weak_valid_pointer p ->
  P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros P p H W. destruct p; try contradiction.
  Local Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. apply andp_right; [apply prop_right; reflexivity | exact W].
Qed.
Local Opaque denote_tc_test_eq.

Ltac wvp_close :=
  repeat (apply sepcon_weak_valid_pointer1 || apply sepcon_weak_valid_pointer2); apply derives_refl.

Lemma typedo_fields: forall s,
  i_hold (s_typedo s) = i_hold s /\ i_bits (s_typedo s) = i_bits s /\ i_head (s_typedo s) = i_head s.
Proof.
  intros. unfold s_typedo. destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); auto.
Qed.

Lemma m_init_eq: forall z L inp,
  m_init z L inp =
  MS (s_typedo (l_s L)) (l_h L) inp (zf_ao z) 0 [] (i_hold (l_s L)) (i_bits (l_s L)) (Zlength inp) (zf_ao z)
     Z_OK 0 (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0.
Proof.
  intros. unfold m_init, s_typedo. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); reflexivity.
Qed.

Lemma pro_part5 : pro_part5_stmt.
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
destruct ob as [o|].
2:{ (* next_out = Z_NULL *)
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
  entailer!. }
destruct HOB as [HNO HOO].
destruct o as [osh op olo on oc].
pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
rewrite HNO. simpl out_ptr. rewrite Z.add_0_r.
unfold bufs_opt at 1. Intros. simpl out_opt. simpl out_tok.
forward_if (temp _t'2 (Vint (Int.repr 0))).
{ dead_branch. }
{ forward. forward.
  { entailer!. apply tc_test_eq_null; [destruct op; try contradiction; exact I | ].
    sep_apply (bytes_wvp osh op olo (Zlength oc) (sublist 0 olo oc ++ sublist olo (Zlength oc) oc) otok);
      [auto | lia | ].
    apply sepcon_weak_valid_pointer1, derives_refl. }
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

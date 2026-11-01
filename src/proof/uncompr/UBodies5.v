(* Version 5 (Spec5.v). *)
(* The bodies of uncompr.c (uncompress2_z, uncompress2, uncompress) against Spec.v, at the compspecs of
   the uncompr unit, with inflate's API specifications (at the inflate unit's compspecs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.USpec5.
Require Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.uncompr.URunFrame Zlib.proof.uncompr.URunRet.
Import Zlib.proof.inflate_api.Spec5.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

Definition Vprog_uncompr5 : varspecs. mk_varspecs Zlib.uncompr.code.prog. Defined.

Definition Gp_uncompress2_z5 : funspecs :=
  [Zlib.proof.inflate_api.Spec5.inflateInit__spec; Zlib.proof.inflate_api.Spec5.inflate_spec;
   Zlib.proof.inflate_api.Spec5.inflateEnd_spec].

Definition uncompr_bodies5_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_uncompr5 Gp_uncompress2_z5 f_uncompress2_z uncompress2_z_spec /\
  semax_body Vprog_uncompr5 [uncompress2_z_spec] f_uncompress2 uncompress2_spec /\
  semax_body Vprog_uncompr5 [uncompress2_spec] f_uncompress uncompress_spec.

#[export] Instance CCE_inflate_uncompr : change_composite_env Zlib.units.Inflate.CS Zlib.units.Uncompr.CS.
Proof. make_cs_preserve Zlib.units.Inflate.CS Zlib.units.Uncompr.CS. Defined.
#[export] Instance CCE_uncompr_inflate : change_composite_env Zlib.units.Uncompr.CS Zlib.units.Inflate.CS.
Proof. make_cs_preserve Zlib.units.Uncompr.CS Zlib.units.Inflate.CS. Defined.

Lemma buf_valid: forall sh n c p (tok: bool),
  readable_share sh -> (tok = false -> 0 < n) ->
  data_at sh (tarray tuchar n) c p * (if tok then malloc_token Ews (tarray tuchar n) p else emp)
  |-- valid_pointer p.
Proof.
  intros sh n c p tok Hsh Hn.
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer1. apply data_at_valid_ptr; [auto | simpl; rep_lia].
  - destruct tok; [| specialize (Hn eq_refl); lia].
    apply sepcon_valid_pointer2. apply malloc_token_valid_pointer. simpl. rep_lia.
Qed.

Ltac buf_valid_tac sh n c p tok :=
  apply derives_trans with (data_at sh (tarray tuchar n) c p *
                            (if tok then malloc_token Ews (tarray tuchar n) p else emp) * TT)%logic;
  [cancel | apply sepcon_valid_pointer1; apply buf_valid; auto].

(* ---------------------------------------------------------------------------------------------- *)
(* the model side of the loop                                                                     *)

(* the loop from (m, used, out) on is a continuation of the loop from the start *)
Definition reach (src: list Z) (cap: Z) (m: mst) (used: Z) (out: list Z) : Prop :=
  forall err u o, unc_loop src cap m used out err u o -> unc_loop src cap m_first 0 [] err u o.

Lemma reach_first: forall src cap, reach src cap m_first 0 [].
Proof. unfold reach. auto. Qed.

Lemma reach_next: forall src cap m used out res,
  reach src cap m used out ->
  run2 0 lenfix_list distfix_list (m_next m (sublist used (Zlength src) src) (cap - Zlength out)) res ->
  r_ret res = Z_OK ->
  reach src cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res)).
Proof. unfold reach. intros. apply H. eapply ul_next; eauto. Qed.

Lemma reach_stop: forall src cap m used out res,
  reach src cap m used out ->
  run2 0 lenfix_list distfix_list (m_next m (sublist used (Zlength src) src) (cap - Zlength out)) res ->
  r_ret res <> Z_OK ->
  unc_loop src cap m_first 0 [] (r_ret res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res)).
Proof. unfold reach. intros. apply H. eapply ul_stop; eauto. Qed.

Lemma m_init_next: forall z L m inp aout,
  l_s L = m_s m -> l_h L = m_h m -> zf_ao z = aout -> zf_adler z = m_adler m -> zf_msg z = m_msg m ->
  zf_tin z = m_tin m -> zf_tout z = m_tout m ->
  m_init z L inp = m_next m inp aout.
Proof.
  intros z L m inp aout Hs Hh Ha Had Hm Hti Hto. unfold m_init, m_next.
  rewrite Hs, Hh, Ha, Had, Hm, Hti, Hto. reflexivity.
Qed.

Lemma m_next_vmode: forall m inp aout,
  vmode (i_mode (m_s m)) -> vmode (i_mode (m_s (m_next m inp aout))).
Proof.
  intros m inp aout Hv. unfold m_next. simpl.
  destruct (i_mode (m_s m) =? Zlib.proof.inflate.Model.TYPE); simpl; auto.
  unfold vmode, TYPEDO, HEAD, BAD. lia.
Qed.

Lemma m_next_head: forall m inp aout, i_head (m_s (m_next m inp aout)) = i_head (m_s m).
Proof. intros. unfold m_next. simpl. destruct (_ =? _); reflexivity. Qed.

Lemma m_next_inp: forall m inp aout, m_inp (m_next m inp aout) = inp.
Proof. reflexivity. Qed.
Lemma m_next_aout: forall m inp aout, m_aout (m_next m inp aout) = aout.
Proof. reflexivity. Qed.

Lemma init_s_head: i_head (init_s 5 15) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma init_s_vmode: vmode (i_mode (init_s 5 15)).
Proof. vm_compute. split; discriminate. Qed.

(* the destination after more bytes *)
Lemma dest_after_app: forall dc dn out ow,
  Zlength dc = dn -> Zlength out + Zlength ow <= dn ->
  sublist 0 (Zlength out) (dest_after dc dn out) ++ byte_vals ow ++
  sublist (Zlength out + Zlength ow) dn (dest_after dc dn out) = dest_after dc dn (out ++ ow).
Proof.
  intros dc dn out ow Hdc Hn. unfold dest_after, byte_vals.
  pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  rewrite map_app, Zlength_app. list_solve.
Qed.

Lemma dest_after_nil: forall dc dn out,
  Zlength dc = dn -> Zlength out <= dn ->
  sublist 0 (Zlength out) (dest_after dc dn out) ++ byte_vals [] ++
  sublist (Zlength out + Zlength (@nil Z)) dn (dest_after dc dn out) = dest_after dc dn out.
Proof.
  intros. rewrite (dest_after_app dc dn out []) by (rewrite ?Zlength_nil; lia). rewrite app_nil_r. auto.
Qed.

Lemma Zlength_dest_after: forall dc dn out,
  Zlength dc = dn -> Zlength out <= dn -> Zlength (dest_after dc dn out) = dn.
Proof.
  intros. unfold dest_after, byte_vals. pose proof (Zlength_nonneg out). list_solve.
Qed.

(* the stream at the compspecs of the uncompr unit *)
Lemma istream_fold: forall gv v z L zca zcf,
  zca = gv inflate.code._zcalloc -> zcf = gv inflate.code._zcfree -> zf_ok z -> live_ok L ->
  data_at Tsh t_strm
    (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
     (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
     (zca, (zcf, (nullval, (Vint (Int.repr (zf_dt z)),
     (Vlong (Int64.repr (zf_adler z)), zf_res z))))))))))))) v * state_mem gv v L
  |-- istream gv Tsh v z (Some L).
Proof.
  intros. subst. unfold istream, zstrm_at, strm_rep. change_compspecs Zlib.units.Uncompr.CS. entailer!.
Qed.

Lemma bufs_eq: forall L ssh sp used sn sc dsh dp out ow dn dc (stok dtok: bool),
  Zlength dc = dn -> Zlength out + Zlength ow <= dn ->
  bufs_opt (Some L) (InBuf ssh sp used sn sc) (Some (OutBuf dsh dp (Zlength out) dn (dest_after dc dn out)))
    ow stok dtok =
  (data_at ssh (tarray tuchar sn) sc sp * data_at dsh (tarray tuchar dn) (dest_after dc dn (out ++ ow)) dp *
   (if stok then malloc_token Ews (tarray tuchar sn) sp else emp) *
   (if dtok then malloc_token Ews (tarray tuchar dn) dp else emp)).
Proof.
  intros. unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok. rewrite dest_after_app by auto.
  destruct stok, dtok; change_compspecs Zlib.units.Uncompr.CS; apply pred_ext; cancel.
Qed.

Lemma head_emp: forall v L, isptr v -> i_head (l_s L) = false -> head_opt (is_live v (Some L)) = emp.
Proof.
  intros v L Hv Hh. unfold is_live. rewrite if_false by (intro; subst; contradiction).
  simpl. unfold head_mem. rewrite Hh. reflexivity.
Qed.

Lemma istream_opt_ptr: forall gv shs v z st, isptr v -> istream_opt gv shs v z st = istream gv shs v z st.
Proof. intros. unfold istream_opt. rewrite if_false by (intro; subst; contradiction). reflexivity. Qed.

Lemma is_live_ptr: forall v (st: option live), isptr v -> is_live v st = st.
Proof. intros. unfold is_live. rewrite if_false by (intro; subst; contradiction). reflexivity. Qed.

Lemma sub_bytes: forall (sc: list val) (src: list Z) used,
  sublist 0 (Zlength src) sc = byte_vals src -> 0 <= used <= Zlength src -> Zlength src <= Zlength sc ->
  sublist used (used + (Zlength src - used)) sc = byte_vals (sublist used (Zlength src) src).
Proof.
  intros sc src used Hs Hu Hl.
  replace (used + (Zlength src - used)) with (Zlength src) by lia.
  unfold byte_vals in *. rewrite <- sublist_map, <- Hs. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma sub64_repr: forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros. unfold Int64.sub. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Ltac ret_tac :=
  unfold unc_ret, Z_STREAM_END, Z_NEED_DICT, Z_BUF_ERROR, Z_DATA_ERROR in *;
  repeat match goal with Hx: ?e <> ?k |- context [?e =? ?k] => rewrite (proj2 (Z.eqb_neq e k) Hx) end;
  cbv iota;
  match goal with |- context [if ?b then _ else _] => destruct b eqn:?E end;
  first [reflexivity | match goal with Hx: typed_true _ _ |- _ => inv Hx | Hx: typed_false _ _ |- _ => inv Hx end].

Lemma body_uncompress2_z5 :
  semax_body Vprog_uncompr5 Gp_uncompress2_z5 f_uncompress2_z uncompress2_z_spec.
Proof.
  start_function.
  forward.
  assert_PROP (isptr slp /\ isptr dlp) as Hpp by entailer!. destruct Hpp as [Hslp Hdlp].
  assert (Hsl: 0 <= Zlength src) by apply Zlength_nonneg.
  forward_if (temp _t'1 (Val.of_bool false)).
  { subst slp; contradiction. }
  { forward. forward_if (temp _t'1 (Val.of_bool false)).
    - rewrite !Int64.unsigned_repr in H12 by rep_lia. forward. forward. entailer!.
      destruct sp; try contradiction; reflexivity.
    - forward. entailer!.
    - entailer!. }
  forward_if (temp _t'2 (Val.of_bool false)).
  { contradiction. }
  { forward. entailer!. destruct dlp; try contradiction; reflexivity. }
  forward_if (temp _t'3 (Val.of_bool false)).
  { contradiction. }
  { forward. forward_if (temp _t'3 (Val.of_bool false)).
    - match goal with Hx: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in Hx by rep_lia end. forward. forward. entailer!.
      destruct dp; try contradiction; reflexivity.
    - forward. entailer!.
    - entailer!. }
  forward_if.
  { contradiction. }
  forward. forward.
  forward_if (temp _t'4 (Val.of_bool false)).
  - forward.
    + entailer!. apply denote_tc_test_eq_split; [| auto with valid_pointer].
      buf_valid_tac dsh (Zlength dc) dc dp dtok.
    + entailer!. destruct dp; try contradiction; reflexivity.
  - forward. entailer!.
  - forward_if (temp _t'4 (Val.of_bool false)).
    + contradiction.
    + forward. entailer!.
    + forward. forward. forward. forward. forward.
  replace_SEP 0 (raw_strm gv Tsh v_stream (RF sp (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef) Vundef Vundef nullval nullval nullval).
  { entailer!. unfold raw_strm. change_compspecs Zlib.units.Uncompr.CS. simpl. cancel. }
  unfold uversion_lit, inflate_globals. Intros.
  assert_PROP (isptr v_stream /\ isptr (gv ___stringlit_uncompr_1)) as Hvl by entailer!. destruct Hvl as [Hvs Hlit].
  forward_call (gv, Tsh, v_stream, RF sp (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef, Vundef, Vundef, nullval, gv ___stringlit_uncompr_1, Ers, map (fun c => Vint (Int.repr c)) [49; 46; 51; 46; 50; 0], 49, 112).
  { rewrite if_false by (intro Hn; rewrite Hn in Hvs; exact Hvs). cancel. }
  { repeat split; try exact Hlit; cbn; rep_lia. }
  Intros vret. destruct vret as [aok stp]. simpl fst in *; simpl snd in *.
  unfold init_ret. simpl orb. rewrite if_false by (intro Hn; rewrite Hn in Hvs; exact Hvs).
  unfold init_mem. rewrite if_false by (intro Hn; rewrite Hn in Hvs; exact Hvs).
  destruct aok; simpl.
  2: { forget (gv inflate.code._zcalloc) as zca. forget (gv inflate.code._zcfree) as zcf.
       forward_if (PROP (False) LOCAL () SEP ()); [| discriminate].
       unfold raw_strm. change_compspecs Zlib.units.Uncompr.CS.
       forward.
       Exists Z_MEM_ERROR (Zlength src) cap (@nil Z).
       cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res].
       apply andp_right; [apply prop_right; split; [left; auto | reflexivity] |].
       unfold dest_after, uversion_lit, inflate_globals. rewrite Zlength_nil, sublist_same by lia. simpl app.
       change (Zlength [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
                        Vint (Int.repr 50); Vint (Int.repr 0)]) with 6.
       simpl map. sep_apply (data_at_data_at_ Tsh t_strm). cancel. }
  forward_if (temp _err (Vint (Int.repr Z_OK))); [discriminate | forward; entailer! |].
  change (Zlength [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
                   Vint (Int.repr 50); Vint (Int.repr 0)]) with 6.
  simpl map. unfold istream_raw. Intros.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  unfold raw_strm. cbn [rf_ni rf_ai rf_tin rf_no rf_ao rf_tout rf_dt rf_adler rf_res raw_after_init].
  change (i_wrap (init_s 5 15)) with 5. simpl (5 =? 0). cbv beta iota. change (Z.land 5 1) with 1.
  change (l_sp (init_live stp 15)) with stp.
  change_compspecs Zlib.units.Uncompr.CS.
  forward. forward.
  forward_loop
    (EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX len: Z, EX left: Z,
     PROP (reach src cap m used out; vmode (i_mode (m_s m)); i_head (m_s m) = false;
           l_s L = m_s m; l_h L = m_h m; zf_adler z = m_adler m; zf_msg z = m_msg m;
           zf_tin z = m_tin m; zf_tout z = m_tout m;
           zf_ni z = offset_val used sp; zf_no z = offset_val (Zlength out) dp;
           (zf_ai z + len = Zlength src - used)%Z; (zf_ao z + left = cap - Zlength out)%Z;
           (len = 0 \/ zf_ai z = 0)%Z; (left = 0 \/ zf_ao z = 0)%Z;
           (0 <= used <= Zlength src)%Z; (Zlength out <= cap)%Z; (0 <= len)%Z; (0 <= left)%Z)
     LOCAL (temp _len (Vlong (Int64.repr len)); temp _left (Vlong (Int64.repr left));
            temp _max (Vint (Int.neg (Int.repr 1)));
            lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp;
            temp _destLen dlp; temp _source sp; temp _sourceLen slp)
     SEP (istream gv Tsh v_stream z (Some L);
          data_at Ers (tarray tschar 6)
            [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
             Vint (Int.repr 50); Vint (Int.repr 0)] (gv ___stringlit_uncompr_1);
          version_lit gv; mem_mgr gv; zfuncs gv;
          data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp;
          if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
          data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
          data_at ssh (tarray tuchar sn) sc sp;
          if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
          data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
          tables_rep gsh gv; Spec.crc_table_at tsh gv))
  break:
    (EX err: Z, EX used: Z, EX out: list Z, EX z: zfields, EX L: live,
     PROP (err <> Z_OK; (-5 <= err <= 2)%Z; unc_loop src cap m_first 0 [] err used out; i_head (l_s L) = false;
           (zf_ai z = Zlength src - used)%Z; (zf_ao z = cap - Zlength out)%Z;
           (0 <= used <= Zlength src)%Z; (Zlength out <= cap)%Z)
     LOCAL (temp _err (Vint (Int.repr err)); temp _len (Vlong (Int64.repr 0));
            temp _left (Vlong (Int64.repr 0));
            lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp;
            temp _destLen dlp; temp _source sp; temp _sourceLen slp)
     SEP (istream gv Tsh v_stream z (Some L);
          data_at Ers (tarray tschar 6)
            [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
             Vint (Int.repr 50); Vint (Int.repr 0)] (gv ___stringlit_uncompr_1);
          version_lit gv; mem_mgr gv; zfuncs gv;
          data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp;
          if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
          data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
          data_at ssh (tarray tuchar sn) sc sp;
          if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
          data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
          tables_rep gsh gv; Spec.crc_table_at tsh gv)).
  { (* the loop entry *)
    Exists m_first 0 (@nil Z) (ZF sp 0 0 dp 0 0 None 0 1 Vundef) (init_live stp 15) (Zlength src) cap.
    go_lower.
    apply andp_right.
    { apply prop_right. cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res].
      rewrite eqb_type_refl, Zlength_nil, !isptr_offset_val_zero by auto.
      refine (conj (reach_first _ _) (conj init_s_vmode (conj init_s_head _))).
      repeat split; try reflexivity; try lia. }
    rewrite <- istream_raw_istream by (try reflexivity; unfold zf_ok; simpl; rep_lia).
    unfold istream_raw, raw_strm.
    cbn [zf_ni zf_ai zf_tin zf_no zf_ao zf_tout zf_msg zf_dt zf_adler zf_res rf_ni rf_ai rf_tin rf_no rf_ao rf_tout
         rf_dt rf_adler rf_res].
    subst zca zcf. change (l_sp (init_live stp 15)) with stp.
    unfold dest_after. rewrite Zlength_nil, sublist_same by lia. simpl app.
    rewrite prop_true_andp by auto.
    change_compspecs Zlib.units.Uncompr.CS. cancel. }
  { (* the loop body *)
    clear dependent zca. clear dependent zcf. clear H12 H13 H14 stp.
    Intros m used out z L len left.
    unfold istream. Intros. unfold zstrm_at, strm_rep.
    remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
    change_compspecs Zlib.units.Uncompr.CS.
    unfold zf_ok in H31.
    forward.
    forward_if (PROP ()
     LOCAL (temp _len (Vlong (Int64.repr (len))); temp _left (Vlong (Int64.repr (0)));
            temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp;
            temp _destLen dlp; temp _source sp; temp _sourceLen slp)
     SEP (data_at Tsh t_strm
            (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
             (Vint (Int.repr (cap - Zlength out)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
             (zca, (zcf, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z)))))))))))))
            v_stream; state_mem gv v_stream L;
          data_at Ers (tarray tschar 6)
            [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
             Vint (Int.repr 50); Vint (Int.repr 0)] (gv ___stringlit_uncompr_1);
          version_lit gv; mem_mgr gv; zfuncs gv;
          data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp;
          if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
          data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
          data_at ssh (tarray tuchar sn) sc sp;
          if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
          data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
          tables_rep gsh gv; Spec.crc_table_at tsh gv)).
    { (* avail_out = 0: offer the rest of the destination *)
      match goal with Hx: zf_ao z = 0 |- _ => rename Hx into Hao end.
      rewrite Hao in *.
      forward_if (temp _t'6 (Vint (Int.repr left))).
      { exfalso. change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. rep_lia. }
      { forward. entailer!. }
      replace left with (cap - Zlength out) in * by lia. forward. forward. forward.
      rewrite Int.unsigned_repr by rep_lia. rewrite Int64.sub_idem.
      entailer!. }
    { match goal with Hx: zf_ao z <> 0 |- _ => rename Hx into Hao end.
      assert (Hl: left = 0) by tauto. assert (Hz: zf_ao z = cap - Zlength out) by lia.
      rewrite Hz, Hl in *. forward. entailer!. }
    clear dependent left.
    forward.
    forward_if (PROP ()
     LOCAL (temp _len (Vlong (Int64.repr (0))); temp _left (Vlong (Int64.repr (0)));
            temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v_stream; gvars gv; temp _dest dp;
            temp _destLen dlp; temp _source sp; temp _sourceLen slp)
     SEP (data_at Tsh t_strm
            (zf_ni z, (Vint (Int.repr (Zlength src - used)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
             (Vint (Int.repr (cap - Zlength out)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L,
             (zca, (zcf, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)), zf_res z)))))))))))))
            v_stream; state_mem gv v_stream L;
          data_at Ers (tarray tschar 6)
            [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
             Vint (Int.repr 50); Vint (Int.repr 0)] (gv ___stringlit_uncompr_1);
          version_lit gv; mem_mgr gv; zfuncs gv;
          data_at dsh (tarray tuchar dn) (dest_after dc dn out) dp;
          if dtok then malloc_token Ews (tarray tuchar dn) dp else emp;
          data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
          data_at ssh (tarray tuchar sn) sc sp;
          if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
          data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
          tables_rep gsh gv; Spec.crc_table_at tsh gv)).
    { (* avail_in = 0: offer the rest of the source *)
      match goal with Hx: zf_ai z = 0 |- _ => rename Hx into Hai end.
      rewrite Hai in *.
      forward_if (temp _t'7 (Vint (Int.repr len))).
      { exfalso. change (Int.unsigned (Int.neg (Int.repr 1))) with 4294967295 in *. rep_lia. }
      { forward. entailer!. }
      replace len with (Zlength src - used) in * by lia. forward. forward. forward.
      rewrite Int.unsigned_repr by rep_lia. rewrite Int64.sub_idem.
      entailer!. }
    { match goal with Hx: zf_ai z <> 0 |- _ => rename Hx into Hai end.
      assert (Hl: len = 0) by tauto. assert (Hz: zf_ai z = Zlength src - used) by lia.
      rewrite Hz, Hl in *. forward. entailer!. }
    clear dependent len.
    sep_apply (istream_fold gv v_stream (ZF (zf_ni z) (Zlength src - used) (zf_tin z) (zf_no z)
                 (cap - Zlength out) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z)) L zca zcf);
      [unfold zf_ok in *; simpl; rep_lia |].
    clear dependent zca. clear dependent zcf.
    forward_call (gv, Tsh, v_stream, ZF (zf_ni z) (Zlength src - used) (zf_tin z) (zf_no z) (cap - Zlength out)
                    (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z), Some L, InBuf ssh sp used sn sc,
                  sublist used (Zlength src) src, Some (OutBuf dsh dp (Zlength out) dn (dest_after dc dn out)), 0,
                  gsh, tsh, stok, dtok).
    { rewrite istream_opt_ptr, head_emp, is_live_ptr by (rewrite ?H15; auto).
      rewrite bufs_eq by (rewrite ?Zlength_nil; lia). rewrite app_nil_r. cancel. }
    { cbn [zf_ni zf_ai zf_no zf_ao in_ptr out_ptr in_ok out_ok]. rewrite H21, H22, !Z.add_0_r.
      rewrite Zlength_sublist by lia.
      split; [reflexivity |]. split; [| split; [| rep_lia]].
      - split; [| lia]. repeat split; auto; try lia; try rep_lia.
        + apply sub_bytes; auto; lia.
        + apply Forall_sublist. auto.
      - split; [reflexivity |]. split; [exact SH |]. repeat split; auto; try lia; try rep_lia.
        apply Zlength_dest_after; lia. }
    Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
    match goal with Hx: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hrel end.
    destruct Hrel as [[Hbad _] | [_ [L0 [o [res [winp [HL [Ho [Hrun [Hsnx [Hr [How [Hz' [Hwin Hst']]]]]]]]]]]]]].
    { exfalso. unfold inflate_bad in Hbad. rewrite is_live_ptr in Hbad by auto.
      destruct Hbad as [Hb | [Hb | [Hb _]]]; discriminate. }
    injection HL as <-. injection Ho as <-. subst r ow z' st'.
    rewrite (m_init_next _ L m _ (cap - Zlength out)) in Hrun by (simpl; auto).
    pose proof (run2_frame _ _ _ _ _ (m_next_vmode m _ _ H13) Hrun) as (Fi & Fa & Fs & Fh & Fv).
    rewrite m_next_inp in Fi. rewrite m_next_aout in Fa. rewrite m_next_head, H14 in Fh.
    rewrite istream_opt_ptr, head_emp, !is_live_ptr by (simpl; auto).
    match goal with |- context [istream _ _ _ ?zz _] =>
      assert_PROP (zf_ok zz) as Hzok by (unfold istream; entailer!) end.
    unfold z_after, zf_ok in Hzok. simpl in Hzok. rewrite Fi, Fa, Fs in Hzok.
    rewrite Zlength_sublist in Hzok by lia.
    rewrite bufs_eq by lia.
    Intros. rewrite Zlength_sublist in Hsnx by lia.
    assert (Hret: -5 <= r_ret res <= 2) by (eapply run2_ret; [| exact Hrun]; simpl; unfold Z_OK; lia).
    forward_if (r_ret res = Z_OK).
    { forward. entailer!. }
    { forward.
      Exists (r_ret res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
        (z_after (ZF (zf_ni z) (Zlength src - used) (zf_tin z) (zf_no z) (cap - Zlength out) (zf_tout z)
                     (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z)) (InBuf ssh sp used sn sc)
                 (OutBuf dsh dp (Zlength out) dn (dest_after dc dn out)) res)
        (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
      entailer!.
      split; [eapply reach_stop; eauto |].
      unfold z_after; simpl. rewrite Fi, Fa, Fs, Zlength_app. rewrite Zlength_sublist by lia. repeat split; lia. }
    Intros.
    Exists (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
      (z_after (ZF (zf_ni z) (Zlength src - used) (zf_tin z) (zf_no z) (cap - Zlength out) (zf_tout z)
                   (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z)) (InBuf ssh sp used sn sc)
               (OutBuf dsh dp (Zlength out) dn (dest_after dc dn out)) res)
      (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)) 0 0.
    entailer!.
    split; [eapply reach_next; eauto |].
    unfold z_after; simpl. rewrite Fi, Fa, Fs, Zlength_app. rewrite Zlength_sublist by lia. repeat split; lia. }
  (* after the loop *)
  Intros err used out z L.
  clear dependent zca. clear dependent zcf. clear H12 H13 H14 stp.
  unfold istream. Intros. unfold zstrm_at, strm_rep.
  remember (gv inflate.code._zcalloc) as zca. remember (gv inflate.code._zcfree) as zcf.
  change_compspecs Zlib.units.Uncompr.CS.
  forward. forward. forward. forward. forward. forward. forward. forward.
  sep_apply (istream_fold gv v_stream z L zca zcf Heqzca Heqzcf H12 H14).
  clear dependent zca. clear dependent zcf.
  forward_call (gv, Tsh, v_stream, z, Some L).
  { rewrite istream_opt_ptr by auto. cancel. }
  rewrite istream_opt_ptr by auto.
  rewrite H19, H20, !Int.unsigned_repr, !Int64.add_zero_l, !sub64_repr by rep_lia.
  replace (cap - (cap - Zlength out)) with (Zlength out) by lia.
  replace (Zlength src - (Zlength src - used)) with used by lia.
  forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
  { forward. entailer!. }
  { forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
    { forward. forward. entailer!. }
    { forward_if (temp _t'10 (Val.of_bool ((err =? -5) && (Zlength src - used =? 0)))).
      { forward. entailer!.
        match goal with Hx: Int.repr err = Int.repr _ |- _ => apply repr_inj_signed in Hx; [| rep_lia | rep_lia] end.
        subst err. simpl andb. unfold Int64.cmpu.
        destruct (Zlength src - used =? 0) eqn:E.
        - apply Z.eqb_eq in E. rewrite E. reflexivity.
        - apply Z.eqb_neq in E. rewrite Int64.eq_false; [reflexivity |].
          intro Hx. apply repr_inj_unsigned64 in Hx; rep_lia. }
      { forward. entailer!.
        assert (Hn5: err <> -5) by (intro; subst; contradiction).
        rewrite (proj2 (Z.eqb_neq _ _) Hn5). reflexivity. }
      forward_if (temp _t'9 (Vint (Int.repr (unc_ret err (Zlength src - used))))).
      { forward. forward. forward. entailer!. ret_tac. }
      { forward. forward. forward. entailer!. ret_tac. }
      all: try entailer!. }
    all: try entailer!. }
  unfold istream, zstrm_at, strm_rep. Intros. change_compspecs Zlib.units.Uncompr.CS.
  forget (gv inflate.code._zcalloc) as zca. forget (gv inflate.code._zcfree) as zcf.
  forward.
  Exists (unc_ret err (Zlength src - used)) used (Zlength out) out.
  apply andp_right; [apply prop_right; split; [right; exists err; auto | reflexivity] |].
  unfold uversion_lit, inflate_globals.
  sep_apply (data_at_data_at_ Tsh t_strm). cancel.
Qed.

Lemma body_uncompress2_5 :
  semax_body Vprog_uncompr5 [uncompress2_z_spec] f_uncompress2 uncompress2_spec.
Proof.
  start_function.
  forward. forward. forward. forward.
  forward_call (gv, dsh, dp, dn, dc, cap, v_got, dtok, stok, ssh, sp, sn, sc, src, v_used, gsh, tsh).
  Intros vret. destruct vret as [[[r slen] dlen] out]. simpl fst; simpl snd.
  forward. forward. forward. forward. forward.
  Exists r slen dlen out. entailer!.
Qed.

Lemma body_uncompress5 :
  semax_body Vprog_uncompr5 [uncompress2_spec] f_uncompress uncompress_spec.
Proof.
  start_function.
  forward.
  forward_call (gv, dsh, dp, dn, dc, cap, dlp, dtok, stok, ssh, sp, sn, sc, src, v_used, gsh, tsh).
  Intros vret. destruct vret as [[[r slen] dlen] out]. simpl fst; simpl snd.
  forward.
  Exists r slen dlen out. entailer!.
Qed.

Lemma uncompr_bodies5 : uncompr_bodies5_stmt.
Proof.
  intros Espec. split; [|split].
  - apply body_uncompress2_z5.
  - apply body_uncompress2_5.
  - apply body_uncompress5.
Qed.

(* Law inflate_decode, main: one iteration of the decode loop (draws, the input and output objects, inflate(),
   the checks of its result by the decode theory's decode_call_stmt, the frees, break at Z_STREAM_END). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.
Require Import Zlib.proof.uncompr.URunFrame.

Lemma idd_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma idd_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma idd_bytes_inflate sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma idd_tok_inflate sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma idd_ptr_adler_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma idd_ptr_adler sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

(* the stream at the law's compspecs (inflate_codes/MainInfKit.v) *)
Definition idd_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma idd_strm_cs sh (v: idd_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition idd_tup (gv: globals) (z: zfields) (sp: val) : idd_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma idd_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (idd_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite idd_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma idd_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (@data_at CS shs (Tstruct _z_stream_s noattr) (idd_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite idd_istream_unfold. entailer!. Qed.

Lemma idd_istream_undef gv vs z L:
  istream gv Tsh vs z (Some L) |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof. rewrite idd_istream_unfold. Intros. sep_apply (@data_at_data_at_ CS). cancel. Qed.

Lemma idd_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma idd_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* the stream fields set before the call *)
Definition idd_zcall (z: zfields) (ni: val) (ai: Z) (no: val) (ao: Z) : zfields :=
  ZF ni ai (zf_tin z) no ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma idd_tup_set gv z sp ni ai no ao:
  idd_tup gv (idd_zcall z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (idd_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (idd_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* the call's input and output objects *)
Lemma idd_bufs_pre L ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
   @data_at CS Ews (tarray tuchar aout) co obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic
  |-- bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) [] true true.
Proof.
  intros Hc. unfold bufs_opt.
  rewrite <- (idd_bytes_inflate Ews ain ci ibp), <- (idd_tok_inflate Ews ain ibp),
          <- (idd_bytes_inflate Ews aout co obp), <- (idd_tok_inflate Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  unfold in_rep, out_opt, out_rep, in_tok, out_tok. rewrite Eo. cancel.
Qed.

Lemma idd_bufs_post L ibp obp ain aout (ci co: list val) (ow: list Z):
  bufs_opt (Some L) (InBuf Ews ibp 0 ain ci) (Some (OutBuf Ews obp 0 aout co)) ow true true
  |-- (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
       @data_at CS Ews (tarray tuchar aout) (byte_vals ow ++ sublist (Zlength ow) aout co) obp *
       @malloc_token CS Ews (tarray tuchar aout) obp)%logic.
Proof.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite (idd_bytes_inflate Ews ain ci ibp), (idd_tok_inflate Ews ain ibp), (idd_tok_inflate Ews aout obp).
  rewrite sublist_nil, Z.add_0_l. simpl app.
  rewrite (idd_bytes_inflate Ews aout _ obp). cancel.
Qed.

Lemma idd_in_ptr sh p n c: isptr p -> in_ptr (InBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.
Lemma idd_out_ptr sh p n c: isptr p -> out_ptr (OutBuf sh p 0 n c) 0 = p.
Proof. intros P. destruct p; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. Qed.

Lemma idd_init_head z L inp: i_head (m_s (m_init z L inp)) = i_head (l_s L).
Proof. unfold m_init. simpl. destruct (_ =? _); reflexivity. Qed.

(* the first k bytes produced, as bytes_same takes them *)
Lemma idd_cbuf_ob obp ow rest aout:
  isptr obp -> is_bytes ow -> Zlength ow <= aout ->
  cbuf_ok false obp Ews obp 0 aout (Zlength ow) (byte_vals ow ++ rest) ow.
Proof.
  intros P B Hl. unfold cbuf_ok.
  split; [rewrite isptr_offset_val_zero; auto | ]. split; [auto with share | ]. split; [lia | ]. split; [lia | ].
  split; [reflexivity | ]. split; [exact B | ]. pose proof (Zlength_nonneg ow).
  rewrite sublist_app1 by (unfold byte_vals; rewrite ?Zlength_map; lia).
  rewrite sublist_same by (unfold byte_vals; rewrite ?Zlength_map; lia). reflexivity.
Qed.

(* data[opos .. opos + k), the expected bytes *)
Lemma idd_cbuf_data datap dcont D opos k:
  isptr datap -> data_ok dcont D -> 0 <= opos -> 0 <= k -> opos + k <= Zlength D ->
  cbuf_ok false (offset_val opos datap) Ews datap opos 262144 k dcont (sublist opos (opos + k) D).
Proof.
  intros P (Hl & HD & B & Hs) Ho Hk Hok. unfold cbuf_ok.
  split; [auto | ]. split; [auto with share | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist; lia | ]. split; [apply is_bytes_sublist; auto | ].
  rewrite <- sublist_bytes_rep, <- Hs, sublist_sublist by lia. f_equal; lia.
Qed.

(* data_type's bits *)
Lemma idd_and_bit dt k: 0 <= k <= 128 ->
  (Int.and (Int.repr dt) (Int.repr k) = Int.zero <-> Z.land dt k = 0).
Proof.
  intros Hk. unfold Int.and. rewrite !Int.unsigned_repr_eq.
  rewrite (Z.mod_small k) by rep_lia.
  assert (E: Z.land (dt mod Int.modulus) k = Z.land dt k).
  { change Int.modulus with (2 ^ 32). rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. f_equal. rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. }
  rewrite E.
  assert (R: 0 <= Z.land dt k < 256).
  { assert (K: Z.land k 255 = k).
    { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. }
    rewrite <- K, Z.land_assoc. apply IntFacts.Z_land_255_range. } split; intros H.
  - apply repr_inj_unsigned in H; [exact H | rep_lia | rep_lia].
  - rewrite H. reflexivity.
Qed.

(* the data of the first k blocks is a prefix of all the data *)
Lemma idd_fold_ext {A} (f: list Z -> A -> list Z) :
  (forall h x, exists t, f h x = h ++ t) -> forall l h, exists t, fold_left f l h = h ++ t.
Proof.
  intros F l. induction l as [ | a l IH]; intros h; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (F h a) as [t1 E1]. destruct (IH (f h a)) as [t2 E2].
    exists (t1 ++ t2). rewrite E2, E1, app_assoc. reflexivity.
Qed.

Lemma idd_lz_ext n d out : exists t, lz_copy n d out = out ++ t.
Proof.
  revert out. induction n as [ | n IH]; intros out; simpl.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH (out ++ [Znth (Zlength out - d) out])) as [t E].
    exists ([Znth (Zlength out - d) out] ++ t). rewrite E, app_assoc. reflexivity.
Qed.

Lemma idd_block_ext h b : exists t, block_data h b = h ++ t.
Proof.
  assert (S: forall h syms, exists t, syms_data h syms = h ++ t).
  { intros h' syms. unfold syms_data. apply idd_fold_ext. intros h'' x. destruct x; simpl.
    - eexists. reflexivity.
    - apply idd_lz_ext. }
  destruct b; simpl; [eexists; reflexivity | apply S | apply S].
Qed.

Lemma idd_outk_len G k : Zlength (outk G k) <= Zlength (full G).
Proof.
  unfold outk, full, expand.
  rewrite <- (firstn_skipn (Z.to_nat k) (dc_bs G)) at 2. rewrite fold_left_app.
  destruct (idd_fold_ext block_data idd_block_ext (skipn (Z.to_nat k) (dc_bs G))
              (fold_left block_data (firstn (Z.to_nat k) (dc_bs G)) (dc_hist G))) as [t E].
  rewrite E, Zlength_app. pose proof (Zlength_nonneg t). lia.
Qed.

(* the slice src[pos .. pos + ain) of the source object (scont: 524288 bytes, the first |src| are src) *)
Lemma idd_cbuf_src srcp scont src pos ain:
  isptr srcp -> Zlength scont = 524288 -> Zlength src <= 524288 -> is_bytes src ->
  sublist 0 (Zlength src) scont = bytes_rep src -> 0 <= pos -> 0 <= ain -> pos + ain <= Zlength src ->
  cbuf_ok false (offset_val pos srcp) Ews srcp pos 524288 ain scont (sublist pos (pos + ain) src).
Proof.
  intros P Hl Hs Hb Hsub Hp Ha Hpa. unfold cbuf_ok.
  split; [auto | ]. split; [auto with share | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist; lia | ]. split; [apply is_bytes_sublist; auto | ].
  rewrite <- sublist_bytes_rep, <- Hsub, sublist_sublist by lia. f_equal; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The decode theory's call statement (the only use of decode_call_stmt: the v2 port changes this lemma) *)

Lemma id_call_use : decode_call_stmt -> forall G pos out L z inp flush res,
    dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, full G = out ++ m_ow m ++ rest) /\
     dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m) = zf_ao z /\ Zlength (out ++ m_ow m) < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES) /\
     exists dt, r_dtype res = Some dt /\ dtype_ok G (out ++ m_ow m) dt).
Proof.
  intros DC G pos out L z inp flush res Gok D Lok Zok Hao Hp Hl Hi R.
  destruct (DC G pos out L z inp flush res Gok D Lok Zok Hao Hp Hl Hi R)
    as [M|(A1 & A2 & A3 & A4 & A5 & A6 & _ & A7 & A8 & A9)].
  - left. exact M.
  - right. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 A9)))))))).
Qed.

(* the modes of the decoder's invariant are those of a running stream (URunFrame.vmode) *)
Lemma idd_vmode G pos out s tout : dinv G pos out s tout -> HEAD <= i_mode s <= DONE.
Proof.
  intros D. destruct D as [AM _]. unfold at_mode in AM. destruct AM as [_ AM].
  decompose [or and] AM; clear AM;
  match goal with E: i_mode s = _ |- _ => rewrite E end; split; vm_compute; discriminate.
Qed.

Lemma idd_vmode_init G pos out z L inp tout :
  dinv G pos out (l_s L) tout -> vmode (i_mode (m_s (m_init z L inp))).
Proof.
  intros D. apply idd_vmode in D. unfold vmode, m_init. simpl.
  destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); simpl.
  - split; vm_compute; discriminate.
  - unfold BAD, DONE in *. lia.
Qed.

(* what the harness checks after the call, from the decode theory *)
Lemma idd_facts G pos opos L z inp flush res isbz ls :
  decode_call_stmt -> dctx_ok G -> dc_hist G = [] -> Zlength (full G) <= 262144 ->
  dinv G pos (sublist 0 opos (full G)) (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->
  0 <= pos -> 0 <= opos <= Zlength (full G) -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  (forall k, 0 <= k <= nblk G -> Znth (Zlength (outk G k)) isbz <> 0) -> ls = Zlength (outk G (nblk G - 1)) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx (r_m res) <= Zlength inp /\ m_inp (r_m res) = inp /\ m_aout (r_m res) = zf_ao z /\
   m_sow (r_m res) = Zlength (m_ow (r_m res)) /\
   opos + Zlength (m_ow (r_m res)) <= Zlength (full G) /\
   m_ow (r_m res) = sublist opos (opos + Zlength (m_ow (r_m res))) (full G) /\
   dinv G (pos + m_snx (r_m res)) (sublist 0 (opos + Zlength (m_ow (r_m res))) (full G)) (m_s (r_m res))
     (m_tout (r_m res)) /\
   (r_ret res = Z_STREAM_END ->
      opos + Zlength (m_ow (r_m res)) = Zlength (full G) /\ pos + m_snx (r_m res) = slen G /\
      m_tout (r_m res) = Zlength (full G)) /\
   exists dt, r_dtype res = Some dt /\
     (Z.land dt 128 <> 0 -> Znth (opos + Zlength (m_ow (r_m res))) isbz <> 0) /\
     (Z.land dt 64 <> 0 -> ls <= opos + Zlength (m_ow (r_m res))) /\
     (Z.land dt 64 = 0 -> opos + Zlength (m_ow (r_m res)) <= ls)).
Proof.
  intros DC Gok Gh Hfl D Lok Zok Hao Hp Ho Hl Hi Hisb Hls R.
  pose proof (run2_frame _ _ _ _ _ (idd_vmode_init _ _ _ z L inp _ D) R) as (Fi & Fa & _ & _ & _).
  destruct (id_call_use DC G pos (sublist 0 opos (full G)) L z inp flush res Gok D Lok Zok Hao Hp Hl Hi R)
    as [M | (Hr & Hsnx & Hsow & Hao' & (rest & Hfull) & D' & Hend & _ & (dt & Hdt & DT))]; [left; exact M | right].
  set (ow := m_ow (r_m res)) in *.
  set (out := sublist 0 opos (full G)) in *.
  assert (Lout: Zlength out = opos) by (unfold out; rewrite Zlength_sublist; lia).
  assert (Lfull: Zlength (full G) = opos + Zlength ow + Zlength rest).
  { rewrite Hfull, !Zlength_app. lia. }
  assert (Eow: sublist opos (opos + Zlength ow) (full G) = ow).
  { rewrite Hfull. rewrite <- Lout. rewrite app_assoc. rewrite sublist_app1 by (rewrite ?Zlength_app; list_solve).
    rewrite sublist_app2 by lia. rewrite Z.sub_diag. replace (Zlength out + Zlength ow - Zlength out) with (Zlength ow) by lia.
    apply sublist_same; lia. }
  assert (Eout: sublist 0 (opos + Zlength ow) (full G) = out ++ ow).
  { rewrite Hfull. rewrite <- Lout. rewrite app_assoc. rewrite sublist_app1 by (rewrite ?Zlength_app; list_solve).
    apply sublist_same; rewrite ?Zlength_app; lia. }
  assert (Lnew: Zlength (out ++ ow) = opos + Zlength ow) by (rewrite Zlength_app; lia).
  split; [exact Hr | ]. split; [exact Hsnx | ]. split; [rewrite Fi; reflexivity | ]. split; [exact Hao' | ].
  split; [exact Hsow | ]. split; [pose proof (Zlength_nonneg rest); lia | ]. split; [symmetry; exact Eow | ].
  split; [rewrite Eout; exact D' | ].
  split.
  { intros SE. destruct (Hend SE) as [E1 E2].
    assert (Lf: opos + Zlength ow = Zlength (full G)) by (rewrite <- Lnew, E1; reflexivity).
    split; [exact Lf | ]. split; [exact E2 | ].
    destruct D' as (_ & _ & _ & _ & Ht). rewrite Ht. rewrite E1.
    unfold produced. rewrite Gh. change (Zlength (@nil Z)) with 0. rewrite sublist_same by lia.
    apply Z.mod_small. pose proof (Zlength_nonneg (full G)). lia. }
  exists dt. split; [exact Hdt | ].
  destruct DT as (D128 & D64 & D64').
  split; [ | split].
  - intros B. destruct (D128 B) as (k & Hk & Ek). rewrite <- Lnew, Ek. apply Hisb; exact Hk.
  - intros B. rewrite Hls, <- Lnew. apply D64; exact B.
  - intros B. rewrite Hls, <- Lnew. apply D64'; exact B.
Qed.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Ltac ret0 := match goal with P := _ : ret_assert |- _ => unfold abbreviate in P; subst P end;
  eapply semax_post with (R' := POST_id);
  [ apply andp_left2; unfold POST_id, frame_ret_assert, function_body_ret_assert; simpl; intros x;
    first [ normalize; contradiction | rewrite FF_sepcon; apply FF_left | apply FF_left ] .. |
    intros vl; apply andp_left2; unfold POST_id; simpl; intros x; apply derives_refl |
    unfold POST_id; forward; Exists (Int.repr 0); sep_apply idd_istream_undef; entailer!;
    repeat (sep_apply data_at_data_at_); cancel ].

Ltac rcase := match goal with Hr: r_ret ?res = Z_OK \/ _ |- _ =>
  let E := fresh in destruct Hr as [E|[E|E]]; rewrite E in *; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END in *;
  unfold Int.zero, Int.one in *; simpl Z.eqb in *;
  first [ reflexivity
        | exfalso; match goal with H: ?a <> ?a |- _ => apply H; reflexivity end
        | exfalso; match goal with H: Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in H; [lia|rep_lia|rep_lia] end
        | vm_compute; reflexivity ] end.

Lemma id_decb_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr
    pos lim opos z L (Post: ret_assert) :
  decode_call_stmt -> RA_return Post = RA_return POST_id ->
  dec_facts G datap srcp isbp dcont scont isbz ls ->
  semax Delta_id
    (dec_at gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr pos lim opos z L)
    seg_decb
    (loop_nocontinue_ret_assert (dec_inv gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr)
       (overridePost (dec_post gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr) Post)).
Proof.
  intros DC HR DF.
  destruct Post as [Pn Pb Pc Pr]; change (Pr = RA_return POST_id) in HR; subst Pr.
  unfold dec_at. Intros.
  unfold seg_decb, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros step.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  pose proof DF as DF'.
  destruct DF' as (Gok & Ghist & Pdata & Psrc & Pisb & Dok & Hscl & Hsrcl & Hscont & Hisbl & Hisbb & Hisbk & Hls).
  set (T := Zlength (dc_src G)) in *.
  set (nlim := if step <? T - lim then lim + step else T).
  assert (Hnlim: lim <= nlim <= T) by (unfold nlim; destruct (Z.ltb_spec step (T - lim)); lia).
  ifpostv _t'42 (Vint (Int.repr nlim)).
  { forward. entailer!. unfold nlim; destruct (Z.ltb_spec step (T - lim)); try lia; reflexivity. }
  { forward. entailer!. unfold nlim; destruct (Z.ltb_spec step (T - lim)); try lia; reflexivity. }
  forward.
  forward.
  set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= T) by (subst ain; lia).
  assert (Hsrcb: is_bytes (dc_src G)) by (destruct Gok as (_ & _ & _ & _ & _ & _ & B & _); exact B).
  set (N0 := 262144) in *. set (N1 := 262145) in *. set (N2 := 524288) in *.
  assert (HN0: 262144 <= N0 <= 262144) by (unfold N0; lia).
  assert (HN1: 262145 <= N1 <= 262145) by (unfold N1; lia).
  assert (HN2: 524288 <= N2 <= 524288) by (unfold N2; lia).
  clearbody N0 N1 N2.
  forward_call (offset_val pos srcp, Ews, srcp, pos, N2, scont, ain, sublist pos (pos + ain) (dc_src G), gv).
  { rewrite idd_bytes_adler. cancel. }
  { assert (E2: N2 = 524288) by lia. rewrite E2 in *. apply idd_cbuf_src; auto; lia. }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite idd_ptr_adler_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite idd_ptr_adler, idd_bytes_adler.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpostv _t'45 (Vint (Int.repr 1)). { forward. entailer!. } { infeas. }
    forward_if. 2: { infeas. }
    ret0. }
  destruct (eq_dec ibp nullval); [contradiction | ]. Intros.
  rewrite ?idd_bytes_adler, ?idd_tok_adler.
  Ltac brs := first [ solve [infeas] |
     solve [match goal with |- context [denote_tc_test_eq ?p _] =>
              match goal with |- context [@malloc_token CS Ews (tarray tuchar ?n) p] =>
                apply (@malloc_test_eq CS _ n); [lia | sep_apply (data_at_data_at_ Ews (tarray tuchar n)); cancel] end end] |
     solve [forward; entailer!; try match goal with P: isptr ?p |- context [sem_cmp_pp Ceq ?p _] =>
              destruct p; try contradiction; reflexivity end] ].
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpostv _t'45 (Vint (Int.repr 1)); [ brs .. | ].
    forward_if. 2: { infeas. }
    ret0. }
  destruct (eq_dec obp nullval); [contradiction | ]. Intros.
  rewrite ?idd_bytes_adler, ?idd_tok_adler.
  assert_PROP (isptr obp /\ isptr ibp) as Pob by entailer!. destruct Pob as [Pob Pib].
  ifpostv _t'45 (Vint (Int.repr 0)); [ brs .. | ].
  forward_if. { infeas. }
  rewrite idd_istream_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  forward. forward. forward. forward.
  rewrite sub_repr. change (nlim - pos) with ain.
  set (inp := sublist pos (pos + ain) (dc_src G)) in *.
  assert (Linp: Zlength inp = ain) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ibf := InBuf Ews ibp 0 ain (bytes_rep inp)).
  set (obf := OutBuf Ews obp 0 aout (bytes_rep bs)).
  rewrite <- (idd_tup_set gv z (l_sp L) ibp ain obp aout).
  set (z1 := idd_zcall z ibp ain obp aout).
  assert (Z1ok: zf_ok z1).
  { destruct H10 as (? & ? & ? & ? & ? & ?). unfold z1, idd_zcall, zf_ok; simpl. rep_lia. }
  sep_apply (idd_istream_fold gv Tsh vs z1 L); auto.
  sep_apply (idd_bufs_pre L ibp obp ain aout (bytes_rep inp) (bytes_rep bs)).
  { rewrite Zlength_bytes_rep; auto. }
  fold ibf obf.
  assert (Hhd: i_head (l_s L) = false) by (destruct H as (_ & (_ & Hh & _) & _); exact Hh).
  forward_call (gv, Tsh, vs, z1, Some L, ibf, inp, Some obf, flush, Ers, Ers, true, true).
  { rewrite idd_istream_opt, idd_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { unfold z1, idd_zcall, ibf, obf; simpl zf_ai; simpl zf_ao; simpl zf_no; simpl zf_ni.
    assert (bytes_ok inp) by (apply Forall_sublist; exact Hsrcb).
    rewrite idd_in_ptr, idd_out_ptr by auto.
    simpl. repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia;
    rewrite ?Zlength_bytes_rep; try rep_lia; try (intros; discriminate).
    rewrite sublist_same by (rewrite ?Zlength_bytes_rep; lia). reflexivity. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into Hrel end.
  destruct Hrel as [(Bad & _) | (_ & L0 & o & res & winp & EL & Eo & R & Hsnx0 & Er & Eow & Ez' & Hwin & Est)].
  { exfalso. unfold inflate_bad in Bad. rewrite idd_is_live in Bad by auto.
    destruct Bad as [B|[B|[B _]]]; discriminate. }
  injection EL as EL; subst L0. injection Eo as Eo; subst o. subst st' r ow.
  pose proof (run2_frame _ _ _ _ _ (idd_vmode_init _ _ _ z1 L inp _ H) R) as (Fi & Fa & Fs & Fh & _).
  rewrite idd_init_head, Hhd in Fh.
  rewrite idd_istream_opt, !idd_is_live by auto.
  simpl head_opt. unfold head_mem at 1. simpl l_s. rewrite Fh.
  unfold ibf, obf. sep_apply idd_bufs_post. fold ibf obf. Intros.
  forward_if.
  { ret0. }
  assert (Hdf: Zlength (full G) <= 262144) by (destruct Dok as (_ & D & _); exact D).
  assert (Hz1t: zf_tout z1 = zf_tout z) by reflexivity.
  destruct (idd_facts G pos opos L z1 inp flush res isbz ls DC Gok Ghist Hdf ltac:(rewrite Hz1t; exact H)
              H12 Z1ok ltac:(unfold z1, idd_zcall; simpl; lia) ltac:(lia) H2 ltac:(lia)
              ltac:(rewrite Linp; reflexivity) Hisbk Hls R)
    as [M | (Hr & Hsnx & Hinp & Hao' & Hsow & Hlen & Eow & D' & Hend & dt & Hdt & B128 & B64 & B64')].
  { exfalso. match goal with Hn: Int.repr (r_ret res) <> _ |- _ => apply Hn; rewrite M; reflexivity end. }
  ifpostv _t'47 (Vint (Int.repr (if r_ret res =? 1 then 0 else 1))).
  1,2: solve [forward; entailer!; rcase].
  ifpostv _t'48 (Vint (Int.repr 1)).
  1,2: solve [forward; entailer!; rcase].
  forward_call (Int.repr 1).
  set (L' := {| l_sp := l_sp L; l_winp := winp; l_s := m_s (r_m res); l_h := m_h (r_m res);
                l_headp := l_headp L; l_hsh := l_hsh L; l_xb := l_xb L; l_nb := l_nb L; l_cb := l_cb L |}).
  set (ow := m_ow (r_m res)) in *.
  set (snx := m_snx (r_m res)) in *.
  assert (Eao: zf_ao z' = aout - Zlength ow).
  { rewrite Ez'. simpl. rewrite Hao', Hsow. reflexivity. }
  assert (Eai: zf_ai z' = ain - snx).
  { rewrite Ez'. simpl. rewrite Hinp, Linp. reflexivity. }
  assert (Edt: zf_dt z' = dt).
  { rewrite Ez'. simpl. rewrite Hdt. reflexivity. }
  assert (Eto: zf_tout z' = m_tout (r_m res)).
  { rewrite Ez'. reflexivity. }
  assert (Els: l_s L' = m_s (r_m res)) by reflexivity.
  clearbody L' ow snx. clear Ez'.
  rewrite idd_istream_unfold. Intros.
  assert (Z'ok: zf_ok z') by assumption.
  assert (Howl: 0 <= Zlength ow <= aout /\ 0 <= snx <= ain).
  { destruct Z'ok as (Hai & Hao & _). rewrite Eao in Hao. rewrite Eai in Hai. pose proof (Zlength_nonneg ow). lia. }
  unfold idd_tup.
  forward.
  forward.
  rewrite Eao, sub_repr. replace (aout - (aout - Zlength ow)) with (Zlength ow) by lia.
  forward_call (Int.repr 1).
  { entailer!. pose proof (Zlength_nonneg ow). arg_cmp. }
  assert (Howb: is_bytes ow).
  { rewrite Eow. apply is_bytes_sublist. destruct Dok as (_ & _ & B & _). exact B. }
  forward_call (obp, Ews, obp, 0, aout, byte_vals ow ++ sublist (Zlength ow) aout (bytes_rep bs), ow,
                offset_val opos datap, Ews, datap, opos, N0, dcont, sublist opos (opos + Zlength ow) (full G),
                Zlength ow).
  { rewrite !idd_bytes_adler. cancel. }
  { pose proof (Zlength_nonneg ow). split.
    - apply idd_cbuf_ob; auto; lia.
    - assert (E0: N0 = 262144) by lia. rewrite E0. apply idd_cbuf_data; auto; lia. }
  rewrite <- Eow. rewrite if_true by auto.
  forward_call (Int.repr 1).
  forward.
  forward.
  rewrite Edt, add_repr.
  set (opos' := opos + Zlength ow) in *.
  assert (Hop: 0 <= opos' <= Zlength (full G)) by (unfold opos'; lia).
  assert (Hopi: 0 <= opos' < Zlength isbz) by (pose proof Hdf; pose proof HN1; lia).
  assert (Eisb: Znth opos' (bytes_rep isbz) = Vint (Int.repr (Znth opos' isbz))) by (apply Znth_bytes_rep; exact Hopi).
  assert (Ezr: 0 <= Znth opos' isbz <= Byte.max_unsigned).
  { apply (Forall_Znth isbz (fun b => 0 <= b <= Byte.max_unsigned)); [exact Hisbb | exact Hopi]. }
  Ltac ifsame := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx [] (LOCALx Q (SEPx R))) end.
  ifsame.
  { assert (B: Z.land dt 128 <> 0).
    { intros Z0. match goal with Hn: Int.and _ _ <> Int.zero |- _ => apply Hn end. apply idd_and_bit; [lia | exact Z0]. }
    specialize (B128 B). fold opos' in B128.
    pose proof Eisb as Eisb'.
    change (@Znth val Inhabitant_val opos' (bytes_rep isbz)) with (@Znth val Vundef opos' (bytes_rep isbz)) in Eisb'.
    forward.
    { entailer!. first [rewrite Eisb | rewrite Eisb']. simpl. rewrite Int.unsigned_repr; rep_lia. }
    first [rewrite Eisb' | rewrite Eisb].
    forward_call (Int.repr 1).
    { entailer!. unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia. destruct (zeq _ _); [contradiction | reflexivity]. }
    entailer!. }
  { forward. entailer!. }
  assert (Hlsr: 0 <= ls <= Zlength (full G)) by (rewrite Hls; split; [apply Zlength_nonneg | apply idd_outk_len]).
  forward.
  ifsame.
  { assert (B: Z.land dt 64 <> 0).
    { intros Z0. match goal with Hn: Int.and _ _ <> Int.zero |- _ => apply Hn end. apply idd_and_bit; [lia | exact Z0]. }
    specialize (B64 B).
    forward_call (Int.repr 1). { entailer!. arg_cmp. }
    entailer!. }
  { assert (B: Z.land dt 64 = 0).
    { match goal with Hn: Int.and _ _ = Int.zero |- _ => apply idd_and_bit in Hn; [exact Hn | lia] end. }
    specialize (B64' B).
    forward_call (Int.repr 1). { entailer!. arg_cmp. }
    entailer!. }
  forward.
  rewrite Eai.
  forward.
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar ain)). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar aout)). cancel. }
  forward.
  assert_PROP (isptr q) as Pq by entailer!.
  forward_call (tarray tuchar aout, q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    cancel. }
  rewrite sub_repr, add_repr. replace (pos + (ain - (ain - snx))) with (pos + snx) by lia.
  sep_apply (data_at_data_at_ Tsh (tptr tuchar) q vosn).
  assert (E0: N0 = 262144) by lia. assert (E1: N1 = 262145) by lia. assert (E2: N2 = 524288) by lia.
  rewrite E0 in *. rewrite E1 in *. rewrite E2 in *. clear E0 E1 E2 HN0 HN1 HN2 N0 N1 N2.
  rewrite <- Eai, <- Eao, <- Edt. fold (idd_tup gv z' (l_sp L')).
  sep_apply (idd_istream_fold gv Tsh vs z' L'); auto.
  forward_if.
  { assert (Er1: r_ret res = Z_STREAM_END).
    { match goal with Hc: Int.repr (r_ret res) = Int.repr 1 |- _ =>
        apply repr_inj_signed in Hc; [rewrite Hc; reflexivity | | rep_lia] end.
      destruct Hr as [Ex|[Ex|Ex]]; rewrite Ex; unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END; rep_lia. }
    destruct (Hend Er1) as (Hoe & Hpe & Hte).
    forward.
    unfold dec_post. Exists nlim z' L'.
    rewrite Eto, Hte, Hpe, Hoe. entailer!. }
  forward.
  unfold dec_inv, dec_at. Exists (pos + snx) nlim opos' z' L'.
  rewrite Els, Eto. entailer!.
Qed.

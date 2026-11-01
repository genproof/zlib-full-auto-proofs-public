(* Law rj_truncated, main: the part rt_loop_stmt of the inflate half (RTIKit.v), as rt_partial's (RPLoop.v) up
   to the check after each call: gp_assert(code != Z_STREAM_END) (IFacts.px_call: no call returns it). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Zlib.proof.deflate.DSpec.
Require Zlib.proof.uncompr.URunRet.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTIKit.
Require Import Zlib.harness.rj_truncated.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Moves between the units' compspecs and the law's                                              *)

Ltac rtl_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma rtl_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rtl_cs_tac CC_inflate. Qed.
Lemma rtl_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma rtl_bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rtl_cs_tac CC_adler32. Qed.

(* the 14 members of struct z_stream *)
Definition rtl_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma rtl_strm_cs sh (v: rtl_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. rtl_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition rtl_tup (gv: globals) (z: zfields) (adv sp: val) : rtl_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma rtl_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (rtl_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rtl_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma rtl_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rtl_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rtl_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite rtl_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma rtl_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite rtl_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma rtl_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsl vs * TT.
Proof.
  intros Pv. rewrite rtl_istreamA_opt_ptr by auto. destruct st as [L|]; [apply rtl_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rtl_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The objects of one inflate() call                                                             *)

(* the output object: out written, then undefined bytes *)
Definition rtl_oc (n: Z) (out: list Z) : list val := bytes_rep out ++ Zrepeat Vundef (n - Zlength out).

(* the input object: the compressed bytes O at the start of the object of b bytes; the call is offered the
   bytes [pos, pos + take) *)
Definition rtl_ib (cp: val) (b pos: Z) (O: list Z) : inbuf := InBuf Ews cp pos b (rtl_oc b O).
Definition rtl_ob (op: val) (n: Z) (out: list Z) : outbuf := OutBuf Ews op (Zlength out) n (rtl_oc n out).

Lemma rtl_oc_len n out: Zlength out <= n -> Zlength (rtl_oc n out) = n.
Proof.
  intros H. unfold rtl_oc, bytes_rep. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia.
Qed.

(* after the call: out ++ ow written *)
Lemma rtl_oc_after n out ow: Zlength out + Zlength ow <= n ->
  sublist 0 (Zlength out) (rtl_oc n out) ++ byte_vals ow ++
    sublist (Zlength out + Zlength ow) n (rtl_oc n out) = rtl_oc n (out ++ ow).
Proof.
  intros H. pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  unfold rtl_oc, bytes_rep, byte_vals.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map.
  rewrite map_app, <- app_assoc. f_equal. f_equal. rewrite Zlength_app.
  unfold Zrepeat. rewrite sublist_repeat by (try rewrite Zlength_repeat; lia).
  f_equal. f_equal. lia.
Qed.

Lemma rtl_zf_ok gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st |-- !! zf_ok z.
Proof.
  intros Pv. rewrite rtl_istreamA_opt_ptr by auto. unfold istreamA. destruct st; entailer!.
Qed.

(* the struct after the harness's stores into avail_in / avail_out: the stream inflate() takes *)
Lemma rtl_offer_fold gv vs z L ib o ai ao:
  isptr vs -> zf_ok z -> live_ok L -> i_head (l_s L) = false ->
  0 <= ai <= Int.max_unsigned -> 0 <= ao <= Int.max_unsigned ->
  data_at Tsh t_zsl
    (in_ptr ib 0, (Vint (Int.repr ai), (Vlong (Int64.repr (zf_tin z)), (out_ptr o 0, (Vint (Int.repr ao),
     (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
     (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
     (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))) vs * state_mem gv vs L
  |-- istreamA_opt gv Tsh vs (offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao) Vundef (Some L) *
      head_opt (is_live vs (Some L)).
Proof.
  intros Pv Zo Lo Hh Hai Hao.
  rewrite rtl_head_none, rtl_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  rewrite rtl_istreamA_unfold. unfold rtl_tup, offer_z, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* the input object (the compressed bytes, offered from pos on) and the output object (out written) as
   inflate()'s buffers, with their tokens *)
Lemma rtl_bufs_pre vs L cp b pos O op n out:
  isptr vs -> Zlength O <= b -> Zlength out <= n ->
  data_at Ews (tarray tuchar b) (rtl_oc b O) cp * malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar n) (rtl_oc n out) op * malloc_token Ews (tarray tuchar n) op
  |-- bufs_opt (is_live vs (Some L)) (rtl_ib cp b pos O) (Some (rtl_ob op n out)) [] true true.
Proof.
  intros Pv Hb Hn. rewrite rtl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, rtl_ib, rtl_ob.
  rewrite app_nil_l, Zlength_nil, Z.add_0_r.
  rewrite (sublist_rejoin 0 (Zlength out) n) by (pose proof (Zlength_nonneg out); rewrite ?rtl_oc_len; lia).
  rewrite sublist_same by (rewrite ?rtl_oc_len; lia).
  rewrite !rtl_bytes_i, !rtl_tok_i. cancel.
Qed.

Lemma rtl_bufs_post vs L cp b pos O op n out ow:
  isptr vs -> Zlength O <= b -> Zlength out + Zlength ow <= n ->
  bufs_opt (is_live vs (Some L)) (rtl_ib cp b pos O) (Some (rtl_ob op n out)) ow true true
  |-- data_at Ews (tarray tuchar b) (rtl_oc b O) cp * malloc_token Ews (tarray tuchar b) cp *
      data_at Ews (tarray tuchar n) (rtl_oc n (out ++ ow)) op * malloc_token Ews (tarray tuchar n) op.
Proof.
  intros Pv Hb Hn. rewrite rtl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, rtl_ib, rtl_ob.
  rewrite rtl_oc_after by auto.
  rewrite !rtl_bytes_i, !rtl_tok_i. cancel.
Qed.

Lemma rtl_in_ok cp b pos len O: isptr cp -> Zlength O <= b -> b <= Ptrofs.max_unsigned -> rbytes O ->
  0 <= pos -> 0 <= len -> pos + len <= Zlength O ->
  in_ok (rtl_ib cp b pos O) (sublist pos (pos + len) O).
Proof.
  intros Pc Hb Hm BO Hp Hl Hpl. unfold in_ok, rtl_ib.
  assert (Hs: Zlength (sublist pos (pos + len) O) = len) by (rewrite Zlength_sublist; lia).
  rewrite Hs. pose proof (Zlength_nonneg O).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [apply rtl_oc_len; lia | ]. split; [lia | ]. split.
  - unfold rtl_oc. rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact BO]. simpl. intros; rep_lia.
Qed.

Lemma rtl_out_ok op n out ao: isptr op -> n <= Ptrofs.max_unsigned -> 0 <= ao -> Zlength out + ao <= n ->
  out_ok (rtl_ob op n out) ao.
Proof.
  intros Po Hn Ha Hao. unfold out_ok, rtl_ob. pose proof (Zlength_nonneg out).
  split; [apply writable_Ews | ]. repeat split; auto; try lia. apply rtl_oc_len; lia.
Qed.

(* a pointer into an object of b bytes, not past its last byte, is valid *)
Lemma rtl_valid_in sh b (c: list val) p i: sepalg.nonidentity sh -> 0 <= i < b ->
  data_at sh (tarray tuchar b) c p |-- valid_pointer (offset_val i p).
Proof.
  intros N Hi. sep_apply (data_at_data_at_ sh (tarray tuchar b) c p). rewrite data_at__memory_block. Intros.
  apply memory_block_valid_pointer; auto. simpl. rewrite Z.max_r by lia. lia.
Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes left *)
Lemma rtl_ptr_sub (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_sub_default tulong tulong (Vlong (Int64.repr m)) (force_val (sem_sub_pp tuchar (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. destruct p; try contradiction. simpl.
  unfold sem_sub_pp, sem_sub_default. simpl. destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

(* (size_t) (p + k - p) *)
Lemma rtl_ptr_diff (p: val) k: isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val k p) p) = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. destruct p; try contradiction. unfold sem_sub_pp. simpl.
  destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* bytes_eq's slices: the first len bytes of the output object and of the data *)
Lemma rtl_cbuf_out (op: val) n w: isptr op -> Zlength w <= n -> is_bytes w ->
  cbuf_ok false op Ews op 0 n (Zlength w) (rtl_oc n w) w.
Proof.
  intros Po Hn Hb. unfold cbuf_ok. pose proof (Zlength_nonneg w).
  split; [destruct op; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [reflexivity | ]. split; [auto | ].
  unfold rtl_oc. rewrite Z.add_0_l. rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
  apply sublist_same; auto. unfold bytes_rep; rewrite Zlength_map; reflexivity.
Qed.

Lemma rtl_cbuf_data (dp: val) D len: isptr dp -> 0 <= len <= Zlength D -> is_bytes D ->
  cbuf_ok false dp Ews dp 0 (Zlength D) len (bytes_rep D) (sublist 0 len D).
Proof.
  intros Pd Hl Hb. unfold cbuf_ok.
  split; [destruct dp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [rewrite Zlength_sublist; lia | ].
  split; [apply Forall_sublist; auto | ].
  rewrite Z.add_0_l. unfold bytes_rep. rewrite sublist_map. reflexivity.
Qed.

Lemma rtl_sameblock (p: val) k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* inflate()'s return code is one of zlib's codes Z_VERSION_ERROR .. Z_NEED_DICT *)
Lemma rtl_ret_range flush strmp z st ib inp ob r z' st' ow :
  inflate_rel flush strmp z st ib inp ob r z' st' ow -> -5 <= r <= 2.
Proof.
  intros [(_ & -> & _) | (_ & L & o & res & winp & _ & _ & Hrun & _ & -> & _)].
  - unfold Z_STREAM_ERROR. lia.
  - eapply Zlib.proof.uncompr.URunRet.run2_ret; [ | exact Hrun ]. simpl. unfold Z_OK. lia.
Qed.

Lemma rt_loop : rt_loop_stmt.
Proof.
  intros Espec P wbits n b lim D O dp op cp vc vd gv PF FA.
  destruct FA as (DF & HD & Hn & HO & Hb & Hw & BD & BD' & BO & Pdp & Pop & Pcp & Hlim).
  unfold max_size in Hn.
  unfold rt_seg25, Delta_rt, POST_B, POST_rt. abbreviate_semax.
  forward_loop (rt_inv P wbits n b lim D O dp op cp vc vd gv)
    break: (rt_inv P wbits n b lim D O dp op cp vc vd gv).
  { apply ENTAIL_refl. }
  2: { unfold rt_inv. Intros pos out z L. forward. Exists (Int.repr 0). sep_apply rtl_a_frame. entailer!. }
  unfold rt_inv. Intros pos out z L.
  rewrite rtl_istreamA_unfold. Intros.
  unfold rtl_tup. rewrite H2, H3.
  forward.
  forward_if.
  { apply denote_tc_test_eq_split.
    - sep_apply (rtl_valid_in Ews b (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp pos); [auto | lia | ].
      repeat apply sepcon_valid_pointer1. apply derives_refl.
    - sep_apply (rtl_valid_in Ews b (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp lim); [auto | lia | ].
      repeat apply sepcon_valid_pointer1. apply derives_refl. }
  2: { forward. unfold rt_inv. Exists pos out z L. rewrite rtl_istreamA_unfold. unfold rtl_tup. rewrite H2, H3.
       entailer!. }
  assert (Hpl: pos < lim).
  { assert (pos <> lim); [ | lia]. intro E; subst pos. apply H7. destruct cp; try contradiction. simpl. f_equal.
    f_equal. unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity. }
  clear H7.
  assert_PROP (isptr vd) as Pvd by entailer!.
  destruct (px_ok P PF _ _ _ _ _ _ _ _ H) as (Hhd & _ & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  forward.
  forward_call (lim - pos).
  { apply prop_right. apply rtl_sameblock; auto. }
  { entailer!. rewrite rtl_ptr_sub by (auto; lia). reflexivity. }
  forward.
  forward.
  forward_call (n - Zlength out).
  { apply prop_right. apply rtl_sameblock; auto. }
  { entailer!. rewrite rtl_ptr_sub by (auto; unfold max_size in *; rep_lia). reflexivity. }
  forward.
  (* the call: the next piece of the prefix and the rest of the output object *)
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ai := Z.min (lim - pos) Int.max_unsigned).
  set (ao := Z.min (n - Zlength out) Int.max_unsigned).
  assert (Hai: 0 <= ai <= lim - pos /\ ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  assert (Hao: 0 <= ao <= n - Zlength out /\ ao <= Int.max_unsigned) by (unfold ao; rep_lia).
  clearbody ai ao.
  set (inp := sublist pos (pos + ai) O).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := rtl_ib cp b pos O). set (o := rtl_ob op n out).
  replace (offset_val pos cp) with (in_ptr ib 0) by (unfold ib, rtl_ib; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) op) with (out_ptr o 0)
    by (unfold o, rtl_ob; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (rtl_offer_fold gv vd z L ib o ai ao); auto; try lia.
  change (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) with (rtl_oc b O).
  change (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) with (rtl_oc n out).
  sep_apply (rtl_bufs_pre vd L cp b pos O op n out); auto; try lia. fold ib o.
  unfold R_rt, R_of, Zlib.proof.deflate.DSpec.deflate_globals. Intros.
  assert (INOK: in_ok ib inp) by (apply rtl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply rtl_out_ok; auto; unfold max_size in *; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (rtl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  forward.
  forward_if.
  { (* Z_MEM_ERROR ends the run *)
    forward. Exists (Int.repr 0). sep_apply (rtl_a_frame_opt gv Tsh vd z' Vundef st'); auto. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (CP: call_pre O pos z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj H6 (conj H4 (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, rtl_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel flush vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  destruct (px_call P PF wbits D O pos out z L vd flush ib inp o ao lim r z' st' ow H CP
              ltac:(lia) ltac:(lia) REL' Hr Zo')
    as (L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & Hnend & HP').
  subst st'.
  destruct (px_ok P PF _ _ _ _ _ _ _ _ HP') as (Hhd' & _ & rest' & Erest').
  rewrite rtl_istreamA_opt_ptr by auto.
  rewrite (rtl_head_none vd L') by auto.
  unfold ib, o. sep_apply (rtl_bufs_post vd L cp b pos O op n out ow); auto; try lia.
  (* the check: code != Z_STREAM_END *)
  rewrite rtl_istreamA_unfold. Intros. unfold rtl_tup.
  assert (Eno: zf_no z' = offset_val (Zlength (out ++ ow)) op)
    by (rewrite Hno'; unfold o, rtl_ob; simpl; f_equal; rewrite Zlength_app; lia).
  rewrite Eno.
  pose proof (rtl_ret_range _ _ _ _ _ _ _ _ _ _ _ REL) as Hrr.
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int.eq.
    destruct (zeq (Int.unsigned (Int.repr r)) (Int.unsigned (Int.repr 1))) as [E | E]; [ | reflexivity ].
    exfalso. apply Hnend. apply (f_equal Int.repr) in E. rewrite !Int.repr_unsigned in E.
    apply repr_inj_signed in E; [ exact E | unfold repable_signed; rep_lia | unfold repable_signed; rep_lia ]. }
  (* the invariant again *)
  unfold rt_inv. Exists (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
  rewrite rtl_istreamA_unfold. unfold rtl_tup. rewrite Eno.
  assert (Eni: zf_ni z' = offset_val (pos + (Zlength inp - zf_ai z')) cp)
    by (rewrite Hni'; unfold ib, rtl_ib; reflexivity).
  unfold rtl_oc, R_rt, R_of, Zlib.proof.deflate.DSpec.deflate_globals. entailer!.
Qed.

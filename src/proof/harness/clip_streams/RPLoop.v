(* Law rt_partial, main: the part rp_loop_stmt of the inflate half (RPKit.v). *)
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
Require Import Zlib.proof.harness.clip_streams.RPKit.
Require Import Zlib.harness.rt_partial.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Moves between the units' compspecs and the law's                                              *)

Ltac rp_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma rpl_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rp_cs_tac CC_inflate. Qed.
Lemma rpl_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma rpl_bytes_a sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. rp_cs_tac CC_adler32. Qed.

(* the 14 members of struct z_stream *)
Definition rpl_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma rpl_strm_cs sh (v: rpl_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. rp_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition rpl_tup (gv: globals) (z: zfields) (adv sp: val) : rpl_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma rpl_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (rpl_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rpl_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma rpl_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rpl_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rpl_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite rpl_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma rpl_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite rpl_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma rpl_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsl vs * TT.
Proof.
  intros Pv. rewrite rpl_istreamA_opt_ptr by auto. destruct st as [L|]; [apply rpl_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite rpl_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The objects of one inflate() call                                                             *)

(* the output object: out written, then undefined bytes *)
Definition rpl_oc (n: Z) (out: list Z) : list val := bytes_rep out ++ Zrepeat Vundef (n - Zlength out).

(* the input object: the compressed bytes O at the start of the object of b bytes; the call is offered the
   bytes [pos, pos + take) *)
Definition rpl_ib (cp: val) (b pos: Z) (O: list Z) : inbuf := InBuf Ews cp pos b (rpl_oc b O).
Definition rpl_ob (op: val) (n: Z) (out: list Z) : outbuf := OutBuf Ews op (Zlength out) n (rpl_oc n out).

Lemma rpl_oc_len n out: Zlength out <= n -> Zlength (rpl_oc n out) = n.
Proof.
  intros H. unfold rpl_oc, bytes_rep. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia.
Qed.

(* after the call: out ++ ow written *)
Lemma rpl_oc_after n out ow: Zlength out + Zlength ow <= n ->
  sublist 0 (Zlength out) (rpl_oc n out) ++ byte_vals ow ++
    sublist (Zlength out + Zlength ow) n (rpl_oc n out) = rpl_oc n (out ++ ow).
Proof.
  intros H. pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  unfold rpl_oc, bytes_rep, byte_vals.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map.
  rewrite map_app, <- app_assoc. f_equal. f_equal. rewrite Zlength_app.
  unfold Zrepeat. rewrite sublist_repeat by (try rewrite Zlength_repeat; lia).
  f_equal. f_equal. lia.
Qed.

Lemma rpl_zf_ok gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st |-- !! zf_ok z.
Proof.
  intros Pv. rewrite rpl_istreamA_opt_ptr by auto. unfold istreamA. destruct st; entailer!.
Qed.

(* the struct after the harness's stores into avail_in / avail_out: the stream inflate() takes *)
Lemma rpl_offer_fold gv vs z L ib o ai ao:
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
  rewrite rpl_head_none, rpl_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  rewrite rpl_istreamA_unfold. unfold rpl_tup, offer_z, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* the input object (the compressed bytes, offered from pos on) and the output object (out written) as
   inflate()'s buffers, with their tokens *)
Lemma rpl_bufs_pre vs L cp b pos O op n out:
  isptr vs -> Zlength O <= b -> Zlength out <= n ->
  data_at Ews (tarray tuchar b) (rpl_oc b O) cp * malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar n) (rpl_oc n out) op * malloc_token Ews (tarray tuchar n) op
  |-- bufs_opt (is_live vs (Some L)) (rpl_ib cp b pos O) (Some (rpl_ob op n out)) [] true true.
Proof.
  intros Pv Hb Hn. rewrite rpl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, rpl_ib, rpl_ob.
  rewrite app_nil_l, Zlength_nil, Z.add_0_r.
  rewrite (sublist_rejoin 0 (Zlength out) n) by (pose proof (Zlength_nonneg out); rewrite ?rpl_oc_len; lia).
  rewrite sublist_same by (rewrite ?rpl_oc_len; lia).
  rewrite !rpl_bytes_i, !rpl_tok_i. cancel.
Qed.

Lemma rpl_bufs_post vs L cp b pos O op n out ow:
  isptr vs -> Zlength O <= b -> Zlength out + Zlength ow <= n ->
  bufs_opt (is_live vs (Some L)) (rpl_ib cp b pos O) (Some (rpl_ob op n out)) ow true true
  |-- data_at Ews (tarray tuchar b) (rpl_oc b O) cp * malloc_token Ews (tarray tuchar b) cp *
      data_at Ews (tarray tuchar n) (rpl_oc n (out ++ ow)) op * malloc_token Ews (tarray tuchar n) op.
Proof.
  intros Pv Hb Hn. rewrite rpl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, rpl_ib, rpl_ob.
  rewrite rpl_oc_after by auto.
  rewrite !rpl_bytes_i, !rpl_tok_i. cancel.
Qed.

Lemma rpl_in_ok cp b pos len O: isptr cp -> Zlength O <= b -> b <= Ptrofs.max_unsigned -> rbytes O ->
  0 <= pos -> 0 <= len -> pos + len <= Zlength O ->
  in_ok (rpl_ib cp b pos O) (sublist pos (pos + len) O).
Proof.
  intros Pc Hb Hm BO Hp Hl Hpl. unfold in_ok, rpl_ib.
  assert (Hs: Zlength (sublist pos (pos + len) O) = len) by (rewrite Zlength_sublist; lia).
  rewrite Hs. pose proof (Zlength_nonneg O).
  split; [auto | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [apply rpl_oc_len; lia | ]. split; [lia | ]. split.
  - unfold rpl_oc. rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist. eapply Forall_impl; [ | exact BO]. simpl. intros; rep_lia.
Qed.

Lemma rpl_out_ok op n out ao: isptr op -> n <= Ptrofs.max_unsigned -> 0 <= ao -> Zlength out + ao <= n ->
  out_ok (rpl_ob op n out) ao.
Proof.
  intros Po Hn Ha Hao. unfold out_ok, rpl_ob. pose proof (Zlength_nonneg out).
  split; [apply writable_Ews | ]. repeat split; auto; try lia. apply rpl_oc_len; lia.
Qed.

(* a pointer into an object of b bytes, not past its last byte, is valid *)
Lemma rpl_valid_in sh b (c: list val) p i: sepalg.nonidentity sh -> 0 <= i < b ->
  data_at sh (tarray tuchar b) c p |-- valid_pointer (offset_val i p).
Proof.
  intros N Hi. sep_apply (data_at_data_at_ sh (tarray tuchar b) c p). rewrite data_at__memory_block. Intros.
  apply memory_block_valid_pointer; auto. simpl. rewrite Z.max_r by lia. lia.
Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes left *)
Lemma rpl_ptr_sub (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
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
Lemma rpl_ptr_diff (p: val) k: isptr p -> 0 <= k <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tuchar (offset_val k p) p) = Vlong (Int64.repr k).
Proof.
  intros Pp Hk. destruct p; try contradiction. unfold sem_sub_pp. simpl.
  destruct (eq_block b b); [ | congruence]. simpl.
  rewrite Ptrofs.sub_add_l, Ptrofs.sub_idem, Ptrofs.add_zero_l.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by (cbv; congruence).
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* bytes_eq's slices: the first len bytes of the output object and of the data *)
Lemma rpl_cbuf_out (op: val) n w: isptr op -> Zlength w <= n -> is_bytes w ->
  cbuf_ok false op Ews op 0 n (Zlength w) (rpl_oc n w) w.
Proof.
  intros Po Hn Hb. unfold cbuf_ok. pose proof (Zlength_nonneg w).
  split; [destruct op; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [reflexivity | ]. split; [auto | ].
  unfold rpl_oc. rewrite Z.add_0_l. rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
  apply sublist_same; auto. unfold bytes_rep; rewrite Zlength_map; reflexivity.
Qed.

Lemma rpl_cbuf_data (dp: val) D len: isptr dp -> 0 <= len <= Zlength D -> is_bytes D ->
  cbuf_ok false dp Ews dp 0 (Zlength D) len (bytes_rep D) (sublist 0 len D).
Proof.
  intros Pd Hl Hb. unfold cbuf_ok.
  split; [destruct dp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
  split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [rewrite Zlength_sublist; lia | ].
  split; [apply Forall_sublist; auto | ].
  rewrite Z.add_0_l. unfold bytes_rep. rewrite sublist_map. reflexivity.
Qed.

Lemma rpl_sameblock (p: val) k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

Lemma rp_loop : rp_loop_stmt.
Proof.
  intros Espec P wbits n b lim D O dp ep op cp vc vd gv PF FA.
  destruct FA as (DF & HD & Hn & HO & Hb & Hw & BD & BD' & BO & Pdp & Pop & Pcp & Hlim & Pep).
  unfold max_size in Hn.
  unfold rp_seg26, Delta_rp, POST_B, POST_rp. abbreviate_semax.
  forward_loop (rp_inv P wbits n b lim D O dp ep op cp vc vd gv)
    break: (rp_inv P wbits n b lim D O dp ep op cp vc vd gv).
  { apply ENTAIL_refl. }
  2: { unfold rp_inv. Intros pos out z L. forward. Exists (Int.repr 0). sep_apply rpl_a_frame. entailer!. }
  unfold rp_inv. Intros pos out z L.
  rewrite rpl_istreamA_unfold. Intros.
  unfold rpl_tup. rewrite H2, H3.
  forward.
  forward_if.
  { apply denote_tc_test_eq_split.
    - sep_apply (rpl_valid_in Ews b (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp pos); [auto | lia | ].
      repeat apply sepcon_valid_pointer1. apply derives_refl.
    - sep_apply (rpl_valid_in Ews b (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp lim); [auto | lia | ].
      repeat apply sepcon_valid_pointer1. apply derives_refl. }
  2: { forward. unfold rp_inv. Exists pos out z L. rewrite rpl_istreamA_unfold. unfold rpl_tup. rewrite H2, H3.
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
  { apply prop_right. apply rpl_sameblock; auto. }
  { entailer!. rewrite rpl_ptr_sub by (auto; lia). reflexivity. }
  forward.
  forward.
  forward_call (n - Zlength out).
  { apply prop_right. apply rpl_sameblock; auto. }
  { entailer!. rewrite rpl_ptr_sub by (auto; unfold max_size in *; rep_lia). reflexivity. }
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
  set (ib := rpl_ib cp b pos O). set (o := rpl_ob op n out).
  replace (offset_val pos cp) with (in_ptr ib 0) by (unfold ib, rpl_ib; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) op) with (out_ptr o 0)
    by (unfold o, rpl_ob; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (rpl_offer_fold gv vd z L ib o ai ao); auto; try lia.
  change (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) with (rpl_oc b O).
  change (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) with (rpl_oc n out).
  sep_apply (rpl_bufs_pre vd L cp b pos O op n out); auto; try lia. fold ib o.
  unfold R_rp, R_of, Zlib.proof.deflate.DSpec.deflate_globals. Intros.
  assert (INOK: in_ok ib inp) by (apply rpl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply rpl_out_ok; auto; unfold max_size in *; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (rpl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  forward_if.
  { (* Z_MEM_ERROR ends the run *)
    forward. Exists (Int.repr 0). sep_apply (rpl_a_frame_opt gv Tsh vd z' Vundef st'); auto. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (CP: call_pre O pos z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj H6 (conj H4 (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, rpl_ib; discriminate.
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
  rewrite rpl_istreamA_opt_ptr by auto.
  rewrite (rpl_head_none vd L') by auto.
  unfold ib, o. sep_apply (rpl_bufs_post vd L cp b pos O op n out ow); auto; try lia.
  (* the check: the bytes written so far are the first bytes of the data *)
  rewrite rpl_istreamA_unfold. Intros. unfold rpl_tup.
  assert (Eno: zf_no z' = offset_val (Zlength (out ++ ow)) op)
    by (rewrite Hno'; unfold o, rpl_ob; simpl; f_equal; rewrite Zlength_app; lia).
  rewrite Eno.
  forward.
  assert (Hwn: Zlength (out ++ ow) <= n) by (rewrite Zlength_app; lia).
  assert (Ew: sublist 0 (Zlength (out ++ ow)) D = out ++ ow)
    by (rewrite Erest', sublist_app1 by (pose proof (Zlength_nonneg (out ++ ow)); lia); apply sublist_same; lia).
  unfold rp_exp. Intros.
  rewrite <- (rpl_bytes_a Ews n (rpl_oc n (out ++ ow)) op), <- (rpl_bytes_a Ews n (bytes_rep D) ep).
  forward_call (op, Ews, op, 0, n, rpl_oc n (out ++ ow), out ++ ow, ep, Ews, ep, 0, n, bytes_rep D,
                sublist 0 (Zlength (out ++ ow)) D, Zlength (out ++ ow)).
  { apply prop_right. apply rpl_sameblock; auto. }
  { entailer!. rewrite rpl_ptr_diff by (auto; unfold max_size in *; rep_lia). reflexivity. }
  { split.
    - apply rpl_cbuf_out; auto. rewrite Erest' in BD'. apply Forall_app in BD'. apply BD'.
    - rewrite <- HD. pose proof (Zlength_nonneg (out ++ ow)). apply rpl_cbuf_data; auto. lia. }
  rewrite Ew. destruct (list_eq_dec Z.eq_dec (out ++ ow) (out ++ ow)) as [_ | C]; [ | contradiction].
  forward_call (Int.repr 1).
  rewrite (rpl_bytes_a Ews n (rpl_oc n (out ++ ow)) op), (rpl_bytes_a Ews n (bytes_rep D) ep).
  (* the invariant again *)
  unfold rp_inv. Exists (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
  rewrite rpl_istreamA_unfold. unfold rpl_tup. rewrite Eno.
  assert (Eni: zf_ni z' = offset_val (pos + (Zlength inp - zf_ai z')) cp)
    by (rewrite Hni'; unfold ib, rpl_ib; reflexivity).
  unfold rpl_oc, rp_exp, R_rp, R_of, Zlib.proof.deflate.DSpec.deflate_globals. entailer!.
Qed.

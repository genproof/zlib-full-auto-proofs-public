(* Law rfc_trailing_bytes, main: the kit of the proof of statement 34 of TBKit.v (the do-while of inflate() calls
   until Z_STREAM_END, then gp_assert(next_in == input + compressed_len) and return 0; TBLoop.v):
   - moves between the inflate unit's compspecs and the law's, the struct z_stream as istreamA holds it, the
     input and output objects as inflate()'s buffers (as BCSegILoop.v for rj_bad_checksum);
   - the assertions inside the loop: tbl_st (the stream unfolded, the harness's stores into avail_in / avail_out
     pending or done), tbl_cont (at the loop's test), tbl_brk (after the loop);
   - the parts of the loop's body (tbl_x1: avail_in = clip(...), tbl_x2: avail_out = clip(...), tbl_x34: the
     inflate() call, the Z_MEM_ERROR return and the check of the code) and the CPS statements of their proofs (TBLoopIn.v,
     TBLoopOut.v, TBLoopCall.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.deflate.DSpec.
Require Zlib.proof.uncompr.URunRet.
Require Import Zlib.proof.harness.clip_streams.CS Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.TBFacts Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.TBKit.
Require Import Zlib.harness.rfc_trailing_bytes.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* Moves between the inflate unit's compspecs and the law's                                       *)

Ltac tbl_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma tbl_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. tbl_cs_tac CC_inflate. Qed.
Lemma tbl_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the 14 members of struct z_stream *)
Definition tbl_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma tbl_strm_cs sh (v: tbl_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS sh t_zsl v q.
Proof. tbl_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition tbl_tup (gv: globals) (z: zfields) (adv sp: val) : tbl_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma tbl_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (tbl_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite tbl_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma tbl_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma tbl_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma tbl_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite tbl_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

Lemma tbl_head_emp L: i_head (l_s L) = false -> head_opt (Some L) = emp.
Proof. intros H. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma tbl_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite tbl_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma tbl_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsl vs * TT.
Proof.
  intros Pv. rewrite tbl_istreamA_opt_ptr by auto. destruct st as [L|]; [apply tbl_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite tbl_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

Lemma tbl_zf_ok gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st |-- !! zf_ok z.
Proof.
  intros Pv. rewrite tbl_istreamA_opt_ptr by auto. unfold istreamA. destruct st; entailer!.
Qed.

(* the struct after the harness's stores into avail_in / avail_out: the stream inflate() takes *)
Lemma tbl_offer_fold gv vs z L ib o ai ao:
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
  rewrite tbl_head_none, tbl_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  rewrite tbl_istreamA_unfold. unfold tbl_tup, offer_z, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes left *)
Lemma tbl_ptr_sub (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
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

Lemma tbl_sameblock (p: val) k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The objects of one inflate() call                                                             *)

(* an object of n bytes holding the bytes l first, undefined bytes after *)
Definition tbl_oc (n: Z) (l: list Z) : list val := bytes_rep l ++ Zrepeat Vundef (n - Zlength l).

Lemma tbl_oc_len n l: Zlength l <= n -> Zlength (tbl_oc n l) = n.
Proof. intros H. unfold tbl_oc, bytes_rep. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

(* after the call: out ++ ow written *)
Lemma tbl_oc_after n out ow: Zlength out + Zlength ow <= n ->
  sublist 0 (Zlength out) (tbl_oc n out) ++ byte_vals ow ++
    sublist (Zlength out + Zlength ow) n (tbl_oc n out) = tbl_oc n (out ++ ow).
Proof.
  intros H. pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  unfold tbl_oc, bytes_rep, byte_vals.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map.
  rewrite map_app, <- app_assoc. f_equal. f_equal. rewrite Zlength_app.
  unfold Zrepeat. rewrite sublist_repeat by (try rewrite Zlength_repeat; lia).
  f_equal. f_equal. lia.
Qed.

(* the input object: src at the start of the object of b bytes at cp, offered from pos on; the output object:
   out written at the start of the object of n bytes at op *)
Definition tbl_ib (cp: val) (b pos: Z) (src: list Z) : inbuf := InBuf Ews cp pos b (tbl_oc b src).
Definition tbl_ob (op: val) (n: Z) (out: list Z) : outbuf := OutBuf Ews op (Zlength out) n (tbl_oc n out).

Lemma tbl_in_ok cp b pos take src:
  isptr cp -> 0 <= pos -> 0 <= take -> pos + take <= Zlength src -> Zlength src <= b ->
  b <= Ptrofs.max_unsigned -> bytes_ok src ->
  in_ok (tbl_ib cp b pos src) (sublist pos (pos + take) src).
Proof.
  intros Pc H1 H2 H3 H4 H5 H6. unfold in_ok, tbl_ib.
  rewrite Zlength_sublist by lia.
  split; [apply writable_readable, writable_Ews | ]. repeat split; auto; try lia.
  - apply tbl_oc_len; lia.
  - unfold tbl_oc. replace (pos + (pos + take - pos)) with (pos + take) by lia.
    rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist; auto.
Qed.

Lemma tbl_out_ok op n out room:
  isptr op -> 0 <= room -> Zlength out + room <= n -> n <= Ptrofs.max_unsigned ->
  out_ok (tbl_ob op n out) room.
Proof.
  intros Po H1 H2 H3. pose proof (Zlength_nonneg out). unfold out_ok, tbl_ob.
  split; [apply writable_Ews | ]. repeat split; auto; try lia. apply tbl_oc_len; lia.
Qed.

(* the two objects as inflate()'s buffers, and back *)
Lemma tbl_bufs_pre vs L cp b pos src op n out:
  isptr vs -> Zlength src <= b -> Zlength out <= n ->
  data_at Ews (tarray tuchar b) (tbl_oc b src) cp * malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar n) (tbl_oc n out) op * malloc_token Ews (tarray tuchar n) op
  |-- bufs_opt (is_live vs (Some L)) (tbl_ib cp b pos src) (Some (tbl_ob op n out)) [] true true.
Proof.
  intros Pv Hb Hn. rewrite tbl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, tbl_ib, tbl_ob.
  rewrite (tbl_oc_after n out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !tbl_bytes_i, !tbl_tok_i. cancel.
Qed.

Lemma tbl_bufs_post vs L cp b pos src op n out ow:
  isptr vs -> Zlength out + Zlength ow <= n ->
  bufs_opt (is_live vs (Some L)) (tbl_ib cp b pos src) (Some (tbl_ob op n out)) ow true true
  |-- data_at Ews (tarray tuchar b) (tbl_oc b src) cp * malloc_token Ews (tarray tuchar b) cp *
      data_at Ews (tarray tuchar n) (tbl_oc n (out ++ ow)) op * malloc_token Ews (tarray tuchar n) op.
Proof.
  intros Pv Hn. rewrite tbl_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, tbl_ib, tbl_ob.
  rewrite (tbl_oc_after n out ow) by lia.
  rewrite !tbl_bytes_i, !tbl_tok_i. cancel.
Qed.

(* inflate()'s return code is one of zlib's codes Z_VERSION_ERROR .. Z_NEED_DICT *)
Lemma tbl_ret_range flush strmp z st ib inp ob r z' st' ow :
  inflate_rel flush strmp z st ib inp ob r z' st' ow -> -5 <= r <= 2.
Proof.
  intros [(_ & -> & _) | (_ & L & o & res & winp & _ & _ & Hrun & _ & -> & _)].
  - unfold Z_STREAM_ERROR. lia.
  - eapply Zlib.proof.uncompr.URunRet.run2_ret; [ | exact Hrun ]. simpl. unfold Z_OK. lia.
Qed.

(* a pointer into an object of n bytes, up to one past its last byte, may be compared (when the object is
   empty, its own address is valid by its malloc token) *)
Lemma tbl_weak_valid sh n (c: list val) p i: sepalg.nonidentity sh -> 0 <= i <= n ->
  data_at sh (tarray tuchar n) c p * malloc_token sh (tarray tuchar n) p * TT
  |-- weak_valid_pointer (offset_val i p).
Proof.
  intros N Hi. apply sepcon_weak_valid_pointer1. destruct (zlt 0 n).
  - sep_apply (data_at_data_at_ sh (tarray tuchar n) c p). rewrite data_at__memory_block. Intros.
    apply sepcon_weak_valid_pointer1. apply memory_block_weak_valid_pointer; auto; simpl; rewrite ?Z.max_r; lia.
  - assert (n = 0) by lia. assert (i = 0) by lia. subst n i.
    assert_PROP (isptr p) by (rewrite data_at_isptr; entailer!). rewrite isptr_offset_val_zero by auto.
    apply sepcon_weak_valid_pointer2. eapply derives_trans; [ | apply valid_pointer_weak].
    apply malloc_token_valid_pointer. simpl. lia.
Qed.

Section TestEq.
Local Transparent denote_tc_test_eq.
(* comparing a pointer with itself needs it weakly valid only *)
Lemma tbl_test_eq_self (q: val): isptr q -> weak_valid_pointer q |-- denote_tc_test_eq q q.
Proof.
  intros Pq. destruct q; try contradiction. unfold denote_tc_test_eq, test_eq_ptrs, sameblock.
  destruct (peq b b); [ | congruence]. simpl. apply andp_right; apply derives_refl.
Qed.
End TestEq.

(* the state after a call that did not run out of memory, at the loop's test: the code r; P holds unless r is
   Z_STREAM_END, which comes with all the bytes of O consumed *)
Definition tbl_cont (P : inv_t) (wbits n : Z) (D O src : list Z) (dp op ip vc vd : val) (gv : globals)
    : environ -> mpred :=
  EX r : Z, EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (-5 <= r <= 2; r <> Z_STREAM_END -> P wbits D O src pos out z L; r = Z_STREAM_END -> pos = Zlength O;
        swfW (l_s L); zf_ni z = offset_val pos ip; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _code (Vint (Int.repr r));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _after (Vlong (Int64.repr (Zlength src - Zlength O))); temp _input ip;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L); Zlib.proof.inflate.Callees.zfuncs gv;
       mem_mgr gv; R_tb gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ip;
       malloc_token Ews (tarray tuchar (Zlength src)) ip;
       data_at_ Tsh t_zsl vc; TT).

(* after the loop: next_in is input + |O| *)
Definition tbl_brk (O src : list Z) (ip vc vd : val) (gv : globals) : environ -> mpred :=
  EX z : zfields, EX L : live,
  PROP (zf_ni z = offset_val (Zlength O) ip)
  LOCAL (temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _input ip;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L);
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ip;
       malloc_token Ews (tarray tuchar (Zlength src)) ip;
       data_at_ Tsh t_zsl vc; TT).

(* ---------------------------------------------------------------------------------------------- *)
(* The loop's body and its parts                                                                  *)

(* statement 34 is `do body while (code != Z_STREAM_END); gp_assert(...); return 0` *)
Definition tbl_body : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [tb_seg34] in tb_seg34 in
        lazymatch x with Ssequence (Sloop ?b _) _ => exact b end).

Definition tbl_x1 : statement :=
  ltac:(let x := eval cbv delta [tbl_body] in tbl_body in lazymatch x with Ssequence ?a _ => exact a end).
Definition tbl_x2 : statement :=
  ltac:(let x := eval cbv delta [tbl_body] in tbl_body in
        lazymatch x with Ssequence _ (Ssequence ?a _) => exact a end).
Definition tbl_x34 : statement :=
  ltac:(let x := eval cbv delta [tbl_body] in tbl_body in
        lazymatch x with Ssequence _ (Ssequence _ ?a) => exact a end).

Lemma tbl_body_eq : tbl_body = Ssequence tbl_x1 (Ssequence tbl_x2 tbl_x34).
Proof. reflexivity. Qed.

(* inside the body: the stream (z, L) unfolded, with vai / vao in its avail_in / avail_out (z's own before the
   stores, clip(...) after them), P at pos and out; the rest as in tb_inv *)
Definition tbl_st (P : inv_t) (wbits n : Z) (D O src : list Z) (dp op ip vc vd : val) (gv : globals)
    (pos : Z) (out : list Z) (z : zfields) (L : live) (vai vao : val) : environ -> mpred :=
  PROP (P wbits D O src pos out z L; swfW (l_s L); zf_ok z; live_ok L)
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         temp _after (Vlong (Int64.repr (Zlength src - Zlength O))); temp _input ip;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at Tsh t_zsl
         (offset_val pos ip, (vai, (Vlong (Int64.repr (zf_tin z)), (offset_val (Zlength out) op, (vao,
          (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
          (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
          (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))) vd;
       state_mem gv vd L; Zlib.proof.inflate.Callees.zfuncs gv; mem_mgr gv; R_tb gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) ip;
       malloc_token Ews (tarray tuchar (Zlength src)) ip;
       data_at_ Tsh t_zsl vc; TT).

(* avail_in = clip(compressed_len + after - (next_in - input)): the bytes of src not consumed, at most 2^32 - 1 *)
Definition tbl_in_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n D O src dp op ip vc vd gv pos out z L vai vao Y R,
  tail_facts P -> tb_facts wbits n D O src dp op ip ->
  semax Delta_tb (tbl_st P wbits n D O src dp op ip vc vd gv pos out z L
                    (Vint (Int.repr (Z.min (Zlength src - pos) Int.max_unsigned))) vao) Y R ->
  semax Delta_tb (tbl_st P wbits n D O src dp op ip vc vd gv pos out z L vai vao) (Ssequence tbl_x1 Y) R.

(* avail_out = clip(data_len - (next_out - out)): the room left in the output object *)
Definition tbl_out_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n D O src dp op ip vc vd gv pos out z L vai vao Y R,
  tail_facts P -> tb_facts wbits n D O src dp op ip ->
  semax Delta_tb (tbl_st P wbits n D O src dp op ip vc vd gv pos out z L vai
                    (Vint (Int.repr (Z.min (n - Zlength out) Int.max_unsigned)))) Y R ->
  semax Delta_tb (tbl_st P wbits n D O src dp op ip vc vd gv pos out z L vai vao) (Ssequence tbl_x2 Y) R.

(* code = inflate(&decompressor, any flush), `if (code == Z_MEM_ERROR) return 0` and the gp_assert of the code:
   the loop's test is reached with tbl_cont (TBFacts.tl_call) *)
Definition tbl_call_stmt : Prop :=
  forall {Espec : OracleKind} P wbits n D O src dp op ip vc vd gv pos out z L,
  tail_facts P -> tb_facts wbits n D O src dp op ip ->
  semax Delta_tb (tbl_st P wbits n D O src dp op ip vc vd gv pos out z L
                    (Vint (Int.repr (Z.min (Zlength src - pos) Int.max_unsigned)))
                    (Vint (Int.repr (Z.min (n - Zlength out) Int.max_unsigned))))
    tbl_x34
    (loop1_ret_assert (tbl_cont P wbits n D O src dp op ip vc vd gv)
       (overridePost (tbl_brk O src ip vc vd gv) POST_B)).

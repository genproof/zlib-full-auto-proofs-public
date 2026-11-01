(* Law rj_bad_checksum, main: statement 31, the do-while of inflate() calls (avail_in = clip(compressed_len -
   consumed), avail_out = clip(data_len - written), code = inflate(&decompressor, any flush), Z_MEM_ERROR returns,
   gp_assert(code is Z_OK, Z_BUF_ERROR or Z_DATA_ERROR), while code != Z_DATA_ERROR), then return 0 (bc_inv,
   IFacts.bd_call). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.


(* ---------------------------------------------------------------------------------------------- *)
(* Moves between the inflate unit's compspecs and the law's                                       *)

Ltac bci_cs_tac CC := apply equal_f; apply (@data_at_change_composite _ _ CC); [apply JMeq_refl | reflexivity].

Lemma bci_bytes_i sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS.CS sh (tarray tuchar n) v q.
Proof. bci_cs_tac CC_inflate. Qed.
Lemma bci_tok_i sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.

(* the 14 members of struct z_stream *)
Definition bci_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma bci_strm_cs sh (v: bci_tuple) q:
  @data_at Zlib.units.Inflate.CS sh t_zsl v q = @data_at CS.CS sh t_zsl v q.
Proof. bci_cs_tac CC_inflate. Qed.

(* the struct as istreamA holds it, at the law's compspecs *)
Definition bci_tup (gv: globals) (z: zfields) (adv sp: val) : bci_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))).

Lemma bci_istreamA_unfold gv shs vs z av L:
  istreamA gv shs vs z av (Some L) =
  (!! (zf_ok z /\ writable_share shs /\ live_ok L) &&
   (data_at shs t_zsl (bci_tup gv z (adler_v (raw_live (Some L)) z av) (l_sp L)) vs * state_mem gv vs L)).
Proof.
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite bci_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma bci_istreamA_opt_ptr gv shs (vs: val) z av st:
  isptr vs -> istreamA_opt gv shs vs z av st = istreamA gv shs vs z av st.
Proof. intros Pv. unfold istreamA_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma bci_is_live_ptr (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros Pv. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma bci_head_none vs L: isptr vs -> i_head (l_s L) = false -> head_opt (is_live vs (Some L)) = emp.
Proof. intros Pv H. rewrite bci_is_live_ptr by auto. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

Lemma bci_head_emp L: i_head (l_s L) = false -> head_opt (Some L) = emp.
Proof. intros H. unfold head_opt, head_mem. rewrite H. reflexivity. Qed.

(* at a `return`: the struct given back to the stack frame *)
Lemma bci_a_frame gv shs vs z av L: istreamA gv shs vs z av (Some L) |-- data_at_ shs t_zsl vs * TT.
Proof. rewrite bci_istreamA_unfold. Intros. sep_apply (data_at_data_at_ shs t_zsl). cancel. Qed.

Lemma bci_a_frame_opt gv shs vs z av st: isptr vs ->
  istreamA_opt gv shs vs z av st |-- data_at_ shs t_zsl vs * TT.
Proof.
  intros Pv. rewrite bci_istreamA_opt_ptr by auto. destruct st as [L|]; [apply bci_a_frame | ].
  unfold istreamA, zstrm_atA. change Rep.t_strm with t_zsl. rewrite bci_strm_cs. Intros.
  sep_apply (data_at_data_at_ shs t_zsl). cancel.
Qed.

Lemma bci_zf_ok gv shs (vs: val) z av st: isptr vs -> istreamA_opt gv shs vs z av st |-- !! zf_ok z.
Proof.
  intros Pv. rewrite bci_istreamA_opt_ptr by auto. unfold istreamA. destruct st; entailer!.
Qed.

(* the struct after the harness's stores into avail_in / avail_out: the stream inflate() takes *)
Lemma bci_offer_fold gv vs z L ib o ai ao:
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
  rewrite bci_head_none, bci_istreamA_opt_ptr by auto. rewrite sepcon_emp.
  rewrite bci_istreamA_unfold. unfold bci_tup, offer_z, adler_v; simpl.
  apply andp_right; [ | apply derives_refl].
  apply prop_right. unfold zf_ok in *; simpl in *. split; [ | split; [apply writable_share_top | auto]].
  intuition.
Qed.

(* m - (size_t) (p + k - p), as the harness computes the bytes left *)
Lemma bci_ptr_sub (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
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

Lemma bci_sameblock (p: val) k: isptr p -> is_true (sameblock (offset_val k p) p).
Proof. intros Pp. destruct p; try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The objects of one inflate() call                                                             *)

(* an object of n bytes holding the bytes l first, undefined bytes after *)
Definition bci_oc (n: Z) (l: list Z) : list val := bytes_rep l ++ Zrepeat Vundef (n - Zlength l).

Lemma bci_oc_len n l: Zlength l <= n -> Zlength (bci_oc n l) = n.
Proof. intros H. unfold bci_oc, bytes_rep. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

(* after the call: out ++ ow written *)
Lemma bci_oc_after n out ow: Zlength out + Zlength ow <= n ->
  sublist 0 (Zlength out) (bci_oc n out) ++ byte_vals ow ++
    sublist (Zlength out + Zlength ow) n (bci_oc n out) = bci_oc n (out ++ ow).
Proof.
  intros H. pose proof (Zlength_nonneg out). pose proof (Zlength_nonneg ow).
  unfold bci_oc, bytes_rep, byte_vals.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia). rewrite Zlength_map.
  rewrite map_app, <- app_assoc. f_equal. f_equal. rewrite Zlength_app.
  unfold Zrepeat. rewrite sublist_repeat by (try rewrite Zlength_repeat; lia).
  f_equal. f_equal. lia.
Qed.

(* the input object: src at the start of the object of b bytes at cp, offered from pos on; the output object:
   out written at the start of the object of n bytes at op *)
Definition bci_ib (cp: val) (b pos: Z) (src: list Z) : inbuf := InBuf Ews cp pos b (bci_oc b src).
Definition bci_ob (op: val) (n: Z) (out: list Z) : outbuf := OutBuf Ews op (Zlength out) n (bci_oc n out).

Lemma bci_in_ok cp b pos take src:
  isptr cp -> 0 <= pos -> 0 <= take -> pos + take <= Zlength src -> Zlength src <= b ->
  b <= Ptrofs.max_unsigned -> bytes_ok src ->
  in_ok (bci_ib cp b pos src) (sublist pos (pos + take) src).
Proof.
  intros Pc H1 H2 H3 H4 H5 H6. unfold in_ok, bci_ib.
  rewrite Zlength_sublist by lia.
  split; [apply writable_readable, writable_Ews | ]. repeat split; auto; try lia.
  - apply bci_oc_len; lia.
  - unfold bci_oc. replace (pos + (pos + take - pos)) with (pos + take) by lia.
    rewrite sublist_app1 by (unfold bytes_rep; rewrite ?Zlength_map; lia).
    unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
  - apply Forall_sublist; auto.
Qed.

Lemma bci_out_ok op n out room:
  isptr op -> 0 <= room -> Zlength out + room <= n -> n <= Ptrofs.max_unsigned ->
  out_ok (bci_ob op n out) room.
Proof.
  intros Po H1 H2 H3. pose proof (Zlength_nonneg out). unfold out_ok, bci_ob.
  split; [apply writable_Ews | ]. repeat split; auto; try lia. apply bci_oc_len; lia.
Qed.

(* the two objects as inflate()'s buffers, and back *)
Lemma bci_bufs_pre vs L cp b pos src op n out:
  isptr vs -> Zlength src <= b -> Zlength out <= n ->
  data_at Ews (tarray tuchar b) (bci_oc b src) cp * malloc_token Ews (tarray tuchar b) cp *
  data_at Ews (tarray tuchar n) (bci_oc n out) op * malloc_token Ews (tarray tuchar n) op
  |-- bufs_opt (is_live vs (Some L)) (bci_ib cp b pos src) (Some (bci_ob op n out)) [] true true.
Proof.
  intros Pv Hb Hn. rewrite bci_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, bci_ib, bci_ob.
  rewrite (bci_oc_after n out []) by (rewrite Zlength_nil; lia). rewrite app_nil_r.
  rewrite !bci_bytes_i, !bci_tok_i. cancel.
Qed.

Lemma bci_bufs_post vs L cp b pos src op n out ow:
  isptr vs -> Zlength out + Zlength ow <= n ->
  bufs_opt (is_live vs (Some L)) (bci_ib cp b pos src) (Some (bci_ob op n out)) ow true true
  |-- data_at Ews (tarray tuchar b) (bci_oc b src) cp * malloc_token Ews (tarray tuchar b) cp *
      data_at Ews (tarray tuchar n) (bci_oc n (out ++ ow)) op * malloc_token Ews (tarray tuchar n) op.
Proof.
  intros Pv Hn. rewrite bci_is_live_ptr by auto.
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok, bci_ib, bci_ob.
  rewrite (bci_oc_after n out ow) by lia.
  rewrite !bci_bytes_i, !bci_tok_i. cancel.
Qed.

(* a branch that cannot be taken *)
Ltac bci_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                  | match goal with H: _ |- _ => solve [discriminate H] end
                                  | contradiction
                                  | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                      apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                                  | lia ].
(* `if (c) t = 1; else t = (expr);` with the value v of t known *)
Ltac bci_ifk t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end;
  [ first [bci_infeas | forward; entailer!] | first [bci_infeas | forward; entailer!] | ].

(* the state after a call that did not run out of memory, at the loop's test: the code r *)
Definition bci_cont (P : inv_t) (wbits n b : Z) (D O src : list Z) (dp op cp vc vd : val) (gv : globals)
    : environ -> mpred :=
  EX r : Z, EX pos : Z, EX out : list Z, EX z : zfields, EX L : live,
  PROP (r <> Z_DATA_ERROR -> P wbits D O src pos out z L; swfW (l_s L);
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op)
  LOCAL (temp _code (Vint (Int.repr r));
         temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op; temp _compressed cp;
         temp _compressed_len (Vlong (Int64.repr (Zlength O)));
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); head_opt (Some L); Zlib.proof.inflate.Callees.zfuncs gv;
       mem_mgr gv; R_bc gv;
       data_at Ews (tarray tuchar n) (bytes_rep D) dp; malloc_token Ews (tarray tuchar n) dp;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar b) (bytes_rep src ++ Zrepeat Vundef (b - Zlength O)) cp;
       malloc_token Ews (tarray tuchar b) cp;
       data_at_ Tsh t_zsl vc; TT).

Definition bci_brk (gv : globals) (vc vd : val) : environ -> mpred :=
  PROP () LOCAL (lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at_ Tsh t_zsl vc; data_at_ Tsh t_zsl vd; TT).

Lemma seg_iloop_ok : seg_iloop_stmt.
Proof.
  intros Espec P wbits n b D O src dp op cp vc vd gv PF FA.
  destruct FA as (DF & HD & Hn & HO & Hb & Hw & Hw8 & BD & BD' & BO & Pdp & Pop & Pcp & SRC).
  destruct SRC as (Hsl & Hsb & Hpre & Htr).
  unfold bc_seg31, Delta_bc, POST_B, POST_bc. abbreviate_semax.
  forward_loop (bc_inv P wbits n b D O src dp op cp vc vd gv)
    continue: (bci_cont P wbits n b D O src dp op cp vc vd gv)
    break: (bci_brk gv vc vd).
  { apply ENTAIL_refl. }
  2: { unfold bci_cont. Intros r pos out z L.
       forward_if.
       - assert (HP: P wbits D O src pos out z L).
         { match goal with H: _ -> P _ _ _ _ _ _ _ _, H': Int.repr _ <> _ |- _ =>
             apply H; intro E; apply H'; rewrite E; reflexivity end. }
         destruct (bd_ok P PF _ _ _ _ _ _ _ _ HP) as (Hhd & _).
         rewrite (bci_head_emp L Hhd).
         forward. unfold bc_inv. Exists pos out z L. entailer!.
       - forward. unfold bci_brk. sep_apply bci_a_frame. entailer!. }
  2: { unfold bci_brk. forward. Exists (Int.repr 0). entailer!. }
  unfold bc_inv. Intros pos out z L.
  rewrite bci_istreamA_unfold. Intros.
  unfold bci_tup. rewrite H1, H2.
  assert_PROP (isptr vd) as Pvd by entailer!.
  destruct (bd_ok P PF _ _ _ _ _ _ _ _ H) as (Hhd & Hpos & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  unfold max_size in Hn.
  forward.
  forward_call (Zlength O - pos).
  { apply prop_right. apply bci_sameblock; auto. }
  { entailer!. rewrite bci_ptr_sub by (auto; rep_lia). reflexivity. }
  forward.
  forward.
  forward_call (n - Zlength out).
  { apply prop_right. apply bci_sameblock; auto. }
  { entailer!. rewrite bci_ptr_sub by (auto; rep_lia). reflexivity. }
  forward.
  (* the call: the next piece of src and the rest of the output object *)
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ai := Z.min (Zlength O - pos) Int.max_unsigned).
  set (ao := Z.min (n - Zlength out) Int.max_unsigned).
  assert (Hai: 0 <= ai <= Zlength O - pos /\ ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  assert (Hao: 0 <= ao <= n - Zlength out /\ ao <= Int.max_unsigned) by (unfold ao; rep_lia).
  clearbody ai ao.
  set (inp := sublist pos (pos + ai) src).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := bci_ib cp b pos src). set (o := bci_ob op n out).
  replace (offset_val pos cp) with (in_ptr ib 0) by (unfold ib, bci_ib; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) op) with (out_ptr o 0)
    by (unfold o, bci_ob; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (bci_offer_fold gv vd z L ib o ai ao); auto; try lia.
  rewrite <- Hsl.
  change (bytes_rep src ++ Zrepeat Vundef (b - Zlength src)) with (bci_oc b src).
  change (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) with (bci_oc n out).
  sep_apply (bci_bufs_pre vd L cp b pos src op n out); auto; try lia. fold ib o.
  unfold R_bc, R_of, Zlib.proof.deflate.DSpec.deflate_globals. Intros.
  assert (INOK: in_ok ib inp) by (apply bci_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply bci_out_ok; auto; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (bci_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  forward.
  forward_if.
  { (* Z_MEM_ERROR ends the run *)
    forward. Exists (Int.repr 0). sep_apply (bci_a_frame_opt gv Tsh vd z' Vundef st'); auto. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (CP: call_pre src pos z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj H5 (conj H3 (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, bci_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel flush vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  destruct (bd_call P PF wbits D O src pos out z L vd flush ib inp o ao r z' st' ow H CP
              ltac:(lia) REL' Hr Zo')
    as (L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & Hcode & HP').
  subst st'.
  rewrite bci_istreamA_opt_ptr by auto.
  rewrite (bci_is_live_ptr vd (Some L')) by auto.
  unfold ib, o. sep_apply (bci_bufs_post vd L cp b pos src op n out ow); auto; try lia. Intros. fold ib o.
  assert (Eni: zf_ni z' = offset_val (pos + (Zlength inp - zf_ai z')) cp)
    by (rewrite Hni'; unfold ib, bci_ib; reflexivity).
  assert (Eno: zf_no z' = offset_val (Zlength (out ++ ow)) op)
    by (rewrite Hno'; unfold o, bci_ob; simpl; f_equal; rewrite Zlength_app; lia).
  (* gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_DATA_ERROR) *)
  apply -> seq_assoc.
  destruct Hcode as [E|[E|E]]; subst r.
  - bci_ifk _t'22 1. bci_ifk _t'23 1. forward_call (Int.repr 1).
    unfold bci_cont. Exists Z_OK (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
    unfold bci_oc, R_bc, R_of, Zlib.proof.deflate.DSpec.deflate_globals. rewrite Hsl. entailer!.
  - bci_ifk _t'22 1. bci_ifk _t'23 1. forward_call (Int.repr 1).
    unfold bci_cont. Exists Z_BUF_ERROR (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
    unfold bci_oc, R_bc, R_of, Zlib.proof.deflate.DSpec.deflate_globals. rewrite Hsl. entailer!.
  - bci_ifk _t'22 0. bci_ifk _t'23 1. forward_call (Int.repr 1).
    unfold bci_cont. Exists Z_DATA_ERROR (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L'.
    unfold bci_oc, R_bc, R_of, Zlib.proof.deflate.DSpec.deflate_globals. rewrite Hsl. entailer!.
Qed.

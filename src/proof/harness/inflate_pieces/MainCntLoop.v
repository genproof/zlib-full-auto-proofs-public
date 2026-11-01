(* Law api_counters, main: one iteration of the do-while (its body), from the loop invariant pk_inv_c to the
   invariant again (or a `return 0` when an allocation or inflate() / inflateSetDictionary runs out of memory):
   the piece and the output space, offer(), inflate(), the checks of api_counters.c (avail_in <= take,
   avail_out <= room, next_in = piece + consumed, next_out = out + produced, total_in = read and
   total_out = written, all from pf_inflate), the two free()s, the optional inflateSetDictionary of any bytes.
   Same structure as MainAnyLoop.v (rj_any_input), whose code check is replaced by these checks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_counters.code.

#[local] Existing Instance Cnt.CS.
#[local] Existing Instances Cnt.CC_inflate Cnt.CC_adler32 Cnt.CC_crc32 Cnt.CC_zutil Cnt.CC_inffast
  Cnt.CC_inftrees Cnt.CC_compress.
Import CntK.

Definition Delta_cnt : tycontext := func_tycontext f_main (QPvarspecs Cnt.p) (@Gk_of Cnt.CS []) nil.
Definition POST_cnt : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the body of the do-while *)
Definition seg_body_cnt : statement := ltac:(get_loop_body f_main).

Ltac ret0a := forward; Exists (Int.repr 0); sep_apply a_frame; entailer!.

Section TestEq.
Local Transparent denote_tc_test_eq.
(* p + k == p + k is defined when p is a malloc'd byte object of n bytes and 0 <= k <= n (one past the end
   included, and also for an object of 0 bytes, whose malloc token keeps p valid) *)
Lemma test_eq_self {cs: compspecs} Q n k p:
  0 <= k <= n ->
  Q |-- (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p * TT)%logic ->
  Q |-- denote_tc_test_eq (offset_val k p) (offset_val k p).
Proof.
  intros Hk H. eapply derives_trans; [exact H | ].
  assert_PROP (isptr p) as Hp by (saturate_local; entailer!).
  destruct p; try contradiction.
  assert (W: (malloc_token Ews (tarray tuchar n) (Vptr b i) * data_at_ Ews (tarray tuchar n) (Vptr b i) * TT)%logic
             |-- weak_valid_pointer (offset_val k (Vptr b i))).
  { apply sepcon_weak_valid_pointer1.
    destruct (zlt 0 n).
    - apply sepcon_weak_valid_pointer2. rewrite data_at__memory_block. normalize.
      simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
      apply memory_block_weak_valid_pointer; auto; lia.
    - assert (n = 0) by lia. assert (k = 0) by lia. subst.
      apply sepcon_weak_valid_pointer1.
      eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | ].
      replace (offset_val 0 (Vptr b i)) with (Vptr b i) by (simpl; rewrite ptrofs_add_repr_0_r; auto).
      apply valid_pointer_weak. }
  simpl offset_val in *. unfold denote_tc_test_eq, test_eq_ptrs, sameblock.
  destruct (peq b b) as [E | X]; [ | contradiction]. simpl.
  apply andp_right; exact W.
Qed.
End TestEq.

(* written += room - avail_out: the sum wraps modulo 2^64 like total_out *)
Lemma written_step tout room ao:
  0 <= ao <= room -> room <= Int.max_unsigned ->
  Int64.add (Int64.repr tout) (Int64.sub (Int64.repr room) (Int64.repr (Int.unsigned (Int.repr ao)))) =
  Int64.repr ((tout + (room - ao)) mod 2 ^ 64).
Proof.
  intros H1 H2. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.add, Int64.sub.
  rewrite (Int64.unsigned_repr room), (Int64.unsigned_repr ao), (Int64.unsigned_repr (room - ao)) by rep_lia.
  rewrite Int64.unsigned_repr_eq.
  rewrite <- (Int64.repr_unsigned (Int64.repr (tout mod Int64.modulus + (room - ao)))), Int64.unsigned_repr_eq.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma body_cnt_loop {Espec: OracleKind} P gv vs inp src Fr z L :
  pieces_facts P -> P z L -> zf_ok z -> 0 <= zf_tin z <= Zlength src -> Zlength src <= 9223372036854775807 ->
  is_bytes src -> isptr inp -> isptr vs ->
  semax Delta_cnt
    (PROP ()
     LOCAL (temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
            temp _read (Vlong (Int64.repr (zf_tin z)));
            temp _written (Vlong (Int64.repr (zf_tout z))); lvar _strm t_zsl vs; gvars gv)
     SEP (istreamA gv Tsh vs z Vundef (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
          malloc_token Ews (tarray tuchar (Zlength src)) inp;
          data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp; Fr))
    seg_body_cnt
    (loop1_ret_assert (pk_inv_c P gv vs inp src Fr) (overridePost (pk_inv_c P gv vs inp src Fr) POST_cnt)).
Proof.
  intros PF HP Zo Ht Hlen Hsb Pinp Pvs.
  unfold seg_body_cnt, Delta_cnt, Gk_of, POST_cnt. simplify_func_tycontext. abbreviate_semax.
  set (tin := zf_tin z) in *.
  forward_call (Zlength src - tin).
  forward_call (Z.min (Zlength src - tin) Int.max_unsigned). Intros take.
  forward.
  split_call. forward_call tt. Intros room. forward. rewrite Int.unsigned_repr by rep_lia.
  assert (Htk: 0 <= take <= Zlength src - tin /\ take <= Int.max_unsigned).
  { pose proof (Z.le_min_l (Zlength src - tin) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength src - tin) Int.max_unsigned). lia. }
  set (data := sublist tin (tin + take) src).
  assert (Hdl: Zlength data = take) by (unfold data; rewrite Zlength_sublist; lia).
  assert (Hdb: is_bytes data) by (unfold data; apply Forall_sublist; auto).
  split_call.
  rewrite <- bytes_a.
  forward_call (offset_val tin inp, Ews, inp, tin, Zlength src, bytes_rep src, take, data, gv).
  { unfold cbuf_ok. repeat split; auto; try lia.
    unfold data, bytes_rep. rewrite sublist_map. reflexivity. }
  Intros piece.
  forward.
  split_call.
  forward_call (room, gv). Intros vret. destruct vret as [outp bs]. simpl fst in *; simpl snd in *.
  rewrite !bytes_a, !tok_a.
  forward.
  destruct (eq_dec piece nullval) as [NP|NP].
  { subst piece. ifpostv _t'12 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
    forward_if; [ret0a | infeas]. }
  Intros. aptr piece Ppiece.
  destruct (eq_dec outp nullval) as [NO|NO].
  { subst outp. ifpostv _t'12 (Vint (Int.repr 1)); [infeas | forward; entailer! | ].
    forward_if; [ret0a | infeas]. }
  Intros. aptr outp Poutp.
  ifpostv _t'12 (Vint (Int.repr 0)); [infeas | forward; entailer!; destruct outp; try contradiction; reflexivity | ].
  forward_if; [infeas | ].
  (* offer(&strm, piece, take, out, room) *)
  sep_apply (istreamA_zs gv vs z Vundef L). Intros.
  assert (HL: live_ok L) by assumption.
  forward_call (vs, Tsh, piece, take, outp, room, zf_ni z, Vint (Int.repr (zf_ai z)), Vlong (Int64.repr tin),
                zf_no z, Vint (Int.repr (zf_ao z)), Vlong (Int64.repr (zf_tout z)), msg_val gv (zf_msg z), l_sp L,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt z)),
                adler_v (raw_live (Some L)) z Vundef, zf_res z).
  pose proof (pf_head P PF z L HP) as Hhd.
  sep_apply (offer_fold gv vs z Vundef L piece take data outp room bs); auto; try lia.
  sep_apply (bufs_pre_l vs L piece take data outp room bs); auto.
  (* code = inflate(&strm, any flush) *)
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  assert (INOK: in_ok (ib_of piece take data) data) by (apply in_ok_of; auto; rep_lia).
  assert (OUTOK: out_ok (ob_of outp room bs) room) by (apply out_ok_of; auto; rep_lia).
  forward_call (gv, Tsh, vs, offer_z z (in_ptr (ib_of piece take data) 0) take (out_ptr (ob_of outp room bs) 0) room,
                Vundef, Some L, ib_of piece take data, data, Some (ob_of outp room bs), flush, Ers, Ers, true, true).
  { pose proof INOK as I'. pose proof OUTOK as O'. pose proof (pf_swf P PF z L HP) as [SW1 SW2]. unfold in_ok, ib_of in I'. unfold out_ok, ob_of in O'.
    decompose [and] I'. decompose [and] O'. repeat split; auto; try discriminate; simpl; try lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply a_frame_opt. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (REL': inflate_rel flush vs (offer_z z (in_ptr (ib_of piece take data) 0) (Zlength data)
                                        (out_ptr (ob_of outp room bs) 0) room)
                  (Some L) (ib_of piece take data) data (Some (ob_of outp room bs)) r z' st' ow)
    by (rewrite Hdl; exact REL).
  destruct (pf_inflate P PF z L vs flush (ib_of piece take data) data (ob_of outp room bs) room r z' st' ow
              HP HL Zo ltac:(intro E; subst vs; contradiction) Hfl ltac:(discriminate) INOK OUTOK
              ltac:(rep_lia) ltac:(rep_lia) REL' Hr)
    as (L' & Est & HP' & Hwrap & Hcode & Hai & Hao & Hni & Hno & Htin & Htout & How).
  subst st'.
  rewrite istreamA_opt_ptr by auto. rewrite head_none by (auto; eapply pf_head; eauto).
  sep_apply (bufs_post_l vs L piece take data outp room bs ow); auto; try lia. Intros.
  (* the checks *)
  rewrite Hdl in Hai, Hni, Htin.
  rewrite (istreamA_unfold gv Tsh vs z' Vundef L'). Intros. unfold pk_tup.
  forward.
  ifpostv _t'15 (Vint (Int.repr 1)).
  { forward. forward. entailer!.
    unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
  { exfalso. rewrite Int.unsigned_repr in * by rep_lia. lia. }
  forward_call (Int.repr 1).
  unfold ib_of in Hni; unfold ob_of in Hno; simpl in Hni, Hno.
  rewrite Hni, Hno.
  forward. forward.
  forward_call (Int.repr 1).
  { apply (test_eq_self _ take); [lia | ].
    sep_apply (data_at_data_at_ Ews (tarray tuchar take) (bytes_rep data) piece). cancel. }
  forward. forward.
  forward_call (Int.repr 1).
  { match goal with |- context [data_at Ews (tarray tuchar ?n) (bytes_rep (ow ++ ?t)) outp] =>
      apply (test_eq_self _ n); [lia | ];
      sep_apply (data_at_data_at_ Ews (tarray tuchar n) (bytes_rep (ow ++ t)) outp); cancel end. }
  forward. forward.
  rewrite (read_step tin take (zf_ai z')) by rep_lia.
  fold tin in Htin. rewrite <- Htin.
  forward. forward.
  rewrite (written_step (zf_tout z) room (zf_ao z')) by rep_lia.
  rewrite <- Htout.
  forward.
  ifpostv _t'16 (Vint (Int.repr 1)).
  { forward. forward. entailer!. rewrite Int64.eq_true. reflexivity. }
  { exfalso. auto. }
  forward_call (Int.repr 1).
  rewrite <- Hni, <- Hno.
  sep_apply (istreamA_fold gv Tsh vs z' Vundef L'); auto.
  (* free(piece); free(out) *)
  sep_apply (free_pre take (bytes_rep data) piece NP).
  forward_call (tarray tuchar take, piece, gv).
  sep_apply (free_pre room (bytes_rep (ow ++ sublist (Zlength ow) room bs)) outp NO).
  forward_call (tarray tuchar room, outp, gv).
  assert (Hz': zf_ok z') by assumption.
  assert (Ht': 0 <= zf_tin z' <= Zlength src) by (rewrite Htin, Z.mod_small by rep_lia; rep_lia).
  (* between calls: inflateSetDictionary of any bytes, or not *)
  forward_call tt. Intros c.
  forward_if.
  2: { forward. unfold pk_inv_c. Exists z' L'. entailer!. }
  split_call. forward_call tt. Intros dl. forward. rewrite Int.unsigned_repr by rep_lia.
  split_call.
  forward_call (dl, gv).
  Intros vret. destruct vret as [dp d]. simpl fst in *; simpl snd in *.
  rewrite !bytes_a, !tok_a.
  forward.
  destruct (eq_dec dp nullval) as [ND|ND].
  { subst dp. if_seq. forward_if; [ | infeas].
    forward. forward_if; [ | infeas]. ret0a. }
  Intros. aptr dp Pdp.
  if_seq. forward_if; [infeas | ].
  rewrite (dict_i dl (bytes_rep d) dp), (dtok_i dl dp).
  rewrite <- (istreamA_opt_ptr gv Tsh vs z' Vundef (Some L')) by auto.
  forward_call (gv, Tsh, vs, z', Vundef, Some L', Ews, dp, 0, dl, bytes_rep d, d, true).
  { entailer!. destruct dp; try contradiction. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    reflexivity. }
  { assert (Zlength (bytes_rep d) = dl) by (unfold bytes_rep; rewrite Zlength_map; auto).
    split; auto. rewrite sublist_same by lia. reflexivity. }
  Intros vret. destruct vret as [aok winp]. simpl fst in *; simpl snd in *.
  rewrite !on_live_fst, !on_live_snd, !on_live_thd by auto.
  set (sd := setdict_f d aok winp z' L') in *.
  forward.
  if_seq. forward_if.
  { forward. Exists (Int.repr 0). sep_apply a_frame_opt. entailer!. }
  match goal with H: Int.repr (fst3 sd) <> _ |- _ => rename H into Hnm end.
  assert (Hsd: fst3 sd <> Z_MEM_ERROR) by (intro E; apply Hnm; rewrite E; reflexivity).
  destruct (pf_setdict P PF z' L' d aok winp HP' ltac:(assumption) Hz' ltac:(assumption) ltac:(rep_lia) Hsd) as (Ez & HP'' & Hw'').
  fold sd in Ez, HP''. rewrite Ez.
  try rewrite <- (dict_i dl (bytes_rep d) dp). try rewrite <- (dtok_i dl dp).
  sep_apply (free_pre dl (bytes_rep d) dp ND).
  forward_call (tarray tuchar dl, dp, gv).
  rewrite istreamA_opt_ptr by auto.
  unfold pk_inv_c. Exists z' (thd3 sd). entailer!.
Qed.


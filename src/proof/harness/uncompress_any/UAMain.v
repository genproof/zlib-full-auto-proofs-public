(* The main of harness/uncompress_any.c, proved against MainLib.main_core_spec R (UAGlobals.v) from the facts of
   UAFacts.v (ua_facts_stmt), calling uncompr.c's uncompress2 / uncompress through their shared specifications
   (uncompr/USpec5.v, at the uncompr unit's compspecs: moved to the law's with UALawCS's instances) and the
   harness helpers through theirs (inflate_common/HarnessLib.v exact_space, be32; adler32/HarnessBytes.v
   bytes_same; adler32/HarnessRef.v ref_adler32), as inflate_codes/Main*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.uncompress_any.UALawCS Zlib.proof.harness.uncompress_any.UAGlobals
               Zlib.proof.harness.uncompress_any.UAFacts.
Require Import Zlib.harness.x_uncompress_any.code.
Require Import Zlib.proof.harness.uncompress_any.UAMainKit Zlib.proof.harness.uncompress_any.UAMainChk
               Zlib.proof.harness.uncompress_any.UAMainRest.

Definition Gmain : funspecs :=
  [uncompress2_spec; uncompress_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; bytes_same_spec; be32_spec; exact_space_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Lemma ua_int_eq a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros A B. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro E. apply repr_inj_signed in E; auto.
Qed.

Lemma ua_cmpu_le a b: 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.cmpu Cle (Int64.repr a) (Int64.repr b) = (a <=? b).
Proof.
  intros A B. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a), (Z.leb_spec a b); simpl; reflexivity || lia.
Qed.

Lemma ua_dest_tail bs cap out dlen: Zlength out <= dlen <= cap -> Zlength bs = cap ->
  sublist dlen cap (dest_after (bytes_rep bs) cap out) = bytes_rep (sublist dlen cap bs).
Proof.
  intros D B. unfold dest_after, byte_vals, bytes_rep. list_solve.
Qed.

Ltac ua_dz := repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ => apply repr_inj_signed in H; [ | rep_lia | rep_lia]
  | H: Int.repr ?a <> Int.repr ?b |- _ =>
      let E := fresh in assert (E: a <> b) by (intro; subst; apply H; reflexivity); clear H
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zle ?a ?b] => destruct (zle a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] => rewrite (ua_int_eq a b) by rep_lia
  | H: context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
  end; simpl in *; try reflexivity; try lia;
  try (exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
                              | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.zero <> Int.zero |- _ => apply H; reflexivity
                              | H: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact H end).

Lemma body_main : ua_facts_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros UF. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  forward_call tt. Intros n.
  forward_call tt. Intros cap.
  ifpost _t'3 (Int.repr (if andb (n <=? 2^24) (cap <=? 2^20) then 1 else 0)).
  { forward. entailer!. ua_shl. arg_cmp. }
  { forward. entailer!. ua_shl. arg_cmp. }
  forward_call (Int.repr (if andb (n <=? 2^24) (cap <=? 2^20) then 1 else 0)).
  assumed. apply andb_true_iff in E. destruct E as [En Ec]. apply Z.leb_le in En, Ec.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros srcp.
  destruct (eq_dec srcp nullval) as [PS|PS].
  { subst srcp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { contradiction. }
  forward_call (srcp, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros src. rewrite if_false by auto.
  match goal with H: Zlength src = n |- _ => rename H into Hsrcn end.
  match goal with H: Forall _ src |- _ => rename H into Hsrcb end.
  subst n. fold (bytes_rep src).
  rewrite <- (ua_ptr_adler_ Tsh v_snap).
  forward_call (cap, v_snap, Tsh, gv).
  Intros vret. destruct vret as [[dstp snapq] bs]. simpl fst in *; simpl snd in *.
  destruct (eq_dec dstp nullval) as [PD|PD].
  { subst dstp. forward_if. { ret0. } { contradiction. } }
  Intros.
  forward_if.
  { eapply (@malloc_test_eq Zlib.units.Adler32.CS _ (Zlength bs)); [rep_lia | ].
    sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dstp). cancel. }
  { contradiction. }
  Intros. ua_law.
  forward. forward.
  rewrite !Int.unsigned_repr by rep_lia.
  assert_PROP (isptr dstp) as Pdst by entailer!.
  assert_PROP (isptr srcp) as Psrc by entailer!.
  rewrite <- (ua_bytes_uncompr Ews cap (bytes_rep bs) dstp), <- (ua_tok_uncompr Ews cap dstp),
          <- (ua_bytes_uncompr Ews (Zlength src) (bytes_rep src) srcp), <- (ua_tok_uncompr Ews (Zlength src) srcp),
          <- (ua_ulong_uncompr Tsh _ v_dlen), <- (ua_ulong_uncompr Tsh _ v_slen).
  sep_apply (ua_ig_to gv).
  forward_call (gv, Ews, dstp, cap, bytes_rep bs, cap, v_dlen, true, true,
                Ews, srcp, Zlength src, bytes_rep src, src, v_slen, Ers, Ers).
  { rewrite !Zlength_bytes_rep, sublist_same by (rewrite ?Zlength_bytes_rep; lia). auto. }
  Intros vret. destruct vret as [[[r slen] dlen] out]. simpl fst in *; simpl snd in *.
  match goal with H: uncompress_rel _ _ _ _ _ _ |- _ => rename H into Hrel end.
  destruct (UF src cap r slen dlen out Hsrcb En ltac:(lia) Hrel) as (Hr & Hsl & Hdl & Hob & Hnm & Hok).
  pose proof (Zlength_nonneg out) as Hout0.
  assert (Rr: -5 <= r <= 0) by (unfold Z_OK, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR in Hr; lia).
  ua_law.
  ifpost _t'7 (Int.repr (if ((r =? 0) || (r =? -4))%bool then 1 else 0)).
  { forward. entailer!; ua_dz. }
  { forward. entailer!; ua_dz. }
  ifpost _t'8 (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5))%bool then 1 else 0)).
  { forward. entailer!; ua_dz. }
  { forward. entailer!; ua_dz. }
  ifpost _t'9 (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5) || (r =? -3))%bool then 1 else 0)).
  { forward. entailer!; ua_dz. }
  { forward. entailer!; ua_dz. }
  forward_call (Int.repr (if ((r =? 0) || (r =? -4) || (r =? -5) || (r =? -3))%bool then 1 else 0)).
  { unfold Z_OK, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR in Hr. ua_dz. }
  forward.
  ifpost _t'10 (Int.repr 1).
  { forward. forward. entailer!. rewrite ua_cmpu_le by rep_lia. ua_dz. }
  { rewrite Int.unsigned_repr in * by rep_lia. lia. }
  forward_call (Int.repr 1).
  forward. forward. forward. forward.
  assert_PROP (isptr snapq) as Psnap by entailer!.
  rewrite <- (ua_bytes_adler Ews cap (dest_after (bytes_rep bs) cap out) dstp),
          <- (ua_bytes_adler Ews cap (bytes_rep bs) snapq).
  forward_call (offset_val dlen dstp, Ews, dstp, dlen, cap, dest_after (bytes_rep bs) cap out, sublist dlen cap bs,
                offset_val dlen snapq, Ews, snapq, dlen, cap, bytes_rep bs, sublist dlen cap bs, cap - dlen).
  { unfold cbuf_ok. replace (dlen + (cap - dlen)) with cap by lia.
    assert (is_bytes (sublist dlen cap bs)) by (apply Forall_sublist; auto).
    rewrite ua_dest_tail by lia. unfold bytes_rep. rewrite sublist_map.
    repeat split; auto with share; try lia; try (rewrite Zlength_sublist by lia; lia). }
  rewrite if_true by reflexivity.
  forward_call (Int.repr 1).
  ua_law.
  forward_if (ua_join gv v_snap v_dlen v_slen v_snap2 v_dlen2).
  { assert (r = 0) by ua_dz. subst r.
    destruct (Hok eq_refl) as (H6 & Hhd & Hbe & Hun).
    assert (F: ua_ok_facts srcp src dstp cap bs slen dlen out).
    { pose proof (Hnm ltac:(discriminate)) as Hd.
      refine (conj Hsrcb (conj En (conj _ (conj H2 (conj H3 (conj Pdst (conj Psrc (conj Hsl (conj Hd
              (conj _ (conj Hob (conj H6 (conj Hhd (conj Hbe Hun)))))))))))))); lia. }
    eapply semax_pre; [ | eapply ua_chk_ok; [exact F | eapply ua_rest_ok; exact F] ].
    unfold ua_okpre. entailer!. }
  { forward. unfold ua_join. entailer!. }
  unfold ua_join. Intros.
  forward. Exists (Int.repr 0). entailer!.
Qed.

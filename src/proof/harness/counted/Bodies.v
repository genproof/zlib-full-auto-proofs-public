(* The bodies of counted_alloc, counted_free and counted_stream (Spec.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
#[local] Existing Instance CS_count.

(* the counters stay size_t values *)
Lemma cnt_range: forall tr, 0 <= fst (cnt tr) <= Int64.max_unsigned /\ 0 <= snd (cnt tr) <= Int64.max_unsigned.
Proof.
  unfold cnt. intros tr. rewrite <- (rev_involutive tr). induction (rev tr) as [| e l IH]; simpl.
  - rep_lia.
  - rewrite fold_left_app. simpl. destruct IH as [A B].
    assert (M: forall x, 0 <= x mod 2 ^ 64 <= Int64.max_unsigned)
      by (intros x; pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)); rep_lia).
    destruct e; simpl; [destruct (_ <? _) | |]; split; auto.
Qed.

(* the flag after a successful allocation or a release is the flag before; after a failed allocation it is 1 *)
Lemma cnt_failed_alloc: forall tr n, cnt_failed (tr ++ [ZAlloc n]) = cnt_failed tr.
Proof. intros. unfold cnt_failed. rewrite za_failed_app. simpl. rewrite orb_false_r. reflexivity. Qed.

Lemma cnt_failed_free: forall tr n, cnt_failed (tr ++ [ZFree n]) = cnt_failed tr.
Proof. intros. unfold cnt_failed. rewrite za_failed_app. simpl. rewrite orb_false_r. reflexivity. Qed.

Lemma cnt_failed_fail: forall tr, cnt_failed (tr ++ [ZFail]) = 1.
Proof. intros. unfold cnt_failed. rewrite za_failed_fail. reflexivity. Qed.

Lemma cnt_fail: forall tr, cnt (tr ++ [ZFail]) = cnt tr.
Proof. intros. unfold cnt. rewrite fold_left_app. reflexivity. Qed.

Lemma body_count_alloc : @semax_body Vprog_count Gprog_count_alloc CS_count HC.f_counted_alloc count_alloc_spec.
Proof.
  start_function.
  unfold count_res. Intros.
  destruct (cnt_range tr) as [R1 R2].
  set (n := items * size) in *.
  forward.
  forward.
  forward_call (tarray tuchar (8 + n), gv).
  { simpl. rep_lia. }
  rewrite !Int.unsigned_repr by rep_lia. rewrite mul64_repr. fold n.
  Intros b.
  forward_if.
  { if_tac; entailer!. }
  { forward. forward. Exists nullval. rewrite if_true by auto. unfold count_res.
    rewrite cnt_fail, cnt_failed_fail. entailer!. }
  rewrite if_false by auto. Intros.
  assert_PROP (malloc_compatible (8 + sizeof t) b) as MC.
  { sep_apply (malloc_token_local_facts Ews (tarray tuchar (8 + n)) b). simpl sizeof.
    rewrite Z.max_r, Z.mul_1_l by lia. rewrite H2. entailer!. }
  rewrite <- H2. rewrite block_split by auto. rewrite H2. Intros.
  assert_PROP (force_val (sem_add_ptr_int tulong Signed b (Vint (Int.repr 0))) = field_address tulong [] b) as E.
  { entailer!. rewrite field_address_offset by auto. destruct b; try contradiction; simpl.
    rewrite !ptrofs_add_repr_0_r. reflexivity. }
  forward.
  forward. forward. forward. forward.
  set (now := (fst (cnt tr) + n) mod 2 ^ 64).
  assert (EN: Int64.add (Int64.repr (fst (cnt tr))) (Int64.repr n) = Int64.repr now).
  { unfold now. rewrite add64_repr. change (2 ^ 64) with Int64.modulus.
    rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned. reflexivity. }
  rewrite EN in *.
  assert (RN: 0 <= now <= Int64.max_unsigned)
    by (unfold now; pose proof (Z.mod_pos_bound (fst (cnt tr) + n) (2 ^ 64) ltac:(lia)); rep_lia).
  set (peak := snd (cnt tr)) in *.
  forward_if (PROP () LOCAL (temp HC._block b; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (8 + n)) b;
         field_at Ews tulong [] (Vlong (Int64.repr n)) b; data_at_ Ews t (offset_val 8 b);
         data_at Tsh t_count (Vlong (Int64.repr now), (Vlong (Int64.repr (if peak <? now then now else peak)),
                                Vint (Int.repr (cnt_failed tr)))) cp)).
  - forward. forward. entailer!.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. auto.
  - forward. entailer!.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. auto.
  - forward. Exists (offset_val 8 b).
    assert (isptr b) by (destruct b; try contradiction; exact I).
    rewrite if_false by (destruct b; try contradiction; discriminate).
    unfold count_res, count_tok. rewrite cnt_failed_alloc. unfold cnt. rewrite fold_left_app. fold (cnt tr).
    simpl cnt_step. fold now peak.
    rewrite offset_offset_val, Z.add_opp_diag_r, isptr_offset_val_zero by auto. rewrite H2.
    entailer!.
Qed.

Lemma body_count_free : @semax_body Vprog_count Gprog_count_free CS_count HC.f_counted_free count_free_spec.
Proof.
  start_function.
  unfold count_res, count_tok. Intros.
  destruct (cnt_range tr) as [R1 R2].
  set (q := offset_val (-8) p).
  assert_PROP (malloc_compatible (8 + sizeof t) q) as MC.
  { sep_apply (malloc_token_local_facts Ews (tarray tuchar (8 + sizeof t)) q). simpl sizeof.
    rewrite Z.max_r, Z.mul_1_l by (pose proof (sizeof_pos t); lia). entailer!. }
  assert (Pp: isptr p) by (destruct p; try contradiction; exact I).
  assert (Eq: p = offset_val 8 q)
    by (unfold q; rewrite offset_offset_val; change (-8 + 8) with 0; rewrite isptr_offset_val_zero by auto; reflexivity).
  assert (EB: force_val (sem_binary_operation' Osub (tptr tulong) tint
                (eval_cast (tptr tvoid) (tptr tulong) p) (Vint (Int.repr 1))) = q)
    by (destruct p; try contradiction; unfold q; simpl; rewrite Ptrofs.sub_add_opp; reflexivity).
  clearbody q.
  forward.
  forward.
  forward.
  rewrite EB. clear EB.
  assert_PROP (force_val (sem_add_ptr_int tulong Signed q (Vint (Int.repr 0))) = field_address tulong [] q) as E.
  { entailer!. rewrite field_address_offset by auto. destruct q; try contradiction; simpl.
    rewrite !ptrofs_add_repr_0_r. reflexivity. }
  forward.
  forward.
  sep_apply (data_at_data_at_ Ews tulong (Vlong (Int64.repr (sizeof t))) q).
  rewrite Eq. sep_apply (block_merge Ews t q MC).
  forward_call (tarray tuchar (8 + sizeof t), q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate). cancel. }
  unfold count_res. rewrite cnt_failed_free. unfold cnt. rewrite fold_left_app. fold (cnt tr). simpl cnt_step.
  rewrite sub64_repr. change (2 ^ 64) with Int64.modulus.
  rewrite <- (Int64.repr_unsigned (Int64.repr (fst (cnt tr) - sizeof t))), Int64.unsigned_repr_eq.
  entailer!.
Qed.

(* struct z_stream_s is the same at the compress unit's compspecs and at the harness unit's *)
#[local] Instance CCE_zs : change_composite_env Zlib.units.Compress.CS CS_count.
Proof. make_cs_preserve Zlib.units.Compress.CS CS_count. Defined.
#[local] Instance CCE_zs' : change_composite_env CS_count Zlib.units.Compress.CS.
Proof. make_cs_preserve CS_count Zlib.units.Compress.CS. Defined.

Lemma body_counted_stream :
  @semax_body Vprog_count Gprog_counted_stream CS_count HC.f_counted_stream counted_stream_spec.
Proof.
  start_function.
  forward. forward. forward.
  erewrite (@data_at_change_composite Zlib.units.Compress.CS CS_count CCE_zs sh t_zs _ _);
    [| apply JMeq_refl | reflexivity].
  forward. forward. forward.
  erewrite (@data_at_change_composite CS_count Zlib.units.Compress.CS CCE_zs' sh t_zs _ _);
    [| apply JMeq_refl | reflexivity].
  forward_call (sp, sh, nullval, 0, nullval, 0, ni, ai, ti, no, ao, to, msg, st,
                gv HC._counted_alloc, gv HC._counted_free, cp, dt, ad, rs).
  entailer!.
Qed.

Lemma counted_bodies : counted_ok.
Proof.
  split; [exact body_count_alloc | split; [exact body_count_free | exact body_counted_stream]].
Qed.

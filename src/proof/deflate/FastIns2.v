(** * deflate_fast part: INSERT_STRING inside the insertion loop [fast_ins2] (statement in FastKit.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FastKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Lemma fj_temp_head {cs : compspecs} {Espec : OracleKind} Delta P i v v' Q R c Post :
  v = v' -> semax Delta (PROPx P (LOCALx (temp i v' :: Q) R)) c Post ->
  semax Delta (PROPx P (LOCALx (temp i v :: Q) R)) c Post.
Proof. intros ->; auto. Qed.

Lemma fj_vi_wrap x : vi x = Vint (Int.repr (u32 (x + 2) - 2)).
Proof.
  unfold vi. f_equal. apply Int.eqm_samerepr. unfold Int.eqm, u32.
  apply Zbits.eqmod_sym. eapply Zbits.eqmod_trans.
  - apply Zbits.eqmod_sub; [apply Zbits.eqmod_sym, Zbits.eqmod_mod; reflexivity|apply Zbits.eqmod_refl].
  - replace (x + 2 - 2) with x by lia. apply Zbits.eqmod_refl.
Qed.

Lemma fj_xor_repr a b : Int.xor (Int.repr a) (Int.repr b) = Int.repr (Z.lxor a b).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_xor by auto. rewrite !Int.testbit_repr by auto.
  rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma fj_hash s a c :
  0 <= a <= Int.max_unsigned -> 0 <= d_hash_shift s < 32 ->
  Int.and (Int.xor (Int.shl (Int.repr a) (Int.repr (d_hash_shift s))) (Int.repr c)) (Int.repr (d_hash_mask s)) =
  Int.repr (update_hash s a c).
Proof.
  intros Ha Hk. unfold update_hash. rewrite repr_u32, <- and_repr32, <- fj_xor_repr. f_equal. f_equal.
  unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite repr_u32. reflexivity.
Qed.

Lemma fj_ranges s uh i v j w : dstate_ranges s -> 0 <= uh <= Int.max_unsigned -> 0 <= v < 65536 -> 0 <= w < 65536 ->
  dstate_ranges (set_d_head (set_d_prev (set_d_ins_h s uh) (upd_Znth i (d_prev s) v)) (upd_Znth j (d_head s) w)).
Proof.
  intros Hs Hu Hv Hw. unfold dstate_ranges, u32_ok, u64_ok, s32_ok, s64_ok in *. dsimpl.
  rewrite !Zlength_upd_Znth. decompose [and] Hs.
  repeat match goal with |- _ /\ _ => split end; try assumption;
    try (apply Forall_upd_Znth; assumption); lia.
Qed.

Lemma fast_ins2_ok : fast_ins2_stmt.
Proof.
  unfold fast_ins2_stmt. intros Espec s s' z p pin pout ish R msgv gv flush h vb H.
  unfold fa, fa_base, Delta_fast, fast_ins2. unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold hash_at, match_at, win_at. Intros.
  unfold c_insert_string in H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  inversion H; subst s' h; clear H.
  rename x0 into c, x1 into h, x2 into prev', x3 into head'.
  unfold guard in Ha. case_if_as Ha Esh; [|discriminate]. clear Ha. apply Z.ltb_lt in Esh.
  dsimpl in Ha1. dsimpl in Ha2. dsimpl in Ha3.
  assert (Hwok : mb_ok (d_window s)) by (open_dranges H3; assumption).
  destruct (mb_rd_vals _ _ _ Hwok Ha0) as (Hi & Hz & Hcr).
  pose proof (Zlength_mb_vals _ Hwok) as Hwl.
  assert (0 <= d_strstart s <= Int.max_unsigned) by drange.
  forward. forward. forward. forward.
  apply (fj_temp_head _ _ _ _ _ _ _ _ _ (fj_vi_wrap (d_strstart s))).
  pose proof (u32_range (d_strstart s + 2)).
  change (MIN_MATCH - 1) with 2 in Hi, Hz, Ha0.
  forward.
  { go_lower. apply prop_right.
    match goal with |- context [Znth ?i ?l] => replace (Znth i l) with (vi c) by
      (replace i with (u32 (d_strstart s + 2)) by lia; symmetry; exact Hz) end.
    exact (tc_val_tuchar_repr c ltac:(lia)). }
  match goal with |- context [temp _t'102 (Znth ?i ?l)] => replace (Znth i l) with (vi c) by
    (replace i with (u32 (d_strstart s + 2)) by lia; symmetry; exact Hz) end.
  assert (0 <= d_ins_h s <= Int.max_unsigned) by drange.
  assert (0 <= d_hash_shift s < 32) by (split; [drange|lia]).
  forward. forward.
  rewrite (fj_hash s (d_ins_h s) c) by auto.
  set (uh := update_hash s (d_ins_h s) c) in *.
  unfold rd, wr, in_range in Ha1, Ha2, Ha3.
  case_if_as Ha1 E1; [|discriminate]. inversion Ha1; subst h; clear Ha1.
  case_if_as Ha2 E2; [|discriminate]. inversion Ha2; subst prev'; clear Ha2.
  inversion Ha3; subst head'; clear Ha3.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in E1, E2.
  assert (Zlength (d_head s) <= Int.max_unsigned /\ Zlength (d_prev s) <= Int.max_unsigned)
    by (open_dranges H3; split; assumption).
  assert (Hhr : Forall (fun x => 0 <= x < 65536) (d_head s)) by (open_dranges H3; assumption).
  assert (Hpr : Forall (fun x => 0 <= x < 65536) (d_prev s)) by (open_dranges H3; assumption).
  assert (Hh : 0 <= Znth uh (d_head s) < 65536) by (rewrite Forall_Znth in Hhr; apply Hhr; lia).
  forward. forward.
  forward.
  { go_lower. apply prop_right. try rewrite Znth_map by lia.
    first [apply tc_val_tushort_repr; lia | rewrite Int.unsigned_repr by rep_lia; lia]. }
  forward.
  forward. forward. forward.
  rewrite zext16_repr, Z.mod_small by lia.
  forward.
  forward. forward. forward. forward. forward.
  pose proof (fj_ranges s uh (Z.land (d_strstart s) (d_w_mask s)) (Znth uh (d_head s)) uh (u16 (d_strstart s)) H3
    ltac:(lia) Hh ltac:(unfold u16; apply Z.mod_pos_bound; lia)) as Hr.
  rewrite Int.zero_ext_idem by lia. rewrite !zext16_repr. rewrite (Z.mod_small (Znth uh (d_head s))) by lia.
  clearbody uh.
  match goal with |- context [d_trm ?t] => lazymatch t with s => fail | _ =>
    replace (d_trm t) with (d_trm s) by reflexivity end end.
  unfold win_at, hash_at, match_at, cfg_at, stat_at. dsimpl. rewrite <- !upd_Znth_map, !Zlength_upd_Znth.
  unfold vi, u16. entailer!.
Qed.

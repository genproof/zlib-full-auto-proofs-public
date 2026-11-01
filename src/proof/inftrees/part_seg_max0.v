(* Part: the segment seg_max0 of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

Lemma seg_max0_maxlen_range (lens: list Z) :
  Forall (fun l => 0 <= l <= MAXBITS) lens -> 0 <= maxlen lens <= 15.
Proof.
unfold MAXBITS. induction 1; simpl; [lia | ]. lia.
Qed.

Lemma seg_max0_cap2 type lens req cap :
  0 <= type <= 2 -> cap_ok type lens req cap -> 2 <= cap.
Proof.
unfold cap_ok, CODES, LENS, DISTS, ENOUGH_LENS, ENOUGH_DISTS. intros T (C0 & C1 & C2).
assert (type = 0 \/ type = 1 \/ type = 2) as [-> | [-> | ->]] by lia.
- apply C0; auto.
- specialize (C1 eq_refl); lia.
- specialize (C2 eq_refl); lia.
Qed.

Lemma seg_max0_tab_unfold sh (a b: entry) (l: list entry) p :
  data_at sh (tarray code_t (Zlength l + 2)) (map entry_rep (a :: b :: l)) p |--
  (data_at sh code_t (entry_rep a) p * data_at sh code_t (entry_rep b) (offset_val 4 p) *
   data_at sh (tarray code_t (Zlength l)) (map entry_rep l) (offset_val 8 p))%logic.
Proof.
saturate_local.
assert (0 <= Zlength l) by list_solve.
change (map entry_rep (a :: b :: l)) with (([entry_rep a] ++ [entry_rep b]) ++ map entry_rep l).
rewrite (split2_data_at_Tarray_app 2 (Zlength l + 2)) by list_solve.
rewrite (split2_data_at_Tarray_app 1 2 sh code_t [entry_rep a]) by list_solve.
rewrite (data_at_singleton_array_eq sh code_t (entry_rep a)) by reflexivity.
rewrite (data_at_singleton_array_eq sh code_t (entry_rep b)) by reflexivity.
rewrite (field_address0_offset (tarray code_t (Zlength l + 2))) by auto with field_compatible.
assert (field_compatible (tarray code_t 2) [] p) by auto with field_compatible.
rewrite (field_address0_offset (tarray code_t 2)) by auto with field_compatible.
simpl nested_field_offset. replace (Zlength l + 2 - 2) with (Zlength l) by lia.
cancel.
Qed.

Lemma seg_max0_tab_fold sh (a b: entry) (l: list entry) p :
  field_compatible (tarray code_t (Zlength l + 2)) [] p ->
  (data_at sh code_t (entry_rep a) p * data_at sh code_t (entry_rep b) (offset_val 4 p) *
   data_at sh (tarray code_t (Zlength l)) (map entry_rep l) (offset_val 8 p))%logic |--
  data_at sh (tarray code_t (Zlength l + 2)) (map entry_rep (a :: b :: l)) p.
Proof.
intros H.
assert (0 <= Zlength l) by list_solve.
change (map entry_rep (a :: b :: l)) with (([entry_rep a] ++ [entry_rep b]) ++ map entry_rep l).
rewrite (split2_data_at_Tarray_app 2 (Zlength l + 2)) by list_solve.
rewrite (split2_data_at_Tarray_app 1 2 sh code_t [entry_rep a]) by list_solve.
rewrite (data_at_singleton_array_eq sh code_t (entry_rep a)) by reflexivity.
rewrite (data_at_singleton_array_eq sh code_t (entry_rep b)) by reflexivity.
rewrite (field_address0_offset (tarray code_t (Zlength l + 2))) by auto with field_compatible.
assert (field_compatible (tarray code_t 2) [] p) by auto with field_compatible.
rewrite (field_address0_offset (tarray code_t 2)) by auto with field_compatible.
simpl nested_field_offset. replace (Zlength l + 2 - 2) with (Zlength l) by lia.
cancel.
Qed.

Lemma seg_max0_add1 p :
  isptr p -> force_val (sem_add_ptr_int (Tstruct ___gp_code noattr) Signed p (Vint (Int.repr 1))) = offset_val 4 p.
Proof.
destruct p; try contradiction. intros _. reflexivity.
Qed.

Lemma seg_max0_ok : loop_facts -> seg_max0_stmt.
Proof.
intros LF Espec X WF.
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; simpl in WF. destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold A_max, A_max1, it_sep, params_locs, count_, work_, count_at, it_mx, POST_it, it_model;
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold seg_max0.
abbreviate_semax.
destruct IN as (TY & NC & LR & RQ).
pose proof (seg_max0_maxlen_range lens LR) as MXR.
pose proof (seg_max0_cap2 type lens req (Zlength old) TY CAP) as CAP2.
forward_if.
2: { forward. entailer!. }
assert (MX0: maxlen lens = 0) by (first [exact H | apply repr_inj_unsigned in H; rep_lia]).
destruct old as [ | e0 [ | e1 rest]]; [list_solve | list_solve | ].
replace (Zlength (e0 :: e1 :: rest)) with (Zlength rest + 2) by list_solve.
assert_PROP (field_compatible (tarray code_t (Zlength rest + 2)) [] pt) as FC by entailer!.
assert (M: inflate_table_model type lens req (e0 :: e1 :: rest) =
           ROk 1 2 (invalid_entry 1 :: invalid_entry 1 :: rest)).
{ unfold inflate_table_model. rewrite MX0. simpl. f_equal. list_solve. }
sep_apply (seg_max0_tab_unfold sh e0 e1 rest pt). Intros.
forward. forward. forward.
change (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 64))) with (Int.repr 64).
change (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 1))) with (Int.repr 1).
change (Int.zero_ext 16 (Int.zero_ext 16 (Int.repr 0))) with (Int.repr 0).
assert_PROP (isptr pt) as PT by entailer!.
do 11 forward.
rewrite (seg_max0_add1 pt PT).
do 11 forward.
rewrite seg_max0_add1 by auto. rewrite offset_offset_val. simpl (4 + 4).
forward. forward.
rewrite M; cbn [it_ret it_tab it_adv it_bits].
change (Vint (Int.repr 64), (Vint (Int.repr 1), Vint (Int.repr 0))) with (entry_rep (invalid_entry 1)).
entailer!.
sep_apply (seg_max0_tab_fold sh (invalid_entry 1) (invalid_entry 1) rest pt FC).
replace (Zlength (e0 :: e1 :: rest)) with (Zlength rest + 2) by list_solve.
cancel.
Qed.

(* Part: the segment seg_fin of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

Lemma seg_fin_rep_fill_len (t: list entry) b i n e :
  Zlength (rep_fill t b i n e) = Zlength t.
Proof.
revert t. induction n; intros t; simpl; [reflexivity | ].
rewrite IHn. apply Zlength_upd_Znth.
Qed.

(* A Break of the model's loop comes from one step of a reached state. *)
Lemma seg_fin_run_break type lens W root mx n st s :
  run type lens W root mx n st = Break s ->
  exists m s0, run type lens W root mx m st = Continue s0 /\ step type lens W root mx s0 = Break s.
Proof.
revert st. induction n; intros st H; simpl in H; [discriminate | ].
destruct (step type lens W root mx st) as [s1 | s1 | s1] eqn:E.
- destruct (IHn s1 H) as (m & s0 & R & St). exists (S m), s0. simpl. rewrite E. auto.
- inversion H; subst. exists O, st. auto.
- discriminate.
Qed.

Lemma seg_fin_bincr_nonneg k huff incr : 0 <= incr -> 0 <= bincr_loop k huff incr.
Proof.
revert incr. induction k; intros incr H; simpl; [lia | ].
destruct (Z.land huff incr =? 0); [lia | ]. apply IHk. apply Z.shiftr_nonneg. lia.
Qed.

Lemma seg_fin_next_huff_nonneg huff len : 0 <= huff -> 1 <= len -> 0 <= next_huff huff len.
Proof.
intros H L. unfold next_huff.
assert (0 <= bincr_loop 16 huff (Z.shiftl 1 (len - 1))).
{ apply seg_fin_bincr_nonneg. rewrite Z.shiftl_1_l. apply Z.pow_nonneg. lia. }
destruct (_ =? 0) eqn:E; [lia | ].
apply Z.eqb_neq in E.
assert (0 <= Z.land huff (bincr_loop 16 huff (Z.shiftl 1 (len - 1)) - 1)) by (apply Z.land_nonneg; lia).
lia.
Qed.

(* A Break step keeps len, drop, used, next and the size of the table. *)
Lemma seg_fin_step_break type lens W root mx s0 s :
  step type lens W root mx s0 = Break s ->
  s_huff s = next_huff (s_huff s0) (s_len s0) /\
  s_len s = s_len s0 /\ s_drop s = s_drop s0 /\ s_used s = s_used s0 /\ s_next s = s_next s0 /\
  Zlength (s_tab s) = Zlength (s_tab s0).
Proof.
unfold step. intros H.
destruct (_ && _)%bool.
- inversion H; subst; simpl. rewrite seg_fin_rep_fill_len. repeat split.
- destruct (_ && _)%bool; [destruct over | ]; discriminate.
Qed.

Lemma seg_fin_model type lens req old s :
  1 <= maxlen lens -> acc_test type lens ->
  over type (Z.shiftl 1 (root_of req lens)) = false ->
  run type lens (sorted_syms lens) (root_of req lens) (maxlen lens)
      (length (sorted_syms lens)) (init_state lens (root_of req lens) old) = Break s ->
  inflate_table_model type lens req old = ROk (root_of req lens) (s_used s) (finish s).
Proof.
intros MX (lft & LF & T) OV R.
unfold inflate_table_model.
replace (maxlen lens =? 0) with false by lia.
rewrite LF, T, OV, R. reflexivity.
Qed.

Lemma seg_fin_ok : loop_facts -> seg_fin_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (LF1 & LF2 & LF3 & LF4 & LF5 & LF6 & LF7 & LF8).
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; simpl in WF. destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold A_brk, it_sep, params_locs, count_at, work_sorted, it_mx, it_root, POST_it, it_model;
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold seg_fin.
abbreviate_semax.
Intros. rename H into MX1, H0 into ACC, H1 into OV, H2 into RUN.
pose proof (seg_fin_model type lens req old s MX1 ACC OV RUN) as M.
destruct (seg_fin_run_break _ _ _ _ _ _ _ _ RUN) as (k & s0 & R0 & S0).
assert (AOK: acc_ok type lens req (Zlength old)) by (unfold acc_ok; tauto).
destruct (LF3 type lens req old k s0 AOK R0) as [IT _].
pose proof (LF6 type lens req old k s0 s AOK R0 S0) as BRK.
destruct (seg_fin_step_break _ _ _ _ _ _ _ S0) as (EH & EL & ED & EU & EN & ET).
unfold iter_ok in IT.
rewrite <- EL, <- ED, <- EU, <- EN in IT. rewrite <- ET in IT.
destruct IT as (_ & LEN & DRP & CR & H0R & NX & NU & UC & U32 & _ & _ & _ & _ & TL).
assert (U0: 0 <= s_used s).
{ rewrite Z.shiftl_1_l in NU. assert (0 < 2 ^ s_curr s0) by (apply Z.pow_pos_nonneg; lia). lia. }
clear CR NU.
assert (H0: 0 <= s_huff s) by (rewrite EH; apply seg_fin_next_huff_nonneg; lia).
assert (HB: s_huff s <> 0 -> 0 <= s_huff s < 32768) by (intros HH; specialize (BRK HH); lia).
clear R0 S0 EH H0R EL ED EU EN ET LF1 LF2 LF4 LF5 LF7 LF8.
match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (?A :: ?B :: ?C :: ?D :: ?E :: ?F :: _ :: ?R)))) _ _ =>
  forward_if (PROPx [] (LOCALx Q (SEPx (A :: B :: C :: D :: E :: F ::
     data_at sh (tarray code_t (Zlength old)) (map entry_rep (finish s)) pt :: R)))) end.
3: {
  assert_PROP (isptr pt) as PT by entailer!.
  forward. forward. forward. forward.
  rewrite M; cbn [it_ret it_tab it_adv it_bits].
  entailer!.
}
2: { assert (F: finish s = s_tab s) by (unfold finish; rewrite H; reflexivity). forward. rewrite F. entailer!. }
specialize (BRK H). specialize (HB H).
forward. forward. forward.
change (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr 64))) with (Int.repr 64).
change (Int.zero_ext 16 (Int.zero_ext 16 (Int.repr 0))) with (Int.repr 0).
assert (ZE: Int.zero_ext 8 (Int.zero_ext 8 (Int.sub (Int.repr (s_len s)) (Int.repr (s_drop s)))) =
            Int.repr (s_len s - s_drop s)).
{ rewrite Int.sub_signed. rewrite !Int.signed_repr by rep_lia.
  assert (Z8: Int.zero_ext 8 (Int.repr (s_len s - s_drop s)) = Int.repr (s_len s - s_drop s))
    by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; lia).
  rewrite !Z8. reflexivity. }
rewrite ZE; clear ZE.
assert (BD: 0 <= s_len s - s_drop s <= 255) by lia.
set (n0 := s_next s) in *. set (h := s_huff s) in *.
assert_PROP (field_compatible (tarray code_t (Zlength old)) [] pt) as FC by entailer!.
replace (map entry_rep (s_tab s)) with
  (map entry_rep (sublist 0 n0 (s_tab s)) ++ map entry_rep (sublist n0 (Zlength old) (s_tab s)))
  by (rewrite <- map_app, sublist_rejoin, sublist_same; auto; lia).
rewrite (split2_data_at_Tarray_app n0 (Zlength old) sh code_t)
  by (rewrite Zlength_map, Zlength_sublist; lia).
rewrite (field_address0_offset (tarray code_t (Zlength old))) by auto with field_compatible.
simpl nested_field_offset. rewrite Z.add_0_l.
Intros. forward. forward. forward. { entailer!. simpl. rep_lia. } forward. forward. forward.
set (L := map entry_rep (sublist n0 (Zlength old) (s_tab s))).
assert (LH: 0 <= h < Zlength L) by (subst L; rewrite Zlength_map, Zlength_sublist; lia).
assert (LD: L = map entry_rep (sublist n0 (Zlength old) (s_tab s))) by reflexivity.
clearbody L.
rewrite !upd_Znth_same by (rewrite ?Zlength_upd_Znth; exact LH).
rewrite !upd_Znth_twice by (rewrite ?Zlength_upd_Znth; exact LH).
cbn [fst snd].
assert (Z8: Int.zero_ext 8 (Int.repr (s_len s - s_drop s)) = Int.repr (s_len s - s_drop s))
  by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; lia).
rewrite Z8. clear Z8.
change (Int.zero_ext 8 (Int.repr 64)) with (Int.repr 64).
change (Int.zero_ext 16 (Int.repr 0)) with (Int.repr 0).
change (Vint (Int.repr 64), (Vint (Int.repr (s_len s - s_drop s)), Vint (Int.repr 0)))
  with (entry_rep (invalid_entry (s_len s - s_drop s))).
assert (F: map entry_rep (finish s) =
  map entry_rep (sublist 0 n0 (s_tab s)) ++ upd_Znth h L (entry_rep (invalid_entry (s_len s - s_drop s)))).
{ unfold finish. replace (s_huff s =? 0) with false by lia. rewrite LD. fold n0 h. list_solve. }
entailer!.
rewrite F.
rewrite (split2_data_at_Tarray_app (s_next s) (Zlength old) sh code_t) by assumption.
rewrite (field_address0_offset (tarray code_t (Zlength old))) by auto with field_compatible.
simpl nested_field_offset. rewrite Z.add_0_l.
cancel.
Qed.

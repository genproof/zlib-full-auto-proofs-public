(* Part: the segment seg_counts of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

(* Pure facts about counts and maxlen. *)
Lemma sc_zseq_len : forall n s, Zlength (zseq s n) = Z.of_nat n.
Proof. induction n; intros; simpl zseq; [reflexivity|]. rewrite Zlength_cons, IHn. lia. Qed.

Lemma sc_zseq_nth : forall n s k, 0 <= k < Z.of_nat n -> Znth k (zseq s n) = s + k.
Proof.
induction n; intros s k H; simpl zseq; [lia|].
destruct (Z.eq_dec k 0) as [->|Hk]; [rewrite Znth_0_cons; lia|].
rewrite Znth_pos_cons by lia. rewrite IHn by lia. lia.
Qed.

Lemma sc_counts_len : forall l, Zlength (counts l) = 16.
Proof. intros. unfold counts. rewrite Zlength_map, sc_zseq_len. reflexivity. Qed.

Lemma sc_counts_nth : forall l k, 0 <= k < 16 -> Znth k (counts l) = count_len l k.
Proof.
intros. unfold counts. rewrite Znth_map by (rewrite sc_zseq_len; simpl; lia).
rewrite sc_zseq_nth by (simpl; lia). f_equal; lia.
Qed.

Lemma sc_counts_nil : counts [] = Zrepeat 0 16.
Proof. reflexivity. Qed.

Lemma sc_count_len_app : forall l1 l2 k, count_len (l1 ++ l2) k = count_len l1 k + count_len l2 k.
Proof. intros. unfold count_len. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma sc_count_len_bound : forall l k, 0 <= count_len l k <= Zlength l.
Proof.
intros. unfold count_len. split; [apply Zlength_nonneg|].
induction l; simpl; [lia|]. destruct (k =? a); rewrite ?Zlength_cons; lia.
Qed.

Lemma sc_counts_step : forall lens i, 0 <= i < Zlength lens -> 0 <= Znth i lens < 16 ->
  counts (sublist 0 (i+1) lens) =
  upd_Znth (Znth i lens) (counts (sublist 0 i lens)) (Znth (Znth i lens) (counts (sublist 0 i lens)) + 1).
Proof.
intros lens i H1 H2.
apply Znth_eq_ext. { rewrite Zlength_upd_Znth, !sc_counts_len; reflexivity. }
intros k Hk. rewrite sc_counts_len in Hk.
rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia.
rewrite sc_counts_nth by lia. rewrite sc_count_len_app.
destruct (Z.eq_dec k (Znth i lens)) as [<-|Hne].
- rewrite upd_Znth_same by (rewrite sc_counts_len; lia). rewrite sc_counts_nth by lia.
  unfold count_len at 2; simpl. rewrite Z.eqb_refl. reflexivity.
- rewrite upd_Znth_diff by (rewrite ?sc_counts_len; lia). rewrite sc_counts_nth by lia.
  unfold count_len at 2; simpl. destruct (Z.eqb_spec k (Znth i lens)); [lia|]. rewrite Zlength_nil; lia.
Qed.

Lemma sc_count_len_zero : forall l k, count_len l k = 0 -> ~ In k l.
Proof.
intros l k H. unfold count_len in H. intros Hin.
assert (In k (filter (Z.eqb k) l)) by (apply filter_In; split; [auto | apply Z.eqb_refl]).
destruct (filter (Z.eqb k) l); [contradiction|]. rewrite Zlength_cons in H. pose proof (Zlength_nonneg l0). lia.
Qed.

Lemma sc_count_len_pos : forall l k, count_len l k <> 0 -> In k l.
Proof.
intros l k H. unfold count_len in H.
destruct (filter (Z.eqb k) l) eqn:E; [contradiction|].
assert (In z (filter (Z.eqb k) l)) by (rewrite E; left; auto).
apply filter_In in H0. destruct H0 as [H0 H3]. apply Z.eqb_eq in H3. subst; auto.
Qed.

Lemma sc_maxlen_ge : forall l x, In x l -> x <= maxlen l.
Proof.
induction l; simpl; intros x H; [contradiction|]. destruct H as [<-|H]; [lia|]. specialize (IHl x H); lia.
Qed.

Lemma sc_maxlen_le : forall l m, 0 <= m -> (forall x, In x l -> x <= m) -> maxlen l <= m.
Proof.
induction l; simpl; intros m Hm H; [lia|].
pose proof (H a (or_introl eq_refl)). pose proof (IHl m Hm (fun x Hx => H x (or_intror Hx))). lia.
Qed.

Lemma sc_maxlen_nonneg : forall l, 0 <= maxlen l.
Proof. induction l; simpl; lia. Qed.

Lemma sc_maxlen_eq : forall lens m, Forall (fun l => 0 <= l <= MAXBITS) lens -> 0 <= m <= 15 ->
  (forall k, m < k <= 15 -> Znth k (counts lens) = 0) ->
  (m = 0 \/ Znth m (counts lens) <> 0) -> maxlen lens = m.
Proof.
intros lens m HF Hm Hz Hnz.
assert (maxlen lens <= m).
{ apply sc_maxlen_le; [lia|]. intros x Hx. rewrite Forall_forall in HF. specialize (HF x Hx).
  unfold MAXBITS in HF. destruct (Z_le_gt_dec x m); [auto|].
  exfalso. specialize (Hz x ltac:(lia)). rewrite sc_counts_nth in Hz by lia.
  apply (sc_count_len_zero _ _ Hz Hx). }
destruct Hnz as [->|Hnz]; [pose proof (sc_maxlen_nonneg lens); lia|].
rewrite sc_counts_nth in Hnz by lia. apply sc_count_len_pos in Hnz. apply sc_maxlen_ge in Hnz. lia.
Qed.

#[local] Opaque counts.

Lemma seg_counts_ok : loop_facts -> seg_counts_stmt.
Proof.
intros LF Espec X WF.
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; simpl in WF. destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold A_start, A_max, it_sep, params_locs, count_, work_, count_at, it_mx, POST_it, it_model; simpl.
unfold Delta_it. simplify_func_tycontext.
unfold seg_counts.
abbreviate_semax.
forward. forward. forward.
match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (?Ro :: _ :: ?R)))) _ _ =>
forward;
forward_loop (EX i:Z, PROPx [0 <= i <= 16] (LOCALx (temp _len (Vint (Int.repr i)) :: Q)
   (SEPx (Ro :: data_at Tsh (tarray tushort 16) (Zrepeat (Vint (Int.repr 0)) i ++ Zrepeat Vundef (16 - i)) vc :: R))))
  continue: (EX i:Z, PROPx [0 <= i < 16] (LOCALx (temp _len (Vint (Int.repr i)) :: Q)
   (SEPx (Ro :: data_at Tsh (tarray tushort 16) (Zrepeat (Vint (Int.repr 0)) (i+1) ++ Zrepeat Vundef (16 - (i+1))) vc :: R))))
  break: (PROPx [] (LOCALx Q
   (SEPx (Ro :: data_at Tsh (tarray tushort 16) (Zrepeat (Vint (Int.repr 0)) 16) vc :: R))))
end.
- Exists 0. entailer!.
- Intros i. forward_if.
  + forward. Exists i. entailer!. replace (Int.zero_ext 16 (Int.repr 0)) with (Int.repr 0) by reflexivity.
    apply derives_refl'. f_equal. list_solve.
  + forward. assert (i = 16) by lia. subst i. entailer!.
- Intros i. forward. Exists (i+1). entailer!.
- destruct IN as (Ht & Hn & Hl & Hr).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (?Ro :: _ :: ?R)))) _ _ =>
  forward;
  forward_loop (EX i:Z, PROPx [0 <= i <= Zlength lens] (LOCALx (temp _sym (Vint (Int.repr i)) :: Q)
     (SEPx (Ro :: data_at Tsh (tarray tushort 16) (zs_rep (counts (sublist 0 i lens))) vc :: R))))
    continue: (EX i:Z, PROPx [0 <= i < Zlength lens] (LOCALx (temp _sym (Vint (Int.repr i)) :: Q)
     (SEPx (Ro :: data_at Tsh (tarray tushort 16) (zs_rep (counts (sublist 0 (i+1) lens))) vc :: R))))
    break: (PROPx [] (LOCALx Q
     (SEPx (Ro :: data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc :: R))))
  end.
  + Exists 0. entailer!.
  + assert (HN: Zlength lens <= 288) by (unfold max_codes in Hn; repeat destruct (_ =? _); lia).
    Intros i. forward_if.
    all: try rewrite !Int.unsigned_repr in H1 by rep_lia.
    all: try rewrite !Int.unsigned_repr in H0 by rep_lia.
    2: { forward. assert (i = Zlength lens) by lia. subst i. rewrite sublist_same by lia. entailer!. }
    assert (Hi: 0 <= Znth i lens <= 15) by (rewrite Forall_forall in Hl; apply Hl; apply Znth_In; lia).
    forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    unfold zs_rep at 1; rewrite Znth_map by lia.
    forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    unfold zs_rep at 1; rewrite Znth_map by lia.
    pose proof (sc_counts_step lens i ltac:(lia) ltac:(lia)) as Hstep.
    set (c := counts (sublist 0 i lens)) in *.
    assert (Hcb: 0 <= Znth (Znth i lens) c <= i) by (unfold c; rewrite sc_counts_nth by lia;
      pose proof (sc_count_len_bound (sublist 0 i lens) (Znth i lens)); rewrite Zlength_sublist in H1 by lia; lia).
    assert (Hcl: Zlength c = 16) by apply sc_counts_len.
    clearbody c.
    forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    unfold zs_rep at 1; rewrite Znth_map by lia.
    forward.
    Exists i. rewrite Hstep. entailer!. apply derives_refl'. f_equal.
    rewrite zero_ext_16 by lia. unfold zs_rep. apply (upd_Znth_map (fun x => Vint (Int.repr x))).
  + Intros i. forward. Exists (i+1). entailer!.
  + forward.
    assert (HN: Zlength lens <= 288) by (unfold max_codes in Hn; repeat destruct (_ =? _); lia).
    assert (Hcb: forall k, 0 <= k < 16 -> 0 <= Znth k (counts lens) <= 288) by
      (intros k Hk; rewrite sc_counts_nth by lia; pose proof (sc_count_len_bound lens k); lia).
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward;
    forward_loop (EX m:Z, PROPx [0 <= m <= 15; forall k, m < k <= 15 -> Znth k (counts lens) = 0]
         (LOCALx (temp _max (Vint (Int.repr m)) :: Q) (SEPx R)))
      continue: (EX m:Z, PROPx [1 <= m <= 15; forall k, m <= k <= 15 -> Znth k (counts lens) = 0]
         (LOCALx (temp _max (Vint (Int.repr m)) :: Q) (SEPx R)))
      break: (PROPx [] (LOCALx (temp _max (Vint (Int.repr (maxlen lens))) :: Q) (SEPx R)))
    end.
    * Exists 15. entailer!.
    * Intros m. forward_if.
      { forward.
        { entailer!. unfold zs_rep; rewrite Znth_map by (rewrite sc_counts_len; lia). simpl.
          specialize (Hcb m ltac:(lia)). rewrite Int.unsigned_repr by rep_lia. lia. }
        unfold zs_rep at 1; rewrite Znth_map by (rewrite sc_counts_len; lia).
        forward_if.
        { forward. rewrite (sc_maxlen_eq lens m) by (auto; try lia; right; intro E; rewrite E in H2; contradiction).
          entailer!. }
        { forward. Exists m. entailer!. intros k Hk. destruct (Z.eq_dec k m); [subst k | apply H0; lia].
          specialize (Hcb m ltac:(lia)). apply repr_inj_unsigned in H2; rep_lia. } }
      { forward. assert (m = 0) by lia. subst m. rewrite (sc_maxlen_eq lens 0) by (auto; lia). entailer!. }
    * Intros m. forward. Exists (m-1). entailer!. intros k Hk; apply H0; lia.
    * pose proof (sc_maxlen_nonneg lens).
      assert (maxlen lens <= 15) by (apply sc_maxlen_le; [lia|]; intros x Hx; rewrite Forall_forall in Hl;
        apply Hl in Hx; unfold MAXBITS in Hx; lia).
      forward_if.
      { forward. rewrite Z.min_r by lia. entailer!. }
      { forward. rewrite Z.min_l by lia. entailer!. }
Qed.

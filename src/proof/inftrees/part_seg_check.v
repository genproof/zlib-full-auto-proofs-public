(* Part: the segment seg_check of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts: count[], min, the `left` loop.                                                      *)

Lemma sc_count_len_cons : forall x xs l,
  count_len (x :: xs) l = (if l =? x then 1 else 0) + count_len xs l.
Proof.
  intros. unfold count_len. simpl. destruct (l =? x); rewrite ?Zlength_cons; lia.
Qed.

Lemma sc_count_len_range : forall xs l, 0 <= count_len xs l <= Zlength xs.
Proof.
  induction xs; intros; [unfold count_len; simpl; rewrite Zlength_nil; lia|].
  rewrite sc_count_len_cons, Zlength_cons. specialize (IHxs l). destruct (l =? a); lia.
Qed.

Lemma sc_count_len_In : forall xs x, In x xs -> count_len xs x <> 0.
Proof.
  induction xs; intros; [contradiction|]. rewrite sc_count_len_cons.
  pose proof (sc_count_len_range xs x).
  destruct H; [subst; rewrite Z.eqb_refl; lia|].
  specialize (IHxs x H). destruct (x =? a); lia.
Qed.

Lemma sc_count_len_nz : forall xs x, count_len xs x <> 0 -> In x xs.
Proof.
  induction xs; intros; [exfalso; apply H; reflexivity|]. rewrite sc_count_len_cons in H.
  destruct (x =? a) eqn:E; [apply Z.eqb_eq in E; subst; left; auto|right; apply IHxs; lia].
Qed.

Lemma sc_zseq_len : forall n start, Zlength (zseq start n) = Z.of_nat n.
Proof. induction n; intros; simpl; [reflexivity|]. rewrite Zlength_cons, IHn. lia. Qed.

Lemma sc_Znth_zseq : forall n start i, 0 <= i < Z.of_nat n -> Znth i (zseq start n) = start + i.
Proof.
  induction n; intros; simpl in *; [lia|].
  destruct (Z.eq_dec i 0).
  - subst. rewrite Znth_0_cons. lia.
  - rewrite Znth_pos_cons by lia. rewrite IHn by lia. lia.
Qed.

Lemma sc_counts_len : forall lens, Zlength (counts lens) = 16.
Proof. intros. unfold counts. rewrite Zlength_map, sc_zseq_len. reflexivity. Qed.

Lemma sc_Znth_counts : forall lens l, 0 <= l < 16 -> Znth l (counts lens) = count_len lens l.
Proof.
  intros. unfold counts. rewrite Znth_map by (rewrite sc_zseq_len; simpl; lia).
  rewrite sc_Znth_zseq by (simpl; lia). f_equal; lia.
Qed.

Lemma sc_minlen_char : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  1 <= minlen lens <= 16 /\
  (forall l, In l lens -> l <> 0 -> minlen lens <= l) /\
  (minlen lens = 16 \/ In (minlen lens) lens).
Proof.
  induction lens as [|x xs IH]; intros H; simpl; [unfold MAXBITS; split; [lia|]; split; [intros; contradiction|auto]|].
  inversion H; subst. destruct (IH H3) as (R1 & R2 & R3).
  fold (minlen xs). unfold MAXBITS in *.
  destruct (x =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E].
  - split; [lia|]. split.
    + intros l [<-|Hl] Hn; [lia|]. auto.
    + destruct R3; auto.
  - split; [lia|]. split.
    + intros l [<-|Hl] Hn; [lia|]. specialize (R2 l Hl Hn). lia.
    + destruct (Z.min_spec x (minlen xs)) as [[_ ->]|[_ ->]]; auto. destruct R3; auto.
Qed.

Lemma sc_maxlen_char : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens ->
  0 <= maxlen lens /\ (forall l, In l lens -> l <= maxlen lens) /\ (maxlen lens = 0 \/ In (maxlen lens) lens).
Proof.
  induction lens as [|x xs IH]; intros H; simpl; [split; [lia|]; split; [intros; contradiction|auto]|].
  inversion H; subst. destruct (IH H3) as (R1 & R2 & R3). fold (maxlen xs).
  split; [lia|]. split.
  - intros l [<-|Hl]; [lia|]. specialize (R2 l Hl). lia.
  - destruct (Z.max_spec x (maxlen xs)) as [[_ ->]|[_ ->]]; auto. destruct R3; auto.
Qed.

(* The min loop ends at minlen. *)
Lemma sc_minlen_at : forall lens m, Forall (fun l => 0 <= l <= MAXBITS) lens -> 1 <= m ->
  (forall l, 1 <= l < m -> count_len lens l = 0) -> count_len lens m <> 0 -> minlen lens = m.
Proof.
  intros lens m H Hm Hz Hc.
  destruct (sc_minlen_char lens H) as (R1 & R2 & R3).
  apply sc_count_len_nz in Hc. specialize (R2 m Hc ltac:(lia)).
  destruct R3 as [R3|R3].
  - rewrite Forall_forall in H. specialize (H m Hc). unfold MAXBITS in H. lia.
  - destruct (Z.eq_dec (minlen lens) m); auto.
    apply sc_count_len_In in R3. exfalso. apply R3. apply Hz. lia.
Qed.

Lemma sc_count_max : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens -> 1 <= maxlen lens ->
  count_len lens (maxlen lens) <> 0.
Proof.
  intros. destruct (sc_maxlen_char lens H) as (_ & _ & [R|R]); [lia|]. apply sc_count_len_In; auto.
Qed.

Lemma sc_maxlen_le : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens -> maxlen lens <= 15.
Proof.
  intros. destruct (sc_maxlen_char lens H) as (R1 & _ & [R|R]); [lia|].
  rewrite Forall_forall in H. specialize (H _ R). unfold MAXBITS in H. lia.
Qed.

Lemma sc_left_loop_S : forall k len left cnt,
  left_loop (S k) len left cnt =
  if 2 * left - Znth len cnt <? 0 then None else left_loop k (len + 1) (2 * left - Znth len cnt) cnt.
Proof. reflexivity. Qed.

Lemma sc_Znth_zs_rep : forall l i, 0 <= i < Zlength l -> Znth i (zs_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold zs_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sc_is_int_count : forall lens i, 0 <= i < 16 ->
  (forall l, 0 <= l < 16 -> 0 <= Znth l (counts lens) <= 288) ->
  is_int I16 Unsigned (Znth i (zs_rep (counts lens))).
Proof.
  intros. rewrite sc_Znth_zs_rep by (rewrite sc_counts_len; lia). specialize (H0 i H).
  simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma sc_min_le_max : forall lens, Forall (fun l => 0 <= l <= MAXBITS) lens -> 1 <= maxlen lens ->
  1 <= minlen lens <= maxlen lens.
Proof.
  intros. destruct (sc_minlen_char lens H) as (R1 & R2 & _).
  destruct (sc_maxlen_char lens H) as (_ & _ & [R|R]); [lia|]. specialize (R2 _ R ltac:(lia)). lia.
Qed.

Lemma sc_model_err1 : forall type lens req old, 1 <= maxlen lens -> left_final (counts lens) = None ->
  inflate_table_model type lens req old = RErr.
Proof.
  intros. unfold inflate_table_model. destruct (maxlen lens =? 0) eqn:E; [lia|]. rewrite H0. reflexivity.
Qed.

Lemma sc_model_err2 : forall type lens req old lft, 1 <= maxlen lens -> left_final (counts lens) = Some lft ->
  ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1)))%bool = true ->
  inflate_table_model type lens req old = RErr.
Proof.
  intros. unfold inflate_table_model. destruct (maxlen lens =? 0) eqn:E; [lia|]. rewrite H0, H1. reflexivity.
Qed.

Lemma sc_shl_sub : forall x c,
  Int.sub (Int.shl (Int.repr x) (Int.repr 1)) (Int.repr c) = Int.repr (2 * x - c).
Proof.
  intros. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  change (two_p 1) with 2. rewrite mul_repr, sub_repr. f_equal. lia.
Qed.

Lemma sc_to_nat_S : forall len, len <= 15 -> Z.to_nat (16 - len) = S (Z.to_nat (15 - len)).
Proof. intros. rewrite <- Z2Nat.inj_succ by lia. f_equal. lia. Qed.

#[local] Arguments counts : simpl never.

(* Thaw a frozen frame that the postcondition mentions (thaw would clear it). *)
Ltac sc_thaw FR := rewrite (FRZL_ax FR); unfold FR; unfold abbreviate at 1; simpl fold_right_sepcon.

(* The end of a `return -1` once the model is known to be RErr. *)
Ltac sc_ret_err E :=
  forward; rewrite E; cbn [it_ret it_tab it_adv it_bits]; rewrite Z.mul_0_r;
  match goal with |- context [offset_val 0 ?p] =>
    assert_PROP (isptr p) by entailer!; rewrite isptr_offset_val_zero by auto end;
  entailer!.

(* ---------------------------------------------------------------------------------------------- *)

Lemma seg_check_ok : loop_facts -> seg_check_stmt.
Proof.
intros LF Espec X WF.
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; simpl in WF. destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold A_max1, A_acc, it_sep, params_locs, count_at, work_, it_mx, it_root, POST_it, it_model.
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold seg_check.
abbreviate_semax.
assert (INr := IN). destruct INr as (Ht & Hn & Hl & Hr).
assert (Hn': Zlength lens <= 288) by (unfold max_codes in Hn; destruct (type =? CODES), (type =? LENS); lia).
pose proof (sc_counts_len lens) as Hcl.
assert (Hcb: forall l, 0 <= l < 16 -> 0 <= Znth l (counts lens) <= 288)
  by (intros; rewrite sc_Znth_counts by lia; pose proof (sc_count_len_range lens l); lia).
pose proof (sc_maxlen_le lens Hl) as Hmx.
forward.
freeze [0;2;3;4;5;6;7;8] FR.
forward_loop (EX m: Z, PROP (1 <= m <= maxlen lens; forall l, 1 <= l < m -> count_len lens l = 0)
   LOCAL (temp _min (Vint (Int.repr m)); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (Z.min req (maxlen lens))));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert
  continue: (EX m: Z, PROP (1 <= m < maxlen lens; forall l, 1 <= l <= m -> count_len lens l = 0)
   LOCAL (temp _min (Vint (Int.repr m)); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (Z.min req (maxlen lens))));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert
  break: (PROP ()
   LOCAL (temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (Z.min req (maxlen lens))));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert.
- Exists 1. entailer!.
- Intros m.
  forward_if.
  + forward.
    { entailer!. apply sc_is_int_count; auto; lia. }
    rewrite sc_Znth_zs_rep by lia.
    forward_if.
    * forward. entailer!.
      rewrite (sc_minlen_at lens m Hl ltac:(lia) H1); auto.
      rewrite <- sc_Znth_counts by lia. intro E; apply H3; rewrite E; reflexivity.
    * forward. Exists m. entailer!.
      intros l Hl'. destruct (Z.eq_dec l m); [subst|apply H1; lia].
      rewrite <- sc_Znth_counts by lia. specialize (Hcb m ltac:(lia)).
      apply repr_inj_unsigned; auto; rep_lia.
  + forward. entailer!.
    assert (m = maxlen lens) by lia. subst m.
    rewrite (sc_minlen_at lens (maxlen lens)); auto. apply sc_count_max; auto.
- Intros m. forward. Exists (m + 1). entailer!. intros; apply H1; lia.
- (* root clamp *)
  pose proof (sc_min_le_max lens Hl H) as Hmm.
  forward_if ((PROP () LOCAL (temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (root_of req lens)));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert).
  + forward. entailer!. unfold root_of. f_equal; f_equal; lia.
  + forward. entailer!. unfold root_of. f_equal; f_equal; lia.
  + forward. forward.
    forward_loop (EX len: Z, EX left: Z,
      PROP (1 <= len <= 16; 0 <= left <= 2 ^ (len - 1);
            left_loop (Z.to_nat (16 - len)) len left (counts lens) = left_final (counts lens))
      LOCAL (temp _len (Vint (Int.repr len)); temp _left (Vint (Int.repr left)); temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (root_of req lens)));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert
    continue: (EX len: Z, EX left: Z,
      PROP (1 <= len <= 15; 0 <= left <= 2 ^ len;
            left_loop (Z.to_nat (15 - len)) (len + 1) left (counts lens) = left_final (counts lens))
      LOCAL (temp _len (Vint (Int.repr len)); temp _left (Vint (Int.repr left)); temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (root_of req lens)));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert
    break: (EX left: Z,
      PROP (0 <= left <= 2 ^ 15; left_final (counts lens) = Some left)
      LOCAL (temp _left (Vint (Int.repr left)); temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (root_of req lens)));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert.
    * Exists 1 1. entailer!.
    * Intros len left.
      forward_if.
      -- forward. forward.
         { entailer!. apply sc_is_int_count; auto; lia. }
         rewrite sc_Znth_zs_rep by lia.
         forward.
         rewrite sc_shl_sub.
         rewrite sc_to_nat_S, sc_left_loop_S in H2 by lia.
         assert (Hc := Hcb len ltac:(lia)).
         assert (2 ^ len = 2 * 2 ^ (len - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
         assert (2 ^ len <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
         forward_if.
         ++ assert (LF0: left_final (counts lens) = None)
              by (rewrite <- H2; destruct (_ <? 0) eqn:E; [reflexivity| apply Z.ltb_ge in E; lia]).
            sc_thaw FR. sc_ret_err (sc_model_err1 type lens req old H LF0).
         ++ forward. Exists len (2 * left - Znth len (counts lens)). entailer!.
            rewrite <- H2. destruct (_ <? 0) eqn:E; [apply Z.ltb_lt in E; lia|reflexivity].
      -- forward. Exists left. entailer!.
         assert (len = 16) by lia. subst len. split; [simpl in H1; lia|]. rewrite <- H2. reflexivity.
    * Intros len left. forward. Exists (len + 1) left. entailer!.
      split.
      -- replace (len + 1 - 1) with len by lia. lia.
      -- rewrite <- H2. f_equal. lia.
    * Intros left.
      forward_if ((PROP () LOCAL (temp _t'1 (Vint (if ((0 <? left) && ((type =? CODES) || negb (maxlen lens =? 1)))%bool
                         then Int.one else Int.zero));
     temp _left (Vint (Int.repr left)); temp _min (Vint (Int.repr (minlen lens))); temp _max (Vint (Int.repr (maxlen lens)));
     temp _root (Vint (Int.repr (root_of req lens)));
     temp _base nullval; temp _extra nullval; temp _match (Vint (Int.repr 0));
     lvar _offs (tarray tushort 16) vo; lvar _count (tarray tushort 16) vc;
     lvar _here (Tstruct ___gp_code noattr) vh; gvars gv;
     temp _type (Vint (Int.repr type)); temp _lens pl;
     temp _codes (Vint (Int.repr (Zlength lens))); temp _table ptab;
     temp _bits pb; temp _work pw)
   SEP (FRZL FR; data_at Tsh (tarray tushort 16) (zs_rep (counts lens)) vc))%assert).
      -- forward_if; [forward; entailer! | forward; forward; entailer!];
           (replace (0 <? left) with true by (symmetry; apply Z.ltb_lt; lia)); [reflexivity|].
         replace (type =? CODES) with false by (symmetry; apply Z.eqb_neq; unfold CODES; lia).
         destruct (zeq (maxlen lens) 1) as [E|E]; [rewrite E; reflexivity|].
         rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity.
      -- forward. entailer!.
         replace (0 <? left) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      -- forward_if.
         ++ destruct ((0 <? left) && ((type =? CODES) || negb (maxlen lens =? 1)))%bool eqn:Eb;
              [|contradiction].
            sc_thaw FR. sc_ret_err (sc_model_err2 type lens req old left H H1 Eb).
         ++ destruct ((0 <? left) && ((type =? CODES) || negb (maxlen lens =? 1)))%bool eqn:Eb;
              [apply Int.one_not_zero in H2; contradiction|].
            forward. sc_thaw FR. entailer!.
            exists left. auto.
Qed.

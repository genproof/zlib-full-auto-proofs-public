(* Part: the segment seg_sort of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts: zseq, counts, the symbols of one length.                                           *)

Lemma ss_zseq_len : forall n s, Zlength (zseq s n) = Z.of_nat n.
Proof. induction n; intros; simpl zseq; [reflexivity|]. rewrite Zlength_cons, IHn. lia. Qed.

Lemma ss_zseq_nth : forall n s k, 0 <= k < Z.of_nat n -> Znth k (zseq s n) = s + k.
Proof.
induction n; intros s k H; simpl zseq; [lia|].
destruct (Z.eq_dec k 0) as [->|Hk]; [rewrite Znth_0_cons; lia|].
rewrite Znth_pos_cons by lia. rewrite IHn by lia. lia.
Qed.

Lemma ss_zseq_app : forall n m s, zseq s (n + m) = zseq s n ++ zseq (s + Z.of_nat n) m.
Proof.
induction n; intros; simpl. f_equal; lia. rewrite IHn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma ss_counts_nth : forall l k, 0 <= k < 16 -> Znth k (counts l) = count_len l k.
Proof.
intros. unfold counts. rewrite Znth_map by (rewrite ss_zseq_len; simpl; lia).
rewrite ss_zseq_nth by (simpl; lia). f_equal; lia.
Qed.

Lemma ss_counts_len : forall l, Zlength (counts l) = 16.
Proof. intros. unfold counts. rewrite Zlength_map, ss_zseq_len. reflexivity. Qed.

Lemma ss_count_len_app : forall l1 l2 k, count_len (l1 ++ l2) k = count_len l1 k + count_len l2 k.
Proof. intros. unfold count_len. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma ss_count_len_nonneg : forall l k, 0 <= count_len l k.
Proof. intros. unfold count_len. apply Zlength_nonneg. Qed.

Lemma ss_count_len_one : forall x k, count_len [x] k = if x =? k then 1 else 0.
Proof. intros. unfold count_len. simpl. rewrite Z.eqb_sym. destruct (x =? k); reflexivity. Qed.

Lemma ss_count_len_prefix : forall lens i k, 0 <= i <= Zlength lens ->
  count_len (sublist 0 i lens) k <= count_len lens k.
Proof.
intros. rewrite <- (sublist_same 0 (Zlength lens) lens) at 2 by lia.
rewrite (sublist_split 0 i (Zlength lens)) by lia. rewrite ss_count_len_app.
pose proof (ss_count_len_nonneg (sublist i (Zlength lens) lens) k). lia.
Qed.

(* syms_of_len with a start index. *)
Definition ss_sl (s: Z) (a: list Z) (l: Z) : list Z :=
  map fst (filter (fun p => snd p =? l) (combine (zseq s (length a)) a)).

Lemma ss_sl_cons : forall s x a l,
  ss_sl s (x :: a) l = (if x =? l then [s] else []) ++ ss_sl (s + 1) a l.
Proof. intros. unfold ss_sl. simpl. destruct (x =? l); reflexivity. Qed.

Lemma ss_sl_len : forall a s l, Zlength (ss_sl s a l) = count_len a l.
Proof.
induction a; intros. reflexivity.
rewrite ss_sl_cons, Zlength_app, IHa.
change (a :: a0) with ([a] ++ a0). rewrite ss_count_len_app, ss_count_len_one.
destruct (a =? l); reflexivity.
Qed.

Lemma ss_sl_snoc : forall a s x l,
  ss_sl s (a ++ [x]) l = ss_sl s a l ++ (if x =? l then [s + Zlength a] else []).
Proof.
induction a; intros.
- rewrite app_nil_l, ss_sl_cons. unfold ss_sl; simpl. rewrite app_nil_r, Z.add_0_r. reflexivity.
- rewrite <- app_comm_cons, !ss_sl_cons, IHa, app_assoc. f_equal. f_equal.
  destruct (x =? l); [|reflexivity]. rewrite Zlength_cons. f_equal. lia.
Qed.

Lemma ss_syms_of_len : forall a l, syms_of_len a l = ss_sl 0 a l.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The offsets and the partially filled work[].                                                    *)

Definition ss_off (lens: list Z) (l: Z) : Z :=
  Zlength (flat_map (syms_of_len lens) (zseq 1 (Z.to_nat (l - 1)))).

Definition ss_offs (lens: list Z) (i: Z) : list val :=
  Vundef :: map (fun l => Vint (Int.repr (ss_off lens l + count_len (sublist 0 i lens) l))) (zseq 1 15).

Definition ss_block (lens: list Z) (i: Z) (l: Z) : list val :=
  zs_rep (syms_of_len (sublist 0 i lens) l) ++
  Zrepeat Vundef (count_len lens l - count_len (sublist 0 i lens) l).

Definition ss_work (lens: list Z) (i: Z) : list val :=
  flat_map (ss_block lens i) (zseq 1 15) ++
  Zrepeat Vundef (Zlength lens - Zlength (sorted_syms lens)).

Lemma ss_flat_map_len : forall {A B C} (f: A -> list B) (g: A -> list C) xs,
  (forall x, In x xs -> Zlength (f x) = Zlength (g x)) ->
  Zlength (flat_map f xs) = Zlength (flat_map g xs).
Proof.
induction xs; intros H; simpl; [reflexivity|].
rewrite !Zlength_app, H by (simpl; auto). rewrite IHxs by (intros; apply H; simpl; auto). reflexivity.
Qed.

Lemma ss_flat_map_app : forall {A B} (f: A -> list B) xs ys,
  flat_map f (xs ++ ys) = flat_map f xs ++ flat_map f ys.
Proof. induction xs; intros; simpl; [reflexivity|]. rewrite IHxs, app_assoc. reflexivity. Qed.

Lemma ss_zseq_split : forall l, 1 <= l <= 15 ->
  zseq 1 15 = zseq 1 (Z.to_nat (l - 1)) ++ [l] ++ zseq (l + 1) (Z.to_nat (15 - l)).
Proof.
intros. replace 15%nat with (Z.to_nat (l - 1) + (1 + Z.to_nat (15 - l)))%nat by lia.
rewrite ss_zseq_app. f_equal. rewrite ss_zseq_app. simpl. f_equal; [f_equal; lia|]. f_equal. lia.
Qed.

Lemma ss_block_len : forall lens i l, 0 <= i <= Zlength lens ->
  Zlength (ss_block lens i l) = count_len lens l.
Proof.
intros. unfold ss_block, zs_rep. rewrite Zlength_app, Zlength_map, ss_syms_of_len, ss_sl_len.
pose proof (ss_count_len_prefix lens i l H). rewrite Zlength_Zrepeat by lia. lia.
Qed.

Lemma ss_off_eq : forall lens i l, 0 <= i <= Zlength lens ->
  Zlength (flat_map (ss_block lens i) (zseq 1 (Z.to_nat (l - 1)))) = ss_off lens l.
Proof.
intros. unfold ss_off. apply ss_flat_map_len. intros. rewrite ss_block_len by lia.
rewrite ss_syms_of_len, ss_sl_len. reflexivity.
Qed.

Lemma ss_sorted_len : forall lens l, 1 <= l <= 15 ->
  ss_off lens l + count_len lens l <= Zlength (sorted_syms lens).
Proof.
intros. unfold sorted_syms, ss_off. rewrite (ss_zseq_split l H), !ss_flat_map_app, !Zlength_app.
simpl flat_map. rewrite app_nil_r, ss_syms_of_len, ss_sl_len.
pose proof (Zlength_nonneg (flat_map (syms_of_len lens) (zseq (l + 1) (Z.to_nat (15 - l))))). lia.
Qed.

Lemma ss_off_step : forall lens l, 1 <= l <= 15 ->
  ss_off lens (l + 1) = ss_off lens l + count_len lens l.
Proof.
intros. unfold ss_off. replace (Z.to_nat (l + 1 - 1)) with (Z.to_nat (l - 1) + 1)%nat by lia.
rewrite ss_zseq_app, ss_flat_map_app, Zlength_app. simpl. rewrite app_nil_r, ss_syms_of_len, ss_sl_len.
do 2 f_equal. lia.
Qed.

Lemma ss_off_1 : forall lens, ss_off lens 1 = 0.
Proof. reflexivity. Qed.

Lemma ss_sublist_snoc : forall (lens: list Z) i, 0 <= i < Zlength lens ->
  sublist 0 (i + 1) lens = sublist 0 i lens ++ [Znth i lens].
Proof. intros. rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

Lemma ss_count_step : forall lens i k, 0 <= i < Zlength lens ->
  count_len (sublist 0 (i + 1) lens) k =
  count_len (sublist 0 i lens) k + (if Znth i lens =? k then 1 else 0).
Proof. intros. rewrite ss_sublist_snoc, ss_count_len_app, ss_count_len_one by lia. reflexivity. Qed.

Lemma ss_block_other : forall lens i k, 0 <= i < Zlength lens -> Znth i lens <> k ->
  ss_block lens (i + 1) k = ss_block lens i k.
Proof.
intros. unfold ss_block. rewrite ss_count_step by lia. rewrite !ss_syms_of_len, ss_sublist_snoc by lia.
rewrite ss_sl_snoc. destruct (Z.eqb_spec (Znth i lens) k); [contradiction|]. rewrite !app_nil_r, Z.add_0_r.
reflexivity.
Qed.

Lemma ss_block_same : forall lens i, 0 <= i < Zlength lens ->
  ss_block lens (i + 1) (Znth i lens) =
  upd_Znth (count_len (sublist 0 i lens) (Znth i lens)) (ss_block lens i (Znth i lens)) (Vint (Int.repr i)).
Proof.
intros. set (l := Znth i lens).
assert (Hc: count_len (sublist 0 (i+1) lens) l <= count_len lens l) by (apply ss_count_len_prefix; lia).
rewrite ss_count_step in Hc by lia. unfold l in Hc at 2; rewrite Z.eqb_refl in Hc.
unfold ss_block. rewrite ss_count_step by lia. unfold l at 3. rewrite Z.eqb_refl.
rewrite !ss_syms_of_len, ss_sublist_snoc by lia. rewrite ss_sl_snoc. unfold l at 3; rewrite Z.eqb_refl.
rewrite Zlength_sublist by lia. rewrite Z.sub_0_r.
pose proof (ss_sl_len (sublist 0 i lens) 0 l).
fold l. unfold zs_rep. rewrite map_app.
set (c := count_len (sublist 0 i lens) l) in *. set (n := count_len lens l) in *.
change (syms_of_len (sublist 0 i lens) l) with (ss_sl 0 (sublist 0 i lens) l).
set (A := ss_sl 0 (sublist 0 i lens) l) in *. clearbody c n A. simpl map. rewrite Z.add_0_l.
rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia).
rewrite Zlength_map, H0, Z.sub_diag. replace (n-c) with (1 + (n-(c+1))) by lia.
rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
rewrite <- app_assoc. reflexivity.
Qed.

Lemma ss_zseq_in : forall n s x, In x (zseq s n) -> s <= x < s + Z.of_nat n.
Proof. induction n; simpl; intros s x H; [contradiction|]. destruct H as [<-|H]; [lia|]. apply IHn in H. lia. Qed.

Lemma ss_flat_map_ext_in : forall {A B} (f g: A -> list B) xs,
  (forall x, In x xs -> f x = g x) -> flat_map f xs = flat_map g xs.
Proof.
induction xs; intros H; simpl; [reflexivity|]. rewrite H by (simpl; auto).
rewrite IHxs by (intros; apply H; simpl; auto). reflexivity.
Qed.

Lemma ss_work_len : forall lens i, 0 <= i <= Zlength lens -> Zlength (sorted_syms lens) <= Zlength lens ->
  Zlength (ss_work lens i) = Zlength lens.
Proof.
intros. unfold ss_work. rewrite Zlength_app, Zlength_Zrepeat by lia.
unfold sorted_syms. rewrite (ss_flat_map_len _ (syms_of_len lens)). lia.
intros. rewrite ss_block_len by lia. rewrite ss_syms_of_len, ss_sl_len. reflexivity.
Qed.

Lemma ss_work_step : forall lens i, 0 <= i < Zlength lens -> 1 <= Znth i lens <= 15 ->
  upd_Znth (ss_off lens (Znth i lens) + count_len (sublist 0 i lens) (Znth i lens)) (ss_work lens i)
           (Vint (Int.repr i)) = ss_work lens (i + 1).
Proof.
intros lens i H Hl. set (l := Znth i lens) in *.
unfold ss_work. rewrite (ss_zseq_split l Hl), !ss_flat_map_app.
rewrite <- (ss_off_eq lens i l) by lia.
pose proof (ss_count_len_prefix lens (i+1) l ltac:(lia)) as Hc. rewrite ss_count_step in Hc by lia.
unfold l in Hc at 2; rewrite Z.eqb_refl in Hc.
assert (Hb: Zlength (ss_block lens i l) = count_len lens l) by (apply ss_block_len; lia).
rewrite <- !app_assoc.
change (flat_map (ss_block lens i) [l]) with (ss_block lens i l ++ []).
change (flat_map (ss_block lens (i+1)) [l]) with (ss_block lens (i+1) l ++ []). rewrite !app_nil_r.
rewrite (ss_flat_map_ext_in (ss_block lens (i+1)) (ss_block lens i) (zseq 1 (Z.to_nat (l - 1)))).
2: { intros x Hx. apply ss_zseq_in in Hx. rewrite ss_block_other by lia. reflexivity. }
rewrite (ss_flat_map_ext_in (ss_block lens (i+1)) (ss_block lens i) (zseq (l + 1) (Z.to_nat (15 - l)))).
2: { intros x Hx. apply ss_zseq_in in Hx. rewrite ss_block_other by lia. reflexivity. }
unfold l at 4. rewrite ss_block_same by lia. fold l.
set (P := flat_map (ss_block lens i) (zseq 1 (Z.to_nat (l - 1)))).
set (Q := flat_map (ss_block lens i) (zseq (l + 1) (Z.to_nat (15 - l)))).
set (R := Zrepeat Vundef (Zlength lens - Zlength (sorted_syms lens))).
set (B := ss_block lens i l) in *.
pose proof (ss_count_len_nonneg (sublist 0 i lens) l).
rewrite upd_Znth_app2 by (rewrite !Zlength_app; pose proof (Zlength_nonneg P); pose proof (Zlength_nonneg Q); pose proof (Zlength_nonneg R); lia).
rewrite Z.add_simpl_l. f_equal.
rewrite upd_Znth_app1 by lia. reflexivity.
Qed.

Lemma ss_work_step0 : forall lens i, 0 <= i < Zlength lens -> Znth i lens = 0 ->
  ss_work lens (i + 1) = ss_work lens i.
Proof.
intros. unfold ss_work. f_equal. apply ss_flat_map_ext_in. intros x Hx. apply ss_zseq_in in Hx.
apply ss_block_other; lia.
Qed.

Lemma ss_repeat_flat_map : forall {A} (v: A) (c: Z -> Z) xs, (forall x, 0 <= c x) ->
  flat_map (fun x => Zrepeat v (c x)) xs = Zrepeat v (Zlength (flat_map (fun x => Zrepeat v (c x)) xs)).
Proof.
induction xs; intros H; simpl; [reflexivity|]. rewrite IHxs at 1 by auto.
rewrite Zlength_app, Zlength_Zrepeat by auto. rewrite Zrepeat_app; auto. apply Zlength_nonneg.
Qed.

Lemma ss_work_init : forall lens, Zlength (sorted_syms lens) <= Zlength lens ->
  ss_work lens 0 = Zrepeat Vundef (Zlength lens).
Proof.
intros. pose proof (ss_work_len lens 0 ltac:(pose proof (Zlength_nonneg lens); lia) H) as HL.
unfold ss_work in *. unfold ss_block in *. rewrite sublist_nil in *.
change (zs_rep (syms_of_len [] _)) with (@nil val) in *.
assert (E: forall l, count_len lens l - count_len [] l = count_len lens l) by (intros; unfold count_len; simpl; rewrite Zlength_nil; lia).
rewrite (ss_flat_map_ext_in _ (fun l => Zrepeat Vundef (count_len lens l))) by (intros; rewrite E; reflexivity).
rewrite (ss_flat_map_ext_in _ (fun l => Zrepeat Vundef (count_len lens l))) in HL by (intros; rewrite E; reflexivity).
rewrite ss_repeat_flat_map in * by apply ss_count_len_nonneg.
rewrite Zrepeat_app; [|apply Zlength_nonneg|].
- f_equal. rewrite Zlength_app, !Zlength_Zrepeat in HL by (try apply Zlength_nonneg; lia). lia.
- lia.
Qed.

Lemma ss_map_flat_map : forall {A B C} (f: B -> C) (g: A -> list B) xs,
  map f (flat_map g xs) = flat_map (fun x => map f (g x)) xs.
Proof. induction xs; simpl; [reflexivity|]. rewrite map_app, IHxs. reflexivity. Qed.

Lemma ss_work_final : forall lens,
  ss_work lens (Zlength lens) = zs_rep (sorted_syms lens) ++ Zrepeat Vundef (Zlength lens - Zlength (sorted_syms lens)).
Proof.
intros. unfold ss_work. f_equal. unfold sorted_syms, zs_rep. rewrite ss_map_flat_map.
apply ss_flat_map_ext_in. intros. unfold ss_block. rewrite sublist_same by lia.
rewrite Z.sub_diag. rewrite app_nil_r. reflexivity.
Qed.

Lemma ss_offs_nth : forall lens i l, 1 <= l <= 15 ->
  Znth l (ss_offs lens i) = Vint (Int.repr (ss_off lens l + count_len (sublist 0 i lens) l)).
Proof.
intros. unfold ss_offs. rewrite Znth_pos_cons by lia. rewrite Znth_map by (rewrite ss_zseq_len; simpl; lia).
rewrite ss_zseq_nth by (simpl; lia). replace (1 + (l - 1)) with l by lia. reflexivity.
Qed.

Lemma ss_offs_len : forall lens i, Zlength (ss_offs lens i) = 16.
Proof. intros. unfold ss_offs. rewrite Zlength_cons, Zlength_map, ss_zseq_len. reflexivity. Qed.

Lemma ss_offs_step : forall lens i, 0 <= i < Zlength lens -> 1 <= Znth i lens <= 15 ->
  upd_Znth (Znth i lens) (ss_offs lens i)
    (Vint (Int.repr (ss_off lens (Znth i lens) + count_len (sublist 0 i lens) (Znth i lens) + 1))) =
  ss_offs lens (i + 1).
Proof.
intros. apply Znth_eq_ext. { rewrite Zlength_upd_Znth, !ss_offs_len. reflexivity. }
intros k Hk. rewrite Zlength_upd_Znth, ss_offs_len in Hk.
destruct (Z.eq_dec k 0) as [->|Hk0].
- rewrite upd_Znth_diff by (rewrite ?ss_offs_len; lia). reflexivity.
- rewrite (ss_offs_nth lens (i+1)) by lia. rewrite ss_count_step by lia.
  destruct (Z.eq_dec k (Znth i lens)) as [<-|Hne].
  + rewrite upd_Znth_same by (rewrite ss_offs_len; lia). rewrite Z.eqb_refl. do 2 f_equal. lia.
  + rewrite upd_Znth_diff by (rewrite ?ss_offs_len; lia). rewrite ss_offs_nth by lia.
    destruct (Z.eqb_spec (Znth i lens) k); [lia|]. do 2 f_equal. lia.
Qed.

Lemma ss_offs_step0 : forall lens i, 0 <= i < Zlength lens -> Znth i lens = 0 ->
  ss_offs lens (i + 1) = ss_offs lens i.
Proof.
intros. unfold ss_offs. f_equal. apply map_ext_in. intros l Hl. apply ss_zseq_in in Hl.
rewrite ss_count_step by lia. destruct (Z.eqb_spec (Znth i lens) l); [lia|]. do 3 f_equal. lia.
Qed.

(* offs[] during the offs loop: offs[1..len] set. *)
Definition ss_offs0 (lens: list Z) (len: Z) : list val :=
  Vundef :: map (fun l => Vint (Int.repr (ss_off lens l))) (zseq 1 (Z.to_nat len)) ++ Zrepeat Vundef (15 - len).

Lemma ss_offs0_step : forall lens len, 1 <= len < 15 ->
  upd_Znth (len + 1) (ss_offs0 lens len) (Vint (Int.repr (ss_off lens len + count_len lens len))) =
  ss_offs0 lens (len + 1).
Proof.
intros. unfold ss_offs0. replace (Z.to_nat (len + 1)) with (Z.to_nat len + 1)%nat by lia.
rewrite ss_zseq_app, map_app. simpl map. rewrite <- ss_off_step by lia.
replace (1 + Z.of_nat (Z.to_nat len)) with (len + 1) by lia.
set (M := map (fun l => Vint (Int.repr (ss_off lens l))) (zseq 1 (Z.to_nat len))).
assert (Zlength M = len) by (unfold M; rewrite Zlength_map, ss_zseq_len; lia). clearbody M.
list_solve.
Qed.

Lemma ss_offs0_nth : forall lens len k, 1 <= k <= len -> len <= 15 ->
  Znth k (ss_offs0 lens len) = Vint (Int.repr (ss_off lens k)).
Proof.
intros. unfold ss_offs0. rewrite Znth_pos_cons by lia.
rewrite Znth_app1 by (rewrite Zlength_map, ss_zseq_len; lia).
rewrite Znth_map by (rewrite ss_zseq_len; lia). rewrite ss_zseq_nth by lia.
replace (1 + (k - 1)) with k by lia. reflexivity.
Qed.

Lemma ss_offs0_len : forall lens len, 0 <= len <= 15 -> Zlength (ss_offs0 lens len) = 16.
Proof.
intros. unfold ss_offs0. rewrite Zlength_cons, Zlength_app, Zlength_map, ss_zseq_len, Zlength_Zrepeat by lia. lia.
Qed.

Lemma ss_offs0_final : forall lens, ss_offs0 lens 15 = ss_offs lens 0.
Proof.
intros. unfold ss_offs0, ss_offs. rewrite app_nil_r. f_equal. apply map_ext. intros.
unfold count_len. rewrite sublist_nil. simpl. rewrite Zlength_nil, Z.add_0_r. reflexivity.
Qed.

#[local] Opaque counts.

Lemma seg_sort_ok : loop_facts -> seg_sort_stmt.
Proof.
intros LF Espec X WF.
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; simpl in WF. destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
destruct LF as [SS _]. destruct IN as (Ht & Hn & Hl & Hr).
destruct (SS lens Hl) as [HS HSF]. clear SS.
assert (HN: Zlength lens <= 288) by (unfold max_codes in Hn; repeat destruct (_ =? _); lia).
unfold A_acc, A_sorted, it_sep, params_locs, count_at, work_, work_sorted, it_mx, it_root, POST_it, it_model.
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold seg_sort.
abbreviate_semax.
Intros.
forward.
change (upd_Znth 1 (default_val (tarray tushort 16)) (Vint (Int.zero_ext 16 (Int.repr 0)))) with (ss_offs0 lens 1).
match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
forward;
forward_loop (EX len:Z, PROPx [1 <= len <= 15] (LOCALx (temp _len (Vint (Int.repr len)) :: Q)
   (SEPx (data_at Tsh (tarray tushort 16) (ss_offs0 lens len) vo :: R))))
  continue: (EX len:Z, PROPx [1 <= len < 15] (LOCALx (temp _len (Vint (Int.repr len)) :: Q)
   (SEPx (data_at Tsh (tarray tushort 16) (ss_offs0 lens (len + 1)) vo :: R))))
  break: (PROPx [] (LOCALx Q
   (SEPx (data_at Tsh (tarray tushort 16) (ss_offs lens 0) vo :: R))))
end.
- Exists 1. entailer!.
- Intros len. forward_if.
  2: { forward. assert (len = 15) by lia. subst len. rewrite ss_offs0_final. entailer!. }
  pose proof (ss_sorted_len lens len ltac:(lia)).
  pose proof (ss_count_len_nonneg lens len).
  assert (0 <= ss_off lens len) by (unfold ss_off; apply Zlength_nonneg).
  forward.
  { entailer!. rewrite ss_offs0_nth by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
  rewrite ss_offs0_nth by lia.
  forward.
  { entailer!. unfold zs_rep; rewrite Znth_map by (rewrite ss_counts_len; lia). rewrite ss_counts_nth by lia.
    simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
  unfold zs_rep at 1; rewrite Znth_map by (rewrite ss_counts_len; lia).
  rewrite ss_counts_nth by lia.
  forward.
  Exists len. entailer!.
  rewrite zero_ext_16 by rep_lia. rewrite ss_offs0_step by lia. auto.
- Intros len. forward. Exists (len + 1). entailer!.
-   match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (_ :: ?R1 :: ?R2 :: ?R3 :: ?R4 :: _ :: ?R5)))) _ _ =>
  forward;
  forward_loop (EX i:Z, PROPx [0 <= i <= Zlength lens] (LOCALx (temp _sym (Vint (Int.repr i)) :: Q)
     (SEPx (data_at Tsh (tarray tushort 16) (ss_offs lens i) vo :: R1 :: R2 :: R3 :: R4 ::
            data_at sh (tarray tushort (Zlength lens)) (ss_work lens i) pw :: R5))))
    continue: (EX i:Z, PROPx [0 <= i < Zlength lens] (LOCALx (temp _sym (Vint (Int.repr i)) :: Q)
     (SEPx (data_at Tsh (tarray tushort 16) (ss_offs lens (i + 1)) vo :: R1 :: R2 :: R3 :: R4 ::
            data_at sh (tarray tushort (Zlength lens)) (ss_work lens (i + 1)) pw :: R5))))
    break: (PROPx [] (LOCALx Q
     (SEPx (data_at Tsh (tarray tushort 16) (ss_offs lens (Zlength lens)) vo :: R1 :: R2 :: R3 :: R4 ::
            data_at sh (tarray tushort (Zlength lens)) (ss_work lens (Zlength lens)) pw :: R5))))
  end.
  + Exists 0. entailer!. rewrite ss_work_init by auto. apply derives_refl'. rewrite data_at__eq. reflexivity.
  + Intros i. forward_if.
    all: try rewrite !Int.unsigned_repr in H2 by rep_lia.
    all: try rewrite !Int.unsigned_repr in H1 by rep_lia.
    2: { forward. assert (i = Zlength lens) by lia. subst i. entailer!. }
    assert (Hi: 0 <= Znth i lens <= 15) by (rewrite Forall_forall in Hl; apply Hl; apply Znth_In; lia).
    forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    unfold zs_rep at 1; rewrite Znth_map by lia.
    pose proof (ss_offs_len lens i).
    pose proof (ss_work_len lens i ltac:(lia) HS).
    forward_if.
    * assert (Hl1: 1 <= Znth i lens <= 15) by (split; [|lia]; destruct (Z.eq_dec (Znth i lens) 0) as [E|E];
        [rewrite E in H5; contradiction|lia]).
      pose proof (ss_sorted_len lens (Znth i lens) Hl1).
      pose proof (ss_count_len_prefix lens (i+1) (Znth i lens) ltac:(lia)).
      rewrite ss_count_step, Z.eqb_refl in H7 by lia.
      pose proof (ss_count_len_nonneg (sublist 0 i lens) (Znth i lens)).
      assert (0 <= ss_off lens (Znth i lens)) by (unfold ss_off; apply Zlength_nonneg).
      forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
      unfold zs_rep at 1; rewrite Znth_map by lia.
      forward. { entailer!. rewrite ss_offs_nth by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
      rewrite ss_offs_nth by lia.
      forward. { entailer!. unfold zs_rep; rewrite Znth_map by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
      unfold zs_rep at 1; rewrite Znth_map by lia.
      forward.
      forward.
      Exists i. entailer!.
      rewrite !zero_ext_16 by rep_lia. rewrite ss_offs_step, ss_work_step by lia. auto.
    * forward.
      Exists i. rewrite ss_offs_step0, ss_work_step0 by lia. entailer!.
  + Intros i. forward. Exists (i+1). entailer!.
  + unfold POSTCONDITION, abbreviate; simpl_ret_assert. rewrite ss_work_final. entailer!.
Qed.

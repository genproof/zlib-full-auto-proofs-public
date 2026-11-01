(* Body proofs of harness/deflate_ref.h helpers: see DRefSpec.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.

#[local] Existing Instance Zlib.contracts.x_inflate_decode.Harness.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts                                                                                     *)

Definition kterm (l: Z) : Z := if l =? 0 then 0 else 2 ^ (MAXLEN - l).

Lemma kraft_sum_app l1 l2: kraft_sum (l1 ++ l2) = kraft_sum l1 + kraft_sum l2.
Proof.
  induction l1 as [|a r IH]; simpl; [reflexivity|].
  unfold kraft_sum in *. simpl. rewrite IH. destruct (a =? 0); lia.
Qed.

Lemma kraft_sum_one l: kraft_sum [l] = kterm l.
Proof. unfold kraft_sum, kterm. simpl. destruct (l =? 0); lia. Qed.

Lemma nused_app l1 l2: nused (l1 ++ l2) = nused l1 + nused l2.
Proof. unfold nused. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma nused_one l: nused [l] = if l =? 0 then 0 else 1.
Proof. unfold nused. simpl. destruct (l =? 0); reflexivity. Qed.

Lemma kraft_sum_bound lens: Forall (fun l => 0 <= l <= 15) lens ->
  0 <= kraft_sum lens <= 2 ^ 15 * Zlength lens.
Proof.
  induction 1 as [|a r Ha Hr IH]; [simpl; lia|].
  change (a :: r) with ([a] ++ r). rewrite kraft_sum_app, kraft_sum_one, Zlength_app, Zlength_cons, Zlength_nil.
  unfold kterm, MAXLEN. destruct (a =? 0); [lia|].
  assert (0 <= 2 ^ (15 - a) <= 2 ^ 15) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  lia.
Qed.

Lemma nused_bound lens: 0 <= nused lens <= Zlength lens.
Proof.
  unfold nused. split; [apply Zlength_nonneg|].
  rewrite !Zlength_correct. apply Nat2Z.inj_le. apply filter_length_le.
Qed.

Lemma sublist_snoc {A} {d: Inhabitant A} (l: list A) i: 0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l].
Proof. intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

Lemma kraft_add K L: 1 <= L <= 15 ->
  Int64.add (Int64.repr K) (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.sub (Int.repr 15) (Int.repr L))))) =
  Int64.repr (K + 2 ^ (15 - L)).
Proof.
  intros HL. unfold Int.sub. rewrite (Int.unsigned_repr 15), (Int.unsigned_repr L) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia.
  rewrite Int64.mul_commut, Int64.mul_one. rewrite two_p_correct by lia.
  unfold Int64.add. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma shift_ok L: 1 <= L <= 15 ->
  Int.ltu (Int.sub (Int.repr 15) (Int.repr L)) Int64.iwordsize' = true.
Proof.
  intros HL. unfold Int.sub. rewrite (Int.unsigned_repr 15), (Int.unsigned_repr L) by rep_lia.
  unfold Int.ltu. rewrite Int.unsigned_repr by rep_lia. assert (W: Int.unsigned Int64.iwordsize' = 64) by reflexivity.
  rewrite W. destruct (zlt _ _); [reflexivity | lia].
Qed.

Lemma Int64_eq_repr a b: 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.repr a = Int64.repr b -> a = b.
Proof. intros. rewrite <- (Int64.unsigned_repr a), <- (Int64.unsigned_repr b) by auto. congruence. Qed.

(* lens[i] as a load *)
Lemma add_ptr_u p n k c:
  field_compatible (tarray tuchar n) [] p -> 0 <= k + c < n -> 0 <= c <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val k p) (Vint (Int.repr c))) =
  field_address (tarray tuchar n) [ArraySubsc (k + c)] p.
Proof.
  intros FC Hk Hc. rewrite arr_field_address by auto.
  destruct p; try (destruct FC; contradiction). simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
  rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia.
Qed.

Lemma Znth_lens lo n lcont lens i:
  sublist lo (lo + n) lcont = Bytes.bytes_rep lens -> Zlength lens = n ->
  0 <= lo -> lo + n <= Zlength lcont -> 0 <= i < n ->
  Znth (lo + i) lcont = Vint (Int.repr (Znth i lens)).
Proof.
  intros Hsub Hlen Hlo Hn Hi.
  rewrite <- Bytes.Znth_bytes_rep by lia. rewrite <- Hsub.
  rewrite Znth_sublist by lia. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* kraft                                                                                          *)

Lemma body_kraft: semax_body Vprog_dref Gprog_kraft HD.f_kraft kraft_spec.
Proof.
  start_function.
  match goal with H: Bytes.cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst lbuf.
  assert_PROP (field_compatible (tarray tuchar ln) [] lp) as FC by entailer!.
  assert_PROP (Zlength lcont = ln) as Hlc by (entailer!; rewrite Zlength_correct in *; auto).
  assert (HL: forall i, 0 <= i < n -> 0 <= Znth i lens <= 15) by
    (intros; match goal with H: Forall _ lens |- _ => rewrite Forall_forall in H; apply H, Znth_In; lia end).
  forward. forward.
  forward_for_simple_bound n (EX i: Z,
     PROP ()
     LOCAL (temp HD._k (Vlong (Int64.repr (kraft_sum (sublist 0 i lens))));
            temp HD._u (Vint (Int.repr (nused (sublist 0 i lens))));
            temp HD._lens (offset_val lo lp); temp HD._n (Vint (Int.repr n)); temp HD._used up)
     SEP (data_at lsh (tarray tuchar ln) lcont lp; data_at_ ush tuint up)).
  - entailer!.
  - assert (E: force_val (sem_add_ptr_int tuchar Unsigned (offset_val lo lp) (Vint (Int.repr i))) =
               field_address (tarray tuchar ln) [ArraySubsc (lo + i)] lp) by (apply add_ptr_u; auto; rep_lia).
    assert (Hb: @Znth val Vundef (lo + i) lcont = Vint (Int.repr (Znth i lens))) by (apply (Znth_lens lo n); auto; lia).
    specialize (HL i ltac:(lia)).
    assert (KB := kraft_sum_bound (sublist 0 i lens) ltac:(apply Forall_sublist; auto)).
    assert (UB := nused_bound (sublist 0 i lens)).
    rewrite Zlength_sublist in KB, UB by lia.
    forward.
    { rewrite Hb. entailer!; simpl; rep_lia. }
    rewrite Hb. forward_if.
    + forward. { rewrite Hb. entailer!; simpl; rep_lia. }
      rewrite Hb. forward.
      { entailer!. assert (W: Int.unsigned Int64.iwordsize' = 64) by reflexivity. lia. }
      rewrite kraft_add by lia. forward.
      entailer!. rewrite sublist_snoc by lia. rewrite kraft_sum_app, kraft_sum_one, nused_app, nused_one.
      unfold kterm, MAXLEN. destruct (Znth i lens =? 0) eqn:Z0; [apply Z.eqb_eq in Z0; lia|]. split; reflexivity.
    + forward. entailer!. rewrite sublist_snoc by lia. rewrite kraft_sum_app, kraft_sum_one, nused_app, nused_one.
      unfold kterm. match goal with H: Znth i lens = 0 |- _ => rewrite H end. simpl. rewrite !Z.add_0_r. split; reflexivity.
  - rewrite sublist_same by lia. forward. forward.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* code_ok                                                                                        *)

Lemma body_code_ok: semax_body Vprog_dref Gprog_code_ok HD.f_code_ok code_ok_spec.
Proof.
  start_function.
  assert (KB := kraft_sum_bound lens ltac:(auto)).
  assert (UB := nused_bound lens).
  assert (Hlen: Zlength lens = n) by
    (match goal with H: Bytes.cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (_ & _ & _ & _ & ? & _) end; auto).
  forward_call (lbuf, lsh, lp, lo, ln, lcont, n, lens, Tsh, v_used).
  assert (KR: 0 <= kraft_sum lens <= Int64.max_unsigned) by rep_lia.
  forward_if.
  { assert (E: kraft_sum lens = 32768) by (apply Int64_eq_repr; [auto | rep_lia | apply Int64.same_if_eq; auto]).
    forward. entailer!. unfold code_okb. rewrite E. reflexivity. }
  assert (K1: kraft_sum lens <> 32768) by (intro E; apply H3; rewrite E; reflexivity).
  forward_if.
  { subst type. forward. entailer!. unfold code_okb. rewrite (proj2 (Z.eqb_neq _ _) K1). reflexivity. }
  forward.
  forward_if (temp HD._t'2 (Vint (if andb (nused lens =? 1) (kraft_sum lens =? 16384) then Int.one else Int.zero))).
  { forward. entailer!. rewrite (proj2 (Z.eqb_eq _ _) H5). simpl.
    destruct (kraft_sum lens =? 16384) eqn:EK; [apply Z.eqb_eq in EK | apply Z.eqb_neq in EK].
    - rewrite EK. reflexivity.
    - unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia. destruct (zeq _ _); [lia|]. reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) H5). reflexivity. }
  forward_if.
  { forward. entailer!. unfold code_okb.
    rewrite (proj2 (Z.eqb_neq _ _) K1), (proj2 (Z.eqb_neq _ _) H4).
    destruct (nused lens =? 1), (kraft_sum lens =? 16384); simpl in *; try reflexivity; contradiction. }
  forward_if (temp HD._t'3 (Vint (if andb (type =? 2) (nused lens =? 0) then Int.one else Int.zero))).
  { subst type. forward. forward. entailer!. simpl.
    destruct (Z.eqb_spec (nused lens) 0); destruct (zeq (nused lens) 0); try lia; reflexivity. }
  { forward. entailer!. match goal with H: type <> 2 |- _ => rewrite (proj2 (Z.eqb_neq _ _) H) end. reflexivity. }
  forward. entailer!. unfold code_okb.
  rewrite (proj2 (Z.eqb_neq _ _) K1), (proj2 (Z.eqb_neq _ _) H4).
  destruct (nused lens =? 1), (kraft_sum lens =? 16384), (type =? 2), (nused lens =? 0); simpl in *;
    try reflexivity; exfalso; apply Int.one_not_zero; assumption.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* canonical: pure facts                                                                          *)

(* count[l] after the counting loop over pre (count[0] included) *)
Definition cnt (pre: list Z) (l: Z) : Z := Zlength (filter (fun x => x =? l) pre).
Definition cntv (pre: list Z) : list val := map (fun l => Vint (Int.repr (cnt pre l))) (upto 16).
(* count[] after count[0] = 0 *)
Definition cofv (lens: list Z) : list val := map (fun l => Vint (Int.repr (count_of lens l))) (upto 16).
(* next[0 .. k) after the next_code loop *)
Definition nextv (lens: list Z) (k: Z) : list val :=
  map (fun l => Vint (Int.repr (next_code_n lens (Z.to_nat l)))) (sublist 0 k (upto 16)) ++ Zrepeat Vundef (16 - k).
(* next[] in the code loop after the symbols pre *)
Definition nxt (lens pre: list Z) : list val :=
  map (fun l => Vint (Int.repr (next_code_n lens (Z.to_nat l) + count_of pre l))) (upto 16).

Lemma Zlength_upto16: Zlength (upto 16) = 16.
Proof. reflexivity. Qed.

Lemma cnt_snoc pre L l: cnt (pre ++ [L]) l = cnt pre l + (if L =? l then 1 else 0).
Proof. unfold cnt. rewrite filter_app, Zlength_app. simpl. destruct (L =? l); reflexivity. Qed.

Lemma cnt_bound pre l: 0 <= cnt pre l <= Zlength pre.
Proof.
  unfold cnt. split; [apply Zlength_nonneg|].
  rewrite !Zlength_correct. apply Nat2Z.inj_le. apply filter_length_le.
Qed.

Lemma count_of_bound pre l: 0 <= count_of pre l <= Zlength pre.
Proof.
  unfold count_of. destruct (l =? 0); [pose proof (Zlength_nonneg pre); lia|].
  apply (cnt_bound pre l).
Qed.

Lemma count_of_snoc pre L l: count_of (pre ++ [L]) l = count_of pre l + (if l =? 0 then 0 else if L =? l then 1 else 0).
Proof.
  unfold count_of. destruct (l =? 0); [reflexivity|]. apply cnt_snoc.
Qed.

Lemma Znth_cntv pre l: 0 <= l < 16 -> Znth l (cntv pre) = Vint (Int.repr (cnt pre l)).
Proof. intros. unfold cntv. rewrite Znth_map by (rewrite ?Zlength_upto16; lia). rewrite Znth_upto by (simpl; lia). reflexivity. Qed.

Lemma Znth_cofv lens l: 0 <= l < 16 -> Znth l (cofv lens) = Vint (Int.repr (count_of lens l)).
Proof. intros. unfold cofv. rewrite Znth_map by (rewrite ?Zlength_upto16; lia). rewrite Znth_upto by (simpl; lia). reflexivity. Qed.

Lemma Znth_nxt lens pre l: 0 <= l < 16 ->
  Znth l (nxt lens pre) = Vint (Int.repr (next_code_n lens (Z.to_nat l) + count_of pre l)).
Proof. intros. unfold nxt. rewrite Znth_map by (rewrite ?Zlength_upto16; lia). rewrite Znth_upto by (simpl; lia). reflexivity. Qed.

Lemma cntv_nil: cntv [] = Zrepeat (Vint (Int.repr 0)) 16.
Proof. reflexivity. Qed.

Lemma cntv_snoc pre L: 0 <= L < 16 ->
  upd_Znth L (cntv pre) (Vint (Int.repr (cnt pre L + 1))) = cntv (pre ++ [L]).
Proof.
  intros HL. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth. unfold cntv. rewrite !Zlength_map. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth in Hj. unfold cntv in Hj. rewrite Zlength_map, Zlength_upto16 in Hj.
    rewrite Znth_cntv by lia. rewrite cnt_snoc.
    destruct (Z.eq_dec j L).
    + subst. rewrite upd_Znth_same by (unfold cntv; rewrite Zlength_map, Zlength_upto16; lia).
      rewrite Z.eqb_refl. reflexivity.
    + rewrite upd_Znth_diff by (unfold cntv; rewrite ?Zlength_map, ?Zlength_upto16; lia).
      rewrite Znth_cntv by lia. rewrite (proj2 (Z.eqb_neq L j)) by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma cofv_of_cntv lens: upd_Znth 0 (cntv lens) (Vint (Int.repr 0)) = cofv lens.
Proof.
  apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth. unfold cntv, cofv. rewrite !Zlength_map. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth in Hj. unfold cntv in Hj. rewrite Zlength_map, Zlength_upto16 in Hj.
    rewrite Znth_cofv by lia. unfold count_of.
    destruct (Z.eq_dec j 0).
    + subst. rewrite upd_Znth_same by (unfold cntv; rewrite Zlength_map, Zlength_upto16; lia). reflexivity.
    + rewrite upd_Znth_diff by (unfold cntv; rewrite ?Zlength_map, ?Zlength_upto16; lia).
      rewrite Znth_cntv by lia. rewrite (proj2 (Z.eqb_neq j 0)) by lia. reflexivity.
Qed.

Lemma next_code_n_bound lens k: 0 <= next_code_n lens k <= (2 ^ Z.of_nat k - 1) * 2 * Zlength lens.
Proof.
  induction k as [|k IH]; simpl next_code_n.
  - simpl. lia.
  - pose proof (count_of_bound lens (Z.of_nat k)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (1 <= 2 ^ Z.of_nat k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    nia.
Qed.

Lemma next_code_small lens k: (k <= 15)%nat -> Zlength lens <= 316 ->
  0 <= next_code_n lens k <= 32767 * 632.
Proof.
  intros Hk Hn. pose proof (next_code_n_bound lens k).
  assert (2 ^ Z.of_nat k <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  pose proof (Zlength_nonneg lens). change (2 ^ 15) with 32768 in H0. nia.
Qed.

Lemma nextv_0: upd_Znth 0 (Zrepeat Vundef 16) (Vint (Int.repr 0)) = nextv [] 1 ++ [].
Proof. reflexivity. Qed.

Lemma nextv_start lens: upd_Znth 0 (Zrepeat Vundef 16) (Vint (Int.repr 0)) = nextv lens 1.
Proof. reflexivity. Qed.

Lemma nextv_step lens l: 1 <= l < 16 ->
  upd_Znth l (nextv lens l) (Vint (Int.repr (next_code_n lens (Z.to_nat l)))) = nextv lens (l + 1).
Proof.
  intros Hl. unfold nextv.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_Zrepeat by (rewrite ?Zlength_upto16; lia); lia).
  rewrite Zlength_map, Zlength_sublist by (rewrite ?Zlength_upto16; lia). rewrite Z.sub_0_r, Z.sub_diag.
  replace (16 - l) with (1 + (16 - (l + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite (sublist_split 0 l (l + 1)) by (rewrite ?Zlength_upto16; lia).
  rewrite sublist_len_1 by (rewrite ?Zlength_upto16; lia). rewrite Znth_upto by (simpl; lia).
  rewrite map_app, <- app_assoc. reflexivity.
Qed.

Lemma Znth_nextv lens k l: 0 <= l < k -> k <= 16 ->
  Znth l (nextv lens k) = Vint (Int.repr (next_code_n lens (Z.to_nat l))).
Proof.
  intros. unfold nextv. rewrite Znth_app1 by (rewrite Zlength_map, Zlength_sublist by (rewrite ?Zlength_upto16; lia); lia).
  rewrite Znth_map by (rewrite Zlength_sublist by (rewrite ?Zlength_upto16; lia); lia).
  rewrite Znth_sublist by (rewrite ?Zlength_upto16; lia). rewrite Znth_upto by (simpl; lia). f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nxt_start lens: nextv lens 16 = nxt lens [].
Proof.
  unfold nextv, nxt. rewrite sublist_same by reflexivity. simpl Zrepeat. rewrite app_nil_r.
  apply map_ext. intros l.
  assert (E: count_of [] l = 0) by (unfold count_of; destruct (l =? 0); reflexivity). rewrite E, Z.add_0_r. reflexivity.
Qed.

Lemma nxt_snoc lens pre L: 1 <= L < 16 ->
  upd_Znth L (nxt lens pre) (Vint (Int.repr (next_code_n lens (Z.to_nat L) + count_of pre L + 1))) = nxt lens (pre ++ [L]).
Proof.
  intros HL. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth. unfold nxt. rewrite !Zlength_map. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth in Hj. unfold nxt in Hj. rewrite Zlength_map, Zlength_upto16 in Hj.
    rewrite Znth_nxt by lia. rewrite count_of_snoc.
    destruct (Z.eq_dec j L).
    + subst. rewrite upd_Znth_same by (unfold nxt; rewrite Zlength_map, Zlength_upto16; lia).
      rewrite (proj2 (Z.eqb_neq L 0)) by lia. rewrite Z.eqb_refl. f_equal. f_equal. lia.
    + rewrite upd_Znth_diff by (unfold nxt; rewrite ?Zlength_map, ?Zlength_upto16; lia).
      rewrite Znth_nxt by lia. rewrite (proj2 (Z.eqb_neq L j)) by lia. destruct (j =? 0); rewrite Z.add_0_r; reflexivity.
Qed.

Lemma nxt_snoc0 lens pre: nxt lens (pre ++ [0]) = nxt lens pre.
Proof.
  unfold nxt. apply map_ext. intros l. rewrite count_of_snoc.
  destruct (l =? 0) eqn:E; [rewrite Z.add_0_r; reflexivity|].
  rewrite Z.eqb_sym, E. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma Zlength_canon_vals lens: Zlength (canon_vals lens) = Zlength lens.
Proof. unfold canon_vals. rewrite Zlength_map, Zlength_correct, seq_length, <- Zlength_correct. reflexivity. Qed.

Lemma Znth_canon_vals lens i: 0 <= i < Zlength lens -> Znth i (canon_vals lens) = canon_val lens i.
Proof.
  intros. unfold canon_vals. rewrite Znth_map by (rewrite Zlength_correct, seq_length, <- Zlength_correct; lia).
  f_equal. rewrite <- (Z2Nat.id i) at 2 by lia. f_equal.
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length, <- Zlength_correct; lia).
  rewrite seq_nth by (rewrite Zlength_correct in H; lia). reflexivity.
Qed.

Lemma canon_val_code lens i: 0 <= i < Zlength lens -> Znth i lens <> 0 ->
  canon_val lens i = (next_code_n lens (Z.to_nat (Znth i lens)) + count_of (sublist 0 i lens) (Znth i lens)) mod 65536.
Proof.
  intros Hi HL. unfold canon_val, code, count_of. rewrite (proj2 (Z.eqb_neq _ 0) HL). reflexivity.
Qed.

Lemma canon_val_zero lens i: Znth i lens = 0 -> canon_val lens i = 0.
Proof. intros HL. unfold canon_val. rewrite HL. reflexivity. Qed.

Lemma codes_step lens K ccont i v: 0 <= i < Zlength lens -> Zlength lens <= K -> Zlength ccont = K ->
  v = canon_val lens i ->
  upd_Znth i (zvals (sublist 0 i (canon_vals lens)) ++ sublist i K ccont) (Vint (Int.repr v)) =
  zvals (sublist 0 (i + 1) (canon_vals lens)) ++ sublist (i + 1) K ccont.
Proof.
  intros Hi HK Hc Hv. subst v. pose proof (Zlength_canon_vals lens).
  rewrite upd_Znth_app2 by (unfold zvals; rewrite Zlength_map, !Zlength_sublist by lia; lia).
  unfold zvals. rewrite Zlength_map, Zlength_sublist by lia. rewrite Z.sub_0_r, Z.sub_diag.
  rewrite (sublist_split i (i + 1) K ccont) by lia.
  rewrite upd_Znth_app1 by (rewrite Zlength_sublist by lia; lia).
  rewrite (sublist_len_1 i ccont) by lia. unfold upd_Znth. simpl.
  rewrite (sublist_split 0 i (i + 1) (canon_vals lens)) by lia. rewrite sublist_len_1 by lia.
  rewrite map_app, <- app_assoc. simpl. rewrite Znth_canon_vals by lia. reflexivity.
Qed.

Lemma zrep_step (x: val) i N: 0 <= i < N ->
  upd_Znth i (Zrepeat x i ++ Zrepeat Vundef (N - i)) x = Zrepeat x (i + 1) ++ Zrepeat Vundef (N - (i + 1)).
Proof.
  intros. rewrite upd_Znth_app2 by (rewrite !Zlength_Zrepeat by lia; lia).
  rewrite Zlength_Zrepeat by lia. rewrite Z.sub_diag.
  replace (N - i) with (1 + (N - (i + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite app_assoc. f_equal. change (upd_Znth 0 (Zrepeat Vundef 1) x) with (Zrepeat x 1).
  rewrite Zrepeat_app by lia. reflexivity.
Qed.

Lemma nc_succ lens l: 1 <= l ->
  next_code_n lens (Z.to_nat l) = (next_code_n lens (Z.to_nat (l - 1)) + count_of lens (l - 1)) * 2.
Proof.
  intros. replace (Z.to_nat l) with (S (Z.to_nat (l - 1))) by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma shl1_repr a: Int.shl (Int.repr a) (Int.repr 1) = Int.repr (a * 2).
Proof.
  rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  change (two_p 1) with 2. rewrite mul_repr. reflexivity.
Qed.

Lemma zext16 v: Int.zero_ext 16 (Int.repr v) = Int.repr (v mod 65536).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. change (two_p 16) with 65536.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | reflexivity | exists 65536; reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* canonical                                                                                      *)

Lemma body_canonical: semax_body Vprog_dref Gprog_canonical HD.f_canonical canonical_spec.
Proof.
  start_function.
  match goal with H: Bytes.cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst lbuf.
  assert_PROP (field_compatible (tarray tuchar ln) [] lp) as FC by entailer!.
  assert_PROP (Zlength lcont = ln) as Hlc by (entailer!; rewrite Zlength_correct in *; auto).
  assert (HL: forall i, 0 <= i < n -> 0 <= Znth i lens <= 15) by
    (intros; match goal with H: Forall _ lens |- _ => rewrite Forall_forall in H; apply H, Znth_In; lia end).
  forward_for_simple_bound 16 (EX l: Z,
     PROP ()
     LOCAL (lvar HD._count (tarray tuint 16) v_count; lvar HD._next (tarray tuint 16) v_next;
            temp HD._lens (offset_val lo lp); temp HD._n (Vint (Int.repr n)); temp HD._codes cp)
     SEP (data_at Tsh (tarray tuint 16) (Zrepeat (Vint (Int.repr 0)) l ++ Zrepeat Vundef (16 - l)) v_count;
          data_at_ Tsh (tarray tuint 16) v_next;
          data_at lsh (tarray tuchar ln) lcont lp; data_at csh (tarray tushort K) ccont cp)).
  - entailer!.
  - forward. entailer!. rewrite zrep_step by lia. apply derives_refl.
  - rewrite Z.sub_diag, Zrepeat_0, app_nil_r, <- cntv_nil.
    forward_for_simple_bound n (EX i: Z,
     PROP ()
     LOCAL (lvar HD._count (tarray tuint 16) v_count; lvar HD._next (tarray tuint 16) v_next;
            temp HD._lens (offset_val lo lp); temp HD._n (Vint (Int.repr n)); temp HD._codes cp)
     SEP (data_at Tsh (tarray tuint 16) (cntv (sublist 0 i lens)) v_count;
          data_at_ Tsh (tarray tuint 16) v_next;
          data_at lsh (tarray tuchar ln) lcont lp; data_at csh (tarray tushort K) ccont cp)).
    + entailer!.
    + assert (E: force_val (sem_add_ptr_int tuchar Unsigned (offset_val lo lp) (Vint (Int.repr i))) =
               field_address (tarray tuchar ln) [ArraySubsc (lo + i)] lp) by (apply add_ptr_u; auto; rep_lia).
      assert (Hb: @Znth val Vundef (lo + i) lcont = Vint (Int.repr (Znth i lens))) by (apply (Znth_lens lo n); auto; lia).
      specialize (HL i ltac:(lia)).
      assert (CB := cnt_bound (sublist 0 i lens) (Znth i lens)). rewrite Zlength_sublist in CB by lia.
      forward.
      { rewrite Hb. entailer!; simpl; rep_lia. }
      rewrite Hb. forward.
      { rewrite Hb. entailer!; simpl; rep_lia. }
      rewrite Hb. forward.
      { entailer!. rewrite Znth_cntv by lia. simpl. auto. }
      rewrite Znth_cntv by lia. forward.
      entailer!. rewrite cntv_snoc by lia. rewrite <- sublist_snoc by lia. apply derives_refl.
    + rewrite sublist_same by lia.
      forward. forward. forward. rewrite cofv_of_cntv.
      forward_for_simple_bound 16 (EX l: Z,
        PROP (1 <= l)
        LOCAL (temp HD._c (Vint (Int.repr (next_code_n lens (Z.to_nat (l - 1)))));
               lvar HD._count (tarray tuint 16) v_count; lvar HD._next (tarray tuint 16) v_next;
               temp HD._lens (offset_val lo lp); temp HD._n (Vint (Int.repr n)); temp HD._codes cp)
        SEP (data_at Tsh (tarray tuint 16) (cofv lens) v_count;
             data_at Tsh (tarray tuint 16) (nextv lens l) v_next;
             data_at lsh (tarray tuchar ln) lcont lp; data_at csh (tarray tushort K) ccont cp)).
      * entailer!.
      * Intros. forward.
        { entailer!. rewrite Znth_cofv by lia. simpl. auto. }
        rewrite Znth_cofv by lia.
        forward. forward.
        entailer!.
        { rewrite ?add_repr, shl1_repr, <- nc_succ by lia. replace (i + 1 - 1) with i by lia. reflexivity. }
        rewrite ?add_repr, shl1_repr, <- nc_succ by lia. rewrite nextv_step by lia. apply derives_refl.
      * rewrite nxt_start.
        forward_for_simple_bound n (EX i: Z,
          PROP ()
          LOCAL (lvar HD._count (tarray tuint 16) v_count; lvar HD._next (tarray tuint 16) v_next;
                 temp HD._lens (offset_val lo lp); temp HD._n (Vint (Int.repr n)); temp HD._codes cp)
          SEP (data_at Tsh (tarray tuint 16) (cofv lens) v_count;
               data_at Tsh (tarray tuint 16) (nxt lens (sublist 0 i lens)) v_next;
               data_at lsh (tarray tuchar ln) lcont lp;
               data_at csh (tarray tushort K) (zvals (sublist 0 i (canon_vals lens)) ++ sublist i K ccont) cp)).
        -- entailer!. rewrite (sublist_same 0 (Zlength ccont) ccont), sublist_nil by lia. apply derives_refl.
        -- assert (E: force_val (sem_add_ptr_int tuchar Unsigned (offset_val lo lp) (Vint (Int.repr i))) =
                   field_address (tarray tuchar ln) [ArraySubsc (lo + i)] lp) by (apply add_ptr_u; auto; rep_lia).
           assert (Hb: @Znth val Vundef (lo + i) lcont = Vint (Int.repr (Znth i lens))) by (apply (Znth_lens lo n); auto; lia).
           specialize (HL i ltac:(lia)).
           forward.
           { rewrite Hb. entailer!; simpl; rep_lia. }
           rewrite Hb. forward_if.
           ++ assert (HL1: 1 <= Znth i lens <= 15) by lia.
              forward.
              { rewrite Hb. entailer!; simpl; rep_lia. }
              rewrite Hb. forward.
              { entailer!. rewrite Znth_nxt by lia. simpl. auto. }
              rewrite Znth_nxt by lia. forward.
              forward.
              { rewrite Hb. entailer!; simpl; rep_lia. }
              rewrite Hb. forward.
              { rewrite Hb. entailer!; simpl; rep_lia. }
              rewrite Hb. forward.
              { entailer!. rewrite Znth_nxt by lia. simpl. auto. }
              rewrite Znth_nxt by lia. forward.
              entailer!. rewrite !zext16, Zmod_mod, (codes_step lens (Zlength ccont) ccont i)
                by (try lia; rewrite canon_val_code by (auto; lia); reflexivity).
              rewrite ?add_repr, nxt_snoc by lia. rewrite <- (sublist_snoc lens i) by lia. cancel.
           ++ forward. entailer!.
              rewrite zext16, (codes_step lens (Zlength ccont) ccont i)
                by (try lia; rewrite canon_val_zero by auto; reflexivity).
              rewrite (sublist_snoc lens i) by lia.
              match goal with H: Znth i lens = 0 |- _ => rewrite H end. rewrite nxt_snoc0. cancel.
        -- rewrite (sublist_same 0 n (canon_vals lens)) by (rewrite ?Zlength_canon_vals; lia). entailer!.
Qed.

Lemma dref_canon_bodies_proof : dref_canon_bodies.
Proof.
  split; [exact body_canonical | split; [exact body_kraft | exact body_code_ok]].
Qed.

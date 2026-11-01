(* Law rj_bad_checksum, main: statements 21-25, the trailer (the last trl_of window_bits bytes of the compressed
   bytes) changed by xor with the bytes of change, and gp_assume(changed != 0) (bc_DH -> bc_TH). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.inflate.Callees.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.MainDefs.
Require Import Zlib.proof.harness.clip_streams.BCKit.
Require Import Zlib.harness.rj_bad_checksum.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The bytes of the compressed object during the loop                                             *)

(* O with its bytes k .. k + i - 1 xor'ed with the bytes 0 .. i - 1 of C: the object after i iterations of the loop
   (k = compressed_len - trailer_len) *)
Definition bc_x (k i : Z) (O C : list Z) : list Z :=
  map (fun j => if andb (k <=? j) (j <? k + i) then Z.lxor (Znth j O) (Znth (j - k) C) else Znth j O)
      (upto (length O)).

(* the value of changed after i iterations: the or of the first i bytes of C *)
Definition bc_or (i : Z) (C : list Z) : Z := fold_left Z.lor (sublist 0 i C) 0.

Lemma bc_x_length k i O C : Zlength (bc_x k i O C) = Zlength O.
Proof. unfold bc_x. rewrite Zlength_map, Zlength_upto, Zlength_correct. lia. Qed.

Lemma bc_x_Znth k i O C j : 0 <= j < Zlength O ->
  Znth j (bc_x k i O C) =
  if andb (k <=? j) (j <? k + i) then Z.lxor (Znth j O) (Znth (j - k) C) else Znth j O.
Proof.
  intros Hj. unfold bc_x. rewrite Znth_map by (rewrite Zlength_upto, <- Zlength_correct; lia).
  rewrite Znth_upto by (rewrite <- Zlength_correct; lia). reflexivity.
Qed.

Lemma bc_x_0 k O C : bc_x k 0 O C = O.
Proof.
  apply Znth_eq_ext; rewrite ?bc_x_length; auto. intros j Hj. rewrite bc_x_Znth by auto.
  destruct (k <=? j) eqn:E1, (j <? k + 0) eqn:E2; simpl; auto; lia.
Qed.

Lemma bc_x_S k i O C : 0 <= i -> 0 <= k -> k + i < Zlength O ->
  bc_x k (i + 1) O C = upd_Znth (k + i) (bc_x k i O C) (Z.lxor (Znth (k + i) O) (Znth i C)).
Proof.
  intros Hi Hk Hki. apply Znth_eq_ext.
  { rewrite upd_Znth_Zlength; rewrite !bc_x_length; lia. }
  intros j Hj. rewrite bc_x_length in Hj.
  destruct (Z.eq_dec j (k + i)) as [->|Ne].
  - rewrite upd_Znth_same by (rewrite bc_x_length; lia). rewrite bc_x_Znth by lia.
    replace (k + i - k) with i by lia.
    destruct (k <=? k + i) eqn:E1, (k + i <? k + (i + 1)) eqn:E2; simpl; auto; lia.
  - rewrite upd_Znth_diff by (rewrite ?bc_x_length; lia). rewrite !bc_x_Znth by lia.
    destruct (k <=? j) eqn:E1, (j <? k + (i + 1)) eqn:E2, (j <? k + i) eqn:E3; simpl; auto; lia.
Qed.

Lemma bc_lxor_byte x y : 0 <= x <= Byte.max_unsigned -> 0 <= y <= Byte.max_unsigned ->
  0 <= Z.lxor x y <= Byte.max_unsigned.
Proof.
  intros Hx Hy. change Byte.max_unsigned with 255 in *.
  assert (0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [lia | ].
  assert (Z.log2 (Z.lxor x y) < 8).
  { eapply Z.le_lt_trans; [apply Z.log2_lxor; lia | ]. apply Z.max_lub_lt.
    - destruct (Z.eq_dec x 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; simpl; lia.
    - destruct (Z.eq_dec y 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; simpl; lia. }
  assert (Z.lxor x y < 2 ^ 8) by (apply Z.log2_lt_pow2; lia). simpl in *. lia.
Qed.

Lemma bc_lor_byte x y : 0 <= x <= Byte.max_unsigned -> 0 <= y <= Byte.max_unsigned ->
  0 <= Z.lor x y <= Byte.max_unsigned.
Proof.
  intros Hx Hy. change Byte.max_unsigned with 255 in *.
  assert (0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
  destruct (Z.eq_dec (Z.lor x y) 0) as [E|E]; [lia | ].
  assert (Z.log2 (Z.lor x y) < 8).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
    - destruct (Z.eq_dec x 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; simpl; lia.
    - destruct (Z.eq_dec y 0) as [E0|E0]; [rewrite E0; simpl; lia | ]. apply Z.log2_lt_pow2; simpl; lia. }
  assert (Z.lor x y < 2 ^ 8) by (apply Z.log2_lt_pow2; lia). simpl in *. lia.
Qed.

Lemma bc_byte_at l j : is_bytes l -> 0 <= j < Zlength l -> 0 <= Znth j l <= Byte.max_unsigned.
Proof. intros H Hj. exact (proj1 (Forall_Znth l _) H j Hj). Qed.

Lemma bc_or_S i C : 0 <= i < Zlength C -> bc_or (i + 1) C = Z.lor (bc_or i C) (Znth i C).
Proof.
  intros Hi. unfold bc_or. rewrite (sublist_split 0 i (i + 1)) by lia.
  rewrite sublist_len_1 by lia. rewrite fold_left_app. reflexivity.
Qed.

Lemma bc_or_byte i C : 0 <= i <= Zlength C -> is_bytes C -> 0 <= bc_or i C <= Byte.max_unsigned.
Proof.
  intros [Hi0 Hi] HC. revert Hi. pattern i. apply natlike_rec2; auto.
  - intros _. unfold bc_or. rewrite sublist_nil. simpl. rep_lia.
  - intros z Hz IH Hz1. rewrite <- Z.add_1_r, bc_or_S by lia. apply bc_lor_byte; [apply IH; lia | ].
    apply bc_byte_at; auto; lia.
Qed.

(* changed != 0 at the end: some byte of the first i of C is not 0 *)
Lemma bc_or_nz i C : 0 <= i <= Zlength C -> bc_or i C <> 0 -> exists j, 0 <= j < i /\ Znth j C <> 0.
Proof.
  intros [Hi0 Hi]. revert Hi. pattern i. apply natlike_rec2; auto.
  - intros _ H. unfold bc_or in H. rewrite sublist_nil in H. simpl in H. congruence.
  - intros z Hz IH Hz1 Hnz. rewrite <- Z.add_1_r, bc_or_S in Hnz by lia.
    destruct (Z.eq_dec (Znth z C) 0) as [E|E].
    + rewrite E, Z.lor_0_r in Hnz. destruct (IH ltac:(lia) Hnz) as (j & Hj & Hj'). exists j; split; auto; lia.
    + exists z; split; auto; lia.
Qed.

Lemma bc_lxor_same x y : Z.lxor x y = x -> y = 0.
Proof.
  intros E. assert (H: Z.lxor x (Z.lxor x y) = Z.lxor x x) by (rewrite E; reflexivity).
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in H. exact H.
Qed.

(* the trailer changed: the facts bc_src_ok of the object after the loop *)
Lemma bc_x_src_ok wbits O C : 4 <= trl_of wbits <= 8 -> trl_of wbits <= Zlength O -> Zlength C = 8 ->
  is_bytes O -> is_bytes C -> bc_or (trl_of wbits) C <> 0 ->
  bc_src_ok wbits O (bc_x (Zlength O - trl_of wbits) (trl_of wbits) O C).
Proof.
  intros Ht HtO HCl HO HC Hnz. unfold bc_src_ok. revert Ht HtO Hnz. generalize (trl_of wbits) as t.
  intros t Ht HtO Hnz. remember (Zlength O - t) as k eqn:Hk.
  split; [apply bc_x_length | ]. split; [ | split].
  - unfold bytes_ok. apply Forall_Znth. intros j Hj. rewrite bc_x_length in Hj. rewrite bc_x_Znth by lia.
    assert (0 <= Znth j O <= Byte.max_unsigned) by (apply bc_byte_at; auto; lia).
    destruct (andb (k <=? j) (j <? k + t)) eqn:E; auto.
    apply andb_prop in E; destruct E as [E1 E2]. apply Z.leb_le in E1; apply Z.ltb_lt in E2.
    apply bc_lxor_byte; auto. apply bc_byte_at; auto; lia.
  - apply Znth_eq_ext.
    { rewrite !Zlength_sublist; rewrite ?bc_x_length; lia. }
    intros j Hj. rewrite Zlength_sublist in Hj by (rewrite ?bc_x_length; lia).
    rewrite !Znth_sublist by (rewrite ?bc_x_length; lia). rewrite bc_x_Znth by lia.
    destruct (k <=? j + 0) eqn:E1; simpl; auto. lia.
  - intros E. apply bc_or_nz in Hnz; [ | lia]. destruct Hnz as (j & Hj & Hcj). apply Hcj.
    apply (f_equal (Znth j)) in E. rewrite !Znth_sublist in E by (rewrite ?bc_x_length; lia).
    rewrite bc_x_Znth in E by lia. replace (j + k - k) with j in E by lia.
    destruct (k <=? j + k) eqn:E1, (j + k <? k + t) eqn:E2; simpl in E; try lia.
    eapply bc_lxor_same; exact E.
Qed.

(* the byte k + i of the object before iteration i: still O's *)
Lemma bc_x_at k i O C b : 0 <= k -> 0 <= i -> k + i < Zlength O ->
  Znth (k + i) (bytes_rep (bc_x k i O C) ++ Zrepeat Vundef (b - Zlength O)) = Vint (Int.repr (Znth (k + i) O)).
Proof.
  intros Hk Hi Hki. unfold bytes_rep.
  rewrite app_Znth1 by (rewrite Zlength_map, bc_x_length; lia).
  rewrite Znth_map by (rewrite bc_x_length; lia). rewrite bc_x_Znth by lia.
  destruct (k <=? k + i) eqn:E1, (k + i <? k + i) eqn:E2; simpl; auto; lia.
Qed.

Lemma bc_C_at C i : 0 <= i < Zlength C -> Znth i (bytes_rep C) = Vint (Int.repr (Znth i C)).
Proof. intros Hi. unfold bytes_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma bc_xor_repr a c : Int.xor (Int.repr a) (Int.repr c) = Int.repr (Z.lxor a c).
Proof.
  apply Int.same_bits_eq. intros j Hj.
  rewrite Int.bits_xor by auto. rewrite !Int.testbit_repr by auto. rewrite Z.lxor_spec. reflexivity.
Qed.

(* the store of iteration i: compressed[k + i] = (unsigned char) (compressed[k + i] ^ change[i]) *)
Lemma bc_x_store k i O C (R : list val) : 0 <= k -> 0 <= i -> k + i < Zlength O -> i < Zlength C ->
  is_bytes O -> is_bytes C ->
  upd_Znth (k + i) (bytes_rep (bc_x k i O C) ++ R)
    (Vint (Int.zero_ext 8 (Int.xor (Int.repr (Znth (k + i) O)) (Int.repr (Znth i C))))) =
  bytes_rep (bc_x k (i + 1) O C) ++ R.
Proof.
  intros Hk Hi Hki HiC HO HC.
  rewrite upd_Znth_app1 by (unfold bytes_rep; rewrite Zlength_map, bc_x_length; lia).
  rewrite bc_x_S by lia. unfold bytes_rep. rewrite <- upd_Znth_map. f_equal. f_equal.
  rewrite bc_xor_repr.
  assert (B := bc_lxor_byte _ _ (bc_byte_at O (k + i) HO ltac:(lia)) (bc_byte_at C i HC ltac:(lia))).
  change Byte.max_unsigned with 255 in B.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)). rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr by rep_lia. change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma seg_trailer_ok : seg_trailer_stmt.
Proof.
  intros Espec P gv vc vd wbits n b D O dp op cp C chp HP K.
  unfold bc_seg21, bc_DH, POST_B, POST_bc. abbreviate_semax.
  Intros.
  match goal with Hc : bc_chg_ok _ _ _ |- _ => destruct Hc as (Hw8 & HCl & HCb & Pchp) end.
  assert (Ht : trl_of wbits <= Zlength O) by (eapply bd_len; eauto).
  assert (Ht48 : 4 <= trl_of wbits <= 8) by (unfold trl_of; destruct (wbits >? 15); lia).
  assert (HOb : is_bytes O).
  { match goal with H : rbytes O |- _ => eapply Forall_impl; [ | exact H] end. simpl. intros; rep_lia. }
  unfold bc_chg. Intros.
  (* everything but the compressed object and change *)
  freeze [0;1;2;3;4;5;7;8;10;11;12] FR.
  forward.
  forward_if (PROP ()
    LOCAL (temp _trailer_len (Vlong (Int64.repr (trl_of wbits)));
           temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
           temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
           temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _change chp;
           lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
    SEP (FRZL FR; data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
         data_at Ews (tarray tuchar 8) (bytes_rep C) chp)).
  { forward. entailer!. unfold trl_of. destruct (wbits >? 15) eqn:E; [reflexivity | lia]. }
  { forward. entailer!. unfold trl_of. destruct (wbits >? 15) eqn:E; [lia | reflexivity]. }
  forward.
  forward_for_simple_bound (trl_of wbits) (EX i : Z,
    PROP ()
    LOCAL (temp _changed (Vint (Int.repr (bc_or i C)));
           temp _trailer_len (Vlong (Int64.repr (trl_of wbits)));
           temp _data_len (Vlong (Int64.repr n)); temp _data dp; temp _out op;
           temp _window_bits (Vint (Int.repr wbits)); temp _compressed cp;
           temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _change chp;
           lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
    SEP (FRZL FR;
         data_at Ews (tarray tuchar b)
           (bytes_rep (bc_x (Zlength O - trl_of wbits) i O C) ++ Zrepeat Vundef (b - Zlength O)) cp;
         data_at Ews (tarray tuchar 8) (bytes_rep C) chp)).
  { entailer!. rewrite bc_x_0. auto. }
  { assert (Bo := bc_byte_at O (Zlength O - trl_of wbits + i) HOb ltac:(lia)).
    assert (Bc := bc_byte_at C i HCb ltac:(lia)).
    forward.
    { erewrite bc_x_at by lia. entailer!; lia. }
    erewrite bc_x_at by lia.
    forward.
    { erewrite bc_C_at by lia. entailer!; lia. }
    erewrite bc_C_at by lia.
    forward.
    rewrite bc_x_store by (auto; lia).
    forward.
    { erewrite bc_C_at by lia. entailer!; lia. }
    erewrite bc_C_at by lia.
    forward.
    entailer!.
    rewrite bc_or_S by lia. reflexivity.
  }
  assert (Bor := bc_or_byte (trl_of wbits) C ltac:(lia) HCb).
  forward_call (Int.repr (if Z.eq_dec (bc_or (trl_of wbits) C) 0 then 0 else 1)).
  { entailer!. destruct (Z.eq_dec (bc_or (trl_of wbits) C) 0) as [E|E]; [rewrite E; reflexivity | ].
    simpl. rewrite Int.eq_false; [reflexivity | ]. intros X. apply repr_inj_unsigned in X; rep_lia. }
  match goal with Ha : Int.repr (if Z.eq_dec _ _ then _ else _) <> Int.zero |- _ =>
    assert (Hnz : bc_or (trl_of wbits) C <> 0)
      by (destruct (Z.eq_dec (bc_or (trl_of wbits) C) 0); [contradiction | auto]) end.
  assert (Hf : bc_facts wbits n b D O (bc_x (Zlength O - trl_of wbits) (trl_of wbits) O C) dp op cp).
  { unfold bc_facts. do 13 (split; [assumption | ]). apply bc_x_src_ok; auto. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  thaw FR.
  eapply semax_pre; [ | apply (K _ Hf)].
  unfold bc_TH. entailer!.
Qed.

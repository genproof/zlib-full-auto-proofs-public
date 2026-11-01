(* The fixed tables of inffixed.h (Fixed.v) are valid decoding tables (Tables.v): lenfix with root 9 bits
   (LENS), distfix with root 5 bits (DISTS).  By computation over Fixed.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.StepInv.
Local Open Scope Z_scope.

(* boolean checks of a final root entry *)
Definition entry_okb (e: entry) : bool :=
  (0 <=? e_op e) && (e_op e <=? 255) && (0 <=? e_bits e) && (e_bits e <=? 255) &&
  (0 <=? e_val e) && (e_val e <=? 65535).

Definition final_okb (kind: Z) (e: entry) : bool :=
  if kind =? CODES then ((e_op e =? 0) && (0 <=? e_val e) && (e_val e <=? 18)) || (e_op e =? 64)
  else if kind =? LENS then
    ((e_op e =? 0) && (0 <=? e_val e) && (e_val e <=? 255)) ||
    ((16 <=? e_op e) && (e_op e <=? 21) && (3 <=? e_val e) && (e_val e <=? 258)) || (e_op e =? 96) ||
    (negb (Z.land (e_op e) 64 =? 0) && (Z.land (e_op e) 48 =? 0))
  else
    ((16 <=? e_op e) && (e_op e <=? 29) && (1 <=? e_val e) && (e_val e <=? 32768)) ||
    (negb (Z.land (e_op e) 64 =? 0) && (Z.land (e_op e) 48 =? 0)).

Definition root_okb (kind rb: Z) (e: entry) : bool :=
  entry_okb e && negb (islink kind (e_op e)) && (e_bits e <=? rb) && final_okb kind e.

Lemma entry_okb_sound: forall e, entry_okb e = true -> entry_ok e.
Proof.
  intros e H. unfold entry_okb, entry_ok in *. repeat rewrite andb_true_iff in H.
  repeat rewrite Z.leb_le in H. lia.
Qed.

Lemma final_okb_sound: forall kind e, final_okb kind e = true -> final_ok kind e.
Proof.
  intros kind e H. unfold final_okb, final_ok in *.
  destruct (kind =? CODES); [|destruct (kind =? LENS)];
  repeat rewrite orb_true_iff in H; repeat rewrite andb_true_iff in H;
  repeat rewrite negb_true_iff in H; repeat rewrite Z.leb_le in H; repeat rewrite Z.eqb_eq in H;
  try rewrite Z.eqb_neq in H; intuition (try rewrite Z.eqb_neq in *; lia).
Qed.

(* a table without links whose entries are all final and fit in the root *)
Lemma tab_nolinks_valid: forall kind rb (l: list entry),
  1 <= rb <= 15 -> Zlength l = 2 ^ rb -> forallb (root_okb kind rb) l = true ->
  tvalid_g kind (fun i => Znth i l) rb (Zlength l).
Proof.
  intros kind rb l Hrb Hl Hf. constructor; [exact Hrb | lia |].
  intros i Hi. cbv zeta.
  assert (Hc: root_okb kind rb (Znth i l) = true).
  { rewrite forallb_forall in Hf. apply Hf. apply Znth_In. lia. }
  unfold root_okb in Hc. repeat rewrite andb_true_iff in Hc.
  destruct Hc as [[[H1 H2] H3] H4]. rewrite negb_true_iff in H2. rewrite H2.
  split; [apply entry_okb_sound; auto|]. split; [apply Z.leb_le; auto | apply final_okb_sound; auto].
Qed.

Lemma lenfix_ok: forallb (root_okb LENS 9) lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma distfix_ok: forallb (root_okb DISTS 5) distfix_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lenfix_len: Zlength lenfix_list = 512.
Proof. vm_compute. reflexivity. Qed.

Lemma distfix_len: Zlength distfix_list = 32.
Proof. vm_compute. reflexivity. Qed.

Definition len_okb (e: entry) : bool :=
  negb ((16 <=? e_op e) && (e_op e <=? 21)) || (e_val e + 2 ^ (e_op e - 16) <=? 259).

Lemma len_okb_sound: forall e, len_okb e = true -> len_ok e.
Proof.
  intros e H R. unfold len_okb in H. apply orb_true_iff in H. destruct H as [H | H].
  - apply negb_true_iff in H. apply andb_false_iff in H. destruct H as [H | H]; apply Z.leb_gt in H; lia.
  - apply Z.leb_le in H. auto.
Qed.

Lemma lenfix_lenok: forallb len_okb lenfix_list = true.
Proof. vm_compute. reflexivity. Qed.

(* the fixed tables are valid, with len_ok of lenfix *)
Lemma tvalid_fixed2 (s: istate) :
  tvalid LENS lenfix_list distfix_list s TLenfix 9 /\ tvalid DISTS lenfix_list distfix_list s TDistfix 5.
Proof.
  split.
  - exists 512. split; [simpl; lia|]. unfold tvalid_b. simpl tab_entry.
    rewrite <- lenfix_len. apply tab_nolinks_valid; [lia | rewrite lenfix_len; reflexivity | exact lenfix_ok].
  - exists 32. split; [simpl; lia|]. unfold tvalid_b. simpl tab_entry.
    rewrite <- distfix_len. apply tab_nolinks_valid; [lia | rewrite distfix_len; reflexivity | exact distfix_ok].
Qed.

Lemma lvalid_fixed (s: istate) : lvalid lenfix_list distfix_list s TLenfix 9.
Proof.
  exists 512. split; [simpl; lia|]. split.
  - unfold tvalid_b. simpl tab_entry.
    rewrite <- lenfix_len. apply tab_nolinks_valid; [lia | rewrite lenfix_len; reflexivity | exact lenfix_ok].
  - intros i Hi. simpl tab_entry. apply len_okb_sound.
    pose proof lenfix_lenok as F. rewrite forallb_forall in F. apply F. apply Znth_In. rewrite lenfix_len. lia.
Qed.

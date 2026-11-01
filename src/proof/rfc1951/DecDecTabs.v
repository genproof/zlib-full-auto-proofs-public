(* Part of DecDec.group_dec: len_code / dist_code and the meaning of the entries.  Statement:
   DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

Definition tabs_lchk (len: Z) : bool :=
  let i := len_code len in
  (0 <=? i) && (i <=? 28) && (0 <=? Znth i len_extra) && (Znth i len_extra <=? 5) &&
  (Znth i len_base <=? len) && (len <? Znth i len_base + 2 ^ Znth i len_extra).

Definition tabs_dchk (dist: Z) : bool :=
  let d := dist_code dist in
  (0 <=? d) && (d <=? 29) && (0 <=? Znth d dist_extra) && (Znth d dist_extra <=? 13) &&
  (Znth d dist_base <=? dist) && (dist <? Znth d dist_base + 2 ^ Znth d dist_extra).

Lemma tabs_lall : forallb tabs_lchk (map (fun n => 3 + Z.of_nat n) (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tabs_dall : forallb tabs_dchk (map (fun n => 1 + Z.of_nat n) (seq 0 32768)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tabs_range (f: Z -> bool) (lo: Z) (n: nat) :
  forallb f (map (fun k => lo + Z.of_nat k) (seq 0 n)) = true ->
  forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  intros A x Hx. rewrite forallb_forall in A. apply A. apply in_map_iff.
  exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma tabs_ok : tabs_stmt.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - intros len Hl. pose proof (tabs_range _ 3 256 tabs_lall len ltac:(lia)) as C.
    unfold tabs_lchk in C. cbv zeta. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in C. lia.
  - intros dist Hd. pose proof (tabs_range _ 1 32768 tabs_dall dist ltac:(change (Z.of_nat 32768) with 32768; lia)) as C.
    unfold tabs_dchk in C. cbv zeta. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in C. lia.
  - intros sy op val Hs M. unfold ref.means_symbol, ref.sym_kind, ref.sym_value in M.
    replace (sy <? 256) with true in M by (symmetry; apply Z.ltb_lt; lia). cbn in M.
    rewrite andb_true_iff, !Z.eqb_eq in M. exact M.
  - intros op val M. unfold ref.means_symbol in M. replace (ref.sym_kind LENS 256) with ref.K_EOB in M by reflexivity.
    cbn [Z.eqb ref.K_EOB ref.K_LIT ref.K_LENDIST Pos.eqb] in M. apply Z.eqb_eq in M. exact M.
  - intros i op val Hi M. unfold ref.means_symbol, ref.sym_kind, ref.sym_value, ref.sym_extra in M.
    replace (257 + i <? 256) with false in M by (symmetry; apply Z.ltb_ge; lia).
    replace (257 + i =? 256) with false in M by (symmetry; apply Z.eqb_neq; lia).
    replace (257 + i <=? 285) with true in M by (symmetry; apply Z.leb_le; lia).
    replace (257 + i - 257) with i in M by lia. cbn in M.
    rewrite andb_true_iff, !Z.eqb_eq in M. exact M.
  - intros d op val Hd M. unfold ref.means_symbol, ref.sym_kind, ref.sym_value, ref.sym_extra in M.
    replace (d <=? 29) with true in M by (symmetry; apply Z.leb_le; lia). cbn in M.
    rewrite andb_true_iff, !Z.eqb_eq in M. exact M.
Qed.

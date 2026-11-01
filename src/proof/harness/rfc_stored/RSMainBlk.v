(* Law rfc_stored, main: statements 19-21, the stored blocks (the lengths chosen by upto, each block's first
   byte keeping s0's padding bits, LEN, NLEN, the data bytes copied) are RSModel.rs_blocks with the padding
   bytes rs_pads (rs_B -> rs_C). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Import Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.proof.harness.rfc_stored.RSMainKit.
Require Import Zlib.harness.rfc_stored.code.
Local Open Scope logic.

(* the first blocks the loop has written: block k (of nb) holds the data bytes from offset o and its first byte
   keeps s0's byte at its position p; it is flagged last iff k + 1 = nb (rs_blocks flags the last of its own list,
   so it does not describe a prefix of the blocks) *)
Fixpoint rsb (k nb o p: Z) (s0 ls d: list Z) : list Z :=
  match ls with
  | [] => []
  | l :: r => rs_block (Znth p s0) (k + 1 =? nb) (sublist o (o + l) d) ++ rsb (k + 1) nb (o + l) (p + 5 + l) s0 r d
  end.

Notation rsum := (fold_right Z.add 0).

Lemma rsum_nonneg ls: Forall (fun l => 0 <= l <= 65535) ls -> 0 <= rsum ls.
Proof. induction 1; simpl; lia. Qed.

(* the value of `len > 65535` *)
Lemma rs_gt65535 x: 0 <= x <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cgt (Int64.repr x) (Int64.repr 65535)) = Vint (if 65535 <? x then Int.one else Int.zero).
Proof.
  intros. unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (Z.ltb_spec 65535 x), (zlt 65535 x); try lia; reflexivity.
Qed.

(* the value of `last = i + 1 == blocks` *)
Lemma rs_last_eq i nb: 0 <= i -> i + 1 <= Int64.max_unsigned -> 0 <= nb <= Int64.max_unsigned ->
  Int64.cmpu Ceq (Int64.add (Int64.repr i) (Int64.repr 1)) (Int64.repr nb) = (i + 1 =? nb).
Proof.
  intros. simpl. rewrite add64_repr. unfold Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zeq (i + 1) nb), (Z.eqb_spec (i + 1) nb); try lia; reflexivity.
Qed.

Lemma rsum_snoc ls l: rsum (ls ++ [l]) = rsum ls + l.
Proof. induction ls; simpl; lia. Qed.

Lemma rs_hdr_len wr c s0: 0 <= wr <= 2 -> rs_hl wr <= Zlength s0 -> Zlength (rs_hdr wr c s0) = rs_hl wr.
Proof.
  intros Hw Hs. unfold rs_hdr, rs_hl in *.
  destruct (Z.eqb_spec wr 1); [reflexivity | ].
  destruct (Z.eqb_spec wr 2); [ | reflexivity].
  rewrite Zlength_app, Zlength_sublist by lia. reflexivity.
Qed.

Lemma rs_block_len pad last ch: Zlength (rs_block pad last ch) = 5 + Zlength ch.
Proof. unfold rs_block. rewrite Zlength_app. reflexivity. Qed.

Lemma rsb_len ls: forall k nb o p s0 d, Forall (fun l => 0 <= l <= 65535) ls -> 0 <= o -> o + rsum ls <= Zlength d ->
  Zlength (rsb k nb o p s0 ls d) = 5 * Zlength ls + rsum ls.
Proof.
  induction ls as [ | l r IH]; intros k nb o p s0 d F Ho Hd; cbn [rsb fold_right] in *; [reflexivity | ].
  inversion F; subst. pose proof (rsum_nonneg r ltac:(assumption)).
  rewrite Zlength_app, rs_block_len, IH by (auto; lia). rewrite Zlength_sublist by lia.
  rewrite Zlength_cons. lia.
Qed.

Lemma rsb_snoc ls: forall k nb o p s0 d l,
  rsb k nb o p s0 (ls ++ [l]) d =
  rsb k nb o p s0 ls d ++
  rs_block (Znth (p + 5 * Zlength ls + rsum ls) s0) (k + Zlength ls + 1 =? nb) (sublist (o + rsum ls) (o + rsum ls + l) d).
Proof.
  induction ls as [ | x r IH]; intros; cbn [rsb app fold_right].
  - rewrite Zlength_nil, app_nil_r. replace (p + 5 * 0 + 0) with p by lia. rewrite !Z.add_0_r. reflexivity.
  - rewrite IH, <- app_assoc. rewrite Zlength_cons. do 2 f_equal.
    replace (p + 5 + x + 5 * Zlength r + rsum r) with (p + 5 * Z.succ (Zlength r) + (x + rsum r)) by lia.
    replace (k + 1 + Zlength r + 1) with (k + Z.succ (Zlength r) + 1) by lia.
    replace (o + x + rsum r) with (o + (x + rsum r)) by lia. reflexivity.
Qed.

(* the loop's blocks are RSModel's: rs_blocks of the remaining lengths, the data from offset o and the padding
   bytes of s0 at the blocks' positions from p *)
Lemma rsb_blocks lens: forall k nb o p s0 d,
  Zlength lens = nb - k -> Forall (fun l => 0 <= l <= 65535) lens -> 0 <= o -> o + rsum lens <= Zlength d ->
  rsb k nb o p s0 lens d = rs_blocks (map (fun q => Znth q s0) (rs_bpos p lens)) lens (sublist o (Zlength d) d).
Proof.
  induction lens as [ | l r IH]; intros k nb o p s0 d Hl F Ho Hd; cbn [rsb rs_blocks rs_bpos map fold_right hd tl] in *;
    [reflexivity | ].
  inversion F; subst. pose proof (rsum_nonneg r ltac:(assumption)). rewrite Zlength_cons in Hl.
  rewrite (IH (k + 1) nb (o + l) (p + 5 + l) s0 d) by (auto; lia). f_equal.
  - f_equal.
    + destruct r; rewrite ?Zlength_nil, ?Zlength_cons in Hl; [apply Z.eqb_eq; lia | ].
      pose proof (Zlength_nonneg r). apply Z.eqb_neq; lia.
    + rewrite sublist_sublist by lia. f_equal; lia.
  - f_equal. rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the stream while the loop writes it: the bytes written X, then s0's bytes from position |X| on *)
Lemma rs_Znth_sub X p s: Zlength X = p -> 0 <= p < Zlength s ->
  Znth p (bytes_rep (X ++ sublist p (Zlength s) s)) = Vint (Int.repr (Znth p s)).
Proof.
  intros HX Hp. unfold bytes_rep. rewrite Znth_map by (rewrite Zlength_app, Zlength_sublist; lia).
  rewrite Znth_app2 by lia. rewrite Znth_sublist by lia. do 3 f_equal. lia.
Qed.

Lemma rs_upd_sub X p q s v: Zlength X = p -> q = p -> 0 <= p < Zlength s ->
  upd_Znth p (bytes_rep (X ++ sublist q (Zlength s) s)) (Vint (Int.repr v)) =
  bytes_rep ((X ++ [v]) ++ sublist (p + 1) (Zlength s) s).
Proof. intros HX -> Hp. unfold bytes_rep. list_solve. Qed.

(* the bytes of a block header as the harness computes them (the forms VST gives to the stored values):
   the first byte keeps the padding bits of the stream byte x and sets BFINAL; LEN and NLEN little-endian *)
Lemma rs_zext8_mod x: Int.zero_ext 8 (Int.repr x) = Int.repr (x mod 256).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change Int.modulus with (2 ^ 32).
  change (two_p 8) with 256. symmetry. apply Znumtheory.Zmod_div_mod; [ lia | lia | ].
  exists (2 ^ 24). reflexivity.
Qed.

(* a check of an equation over the integers 0 .. m - 1 (run by vm_compute) *)
Definition rs_chk (m: Z) (f g: Z -> Z) : bool :=
  forallb (fun k => f k =? g k) (map Z.of_nat (seq 0 (Z.to_nat m))).

Lemma rs_chk_ok m f g: rs_chk m f g = true -> forall x, 0 <= x < m -> f x = g x.
Proof.
  unfold rs_chk. rewrite forallb_forall. intros C x Hx. apply Z.eqb_eq. apply C.
  apply in_map_iff. exists (Z.to_nat x). split; [lia | ]. apply in_seq. lia.
Qed.

(* the bytes of a block header as the harness computes them (the forms VST gives to the stored values):
   the first byte keeps the padding bits of the stream byte x and sets BFINAL; LEN and NLEN little-endian *)
Lemma rs_byte0 x (b: bool): 0 <= x < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.or (Int.and (Int.repr x) (Int.repr 248)) (Int.repr (Z.b2z b)))) =
  Int.repr (Z.lor (Z.land x 248) (if b then 1 else 0)).
Proof.
  intros Hx. rewrite and_repr, or_repr, !rs_zext8_mod, Zmod_mod. f_equal. destruct b.
  - apply (rs_chk_ok 256 (fun x => Z.lor (Z.land x 248) (Z.b2z true) mod 256) (fun x => Z.lor (Z.land x 248) 1));
      [vm_compute; reflexivity | lia].
  - apply (rs_chk_ok 256 (fun x => Z.lor (Z.land x 248) (Z.b2z false) mod 256) (fun x => Z.lor (Z.land x 248) 0));
      [vm_compute; reflexivity | lia].
Qed.

Lemma rs_mm64 x: 0 <= x < 2 ^ 64 -> Int64.Z_mod_modulus x = x.
Proof. intros. rewrite Int64.Z_mod_modulus_eq. apply Z.mod_small. exact H. Qed.

Lemma rs_land255 x: Z.land x 255 = x mod 256.
Proof. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

(* ~len as an unsigned long: 2^64 - 1 - len *)
Lemma rs_not64 len: 0 <= len <= 65535 ->
  Int64.Z_mod_modulus (Z.lxor (Int64.Z_mod_modulus len) 18446744073709551615) = 18446744073709551615 - len.
Proof.
  intros Hl.
  change (Int64.Z_mod_modulus (Z.lxor (Int64.Z_mod_modulus len) 18446744073709551615))
    with (Int64.unsigned (Int64.not (Int64.repr len))).
  assert (E: Int64.not (Int64.repr len) = Int64.repr (- len - 1)).
  { pose proof (Int64.neg_not (Int64.repr len)) as N.
    assert (N2: Int64.not (Int64.repr len) = Int64.sub (Int64.neg (Int64.repr len)) Int64.one).
    { rewrite N, Int64.sub_add_opp, Int64.add_assoc, Int64.add_neg_zero, Int64.add_zero. reflexivity. }
    rewrite N2, Int64.neg_repr. unfold Int64.one. rewrite sub64_repr. f_equal. }
  rewrite E, Int64.unsigned_repr_eq. change Int64.modulus with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (- len - 1) 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
Qed.

Lemma rs_byte1 len: 0 <= len <= 65535 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus len) 255)))) =
  Int.repr (len mod 256).
Proof.
  intros Hl. rewrite !rs_zext8_mod, Zmod_mod. f_equal.
  rewrite (rs_mm64 len), rs_land255 by lia.
  pose proof (Z.mod_pos_bound len 256 ltac:(lia)). rewrite rs_mm64 by lia. apply Zmod_mod.
Qed.

Lemma rs_byte2 len: 0 <= len <= 65535 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus len) 8)))) =
  Int.repr (len / 256).
Proof.
  intros Hl. rewrite !rs_zext8_mod, Zmod_mod. f_equal.
  rewrite (rs_mm64 len) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  assert (0 <= len / 256 < 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite rs_mm64 by lia. apply Z.mod_small. lia.
Qed.

Lemma rs_byte3 len: 0 <= len <= 65535 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus
    (Z.land (Int64.Z_mod_modulus (Z.lxor (Int64.Z_mod_modulus len) 18446744073709551615)) 255)))) =
  Int.repr ((65535 - len) mod 256).
Proof.
  intros Hl. rewrite !rs_zext8_mod, Zmod_mod. f_equal.
  rewrite rs_not64, rs_land255 by lia.
  replace (18446744073709551615 - len) with ((65535 - len) + 72057594037927680 * 256) by lia.
  rewrite Z_mod_plus_full.
  pose proof (Z.mod_pos_bound (65535 - len) 256 ltac:(lia)). rewrite rs_mm64 by lia. apply Zmod_mod.
Qed.

Lemma rs_byte4 len: 0 <= len <= 65535 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus
    (Z.land (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus
       (Z.lxor (Int64.Z_mod_modulus len) 18446744073709551615)) 8)) 255)))) =
  Int.repr ((65535 - len) / 256).
Proof.
  intros Hl. rewrite !rs_zext8_mod, Zmod_mod. f_equal.
  rewrite rs_not64 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (18446744073709551615 - len) with ((65535 - len) + 72057594037927680 * 256) by lia.
  rewrite Z.div_add by lia.
  assert (0 <= (65535 - len) / 256 < 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (rs_mm64 ((65535 - len) / 256 + 72057594037927680)) by lia. rewrite rs_land255.
  replace 72057594037927680 with (281474976710655 * 256)%Z by lia.
  rewrite Z_mod_plus_full.
  rewrite (Z.mod_small ((65535 - len) / 256)) by lia. rewrite rs_mm64 by lia. apply Z.mod_small. lia.
Qed.

(* a data byte copied into the stream *)
Lemma rs_zext8 x: 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros Hx. rewrite rs_zext8_mod, Z.mod_small by lia. reflexivity. Qed.

(* the loop's comparisons of unsigned longs as comparisons of their values *)
Ltac rs_cmp_h := repeat match goal with Hx: context [Int64.unsigned (Int64.add (Int64.repr _) (Int64.repr _))] |- _ =>
  rewrite add64_repr, !Int64.unsigned_repr in Hx by rep_lia end.

Lemma seg_blk_ok {Espec: OracleKind} gv vs vwb n nb na wr window stp s0 dp d op ep c:
  rs_A_facts n nb na wr window stp s0 dp d op -> rs_c_ok wr window c ->
  (forall lens, rs_lens_ok nb n lens ->
     semax Delta_m (rs_C gv vs vwb n nb na wr window stp s0 dp d op ep c lens) rs_seg22 POST_B) ->
  semax Delta_m (rs_B gv vs vwb n nb na wr window stp s0 dp d op ep c) rs_seg19 POST_B.
Proof.
  intros HA Hc K.
  pose proof HA as (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & Ps & Pd & Po).
  assert (Hhl: 0 <= rs_hl wr <= 10) by (unfold rs_hl; destruct (wr =? 1), (wr =? 2); lia).
  assert (Htl: 0 <= rs_tl wr <= 8) by (unfold rs_tl; destruct (wr =? 1), (wr =? 2); lia).
  unfold rs_B, rs_seg19, Delta_m, POST_B.
  abbreviate_semax.
  forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: _ :: _ :: ?Q)
       (SEPx (?r1 :: ?r2 :: ?r3 :: ?r4 :: ?r5 :: ?r6 :: ?r7 :: ?r8 :: ?r9 :: _ :: ?R)))) _ _ =>
  forward_loop
    (EX i: Z, EX ls: list Z,
     PROPx [0 <= i <= nb; Zlength ls = i; Forall (fun l => 0 <= l <= 65535) ls; rsum ls <= n; i = nb -> rsum ls = n]
     (LOCALx (temp _i (Vlong (Int64.repr i)) :: temp _done (Vlong (Int64.repr (rsum ls))) ::
            temp _at (Vlong (Int64.repr (rs_hl wr + 5 * i + rsum ls))) :: Q)
     (SEPx (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 ::
          data_at Ews (tarray tuchar (Zlength s0))
            (bytes_rep (rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 ls d ++
                        sublist (rs_hl wr + 5 * i + rsum ls) (Zlength s0) s0)) stp :: R))))
  continue:
    (EX i: Z, EX ls: list Z,
     PROPx [0 <= i < nb; Zlength ls = i + 1; Forall (fun l => 0 <= l <= 65535) ls; rsum ls <= n;
           i + 1 = nb -> rsum ls = n]
     (LOCALx (temp _i (Vlong (Int64.repr i)) :: temp _done (Vlong (Int64.repr (rsum ls))) ::
            temp _at (Vlong (Int64.repr (rs_hl wr + 5 * (i + 1) + rsum ls))) :: Q)
     (SEPx (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 ::
          data_at Ews (tarray tuchar (Zlength s0))
            (bytes_rep (rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 ls d ++
                        sublist (rs_hl wr + 5 * (i + 1) + rsum ls) (Zlength s0) s0)) stp :: R))))
  break:
    (EX ls: list Z,
     PROPx [Zlength ls = nb; Forall (fun l => 0 <= l <= 65535) ls; rsum ls = n]
     (LOCALx (temp _at (Vlong (Int64.repr (rs_hl wr + 5 * nb + n))) :: Q)
     (SEPx (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 ::
          data_at Ews (tarray tuchar (Zlength s0))
            (bytes_rep (rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 ls d ++
                        sublist (rs_hl wr + 5 * nb + n) (Zlength s0) s0)) stp :: R))))
  end.
  { Exists 0 (@nil Z). entailer!; simpl; [lia | cancel]. }
  { Intros i ls. pose proof (rsum_nonneg ls H1) as Hs.
    forward_if.
    2: { assert (E: i = nb) by lia. specialize (H3 E). subst i.
         forward. Exists ls. rewrite H3. entailer!. }
    forward. rewrite sub64_repr.
    match goal with |- semax _ (PROPx _ (LOCALx (_ :: ?Q) (SEPx ?R))) (Ssequence ?c1 _) _ =>
      apply semax_seq' with (P' := EX len: Z, PROPx [0 <= len <= 65535 \/ i + 1 = nb; rsum ls + len <= n;
                                                i + 1 = nb -> len = n - rsum ls]
                                          (LOCALx (temp _len (Vlong (Int64.repr len)) :: Q) (SEPx R))) end.
    { match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp _t'15 (Vint (if andb (i + 1 <? nb) (65535 <? n - rsum ls) then Int.one
                                                     else Int.zero)) :: Q) (SEPx R))) end.
      { rs_cmp_h.
        forward. entailer!. rewrite rs_gt65535 by rep_lia.
        destruct (Z.ltb_spec (Zlength ls + 1) nb); try lia. reflexivity. }
      { rs_cmp_h.
        forward. entailer!. destruct (Z.ltb_spec (Zlength ls + 1) nb); try lia. reflexivity. }
      destruct (andb (i + 1 <? nb) (65535 <? n - rsum ls)) eqn:Eb.
      { apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.ltb_lt in E1, E2.
        forward_if; [ | exfalso; exact (Int.one_not_zero ltac:(assumption))].
        forward_call 65535. Intros v. forward. Exists v. entailer!. }
      forward_if; [exfalso; auto | ].
      forward_if.
      { rs_cmp_h.
        forward_call (n - rsum ls). Intros v. forward. Exists v. entailer!. }
      { rs_cmp_h.
        forward. Exists (n - rsum ls). entailer!. } }
    Intros len.
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. abbreviate_semax.
    assert (Hlen: 0 <= len) by (destruct H5; [lia | rewrite H7 by auto; lia]).
    destruct (Z.le_gt_cases len 65535) as [Hl | Hl].
    2: { forward_call Int.zero.
         { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
           destruct zlt; try lia; reflexivity. }
         Intros. contradiction. }
    forward_call Int.one.
    { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. destruct zlt; try lia; reflexivity. }
    Intros. clear H5.
    forward.
    change (Int.signed (Int.repr 1)) with 1. rewrite rs_last_eq by rep_lia.
    assert (Za: Zlength (rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 ls d) = rs_hl wr + 5 * i + rsum ls).
    { rewrite Zlength_app, rs_hdr_len, rsb_len by (auto; lia). lia. }
    rewrite app_assoc.
    set (a := rs_hl wr + 5 * i + rsum ls) in *.
    set (X := rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 ls d) in *.
    assert (Ha: a + 5 + len <= Zlength s0) by lia.
    assert (Bs0: forall q, 0 <= q < Zlength s0 -> 0 <= Znth q s0 < 256)
      by (intros q Hq; exact (proj1 (Forall_Znth _ _) Bs q Hq)).
    forward.
    { rewrite rs_Znth_sub by lia. specialize (Bs0 a ltac:(lia)). entailer!. rep_lia. }
    rewrite rs_Znth_sub by lia.
    forward. rewrite rs_byte0, rs_upd_sub by (try apply Bs0; lia).
    forward. rewrite rs_byte1, rs_upd_sub by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
    forward. rewrite rs_byte2, rs_upd_sub by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
    forward. rewrite rs_byte3, rs_upd_sub by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
    forward. rewrite rs_byte4, rs_upd_sub by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).
    match goal with |- context [bytes_rep (?y ++ sublist ?q (Zlength s0) s0)] =>
      replace q with (a + 5) by lia; set (Y := y) end.
    assert (ZY: Zlength Y = a + 5) by (subst Y; rewrite !Zlength_app, Za, !Zlength_cons, !Zlength_nil; lia).
    pose proof (eq_refl Y) as EY. unfold Y at 2 in EY. clearbody Y.
    match goal with |- semax _ (PROPx _ (LOCALx ?Q
       (SEPx (?r1 :: ?r2 :: ?r3 :: ?r4 :: ?r5 :: ?r6 :: ?r7 :: ?r8 :: ?r9 :: _ :: ?R)))) _ _ =>
    forward_for_simple_bound len
      (EX j: Z, PROPx [] (LOCALx Q
        (SEPx (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 ::
          data_at Ews (tarray tuchar (Zlength s0))
            (bytes_rep ((Y ++ sublist (rsum ls) (rsum ls + j) d) ++ sublist (a + 5 + j) (Zlength s0) s0)) stp
          :: R)))) end.
    { rewrite Z.add_0_r, sublist_nil, app_nil_r. entailer!. cancel. }
    { assert (Bq: 0 <= Znth (rsum ls + i0) d < 256)
        by (exact (proj1 (Forall_Znth _ _) Bd (rsum ls + i0) ltac:(lia))).
      forward.
      { rewrite Znth_bytes_rep by lia. entailer!. rep_lia. }
      rewrite Znth_bytes_rep by lia.
      forward.
      rewrite rs_zext8, rs_upd_sub by (rewrite ?Zlength_app, ?Zlength_sublist; lia).
      replace ((Y ++ sublist (rsum ls) (rsum ls + i0) d) ++ [Znth (rsum ls + i0) d])
        with (Y ++ sublist (rsum ls) (rsum ls + (i0 + 1)) d) by list_solve.
      replace (a + 5 + i0 + 1) with (a + 5 + (i0 + 1)) by lia.
      entailer!. }
    forward. forward.
    assert (EC: Y ++ sublist (rsum ls) (rsum ls + len) d = rs_hdr wr c s0 ++ rsb 0 nb 0 (rs_hl wr) s0 (ls ++ [len]) d).
    { rewrite rsb_snoc, EY. subst X a. unfold rs_block. rewrite H0, !Z.add_0_l. rewrite Zlength_sublist by lia.
      replace (rsum ls + len - rsum ls) with len by lia. rewrite <- !app_assoc. reflexivity. }
    rewrite EC, <- app_assoc.
    replace (a + 5 + len) with (rs_hl wr + 5 * (i + 1) + rsum (ls ++ [len])) by (rewrite rsum_snoc; lia).
    Exists i (ls ++ [len]).
    rewrite Zlength_app, rsum_snoc. change (Int.signed (Int.repr 5)) with 5. rewrite !add64_repr.
    assert (Fl: Forall (fun l => 0 <= l <= 65535) (ls ++ [len])) by (apply Forall_app; split; auto).
    replace (a + (5 + len)) with (rs_hl wr + 5 * (i + 1) + (rsum ls + len)) by (subst a; lia).
    assert (Hn1: i + 1 = nb -> rsum ls + len = n) by (intros E; rewrite H7 by lia; lia).
    clearbody a X. entailer!. }
  { Intros i ls. forward. Exists (i + 1) ls. entailer!. }
  Intros ls.
  assert (Hok: rs_lens_ok nb n ls).
  { split; [ | split; [ | split]]; auto. intros E. subst ls. rewrite Zlength_nil in H. lia. }
  rewrite (rsb_blocks ls 0 nb 0 (rs_hl wr) s0 d) by (auto; lia).
  rewrite sublist_same by lia. change (map (fun q => Znth q s0) (rs_bpos (rs_hl wr) ls)) with (rs_pads wr s0 ls).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K ls Hok) ].
  unfold rs_C. entailer!.
Qed.

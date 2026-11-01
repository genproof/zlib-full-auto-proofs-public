(* Law inflate_dict, main encoder half: a stored block (statement in ITEncKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITEncKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.


(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts over bits and pack                                                                  *)

Lemma ies_Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma ies_Zlength_zeros n : 0 <= n -> Zlength (zeros n) = n.
Proof. intros. unfold zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma ies_Zlength_bytes_bits l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|x r IH]; [reflexivity|].
  change (bytes_bits (x :: r)) with (bits_le x 8 ++ bytes_bits r).
  rewrite Zlength_app, IH, ies_Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma ies_bits_le_ext a b n : 0 <= n -> (forall i, 0 <= i < n -> Z.testbit a i = Z.testbit b i) ->
  bits_le a n = bits_le b n.
Proof.
  intros Hn H. unfold bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma ies_bits_le_mod v n : 0 <= n -> bits_le (v mod 2 ^ n) n = bits_le v n.
Proof. intros. apply ies_bits_le_ext; auto. intros. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma ies_map_seq_shift {A} (f: nat -> A) s len : map f (seq s len) = map (fun i => f (s + i)%nat) (seq 0 len).
Proof.
  revert s; induction len as [|len IH]; intros s; [reflexivity|].
  simpl. rewrite IH. rewrite Nat.add_0_r. f_equal. rewrite <- seq_shift, map_map.
  apply map_ext. intros i. f_equal. lia.
Qed.

Lemma ies_bits_le_split v a b : 0 <= a -> 0 <= b -> bits_le v (a + b) = bits_le v a ++ bits_le (v / 2 ^ a) b.
Proof.
  intros Ha Hb. unfold bits_le. rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  rewrite ies_map_seq_shift. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma ies_skipn_app_ge {A} n (l1 l2: list A) : (length l1 <= n)%nat -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof. intros. rewrite skipn_app. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma ies_sublist_app_ge {A} (B C: list A) lo hi : Zlength B <= lo <= hi ->
  sublist lo hi (B ++ C) = sublist (lo - Zlength B) (hi - Zlength B) C.
Proof.
  intros H. unfold sublist. rewrite Zlength_correct in *. rewrite List.firstn_app.
  rewrite firstn_all2 by lia. rewrite ies_skipn_app_ge by lia.
  f_equal; [lia | f_equal; lia].
Qed.

Lemma ies_Zlength_pack B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  pose proof (Zlength_nonneg B). rewrite Z2Nat.id; auto. apply Z.div_pos; lia.
Qed.

Lemma ies_pack_app B C : Zlength B mod 8 = 0 -> pack (B ++ C) = pack B ++ pack C.
Proof.
  intros HB. pose proof (Zlength_nonneg B) as HB0. pose proof (Zlength_nonneg C) as HC0.
  assert (EB: Zlength B = 8 * (Zlength B / 8)) by (pose proof (Z.div_mod (Zlength B) 8); lia).
  set (k := Zlength B / 8) in *. assert (Hk: 0 <= k) by (apply Z.div_pos; lia).
  unfold pack. rewrite Zlength_app.
  assert (E1: (Zlength B + Zlength C + 7) / 8 = k + (Zlength C + 7) / 8).
  { rewrite EB. replace (8 * k + Zlength C + 7) with ((Zlength C + 7) + k * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (E2: (Zlength B + 7) / 8 = k).
  { rewrite EB. replace (8 * k + 7) with (7 + k * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite E1, E2. assert (HCk: 0 <= (Zlength C + 7) / 8) by (apply Z.div_pos; lia).
  rewrite Z2Nat.inj_add by lia. rewrite seq_app, map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal.
    rewrite sublist_app1; auto; try lia.
  - rewrite ies_map_seq_shift. apply map_ext_in. intros i Hi. f_equal.
    rewrite ies_sublist_app_ge by lia. f_equal; lia.
Qed.

Lemma ies_bval_byte_all :
  forallb (fun x => bval (bits_le x 8) =? x) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ies_bval_byte x : 0 <= x < 256 -> bval (bits_le x 8) = x.
Proof.
  intros Hx. pose proof ies_bval_byte_all as H. rewrite forallb_forall in H.
  apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma ies_pack_byte x : 0 <= x < 256 -> pack (bits_le x 8) = [x].
Proof.
  intros Hx. unfold pack. rewrite ies_Zlength_bits_le by lia. change (Z.to_nat ((8 + 7) / 8)) with 1%nat.
  cbn [seq map]. change (8 * Z.of_nat 0) with 0. change (0 + 8) with 8.
  rewrite sublist_same by (rewrite ?ies_Zlength_bits_le; lia). rewrite ies_bval_byte; auto.
Qed.

Lemma ies_pack_bytes_bits l : is_bytes l -> pack (bytes_bits l) = l.
Proof.
  induction l as [|x r IH]; intros Hl; [reflexivity|].
  inversion Hl; subst. change (bytes_bits (x :: r)) with (bits_le x 8 ++ bytes_bits r). rewrite ies_pack_app.
  - rewrite ies_pack_byte by rep_lia. rewrite IH; auto.
  - rewrite ies_Zlength_bits_le by lia. reflexivity.
Qed.

Lemma ies_pack_app_bytes B l : Zlength B mod 8 = 0 -> is_bytes l -> pack (B ++ bytes_bits l) = pack B ++ l.
Proof. intros. rewrite ies_pack_app, ies_pack_bytes_bits; auto. Qed.

Lemma ies_zext8 x : Int.zero_ext 8 x = Int.repr (Int.unsigned x mod 256).
Proof. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)). rewrite Int.zero_ext_mod by (cbn; lia). reflexivity. Qed.

Lemma ies_shru8 v : 0 <= v <= Int.max_unsigned -> Int.shru (Int.repr v) (Int.repr 8) = Int.repr (v / 256).
Proof.
  intros. rewrite Int.shru_div_two_p. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma ies_not v : 0 <= v <= Int.max_unsigned -> Int.not (Int.repr v) = Int.repr (Int.max_unsigned - v).
Proof.
  intros. rewrite Int.not_neg. unfold Int.neg. rewrite Int.unsigned_repr by rep_lia.
  unfold Int.mone. rewrite add_repr. apply Int.eqm_samerepr. exists (-1).
  change Int.max_unsigned with (Int.modulus - 1). lia.
Qed.

Lemma ies_pad8_shift h q : pad8 (8 * h + q) = pad8 q.
Proof. unfold pad8. f_equal. f_equal. replace (8 * h + q) with (q + h * 8) by lia. apply Z_mod_plus_full. Qed.

Lemma ies_Zlength_blk_bits E bs :
  Zlength (blk_bits E bs) = 8 * Zlength (hdr_bytes E) + Zlength (enc_nf 0 bs).
Proof. unfold blk_bits. rewrite Zlength_app, ies_Zlength_bytes_bits. reflexivity. Qed.

Lemma ies_bits_stored E bs last l : last = 0 \/ last = 1 -> Zlength l <= 65535 ->
  let n := Zlength l in
  let B1 := (blk_bits E bs ++ bits_le last 1) ++ bits_le 0 2 in
  ((((B1 ++ zeros (pad8 (Zlength B1))) ++ bits_le (n mod 256) 8) ++ bits_le ((n / 256) mod 256) 8) ++
     bits_le ((Int.max_unsigned - n) mod 256) 8) ++ bits_le (((Int.max_unsigned - n) / 256) mod 256) 8 ++
   bytes_bits l =
  blk_bits E bs ++ enc_block (Zlength (enc_nf 0 bs)) (last =? 1) (Stored l).
Proof.
  intros Hlast Hl n B1. pose proof (Zlength_nonneg l) as Hl0.
  assert (HB1: Zlength B1 = 8 * Zlength (hdr_bytes E) + (Zlength (enc_nf 0 bs) + 3)).
  { unfold B1. rewrite !Zlength_app, ies_Zlength_blk_bits, !ies_Zlength_bits_le by lia. lia. }
  rewrite HB1, ies_pad8_shift. unfold B1. rewrite <- !app_assoc. f_equal.
  unfold enc_block. fold n.
  assert (E1: bits_le last 1 = [last =? 1]) by (destruct Hlast; subst; reflexivity).
  rewrite E1. change ([last =? 1] ++ ?r) with ((last =? 1) :: r). f_equal.
  change (bits_le 0 2) with [false; false]. f_equal. f_equal.
  change 256 with (2 ^ 8). rewrite !ies_bits_le_mod by lia.
  assert (E2: bits_le (65535 - n) 16 = bits_le (Int.max_unsigned - n) 16).
  { rewrite <- (ies_bits_le_mod (65535 - n)), <- (ies_bits_le_mod (Int.max_unsigned - n)) by lia. f_equal.
    change Int.max_unsigned with (65535 + 65535 * 2 ^ 16).
    replace (65535 + 65535 * 2 ^ 16 - n) with ((65535 - n) + 65535 * 2 ^ 16) by lia.
    rewrite Z_mod_plus_full. auto. }
  rewrite E2. change 16 with (8 + 8). rewrite !ies_bits_le_split by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma ies_pad8_props p : (p + pad8 p) mod 8 = 0 /\ 0 <= pad8 p < 8.
Proof. unfold pad8. split; Z.div_mod_to_equations; lia. Qed.

Lemma ies_byte_val v : 0 <= v <= Int.max_unsigned -> Int.zero_ext 8 (Int.repr v) = Int.repr (v mod 256).
Proof. intros. rewrite ies_zext8, Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma ies_zext_mod x : Int.zero_ext 8 (Int.repr (x mod 256)) = Int.repr (x mod 256).
Proof.
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)).
  rewrite ies_zext8, Int.unsigned_repr by rep_lia. rewrite Zmod_mod. reflexivity.
Qed.

Ltac ies_bnd := first [rep_lia | (Z.div_mod_to_equations; rep_lia)].
Ltac ies_args :=
  repeat first [rewrite ies_zext_mod | rewrite ies_not by ies_bnd | rewrite ies_shru8 by ies_bnd |
                rewrite ies_byte_val by ies_bnd];
  try reflexivity.

Ltac ies_room Ht := unfold bw_room; rewrite ?Zlength_app, ?ies_Zlength_bits_le, ?Ht by lia;
  repeat split; try rep_lia; Z.div_mod_to_equations; lia.

Local Arguments Z.div : simpl never.
Local Arguments Z.modulo : simpl never.

(* ---------------------------------------------------------------------------------------------- *)
(* Byte objects: slices                                                                          *)

Lemma ies_offset0 n j p:
  field_compatible (tarray tuchar n) [] p -> 0 <= j <= n ->
  field_address0 (Tarray tuchar n noattr) [ArraySubsc j] p = offset_val j p.
Proof.
  intros. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - eapply field_compatible0_cons_Tarray; [reflexivity | auto | lia].
Qed.

Lemma ies_split3 sh n a b (v: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar a) (sublist 0 a v) p *
   data_at sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   data_at sh (tarray tuchar (n - b)) (sublist b n v) (offset_val b p))%logic.
Proof.
  intros FC A B L.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a b v p) by (first [exact L | lia]).
  rewrite !ies_offset0 by (auto; lia). reflexivity.
Qed.

Lemma ies_join3 sh n a b (x y z: list val) p:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n ->
  Zlength x = a -> Zlength y = b - a -> Zlength z = n - b ->
  (data_at sh (tarray tuchar a) x p * data_at sh (tarray tuchar (b - a)) y (offset_val a p) *
   data_at sh (tarray tuchar (n - b)) z (offset_val b p))%logic =
  data_at sh (tarray tuchar n) (x ++ y ++ z) p.
Proof.
  intros FC A B Lx Ly Lz. rewrite (ies_split3 sh n a b (x ++ y ++ z) p) by (auto; list_solve).
  f_equal; [f_equal|]; f_equal; list_solve.
Qed.

Lemma ies_dest sh n (v: list val) p :
  @data_at CS sh (tarray tuchar n) v p |-- @data_at_ Zlib.units.Adler32.CS sh (tarray tuchar n) p.
Proof.
  eapply derives_trans; [apply data_at_data_at_|]. unfold data_at_.
  change (@field_at_ CS sh (tarray tuchar n) [] p) with
    (@data_at CS sh (tarray tuchar n) (@default_val CS (tarray tuchar n)) p).
  change (@field_at_ Zlib.units.Adler32.CS sh (tarray tuchar n) [] p) with
    (@data_at Zlib.units.Adler32.CS sh (tarray tuchar n) (@default_val Zlib.units.Adler32.CS (tarray tuchar n)) p).
  rewrite bytes_adler_cs. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* After the copy: the bit writer's bytes and the data                                            *)

Lemma ies_bw_ok B cap c k l :
  bw_bytes_ok B cap c -> Zlength B = 8 * k -> is_bytes l -> 0 <= k -> k + Zlength l <= cap ->
  bw_bytes_ok (B ++ bytes_bits l) cap (sublist 0 k c ++ bytes_rep l ++ sublist (k + Zlength l) cap c).
Proof.
  intros (Hc & Hp & Hs) HB Hl Hk Hcap. pose proof (Zlength_nonneg l).
  assert (HpB: Zlength (pack B) = k) by (rewrite ies_Zlength_pack, HB; Z.div_mod_to_equations; lia).
  assert (Hm: Zlength B mod 8 = 0) by (rewrite HB, Z.mul_comm, Z_mod_mult; auto).
  pose proof (Zlength_bytes_rep l). unfold bw_bytes_ok. rewrite ies_pack_app_bytes by auto.
  rewrite (Zlength_app _ (pack B) l), HpB.
  rewrite HpB in Hs. split; [|split]; [list_solve | lia |].
  rewrite bytes_rep_app, <- Hs. list_solve.
Qed.

Lemma ies_data_ok dcont D l :
  data_ok dcont D -> is_bytes l -> Zlength D + Zlength l <= 2 ^ 18 ->
  data_ok (sublist 0 (Zlength D) dcont ++ bytes_rep l ++ sublist (Zlength D + Zlength l) (2 ^ 18) dcont) (D ++ l).
Proof.
  intros (Hc & HD & Hb & Hs) Hl Hn. pose proof (Zlength_nonneg l). pose proof (Zlength_nonneg D).
  pose proof (Zlength_bytes_rep l). pose proof (Zlength_bytes_rep D).
  unfold data_ok. split; [list_solve|]. split; [rewrite Zlength_app; lia|]. split.
  - unfold is_bytes in *. apply Forall_app; auto.
  - rewrite bytes_rep_app, <- Hs, (Zlength_app _ D l). list_solve.
Qed.

Lemma seg_stored_ok {Espec: OracleKind} : seg_stored_stmt.
Proof.
  intros E bs dcont last Post. unfold blk_mid, seg_stored. Intros.
  forward_call tt. Intros len.
  forward_call (Int.repr (if len <=? 65535 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E0.
  destruct H1 as (Hdc & HDl & HDb & HDs).
  set (N := Zlength (edata E bs)) in *.
  assert (HN0: 0 <= N) by apply Zlength_nonneg.
  forward_call (Int.repr (if N + len <=? 2 ^ 18 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 18)) with (Int.repr (2 ^ 18)). arg_cmp. }
  assumed. apply Z.leb_le in E1.
  pose proof (Zlength_nonneg (blk_bits E bs)) as HB0.
  forward_call (Tsh, Ews, blk_bits E bs ++ bits_le last 1, 2 ^ 19, e_srcp E, e_vw E, 0, 2).
  { unfold bw_room. rewrite Zlength_app, ies_Zlength_bits_le by lia. repeat split; auto; try rep_lia.
    Z.div_mod_to_equations; lia. }
  set (B1 := (blk_bits E bs ++ bits_le last 1) ++ bits_le 0 2).
  assert (HB1: Zlength B1 = Zlength (blk_bits E bs) + 3).
  { unfold B1. rewrite !Zlength_app, !ies_Zlength_bits_le by lia. lia. }
  forward_call (Tsh, Ews, B1, 2 ^ 19, e_srcp E, e_vw E).
  { unfold bw_room. repeat split; auto; try rep_lia. rewrite HB1. Z.div_mod_to_equations; lia. }
  set (p1 := pad8 (Zlength B1)). pose proof (ies_pad8_props (Zlength B1)) as Hp1. fold p1 in Hp1.
  set (B2 := B1 ++ zeros p1).
  assert (HB2: Zlength B2 = Zlength B1 + p1) by (unfold B2; rewrite Zlength_app, ies_Zlength_zeros by lia; lia).
  set (t := Zlength B2 / 8).
  assert (Ht: Zlength B2 = 8 * t) by (unfold t; rewrite HB2 in *; Z.div_mod_to_equations; lia).
  assert (Ht0: 8 * t <= 8 * (Zlength (blk_bits E bs) / 8) + 16) by (rewrite <- Ht, HB2, HB1; Z.div_mod_to_equations; lia).
  assert (Hmod2: Zlength B2 mod 8 = 0) by (rewrite Ht; rewrite Z.mul_comm, Z_mod_mult; auto).
  clearbody t.
  assert (Hdiv2: Zlength B2 / 8 = t) by (rewrite Ht, Z.mul_comm, Z_div_mult; lia).
  rewrite bw_at_law. Intros c2. rewrite Hdiv2, Hmod2. clear Hdiv2.
  forward.
  forward_call (Int.repr (if t + 4 + len <=? 2 ^ 19 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr (2 ^ 19)). arg_cmp. }
  assumed. apply Z.leb_le in E2.
  gather_SEP (data_at Tsh (Tstruct _bw noattr) _ (e_vw E)) (data_at Ews (tarray tuchar (2 ^ 19)) c2 (e_srcp E)).
  replace_SEP 0 (bw_at Tsh Ews B2 (2 ^ 19) (e_srcp E) (e_vw E)).
  { entailer!. rewrite bw_at_law. Exists c2. rewrite Hmod2.
    assert (Zlength B2 / 8 = t) as -> by (rewrite Ht, Z.mul_comm, Z_div_mult; lia). entailer!. }
  forward_call (Tsh, Ews, B2, 2 ^ 19, e_srcp E, e_vw E, len mod 256).
  { entailer!. simpl. ies_args. }
  { ies_room Ht. }
  forward_call (Tsh, Ews, B2 ++ bits_le (len mod 256) 8, 2 ^ 19, e_srcp E, e_vw E, (len / 256) mod 256).
  { entailer!. simpl. ies_args. }
  { ies_room Ht. }
  forward_call (Tsh, Ews, (B2 ++ bits_le (len mod 256) 8) ++ bits_le ((len / 256) mod 256) 8, 2 ^ 19,
                e_srcp E, e_vw E, (Int.max_unsigned - len) mod 256).
  { entailer!. simpl. ies_args. }
  { ies_room Ht. }
  forward_call (Tsh, Ews, ((B2 ++ bits_le (len mod 256) 8) ++ bits_le ((len / 256) mod 256) 8) ++
                          bits_le ((Int.max_unsigned - len) mod 256) 8, 2 ^ 19,
                e_srcp E, e_vw E, ((Int.max_unsigned - len) / 256) mod 256).
  { entailer!. simpl. ies_args. }
  { ies_room Ht. }
  set (B6 := (((B2 ++ bits_le (len mod 256) 8) ++ bits_le ((len / 256) mod 256) 8) ++
              bits_le ((Int.max_unsigned - len) mod 256) 8) ++ bits_le (((Int.max_unsigned - len) / 256) mod 256) 8).
  assert (HB6: Zlength B6 = 8 * (t + 4)) by (unfold B6; rewrite !Zlength_app, !ies_Zlength_bits_le, Ht by lia; lia).
  assert (EB6: forall l', Zlength l' = len ->
            B6 ++ bytes_bits l' = blk_bits E bs ++ enc_block (Zlength (enc_nf 0 bs)) (last =? 1) (Stored l')).
  { intros l' Hl'. pose proof (ies_bits_stored E bs last l' H2 ltac:(lia)) as X. cbv zeta in X.
    rewrite <- X. subst len. unfold B6, B2, p1, B1. rewrite <- !app_assoc. reflexivity. }
  clearbody B6.
  assert_PROP (field_compatible (tarray tuchar (2 ^ 18)) [] (e_datap E)) as FCd by entailer!.
  rewrite (ies_split3 Ews (2 ^ 18) N (N + len) dcont (e_datap E)) by (auto; lia).
  Intros.
  assert (Hdp: isptr (e_datap E)) by (destruct H as (? & ? & ? & ? & ? & ? & ? & ? & ? & ?); auto).
  forward_call (offset_val N (e_datap E), len, Ews).
  { rewrite if_false by (destruct (e_datap E); try contradiction; discriminate). replace (N + len - N) with len by lia.
    sep_apply (data_at_data_at_ Ews (tarray tuchar len) (sublist N (N + len) dcont) (offset_val N (e_datap E))).
    cancel. }
  Intros l. rewrite if_false by (destruct (e_datap E); try contradiction; discriminate).
  fold (bytes_rep l). subst len.
  set (dcont' := sublist 0 N dcont ++ bytes_rep l ++ sublist (N + Zlength l) (2 ^ 18) dcont).
  gather_SEP (data_at Ews (tarray tuchar N) _ (e_datap E)) (data_at Ews (tarray tuchar (Zlength l)) _ _)
             (data_at Ews (tarray tuchar (2 ^ 18 - (N + Zlength l))) _ _).
  replace_SEP 0 (data_at Ews (tarray tuchar (2 ^ 18)) dcont' (e_datap E)).
  { entailer!. pose proof (Zlength_bytes_rep l). unfold dcont'.
    rewrite <- (ies_join3 Ews (2 ^ 18) (Zlength (edata E bs)) (Zlength (edata E bs) + Zlength l))
      by (auto; try list_solve).
    replace (Zlength (edata E bs) + Zlength l - Zlength (edata E bs)) with (Zlength l) by lia. cancel. }
  assert (Hdc': cbuf_ok false (offset_val N (e_datap E)) Ews (e_datap E) N (2 ^ 18) (Zlength l) dcont' l).
  { pose proof (Zlength_bytes_rep l). unfold cbuf_ok, dcont'. repeat split; auto; try lia. list_solve. }
  rewrite bw_at_law. Intros c6. rename H5 into Hbw6.
  assert (Hd6: Zlength B6 / 8 = t + 4) by (rewrite HB6, Z.mul_comm, Z_div_mult; lia).
  assert (Hm6: Zlength B6 mod 8 = 0) by (rewrite HB6, Z.mul_comm, Z_mod_mult; auto).
  rewrite Hd6, Hm6. clear Hd6.
  forward.
  assert_PROP (field_compatible (tarray tuchar (2 ^ 19)) [] (e_srcp E)) as FCs by entailer!.
  assert (Hc6: Zlength c6 = 2 ^ 19) by (destruct Hbw6 as (? & _); auto).
  rewrite (ies_split3 Ews (2 ^ 19) (t + 4) (t + 4 + Zlength l) c6 (e_srcp E)) by (auto; lia).
  replace (t + 4 + Zlength l - (t + 4)) with (Zlength l) by lia.
  sep_apply (ies_dest Ews (Zlength l) (sublist (t + 4) (t + 4 + Zlength l) c6) (offset_val (t + 4) (e_srcp E))).
  rewrite <- (bytes_adler_cs Ews (2 ^ 18) dcont' (e_datap E)).
  forward_call (offset_val (t + 4) (e_srcp E), Ews, offset_val N (e_datap E), Ews, e_datap E, N, 2 ^ 18, dcont',
                Zlength l, l).
  rewrite ?bytes_adler_cs.
  forward. forward. forward.
  assert (Hdata: edata E (bs ++ [Stored l]) = edata E bs ++ l) by (unfold edata; apply data_stored).
  pose proof (Zlength_bytes_rep l) as HLr.
  set (c7 := sublist 0 (t + 4) c6 ++ bytes_rep l ++ sublist (t + 4 + Zlength l) (2 ^ 19) c6).
  assert (Hbw7: bw_bytes_ok (B6 ++ bytes_bits l) (2 ^ 19) c7) by (apply ies_bw_ok; auto; lia).
  assert (HL7: Zlength (B6 ++ bytes_bits l) = 8 * (t + 4 + Zlength l))
    by (rewrite Zlength_app, ies_Zlength_bytes_bits; lia).
  gather_SEP (data_at Ews (tarray tuchar (t + 4)) _ (e_srcp E)) (data_at Ews (tarray tuchar (Zlength l)) _ _)
             (data_at Ews (tarray tuchar (2 ^ 19 - (t + 4 + Zlength l))) _ _).
  replace_SEP 0 (data_at Ews (tarray tuchar (2 ^ 19)) c7 (e_srcp E)).
  { entailer!. unfold c7.
    rewrite <- (ies_join3 Ews (2 ^ 19) (t + 4) (t + 4 + Zlength l)) by (auto; try list_solve).
    replace (t + 4 + Zlength l - (t + 4)) with (Zlength l) by lia. cancel. }
  destruct Post as [Rn Rb Rc Rr].
  change (RA_normal _) with (EX l0: list Z, EX d0: list val, blk_done E bs last (Stored l0) d0).
  Exists l dcont'. unfold blk_done. rewrite <- EB6 by lia. rewrite Hdata. rewrite bw_at_law. Exists c7.
  assert (Hq: Zlength (B6 ++ bytes_bits l) / 8 = t + 4 + Zlength l) by (rewrite HL7, Z.mul_comm, Z_div_mult; lia).
  assert (Hr: Zlength (B6 ++ bytes_bits l) mod 8 = 0) by (rewrite HL7, Z.mul_comm, Z_mod_mult; auto).
  rewrite Hq, Hr. rewrite Zlength_app. rewrite !add_repr.
  entailer!. split.
  - simpl. split; [lia|]. eapply Forall_impl; [|exact H6]. intros b Hb. unfold byte_ok. rep_lia.
  - unfold dcont'. apply ies_data_ok; auto. unfold data_ok. auto.
Qed.

(* Law inflate_decode, main: a stored block (the branch bt == 0 of the block loop's body). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts: bits and bytes                                                                     *)

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma Zlength_zeros n : 0 <= n -> Zlength (zeros n) = n.
Proof. intros. unfold zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma Zlength_bytes_bits l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity | ].
  change (bytes_bits (b :: r)) with (bits_le b 8 ++ bytes_bits r).
  rewrite Zlength_app, IH, Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma bits_le_S v n : bits_le v (Z.of_nat (S n)) = Z.testbit v 0 :: bits_le (Z.div2 v) (Z.of_nat n).
Proof.
  unfold bits_le. rewrite !Nat2Z.id. cbn [seq map]. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros i.
  rewrite <- Zbits.Ztestbit_succ by lia. f_equal. lia.
Qed.

Lemma bval_bits_le v n : 0 <= n -> bval (bits_le v n) = v mod 2 ^ n.
Proof.
  intros Hn. rewrite <- (Z2Nat.id n Hn). generalize (Z.to_nat n) as k. clear n Hn. intros k. revert v.
  induction k as [|k IH]; intros v.
  - change (2 ^ Z.of_nat 0) with 1. rewrite Z.mod_1_r. reflexivity.
  - rewrite bits_le_S. cbn [bval]. rewrite IH, Z.div2_div, Z.bit0_odd.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.rem_mul_r by (try apply Z.pow_pos_nonneg; lia).
    rewrite Zodd_mod. pose proof (Z.mod_pos_bound v 2 ltac:(lia)). assert (E: v mod 2 = 0 \/ v mod 2 = 1) by lia.
    destruct E as [E | E]; rewrite E; reflexivity.
Qed.

Lemma pack_nil : pack [] = [].
Proof. reflexivity. Qed.

Lemma pack_cons8 b8 C : Zlength b8 = 8 -> pack (b8 ++ C) = bval b8 :: pack C.
Proof.
  intros H8. unfold pack. rewrite Zlength_app, H8.
  replace ((8 + Zlength C + 7) / 8) with (1 + (Zlength C + 7) / 8)
    by (rewrite <- Z.div_add_l by lia; f_equal; lia).
  pose proof (Zlength_nonneg C).
  rewrite Z2Nat.inj_add by (try apply Z.div_pos; lia). cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add seq map].
  f_equal.
  - rewrite sublist_app1 by lia. rewrite sublist_same by lia. reflexivity.
  - rewrite <- seq_shift, map_map. apply map_ext. intros k.
    rewrite sublist_app2 by lia. rewrite H8. f_equal; f_equal; lia.
Qed.

Lemma bits_le_8_byte b : 0 <= b < 256 -> pack (bits_le b 8) = [b].
Proof.
  intros Hb. rewrite <- (app_nil_r (bits_le b 8)). rewrite pack_cons8 by (apply Zlength_bits_le; lia).
  rewrite bval_bits_le by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

Lemma pack_app8 B C : Zlength B mod 8 = 0 -> pack (B ++ C) = pack B ++ pack C.
Proof.
  intros HB. remember (Z.to_nat (Zlength B / 8)) as k eqn:Ek. revert B HB Ek.
  induction k as [|k IH]; intros B HB Ek.
  - assert (Zlength B = 0).
    { pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
      assert (Zlength B / 8 <= 0) by lia. assert (0 <= Zlength B / 8) by (apply Z.div_pos; lia). lia. }
    apply Zlength_nil_inv in H. subst B. reflexivity.
  - pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
    assert (HL: 8 <= Zlength B) by lia.
    assert (EB: B = sublist 0 8 B ++ sublist 8 (Zlength B) B)
      by (rewrite sublist_rejoin, sublist_same by lia; auto).
    assert (EP: forall X, pack (B ++ X) = bval (sublist 0 8 B) :: pack (sublist 8 (Zlength B) B ++ X)).
    { intros X. rewrite EB at 1. rewrite <- app_assoc, pack_cons8 by (rewrite Zlength_sublist; lia). reflexivity. }
    pose proof (EP []) as EP0. rewrite !app_nil_r in EP0. rewrite (EP C), EP0. clear EP EP0 EB.
    rewrite IH; [reflexivity | rewrite Zlength_sublist by lia; replace (Zlength B - 8) with ((Zlength B / 8 - 1) * 8) by lia; apply Z_mod_mult | ].
    rewrite Zlength_sublist by lia.
    replace (Zlength B - 8) with ((Zlength B / 8 - 1) * 8) by lia. rewrite Z_div_mult by lia. lia.
Qed.

Lemma pack_bytes_bits l : is_bytes l -> pack (bytes_bits l) = l.
Proof.
  induction l as [|b r IH]; intros Hl; [reflexivity | ].
  inversion Hl; subst. change (bytes_bits (b :: r)) with (bits_le b 8 ++ bytes_bits r).
  rewrite pack_cons8 by (apply Zlength_bits_le; lia). rewrite IH by auto.
  rewrite bval_bits_le by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; rep_lia). reflexivity.
Qed.

Lemma pack_app_bytes B l : Zlength B mod 8 = 0 -> is_bytes l -> pack (B ++ bytes_bits l) = pack B ++ l.
Proof. intros. rewrite pack_app8, pack_bytes_bits by auto. reflexivity. Qed.

Lemma bits_le_ext v1 v2 n : 0 <= n -> v1 mod 2 ^ n = v2 mod 2 ^ n -> bits_le v1 n = bits_le v2 n.
Proof.
  intros Hn E. unfold bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite <- (Z.mod_pow2_bits_low v1 n), <- (Z.mod_pow2_bits_low v2 n) by lia. rewrite E. reflexivity.
Qed.

Lemma seq_offset a b : seq a b = map (Nat.add a) (seq 0 b).
Proof.
  induction a as [|a IH].
  - simpl. rewrite map_id. reflexivity.
  - rewrite <- seq_shift, IH, map_map. apply map_ext. intros; reflexivity.
Qed.

Lemma bits_le_add v a b : 0 <= a -> 0 <= b -> bits_le v (a + b) = bits_le v a ++ bits_le (v / 2 ^ a) b.
Proof.
  intros Ha Hb. unfold bits_le. rewrite Z2Nat.inj_add, seq_app, map_app by lia. f_equal.
  rewrite seq_offset, map_map. apply map_ext. intros i.
  rewrite <- Z.shiftr_div_pow2, Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma bits_le_16 v : 0 <= v < 65536 -> bits_le (v mod 256) 8 ++ bits_le ((v / 256) mod 256) 8 = bits_le v 16.
Proof.
  intros Hv. change 16 with (8 + 8). rewrite bits_le_add by lia. change (2 ^ 8) with 256. f_equal.
  - apply bits_le_ext; [lia | ]. change (2 ^ 8) with 256. rewrite Z.mod_mod; lia.
  - apply bits_le_ext; [lia | ]. change (2 ^ 8) with 256. rewrite Z.mod_mod; lia.
Qed.

Lemma zero_ext8_repr x : Int.zero_ext 8 (Int.repr x) = Int.repr (x mod 256).
Proof.
  apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_zero_ext by lia. rewrite !Int.testbit_repr by lia.
  change 256 with (2 ^ 8). destruct (zlt i 8).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma not_repr x : 0 <= x <= Int.max_unsigned -> Int.not (Int.repr x) = Int.repr (Int.max_unsigned - x).
Proof. intros. rewrite <- (Int.repr_unsigned (Int.not _)), Int.unsigned_not, Int.unsigned_repr by lia. reflexivity. Qed.

Lemma shru8_repr x : 0 <= x <= Int.max_unsigned -> Int.shru (Int.repr x) (Int.repr 8) = Int.repr (x / 256).
Proof. intros. rewrite Int.shru_div_two_p, !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma Zlength_enc_bits W bs : Zlength (enc_bits W bs) = 8 * Zlength (hdr_bytes W) + Zlength (enc_nf 0 bs).
Proof. unfold enc_bits. rewrite Zlength_app, Zlength_bytes_bits. reflexivity. Qed.

Lemma stored_bits E p last len bytes :
  Zlength E = 8 * ((Zlength E - p) / 8) + p -> 0 <= p -> 0 <= (Zlength E - p) / 8 ->
  (last = 0 \/ last = 1) -> Zlength bytes = len -> 0 <= len <= 65535 ->
  (((((((E ++ bits_le last 1) ++ bits_le 0 2) ++ zeros (pad8 (Zlength ((E ++ bits_le last 1) ++ bits_le 0 2)))) ++
        bits_le (len mod 256) 8) ++ bits_le ((len / 256) mod 256) 8) ++
      bits_le ((Int.max_unsigned - len) mod 256) 8) ++ bits_le (((Int.max_unsigned - len) / 256) mod 256) 8) ++
  bytes_bits bytes
  = E ++ enc_block p (last =? 1) (Stored bytes).
Proof.
  intros Hp Hp0 Hq Hl Hn Hlen. unfold enc_block. rewrite Hn.
  rewrite <- !app_assoc. f_equal.
  replace (bits_le last 1) with [last =? 1] by (destruct Hl; subst; reflexivity).
  cbn [app]. f_equal. change (bits_le 0 2 ++ ?X) with (false :: false :: X). cbn [app]. f_equal. f_equal.
  replace (Zlength (E ++ (last =? 1) :: bits_le 0 2)) with (Zlength E + 3)
    by (rewrite Zlength_app, Zlength_cons, Zlength_bits_le; lia).
  replace (pad8 (Zlength E + 3)) with (pad8 (p + 3)) 
    by (unfold pad8; rewrite Hp; replace (8 * ((Zlength E - p) / 8) + p + 3) with (p + 3 + ((Zlength E - p) / 8) * 8) by lia;
        rewrite Z_mod_plus_full; reflexivity).
  f_equal.
  rewrite app_assoc, bits_le_16 by lia. f_equal. rewrite app_assoc.
  assert (EM: Int.max_unsigned - len = (65535 - len) + 16776960 * 256)
    by (change Int.max_unsigned with 4294967295; lia).
  rewrite EM, Z_mod_plus_full, Z_div_plus_full by lia.
  change 16776960 with (65535 * 256). rewrite Z_mod_plus_full.
  rewrite bits_le_16 by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit writer at the law's compspecs (as IDMainBlk.v)                                         *)

Lemma st_bw_struct_cs sh (v: val * (val * val)) q :
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh t_bw v q = @data_at CS sh (Tstruct _bw noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma st_bytes_harness_cs sh n (v: list val) q:
  @data_at Zlib.contracts.x_inflate_decode.Harness.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_harness); [apply JMeq_refl | reflexivity]. Qed.

Lemma st_bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma st_dest_adler sh n v p :
  @data_at CS sh (tarray tuchar n) v p |-- @data_at_ Zlib.units.Adler32.CS sh (tarray tuchar n) p.
Proof. rewrite <- st_bytes_adler_cs. apply data_at_data_at_. Qed.

Lemma st_bw_at_law sh bsh B cap buf w :
  bw_at sh bsh B cap buf w =
  EX c: list val, !! bw_bytes_ok B cap c &&
    (@data_at CS sh (Tstruct _bw noattr)
       (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
     @data_at CS bsh (tarray tuchar cap) c buf)%logic.
Proof.
  unfold bw_at, bw_rep. f_equal. extensionality c. rewrite st_bw_struct_cs, st_bytes_harness_cs. reflexivity.
Qed.

Lemma st_bw_fold sh bsh B cap buf w c : bw_bytes_ok B cap c ->
  (@data_at CS sh (Tstruct _bw noattr)
     (buf, (Vint (Int.repr (Zlength B / 8)), Vint (Int.repr (Zlength B mod 8)))) w *
   @data_at CS bsh (tarray tuchar cap) c buf)%logic
  |-- bw_at sh bsh B cap buf w.
Proof. intros. rewrite st_bw_at_law. Exists c. entailer!. Qed.

Lemma st_room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma st_pack_len B : Zlength (pack B) = (Zlength B + 7) / 8.
Proof.
  unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg B) | ]; lia.
Qed.

Lemma st_split3 {cs: compspecs} sh n lo k (v: list val) p :
  0 <= lo -> 0 <= k -> lo + k <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar lo) (sublist 0 lo v) p *
   data_at sh (tarray tuchar k) (sublist lo (lo + k) v) (offset_val lo p) *
   data_at sh (tarray tuchar (n - (lo + k))) (sublist (lo + k) n v) (offset_val (lo + k) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n lo (lo + k)) by (auto; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.mul_1_l, !Z.add_0_l. replace (lo + k - lo) with k by lia. reflexivity.
Qed.

Ltac dm x := pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)).

Ltac assumed := match goal with H: Int.repr (if ?c then 1 else 0) <> Int.zero |- _ =>
  let E := fresh "E" in destruct c eqn:E; [clear H | exfalso; apply H; reflexivity] end.

Lemma st_byte_len B b : Zlength (B ++ bits_le b 8) = Zlength B + 8.
Proof. rewrite Zlength_app, Zlength_bits_le by lia. reflexivity. Qed.

Lemma st_byte_mod B b : Zlength B mod 8 = 0 -> Zlength (B ++ bits_le b 8) mod 8 = 0.
Proof. intros. rewrite st_byte_len. replace (Zlength B + 8) with (Zlength B + 1 * 8) by lia. rewrite Z_mod_plus_full. auto. Qed.

Lemma st_byte_div B b : Zlength (B ++ bits_le b 8) / 8 = Zlength B / 8 + 1.
Proof. rewrite st_byte_len. replace (Zlength B + 8) with (Zlength B + 1 * 8) by lia. rewrite Z_div_plus_full by lia. auto. Qed.

Lemma st_room_byte B cap : Zlength B mod 8 = 0 -> Zlength B / 8 + 1 <= cap -> cap <= Int.max_unsigned -> bw_room B cap 8.
Proof.
  intros. unfold bw_room. split; [lia | split; [ | lia]].
  replace (Zlength B + 8 + 7) with (Zlength B + 7 + 1 * 8) by lia. rewrite Z_div_plus_full by lia.
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  replace (Zlength B + 7) with (7 + (Zlength B / 8) * 8) by lia. rewrite Z_div_plus_full by lia.
  change (7 / 8) with 0. lia.
Qed.

Ltac byte_arg := entailer!; simpl;
  rewrite ?not_repr, ?shru8_repr, ?zero_ext8_repr by rep_lia; rewrite ?Zmod_mod; reflexivity.

Lemma st_join3 {cs: compspecs} sh n lo k (v1 v2 v3: list val) p :
  Zlength v1 = lo -> Zlength v2 = k -> Zlength v3 = n - (lo + k) -> 0 <= lo -> 0 <= k -> lo + k <= n ->
  field_compatible (tarray tuchar n) [] p ->
  (data_at sh (tarray tuchar lo) v1 p * data_at sh (tarray tuchar k) v2 (offset_val lo p) *
   data_at sh (tarray tuchar (n - (lo + k))) v3 (offset_val (lo + k) p))%logic =
  data_at sh (tarray tuchar n) (v1 ++ v2 ++ v3) p.
Proof.
  intros. rewrite (st_split3 sh n lo k (v1 ++ v2 ++ v3) p) by (auto; rewrite !Zlength_app; lia).
  repeat f_equal; list_solve.
Qed.

Lemma st_join3_d {cs: compspecs} sh n lo k (v1 v2 v3: list val) p :
  Zlength v1 = lo -> Zlength v2 = k -> Zlength v3 = n - (lo + k) -> 0 <= lo -> 0 <= k -> lo + k <= n ->
  field_compatible (tarray tuchar n) [] p ->
  (data_at sh (tarray tuchar lo) v1 p * data_at sh (tarray tuchar k) v2 (offset_val lo p) *
   data_at sh (tarray tuchar (n - (lo + k))) v3 (offset_val (lo + k) p))%logic
  |-- data_at sh (tarray tuchar n) (v1 ++ v2 ++ v3) p.
Proof. intros. rewrite st_join3 by auto. apply derives_refl. Qed.

Lemma id_stored_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls dcont isbz llc lcc dcc last (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last ->
  semax Delta_id
    (blk_mid gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls dcont isbz llc lcc dcc last 0)
    seg_stored
    (overridePost (blk_done gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last) R).
Proof.
  intros HH. destruct R as [Rn Rb Rc Rr].
  unfold blk_mid. Intros.
  unfold seg_stored, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros len.
  destruct H as (HD1 & HD2 & HD3 & HD4).
  set (D := expand [] bs) in *.
  set (E0 := enc_bits (id_wrapper wrap wb flevel) bs) in *.
  pose proof (Zlength_nonneg D) as HD0.
  forward_call (Int.repr (if len <=? 65535 then 1 else 0)).
  { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt 65535 len); destruct (Z.leb_spec len 65535); try lia; reflexivity. }
  assumed. apply Z.leb_le in E.
  forward_call (Int.repr (if Zlength D + len <=? 262144 then 1 else 0)).
  { entailer!. simpl. change (Int.shl (Int.repr 1) (Int.repr 18)) with (Int.repr 262144).
    unfold Int.ltu. rewrite ?add_repr, !Int.unsigned_repr by rep_lia.
    destruct (zlt 262144 (Zlength D + len)); destruct (Z.leb_spec (Zlength D + len) 262144); try lia; reflexivity. }
  assumed. apply Z.leb_le in E1.
  forward_call (Tsh, Ews, E0 ++ bits_le last 1, 524288, srcp, vw, 0, 2).
  { unfold bw_room. rewrite Zlength_app, Zlength_bits_le by lia. pose proof (Zlength_nonneg E0).
    dm (Zlength E0). dm (Zlength E0 + 1 + 2 + 7). rep_lia. }
  forward_call (Tsh, Ews, (E0 ++ bits_le last 1) ++ bits_le 0 2, 524288, srcp, vw).
  { unfold bw_room. rewrite !Zlength_app, !Zlength_bits_le by lia. pose proof (Zlength_nonneg E0).
    dm (Zlength E0). dm (Zlength E0 + 1 + 2 + 0 + 7). rep_lia. }
  set (B2 := (E0 ++ bits_le last 1) ++ bits_le 0 2).
  set (B3 := B2 ++ zeros (pad8 (Zlength B2))).
  assert (HL2: Zlength B2 = Zlength E0 + 3) by (unfold B2; rewrite !Zlength_app, !Zlength_bits_le by lia; lia).
  assert (HL3: Zlength B3 = Zlength B2 + pad8 (Zlength B2)).
  { unfold B3. rewrite Zlength_app, Zlength_zeros; auto. unfold pad8. apply Z.mod_pos_bound. lia. }
  assert (HM3: Zlength B3 mod 8 = 0).
  { rewrite HL3. unfold pad8. rewrite Zplus_mod, Zmod_mod, <- Zplus_mod.
    replace (Zlength B2 + (8 - Zlength B2 mod 8)) with (Zlength B2 - Zlength B2 mod 8 + 1 * 8) by lia.
    rewrite Z_mod_plus_full, Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
  rewrite st_bw_at_law. Intros c.
  assert (Hq3: 0 <= Zlength B3 / 8 <= 524288).
  { destruct H as (_ & Hp & _). rewrite st_pack_len in Hp. pose proof (Zlength_nonneg B3).
    dm (Zlength B3). dm (Zlength B3 + 7). lia. }
  forward.
  forward_call (Int.repr (if Zlength B3 / 8 + 4 + len <=? 524288 then 1 else 0)).
  { entailer!. simpl. change (Int.shl (Int.repr 1) (Int.repr 19)) with (Int.repr 524288).
    change (let (q, _) := Z.div_eucl (Zlength B3) 8 in q) with (Zlength B3 / 8).
    unfold Int.ltu. rewrite ?add_repr, !Int.unsigned_repr by rep_lia.
    destruct (zlt 524288 (Zlength B3 / 8 + 4 + len)); destruct (Z.leb_spec (Zlength B3 / 8 + 4 + len) 524288);
      try lia; reflexivity. }
  assumed. apply Z.leb_le in E2.
  sep_apply (st_bw_fold Tsh Ews B3 524288 srcp vw c H).
  set (q3 := Zlength B3 / 8) in *.
  assert (HB3: Zlength B3 = 8 * q3) by (dm (Zlength B3); lia).
  forward_call (Tsh, Ews, B3, 524288, srcp, vw, len mod 256).
  { byte_arg. }
  { split; [apply st_room_byte; rep_lia | pose proof (Z.mod_pos_bound len 256); lia]. }
  set (B4 := B3 ++ bits_le (len mod 256) 8).
  assert (HM4: Zlength B4 mod 8 = 0) by (apply st_byte_mod; auto).
  assert (HQ4: Zlength B4 / 8 = q3 + 1) by apply st_byte_div.
  forward_call (Tsh, Ews, B4, 524288, srcp, vw, (len / 256) mod 256).
  { byte_arg. }
  { split; [apply st_room_byte; rep_lia | pose proof (Z.mod_pos_bound (len / 256) 256); lia]. }
  set (B5 := B4 ++ bits_le ((len / 256) mod 256) 8).
  assert (HM5: Zlength B5 mod 8 = 0) by (apply st_byte_mod; auto).
  assert (HQ5: Zlength B5 / 8 = q3 + 2) by (unfold B5; rewrite st_byte_div; lia).
  forward_call (Tsh, Ews, B5, 524288, srcp, vw, (Int.max_unsigned - len) mod 256).
  { byte_arg. }
  { split; [apply st_room_byte; rep_lia | pose proof (Z.mod_pos_bound (Int.max_unsigned - len) 256); lia]. }
  set (B6 := B5 ++ bits_le ((Int.max_unsigned - len) mod 256) 8).
  assert (HM6: Zlength B6 mod 8 = 0) by (apply st_byte_mod; auto).
  assert (HQ6: Zlength B6 / 8 = q3 + 3) by (unfold B6; rewrite st_byte_div; lia).
  forward_call (Tsh, Ews, B6, 524288, srcp, vw, ((Int.max_unsigned - len) / 256) mod 256).
  { byte_arg. }
  { split; [apply st_room_byte; rep_lia | pose proof (Z.mod_pos_bound ((Int.max_unsigned - len) / 256) 256); lia]. }
  set (B7 := B6 ++ bits_le (((Int.max_unsigned - len) / 256) mod 256) 8).
  assert (HM7: Zlength B7 mod 8 = 0) by (apply st_byte_mod; auto).
  assert (HQ7: Zlength B7 / 8 = q3 + 4) by (unfold B7; rewrite st_byte_div; lia).
  assert_PROP (field_compatible (tarray tuchar 262144) [] datap) as FCd by entailer!.
  rewrite (st_split3 Ews 262144 (Zlength D) len dcont datap) by (auto; lia).
  assert (Hnn: offset_val (Zlength D) datap <> nullval).
  { destruct HH as (_ & Pd & _). destruct datap; try contradiction. discriminate. }
  forward_call (offset_val (Zlength D) datap, len, Ews).
  { rewrite if_false by auto. cancel. }
  Intros bytes. rewrite if_false by auto.
  rename H4 into Hbl. rename H5 into Hbb. fold (bytes_rep bytes).
  set (dcont2 := sublist 0 (Zlength D) dcont ++ bytes_rep bytes ++ sublist (Zlength D + len) 262144 dcont).
  sep_apply (st_join3_d Ews 262144 (Zlength D) len (sublist 0 (Zlength D) dcont) (bytes_rep bytes)
               (sublist (Zlength D + len) 262144 dcont) datap); [ unfold bytes_rep; list_solve .. | ].
  fold dcont2.
  rewrite st_bw_at_law. Intros c7. rename H4 into Hc7.
  forward.
  rewrite HQ7.
  assert_PROP (field_compatible (tarray tuchar 524288) [] srcp) as FCs by entailer!.
  assert (Hc7l: Zlength c7 = 524288) by apply Hc7.
  rewrite (@st_split3 CS Ews 524288 (q3 + 4) len c7 srcp) by first [exact FCs | lia].
  rewrite <- (st_bytes_adler_cs Ews 262144 dcont2 datap).
  sep_apply (st_dest_adler Ews len (sublist (q3 + 4) (q3 + 4 + len) c7) (offset_val (q3 + 4) srcp)).
  forward_call (offset_val (q3 + 4) srcp, Ews, offset_val (Zlength D) datap, Ews, datap, Zlength D, 262144,
                dcont2, len, bytes).
  { unfold cbuf_ok. split; [reflexivity | ]. split; [auto with share | ]. split3; [lia | lia | ].
    split3; [auto | exact Hbb | ]. subst dcont2. unfold bytes_rep; list_solve. }
  rewrite (st_bytes_adler_cs Ews len (bytes_rep bytes)), (st_bytes_adler_cs Ews 262144 dcont2).
  forward. forward. forward.
  (* the bit writer: B7 ++ the bytes *)
  set (c8 := sublist 0 (q3 + 4) c7 ++ bytes_rep bytes ++ sublist (q3 + 4 + len) 524288 c7).
  sep_apply (@st_join3_d CS Ews 524288 (q3 + 4) len (sublist 0 (q3 + 4) c7) (bytes_rep bytes)
               (sublist (q3 + 4 + len) 524288 c7) srcp); [ unfold bytes_rep; list_solve .. | ].
  fold c8.
  set (B8 := B7 ++ bytes_bits bytes).
  assert (HL8: Zlength B8 = Zlength B7 + 8 * len) by (unfold B8; rewrite Zlength_app, Zlength_bytes_bits; lia).
  assert (HB7: Zlength B7 = 8 * (q3 + 4)) by (dm (Zlength B7); lia).
  assert (EQ8: Zlength B8 / 8 = q3 + 4 + len).
  { rewrite HL8, HB7. replace (8 * (q3 + 4) + 8 * len) with (0 + (q3 + 4 + len) * 8) by lia.
    rewrite Z_div_plus_full by lia. reflexivity. }
  assert (EM8: Zlength B8 mod 8 = Zlength B7 mod 8).
  { rewrite HM7, HL8, HB7. replace (8 * (q3 + 4) + 8 * len) with (0 + (q3 + 4 + len) * 8) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  assert (Hp7: pack B7 = sublist 0 (q3 + 4) (pack B7)).
  { rewrite sublist_same; auto. rewrite st_pack_len, HB7. replace (8 * (q3 + 4) + 7) with (7 + (q3 + 4) * 8) by lia.
    rewrite Z_div_plus_full by lia. reflexivity. }
  assert (Hpl7: Zlength (pack B7) = q3 + 4).
  { rewrite st_pack_len, HB7. replace (8 * (q3 + 4) + 7) with (7 + (q3 + 4) * 8) by lia.
    rewrite Z_div_plus_full by lia. reflexivity. }
  assert (Hc8: bw_bytes_ok B8 524288 c8).
  { destruct Hc7 as (_ & Hc7b & Hc7c). rewrite Hpl7 in Hc7c.
    unfold bw_bytes_ok, B8. rewrite pack_app_bytes by auto. split; [subst c8; unfold bytes_rep; list_solve | ].
    rewrite Zlength_app, Hpl7, Hbl. split; [lia | ].
    subst c8. unfold bytes_rep in *. rewrite map_app. list_solve. }
  rewrite !add_repr, <- EQ8, <- EM8.
  sep_apply (st_bw_fold Tsh Ews B8 524288 srcp vw c8 Hc8).
  replace B8 with (E0 ++ enc_block (Zlength (enc_nf 0 bs)) (last =? 1) (Stored bytes)).
  2: { symmetry. unfold B8, B7, B6, B5, B4, B3, B2.
       assert (HE0: Zlength E0 = 8 * Zlength (hdr_bytes (id_wrapper wrap wb flevel)) + Zlength (enc_nf 0 bs))
         by apply Zlength_enc_bits.
       assert (Hdq: (Zlength E0 - Zlength (enc_nf 0 bs)) / 8 = Zlength (hdr_bytes (id_wrapper wrap wb flevel))).
       { rewrite HE0. replace (8 * Zlength (hdr_bytes (id_wrapper wrap wb flevel)) + Zlength (enc_nf 0 bs) -
                               Zlength (enc_nf 0 bs)) with (Zlength (hdr_bytes (id_wrapper wrap wb flevel)) * 8) by lia.
         apply Z_div_mult. lia. }
       pose proof (Zlength_nonneg (enc_nf 0 bs)). pose proof (Zlength_nonneg (hdr_bytes (id_wrapper wrap wb flevel))).
       apply stored_bits; try rewrite Hdq; auto; try lia.
       destruct HH as (_ & _ & _ & _ & _ & _ & _ & ? & _). auto. }
  unfold blk_done. Exists (Stored bytes) dcont2 llc lcc dcc.
  entailer!.
  2: apply derives_refl.
  change (expand [] bs) with D. unfold block_data.
  split3.
  - split; [lia | ]. eapply Forall_impl; [ | exact Hbb]. intros b Hb. unfold byte_ok. rep_lia.
  - unfold data_ok. rewrite Zlength_app. split; [exact H8 | ]. split; [lia | ].
    split; [apply Forall_app; split; auto | ].
    subst dcont2. unfold bytes_rep in *. rewrite map_app. list_solve.
  - rewrite Zlength_app. reflexivity.
Qed.

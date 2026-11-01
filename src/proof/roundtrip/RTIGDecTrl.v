(* RT-I: copy of rfc1951/DecTrl.v over the generalized definitions RTIGDefs.v. *)
(* Part of the decode theory: the passes from CHECK, LENGTH, DONE.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Zlib.proof.crc32.Combine.
From Coq Require Znumtheory.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bits of bytes                                                                                  *)

Lemma trl_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma trl_bytes_bits_len l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, trl_bits_le_len by lia.
  rewrite Zlength_cons. lia.
Qed.

Lemma trl_bytes_bits_app l1 l2 : bytes_bits (l1 ++ l2) = bytes_bits l1 ++ bytes_bits l2.
Proof. unfold bytes_bits. apply flat_map_app. Qed.

Lemma trl_sublist_bytes_bits l a b : 0 <= a <= b -> b <= Zlength l ->
  sublist (8 * a) (8 * b) (bytes_bits l) = bytes_bits (sublist a b l).
Proof.
  intros H1 H2.
  assert (E: l = sublist 0 a l ++ sublist a b l ++ sublist b (Zlength l) l).
  { rewrite sublist_rejoin, sublist_rejoin, sublist_same by lia. reflexivity. }
  rewrite E at 1. rewrite !trl_bytes_bits_app.
  assert (La: Zlength (sublist 0 a l) = a) by (rewrite Zlength_sublist by lia; lia).
  assert (Lb: Zlength (bytes_bits (sublist a b l)) = 8 * (b - a))
    by (rewrite trl_bytes_bits_len, Zlength_sublist by lia; lia).
  rewrite sublist_app2 by (rewrite trl_bytes_bits_len; lia).
  rewrite trl_bytes_bits_len, La.
  rewrite sublist_app1 by lia.
  replace (8 * a - 8 * a) with 0 by lia. replace (8 * b - 8 * a) with (Zlength (bytes_bits (sublist a b l))) by lia.
  apply sublist_same; lia.
Qed.

Lemma trl_bval_app x y : bval (x ++ y) = bval x + 2 ^ Zlength x * bval y.
Proof.
  induction x as [|b x IH]; cbn [app bval].
  - change (Zlength (@nil bool)) with 0. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). lia.
Qed.

Lemma trl_bval_map_testbit n : forall v, 0 <= v ->
  bval (map (fun i => Z.testbit v (Z.of_nat i)) (seq 0 n)) = v mod 2 ^ Z.of_nat n.
Proof.
  induction n as [|n IH]; intros v Hv.
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - change (seq 0 (S n)) with (0%nat :: seq 1 n).
    rewrite <- seq_shift. cbn [map bval].
    rewrite map_map.
    rewrite (map_ext _ (fun i => Z.testbit (v / 2) (Z.of_nat i))).
    2:{ intros i. rewrite Nat2Z.inj_succ, <- Z.div2_bits by lia. try rewrite Z.div2_div. reflexivity. }
    rewrite IH by (apply Z.div_pos; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite Z.bit0_mod. set (P := 2 ^ Z.of_nat n). assert (HP: 0 < P) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_mod v 2 ltac:(lia)). pose proof (Z.div_mod (v/2) P ltac:(lia)).
    pose proof (Z.mod_pos_bound v 2 ltac:(lia)). pose proof (Z.mod_pos_bound (v/2) P HP).
    apply Z.mod_unique with (q := (v/2)/P); [left; lia | nia].
Qed.

Lemma trl_bval_byte b : 0 <= b < 256 -> bval (bits_le b 8) = b.
Proof.
  intros H. unfold bits_le. change (Z.to_nat 8) with 8%nat.
  rewrite trl_bval_map_testbit by lia. apply Z.mod_small. simpl. lia.
Qed.

(* the value of bytes, little-endian *)
Fixpoint trl_le (l: list Z) : Z := match l with [] => 0 | b :: r => b + 256 * trl_le r end.

Lemma trl_bval_bytes l : Forall (fun b => 0 <= b < 256) l -> bval (bytes_bits l) = trl_le l.
Proof.
  induction l as [|b l IH]; intros F; [reflexivity|].
  inversion F; subst. unfold bytes_bits in *. cbn [flat_map].
  rewrite trl_bval_app, trl_bits_le_len, trl_bval_byte, IH by (auto; lia). simpl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Four bytes: little-endian value, ZSWAP32 (as TheoryDict.v of inflate_codes)                     *)

Fixpoint trl_zup (n: nat) (z: Z) : list Z := match n with O => [] | S n' => z :: trl_zup n' (z + 1) end.

Lemma trl_in_zup n : forall z x, z <= x < z + Z.of_nat n -> In x (trl_zup n z).
Proof.
  induction n as [|n IH]; intros z x H; [lia|]. cbn [trl_zup].
  destruct (Z.eq_dec x z) as [E|E]; [left; auto|right; apply IH; lia].
Qed.

Lemma trl_ff00_tab : forallb (fun v => Z.land v 65280 =? v / 256 * 256) (trl_zup (Z.to_nat 65536) 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trl_ff00 y : Z.land y 65280 = (y mod 65536) / 256 * 256.
Proof.
  change 65280 with (Z.land (Z.ones 16) 65280) at 1. rewrite Z.land_assoc, Z.land_ones by lia.
  change (2 ^ 16) with 65536.
  pose proof trl_ff00_tab as T. rewrite forallb_forall in T.
  assert (R : 0 <= y mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  assert (I : In (y mod 65536) (trl_zup (Z.to_nat 65536) 0))
    by (apply trl_in_zup; change (Z.of_nat (Z.to_nat 65536)) with 65536; lia).
  specialize (T _ I). apply Z.eqb_eq in T. exact T.
Qed.

Lemma trl_swap b0 b1 b2 b3 :
  0 <= b0 <= 255 -> 0 <= b1 <= 255 -> 0 <= b2 <= 255 -> 0 <= b3 <= 255 ->
  swap32 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3.
Proof.
  intros H0 H1 H2 H3. unfold swap32.
  rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia. rewrite !trl_ff00.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  set (x := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))).
  assert (E1 : x / 16777216 = b3)
    by (symmetry; apply Z.div_unique with (r := b0 + 256 * b1 + 65536 * b2); [left|]; unfold x; lia).
  assert (E2 : x / 256 = b1 + 256 * b2 + 65536 * b3)
    by (symmetry; apply Z.div_unique with (r := b0); [left|]; unfold x; lia).
  assert (E3 : x mod 65536 = b0 + 256 * b1)
    by (symmetry; apply Z.mod_unique with (q := b2 + 256 * b3); [left|]; unfold x; lia).
  assert (E4 : x mod 256 = b0)
    by (symmetry; apply Z.mod_unique with (q := b1 + 256 * (b2 + 256 * b3)); [left|]; unfold x; lia).
  rewrite E1, E2, E3, E4. clear E1 E2 E3 E4 x.
  assert (E5 : (b1 + 256 * b2 + 65536 * b3) mod 65536 = b1 + 256 * b2)
    by (symmetry; apply Z.mod_unique with (q := b3); [left|]; lia).
  assert (E6 : (b1 + 256 * b2) / 256 = b2) by (symmetry; apply Z.div_unique with (r := b1); [left|]; lia).
  assert (E7 : (b0 + 256 * b1) / 256 = b1) by (symmetry; apply Z.div_unique with (r := b0); [left|]; lia).
  rewrite E5, E6, E7. rewrite (Z.mod_small b3 256) by lia. lia.
Qed.

Lemma trl_le_bytes4 v : le_bytes v 4 = [v mod 256; v / 256 mod 256; v / 65536 mod 256; v / 16777216 mod 256].
Proof.
  unfold le_bytes. change (seq 0 (Z.to_nat 4)) with [0; 1; 2; 3]%nat. cbn [map].
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 3)) with 16777216.
  rewrite Z.div_1_r. reflexivity.
Qed.

Lemma trl_le4_val v : 0 <= v -> trl_le (le_bytes v 4) = v mod 2 ^ 32.
Proof.
  intros Hv. rewrite trl_le_bytes4. cbn [trl_le].
  pose proof (Z.div_mod v 256 ltac:(lia)). pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 256) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 65536) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 65536) 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 16777216) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 16777216) 256 ltac:(lia)).
  rewrite Z.div_div in H1, H3, H5 by lia.
  change (256 * 256) with 65536 in H1. change (65536 * 256) with 16777216 in H3.
  change (16777216 * 256) with 4294967296 in H5. change (2 ^ 32) with 4294967296.
  apply Z.mod_unique with (q := v / 4294967296); [left|]; lia.
Qed.

Lemma trl_be4_swap v : 0 <= v < 2 ^ 32 -> swap32 (trl_le (be_bytes v 4)) = v.
Proof.
  intros Hv. unfold be_bytes. rewrite trl_le_bytes4. cbn [rev app trl_le].
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 256) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound (v / 65536) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (v / 16777216) 256 ltac:(lia)).
  rewrite trl_swap by lia.
  pose proof (trl_le4_val v ltac:(lia)) as E. rewrite trl_le_bytes4 in E. cbn [trl_le] in E.
  rewrite (Z.mod_small v (2 ^ 32)) in E by lia. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  lia.
Qed.

Lemma trl_le_bytes_ok v n : Forall (fun b => 0 <= b < 256) (le_bytes v n).
Proof.
  unfold le_bytes. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (i & <- & _).
  apply Z.mod_pos_bound. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The data are bytes                                                                             *)

Lemma trl_Znth_byte (l: list Z) i : Forall byte_ok l -> byte_ok (Znth i l).
Proof.
  intros F. destruct (Z_lt_ge_dec i 0) as [Hi|Hi]; [rewrite Znth_underflow by lia; unfold byte_ok, Inhabitant_Z; lia|].
  destruct (Z_lt_ge_dec i (Zlength l)) as [Hj|Hj].
  - rewrite Forall_forall in F. apply F, Znth_In. lia.
  - rewrite Znth_overflow by lia. unfold byte_ok, Inhabitant_Z; lia.
Qed.

Lemma trl_lz_copy_bytes n : forall dist out, Forall byte_ok out -> Forall byte_ok (lz_copy n dist out).
Proof.
  induction n as [|n IH]; intros dist out F; [exact F|]. cbn [lz_copy]. apply IH.
  apply Forall_app; split; [exact F|]. constructor; [apply trl_Znth_byte; exact F | constructor].
Qed.

Lemma trl_syms_bytes wmax ll dl syms : forall out, Forall byte_ok out -> syms_ok wmax ll dl out syms ->
  Forall byte_ok (syms_data out syms).
Proof.
  induction syms as [|s syms IH]; intros out F H; [exact F|].
  destruct H as [Hs Hr]. unfold syms_data. cbn [fold_left]. apply IH; [|exact Hr].
  destruct s as [b|len dist]; cbn [sym_data].
  - destruct Hs as [Hb _]. apply Forall_app; split; [exact F | constructor; [exact Hb | constructor]].
  - apply trl_lz_copy_bytes. exact F.
Qed.

Lemma trl_blocks_bytes wmax bs : forall out, Forall byte_ok out -> blocks_ok wmax out bs ->
  Forall byte_ok (expand out bs).
Proof.
  induction bs as [|b bs IH]; intros out F H; [exact F|].
  destruct H as [Hb Hr]. unfold expand. cbn [fold_left]. apply IH; [|exact Hr].
  destruct b as [bytes|syms|nlen ndist clsent toks syms]; cbn [block_data]; cbn [block_ok] in Hb.
  - apply Forall_app; split; [exact F | apply Hb].
  - apply (trl_syms_bytes wmax fixed_ll fixed_dl); auto.
  - eapply trl_syms_bytes; [exact F | apply Hb].
Qed.

Lemma trl_full_bytes G : dctx_ok G -> Forall byte_ok (full G).
Proof.
  intros (Hs & _). destruct Hs as (_ & _ & _ & _ & Hh & Hb). unfold full. eapply trl_blocks_bytes; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(32) from a byte-aligned bit buffer                                                   *)

Definition trl_nb (m: mst) (nx hold bits lv: Z) : mst :=
  set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) hold) bits) lv.

Lemma trl_needbits_frame k n : forall m,
  needbits_f k n m = trl_nb m (m_nx (needbits_f k n m)) (m_hold (needbits_f k n m))
                              (m_bits (needbits_f k n m)) (m_leave (needbits_f k n m)).
Proof.
  induction k as [|k IH]; intros m; [destruct m; reflexivity|].
  cbn [needbits_f]. destruct (m_bits m <? n).
  - destruct (m_have m =? 0); [destruct m; reflexivity|].
    rewrite (IH (pull m)) at 1. destruct m; reflexivity.
  - destruct m; reflexivity.
Qed.

Ltac trl_nbfin :=
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); [reflexivity|assumption|lia|lia|lia|];
  first [left; refine (conj _ (conj _ _)); lia | right; split; lia].

Lemma trl_needbits_f G pos (K: dkit_stmt) k : forall m,
  bytes_ok (dc_src G) -> 0 <= pos -> pos + Zlength (m_inp m) <= Zlength (dc_src G) ->
  m_inp m = sublist pos (pos + Zlength (m_inp m)) (dc_src G) ->
  0 <= m_nx m <= Zlength (m_inp m) ->
  hold_ok G (pos + m_nx m) (m_hold m) (m_bits m) -> m_bits m mod 8 = 0 -> 0 <= m_bits m <= 32 ->
  32 - m_bits m <= 8 * Z.of_nat k -> m_leave m = 0 ->
  let m' := needbits_f k 32 m in
  m_inp m' = m_inp m /\
  hold_ok G (pos + m_nx m') (m_hold m') (m_bits m') /\
  8 * (pos + m_nx m') - m_bits m' = 8 * (pos + m_nx m) - m_bits m /\
  m_bits m' mod 8 = 0 /\ m_nx m <= m_nx m' <= Zlength (m_inp m) /\
  ((m_leave m' = 1 /\ m_nx m' = Zlength (m_inp m) /\ 0 <= m_bits m' < 32) \/ (m_leave m' = 0 /\ m_bits m' = 32)).
Proof.
  induction k as [|k IH]; intros m Hb Hp Hl Hi Hn Hh H8 Hr Hk Hv; cbv zeta.
  - cbn [needbits_f]. assert (m_bits m = 32) by lia. trl_nbfin.
  - cbn [needbits_f]. destruct (m_bits m <? 32) eqn:E1.
    2:{ apply Z.ltb_ge in E1. trl_nbfin. }
    apply Z.ltb_lt in E1. destruct (m_have m =? 0) eqn:E2.
    + apply Z.eqb_eq in E2. unfold m_have in E2. unfold set_leave.
      cbn [m_inp m_nx m_hold m_bits m_leave set_m_leave]. trl_nbfin.
    + apply Z.eqb_neq in E2. unfold m_have in E2.
      assert (Bz: Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src G)).
      { rewrite Hi at 1. rewrite Znth_sublist by lia. f_equal. lia. }
      assert (Hp1: hold_ok G (pos + m_nx (pull m)) (m_hold (pull m)) (m_bits (pull m))).
      { unfold pull. cbn [m_nx m_hold m_bits set_m_bits set_m_hold set_m_nx]. rewrite Bz.
        unfold u64, u32. rewrite (Z.mod_small (m_bits m + 8)) by lia.
        replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia.
        apply (dk_pull K); auto; lia. }
      assert (P1: m_inp (pull m) = m_inp m) by reflexivity.
      assert (P2: m_nx (pull m) = m_nx m + 1) by reflexivity.
      assert (P3: m_bits (pull m) = m_bits m + 8)
        by (unfold pull; cbn [m_bits set_m_bits]; unfold u32; apply Z.mod_small; lia).
      assert (P4: m_leave (pull m) = 0) by exact Hv.
      rewrite P2, P3 in Hp1.
      rewrite Nat2Z.inj_succ in Hk.
      assert (Hb24: m_bits m <= 24) by (pose proof (Z.div_mod (m_bits m) 8 ltac:(lia)); lia).
      assert (Hm8: (m_bits m + 8) mod 8 = 0) by (rewrite Z.add_mod, H8 by lia; reflexivity).
      assert (A1: pos + Zlength (m_inp (pull m)) <= Zlength (dc_src G)) by (rewrite P1; lia).
      assert (A2: m_inp (pull m) = sublist pos (pos + Zlength (m_inp (pull m))) (dc_src G)) by (rewrite P1; exact Hi).
      assert (A3: 0 <= m_nx (pull m) <= Zlength (m_inp (pull m))) by (rewrite P1, P2; lia).
      assert (A4: hold_ok G (pos + m_nx (pull m)) (m_hold (pull m)) (m_bits (pull m))) by (rewrite P2, P3; exact Hp1).
      assert (A5: m_bits (pull m) mod 8 = 0) by (rewrite P3; exact Hm8).
      assert (A6: 0 <= m_bits (pull m) <= 32) by (rewrite P3; lia).
      assert (A7: 32 - m_bits (pull m) <= 8 * Z.of_nat k) by (rewrite P3; lia).
      pose proof (IH (pull m) Hb Hp A1 A2 A3 A4 A5 A6 A7 P4) as (I1 & I2 & I3 & I4 & I5 & I6).
      rewrite P1 in *. rewrite P2, P3 in I3. rewrite P2 in I5.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The wrapper: wrap, flags, the trailer's place                                                  *)

Lemma trl_wb_cases wb : 8 <= wb <= 15 ->
  wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15.
Proof. lia. Qed.

Lemma trl_wrap G s : dctx_ok G -> glob_ok G s ->
  (wrapped G = false -> i_wrap s = 0) /\ (wrapped G = true -> Z.land (i_wrap s) 4 <> 0).
Proof.
  intros D ((wb0 & R0 & _) & _). destruct (rtig_wrap_bits G s wb0 R0) as (w & R & Z0 & ->).
  cut ((wrapped G = false -> w = 0) /\ (wrapped G = true -> Z.land w 4 <> 0));
    [intros (A & B); split; [intros X; exact (Z0 (A X)) | exact B]|]. clear Z0 R0.
  destruct D as ((Hwb & Hw & Hz & _) & Ha & _).
  unfold accepts, wrapped in *.
  destruct (dc_w G) as [|wb fl did|h]; destruct (trl_wb_cases _ Hwb) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]];
    rewrite E in *;
    repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] end; rewrite Ha in R;
    cbv in R; inversion R; subst; split; intros; try discriminate; cbv; congruence.
Qed.

Lemma trl_flags G s : glob_ok G s -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
  (forall wb fl did, dc_w G = WZlib wb fl did -> i_flags s = 0) /\
  (forall h, dc_w G = WGzip h -> i_flags s <> 0).
Proof.
  intros (_ & _ & _ & F) H1 H2. split.
  - intros wb fl did E. rewrite F; [rewrite E; reflexivity | unfold wrapped; rewrite E; reflexivity | auto | auto].
  - intros h E. rewrite F; [rewrite E | unfold wrapped; rewrite E; reflexivity | auto | auto].
    unfold gz_flg. destruct (gz_text h), (gz_hcrc h), (gz_extra h), (gz_name h), (gz_comment h); lia.
Qed.

(* v4: only gzip has no history (zlib FDICT: the dictionary) *)
Lemma trl_hist_gzip G h : dctx_ok G -> dc_w G = WGzip h -> dc_hist G = [].
Proof.
  intros ((_ & Hw & _) & _) W. unfold wrapper_ok in Hw. rewrite W in Hw. apply Hw.
Qed.

Lemma trl_produced_gzip G h x : dctx_ok G -> dc_w G = WGzip h -> produced G x = x.
Proof.
  intros D W. unfold produced. rewrite (trl_hist_gzip G h D W), Zlength_nil. apply sublist_same; lia.
Qed.

Lemma trl_produced_pre G d : produced G (dc_hist G ++ d) = d.
Proof.
  unfold produced. rewrite Zlength_app. pose proof (Zlength_nonneg d). pose proof (Zlength_nonneg (dc_hist G)).
  rewrite sublist_app2 by lia. rewrite Z.sub_diag. apply sublist_same; lia.
Qed.

Lemma trl_produced_app G ob ow : (exists d', ob = dc_hist G ++ d') ->
  produced G (ob ++ ow) = produced G ob ++ ow.
Proof.
  intros (d' & E). subst ob. rewrite <- app_assoc, !trl_produced_pre. reflexivity.
Qed.

Lemma trl_produced_bytes G x : Forall byte_ok x -> Forall byte_ok (produced G x).
Proof. intros F. unfold produced. apply Forall_sublist, F. Qed.

Lemma trl_le_bytes_len v n : 0 <= n -> Zlength (le_bytes v n) = n.
Proof. intros. unfold le_bytes. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma trl_be_bytes_len v n : 0 <= n -> Zlength (be_bytes v n) = n.
Proof. intros. unfold be_bytes. rewrite Zlength_rev. apply trl_le_bytes_len; auto. Qed.

Lemma trl_be_bytes_ok v n : Forall (fun b => 0 <= b < 256) (be_bytes v n).
Proof. unfold be_bytes. apply Forall_rev. apply trl_le_bytes_ok. Qed.

Lemma trl_endpos_nonneg G : 0 <= endpos G.
Proof. unfold endpos, D0. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). pose proof (Zlength_nonneg (deflate_bits (dc_bs G))). lia. Qed.

(* the trailer, located: sublist e slen = T with |T| = n *)
Lemma trl_place G (K: dkit_stmt) T : dctx_ok G -> 0 < Zlength T ->
  sublist (endpos G / 8) (slen G) (dc_src G) = T ->
  endpos G / 8 + Zlength T = slen G /\ slen G <= Zlength (dc_src G).
Proof.
  intros D HT E. pose proof (trl_endpos_nonneg G).
  assert (Hs: slen G <= Zlength (dc_src G)) by apply D.
  destruct (Z_lt_ge_dec (slen G) (endpos G / 8)) as [L|L].
  - rewrite sublist_nil_gen in E by lia. subst T. rewrite Zlength_nil in HT. lia.
  - rewrite <- E, Zlength_sublist; [lia | | lia]. split; [apply Z.div_pos; lia | lia].
Qed.

Lemma trl_trail_zlib G (K: dkit_stmt) wb fl did : dctx_ok G -> dc_w G = WZlib wb fl did ->
  endpos G = 8 * (endpos G / 8) /\ slen G = endpos G / 8 + 4 /\ slen G <= Zlength (dc_src G) /\
  sublist (endpos G / 8) (endpos G / 8 + 4) (dc_src G) = be_bytes (ref_adler32 1 (produced G (full G))) 4.
Proof.
  intros D W. destruct (dk_trailer K G D) as [M E]. rewrite W in E.
  assert (LT: 0 < Zlength (be_bytes (ref_adler32 1 (produced G (full G))) 4)) by (rewrite trl_be_bytes_len; lia).
  destruct (trl_place G K _ D LT E) as [L1 L2].
  rewrite trl_be_bytes_len in L1 by lia.
  split; [pose proof (Z.div_mod (endpos G) 8 ltac:(lia)); lia|]. split; [lia|]. split; [lia|].
  rewrite <- L1 in E. exact E.
Qed.

Lemma trl_trail_gzip G (K: dkit_stmt) h : dctx_ok G -> dc_w G = WGzip h ->
  endpos G = 8 * (endpos G / 8) /\ slen G = endpos G / 8 + 8 /\ slen G <= Zlength (dc_src G) /\
  sublist (endpos G / 8) (endpos G / 8 + 4) (dc_src G) = le_bytes (ref_crc32 0 (full G)) 4 /\
  sublist (endpos G / 8 + 4) (endpos G / 8 + 8) (dc_src G) = le_bytes (Zlength (full G) mod 2 ^ 32) 4.
Proof.
  intros D W. destruct (dk_trailer K G D) as [M E]. rewrite W in E.
  rewrite (trl_produced_gzip G h) in E by auto.
  assert (LT: Zlength (le_bytes (ref_crc32 0 (full G)) 4 ++ le_bytes (Zlength (full G) mod 2 ^ 32) 4) = 8)
    by (rewrite Zlength_app, !trl_le_bytes_len; lia).
  assert (LT': 0 < Zlength (le_bytes (ref_crc32 0 (full G)) 4 ++ le_bytes (Zlength (full G) mod 2 ^ 32) 4)) by lia.
  destruct (trl_place G K _ D LT' E) as [L1 L2]. rewrite LT in L1.
  pose proof (trl_endpos_nonneg G). assert (0 <= endpos G / 8) by (apply Z.div_pos; lia).
  split; [pose proof (Z.div_mod (endpos G) 8 ltac:(lia)); lia|]. split; [lia|]. split; [lia|].
  split.
  - replace (endpos G / 8 + 4) with (4 + endpos G / 8) by lia.
    replace (sublist (endpos G / 8) _ _) with (sublist (0 + endpos G / 8) (4 + endpos G / 8) (dc_src G)) by reflexivity.
    rewrite <- (sublist_sublist 4 (slen G) 0 (endpos G / 8)) by lia. rewrite E.
    rewrite sublist_app1 by (rewrite ?trl_le_bytes_len; lia). apply sublist_same; rewrite ?trl_le_bytes_len; lia.
  - replace (endpos G / 8 + 4) with (4 + endpos G / 8) by lia. replace (endpos G / 8 + 8) with (8 + endpos G / 8) by lia.
    rewrite <- (sublist_sublist 8 (slen G) 4 (endpos G / 8)) by lia. rewrite E.
    rewrite sublist_app2 by (rewrite ?trl_le_bytes_len; lia). rewrite trl_le_bytes_len by lia.
    apply sublist_same; rewrite ?trl_le_bytes_len; lia.
Qed.

(* 32 bits of the input at a byte position *)
Lemma trl_bits32 G e l : 0 <= e -> e + 4 <= Zlength (dc_src G) -> sublist e (e + 4) (dc_src G) = l ->
  Forall (fun b => 0 <= b < 256) l -> bval (sublist (8 * e) (8 * e + 32) (sbits G)) = trl_le l.
Proof.
  intros H1 H2 E F. unfold sbits. replace (8 * e + 32) with (8 * (e + 4)) by lia.
  rewrite trl_sublist_bytes_bits by lia. rewrite E. apply trl_bval_bytes, F.
Qed.

Lemma trl_slen_raw G (K: dkit_stmt) : dctx_ok G -> dc_w G = WRaw -> 8 * slen G = endpos G.
Proof.
  intros D W. destruct (dk_trailer K G D) as [M _].
  unfold slen, endpos, D0, hdr_bytes, stream_bytes in *. rewrite W in *. rewrite Zlength_nil in *.
  unfold deflate_bytes, pack. rewrite Zlength_map, Zlength_correct, seq_length, Z2Nat.id.
  2:{ apply Z.div_pos; [pose proof (Zlength_nonneg (deflate_bits (dc_bs G))); lia | lia]. }
  set (L := Zlength (deflate_bits (dc_bs G))) in *. pose proof (Zlength_nonneg (deflate_bits (dc_bs G))).
  pose proof (Z.div_mod (8 * 0 + L) 8 ltac:(lia)). pose proof (Z.div_mod (L + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (L + 7) 8 ltac:(lia)).
  replace (8 * 0 + L) with L in * by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* at_mode at CHECK, LENGTH, DONE                                                                 *)

Lemma trl_at_get G s c h b out : at_mode G s c h b out ->
  hold_ok G c h b /\ (i_mode s = CHECK -> at_check G s (8 * c - b) b out) /\
  (i_mode s = LENGTH -> at_length G s (8 * c - b) b out).
Proof.
  unfold at_mode. cbv zeta. intros [Hh D]. split; [exact Hh|].
  split; intros Hm; rewrite Hm in D;
    cbv [HEAD FLAGS TIME OS Zlib.proof.inflate.Model.TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS
         LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE] in D;
    repeat match goal with H: _ \/ _ |- _ => destruct H as [H|H] | H: _ /\ _ |- _ => destruct H as [H ?] end;
    try discriminate; assumption.
Qed.

Lemma trl_at_mk_check G s c h b out : hold_ok G c h b -> i_mode s = CHECK -> at_check G s (8 * c - b) b out ->
  at_mode G s c h b out.
Proof. intros. unfold at_mode. cbv zeta. split; [auto|]. do 14 right. left. auto. Qed.

Lemma trl_at_mk_length G s c h b out : hold_ok G c h b -> i_mode s = LENGTH -> at_length G s (8 * c - b) b out ->
  at_mode G s c h b out.
Proof. intros. unfold at_mode. cbv zeta. split; [auto|]. do 15 right. left. auto. Qed.

Lemma trl_at_mk_done G s c h b out : hold_ok G c h b -> i_mode s = DONE -> at_done G s (8 * c - b) b out ->
  at_mode G s c h b out.
Proof. intros. unfold at_mode. cbv zeta. split; [auto|]. do 16 right. auto. Qed.

Lemma trl_glob G s s' : glob_ok G s ->
  i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_wbits s' = i_wbits s -> i_flags s' = i_flags s ->
  i_mode s <> HEAD -> i_mode s <> FLAGS -> i_mode s' <> HEAD -> i_mode s' <> FLAGS -> glob_ok G s'.
Proof.
  intros ((wb0 & R & _) & Hh & Hw & Hf) E1 E2 E3 E4 M1 M2 M3 M4.
  split; [exists wb0; rewrite E1; split; [exact R | intros; contradiction]|].
  rewrite E2, E3, E4. split; [exact Hh|]. split; [intros _; apply Hw; exact M1|].
  intros W _ _. apply Hf; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* DONE                                                                                           *)

Ltac trl_cbn := cbn [m_inp m_s m_h m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
  m_snx m_sow set_m_s set_m_h set_m_inp set_m_aout set_m_nx set_m_ow set_m_hold set_m_bits set_m_in set_m_out
  set_m_ret set_m_leave set_m_adler set_m_tout set_leave set_mode upd_s initbits trl_nb
  i_mode i_last i_wrap i_flags i_check i_total i_head i_wbits set_i_mode set_i_check set_i_total] in *.

Lemma trl_done G pos inp ob flush m0 m : Kd G pos inp ob m -> m_mode m = DONE -> m_ow m = m_ow m0 ->
  dstep_post G pos inp ob flush m0 (c_DONE m).
Proof.
  intros Kd Hm Ho. unfold c_DONE, dstep_post. destruct Kd as [K1 K2 K3 K4 K5 K6 K7 K8].
  unfold m_mode, m_left in *. trl_cbn.
  split; [|split; [exists []; rewrite app_nil_r; exact Ho | intros _; left; exact Hm]].
  constructor; unfold m_mode, m_left; trl_cbn; auto. rewrite Hm. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The check value and total                                                                      *)

Lemma trl_after G md : wrapped G = true -> md = LENGTH \/ md = DONE -> after_check G md = true.
Proof. intros W [E|E]; subst md; unfold after_check; rewrite W; reflexivity. Qed.

Lemma trl_not_after G md : md = CHECK -> after_check G md = false.
Proof. intros E; subst md; unfold after_check; destruct (wrapped G); reflexivity. Qed.

Lemma trl_chk_get G s ob ow : chk_ok G s ob ow -> wrapped G = true -> i_mode s = LENGTH \/ i_mode s = DONE ->
  i_check s = chkv G (produced G (ob ++ ow)) /\ i_total s = Zlength (produced G (ob ++ ow)) mod 2 ^ 64.
Proof.
  intros C W M. unfold chk_ok in C. cbv zeta in C.
  destruct M as [M|M]; rewrite M in C;
    (assert (X := C W ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate)));
    exact (conj (proj1 X) (proj1 (proj2 X))).
Qed.

Lemma trl_chk_get_check G s ob ow : chk_ok G s ob ow -> wrapped G = true -> i_mode s = CHECK ->
  i_check s = chkv G (produced G ob) /\ i_total s = Zlength (produced G ob) mod 2 ^ 64.
Proof.
  intros C W M. unfold chk_ok in C. cbv zeta in C. rewrite M in C.
  assert (X := C W ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate)).
  exact (conj (proj1 X) (proj1 (proj2 X))).
Qed.

Lemma trl_chk_mk G s ob ow : i_mode s = LENGTH \/ i_mode s = DONE ->
  i_check s = chkv G (produced G (ob ++ ow)) -> i_total s = Zlength (produced G (ob ++ ow)) mod 2 ^ 64 ->
  (exists d', ob = dc_hist G ++ d') ->
  chk_ok G s ob ow.
Proof.
  intros M C T P. unfold chk_ok. cbv zeta. intros. destruct M as [M|M]; rewrite M; split; [assumption| |assumption|];
    split; assumption.
Qed.

Lemma trl_chk_pre G s ob ow : chk_ok G s ob ow -> wrapped G = true ->
  i_mode s = CHECK \/ i_mode s = LENGTH \/ i_mode s = DONE -> exists d', ob = dc_hist G ++ d'.
Proof.
  intros C W M. unfold chk_ok in C. cbv zeta in C.
  destruct M as [M|[M|M]]; rewrite M in C;
    exact (proj2 (proj2 (C W ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate) ltac:(cbv; discriminate)))).
Qed.

Lemma trl_hold0 G c : 0 <= c -> c <= Zlength (dc_src G) -> hold_ok G c 0 0.
Proof.
  intros. unfold hold_ok. split; [lia|]. split; [lia|]. rewrite Z.sub_0_r, sublist_nil. reflexivity.
Qed.

Lemma trl_DONE_lt : ~ DONE < CHECK.
Proof. cbv. discriminate. Qed.
Lemma trl_LENGTH_lt : ~ LENGTH < CHECK.
Proof. cbv. discriminate. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENGTH (gzip): NEEDBITS(32), the length mod 2^32, DONE                                          *)

Lemma trl_length (K: dkit_stmt) G pos inp ob flush m0 m h :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  Kd G pos inp ob m -> 0 <= m_nx m <= Zlength (m_inp m) -> m_leave m = 0 -> m_mode m = LENGTH ->
  dc_w G = WGzip h -> m_ow m = m_ow m0 ->
  dstep_post G pos inp ob flush m0 (c_LENGTH m).
Proof.
  intros D Hp Hl Hi Kd Hn Hv Hm W Ho.
  pose proof Kd as Kd0. destruct Kd as [K1 K2 K3 K4 K5 K6 K7 K8].
  unfold m_mode, m_left in *.
  destruct (trl_at_get _ _ _ _ _ _ K2) as (Hh & _ & AL). specialize (AL Hm).
  destruct AL as (Ao & Al & Aq & A8 & Ab & Ax).
  assert (Wr: wrapped G = true) by (unfold wrapped; rewrite W; reflexivity).
  destruct (trl_wrap G _ D K3) as [_ Hw]. specialize (Hw Wr).
  assert (Hw0: i_wrap (m_s m) <> 0) by (intros E; rewrite E in Hw; apply Hw; reflexivity).
  destruct (trl_flags G _ K3) as [_ Hf]; try (rewrite Hm; cbv; discriminate). specialize (Hf h W).
  destruct (trl_trail_gzip G K h D W) as (E8 & Es & Esl & T1 & T2).
  destruct (trl_chk_get G _ ob (m_ow m) K5 Wr (or_introl Hm)) as [Ck Tt].
  pose proof (trl_chk_pre G _ ob (m_ow m) K5 Wr (or_intror (or_introl Hm))) as Pre.
  rewrite (trl_produced_gzip G h) in Ck, Tt by auto. rewrite Ao in Ck, Tt.
  assert (Hr: m_ret m = Z_OK) by (rewrite K8, Hm, Hv; reflexivity).
  rewrite trl_after in K6, K7 by auto.
  unfold c_LENGTH. cbv beta zeta.
  replace (negb (i_wrap (m_s m) =? 0) && negb (i_flags (m_s m) =? 0)) with true
    by (symmetry; apply andb_true_intro; split; apply negb_true_iff, Z.eqb_neq; auto).
  unfold needbits. rewrite (trl_needbits_frame 4 32 m).
  assert (Bs: bytes_ok (dc_src G)) by apply D.
  assert (I1: pos + Zlength (m_inp m) <= Zlength (dc_src G)) by (rewrite K1; lia).
  assert (I2: m_inp m = sublist pos (pos + Zlength (m_inp m)) (dc_src G)) by (rewrite K1; exact Hi).
  pose proof (proj1 Hh) as Hb0.
  assert (I3: 32 - m_bits m <= 8 * Z.of_nat 4) by (change (8 * Z.of_nat 4) with 32; lia).
  assert (I4: 0 <= m_bits m <= 32) by lia.
  destruct (trl_needbits_f G pos K 4 m Bs Hp I1 I2 Hn Hh A8 I4 I3 Hv) as (N1 & N2 & N3 & N4 & N5 & N6).
  set (N := needbits_f 4 32 m) in *.
  rewrite K1 in N5, N6.
  pose proof (proj1 (proj2 N2)) as Nc.
  destruct N6 as [(L1 & L2 & L3) | (L1 & L2)]; trl_cbn; rewrite L1; cbn [Z.eqb Pos.eqb].
  - unfold dstep_post. split; [|split].
    + constructor; unfold m_mode, m_left; trl_cbn.
      * exact K1.
      * apply trl_at_mk_length; auto. unfold at_length.
        refine (conj Ao (conj Al (conj _ (conj N4 (conj _ (ex_intro _ h W)))))); lia.
      * exact K3.
      * exact K4.
      * exact K5.
      * rewrite trl_after by auto. exact K6.
      * rewrite trl_after by auto. exact K7.
      * rewrite Hm, Hr. reflexivity.
    + exists []. trl_cbn. rewrite app_nil_r. exact Ho.
    + intros _. right; left. trl_cbn. split; lia.
  - assert (Hhold: m_hold N = Zlength (full G) mod 2 ^ 32).
    { destruct N2 as (_ & _ & H). rewrite H, L2.
      replace (8 * (pos + m_nx N) - 32) with (8 * (endpos G / 8 + 4)) by lia.
      replace (8 * (pos + m_nx N)) with (8 * (endpos G / 8 + 4) + 32) by lia.
      replace (endpos G / 8 + 8) with (endpos G / 8 + 4 + 4) in T2 by lia.
      rewrite (trl_bits32 G (endpos G / 8 + 4) _ ltac:(pose proof (trl_endpos_nonneg G); apply Z.add_nonneg_nonneg; [apply Z.div_pos|]; lia) ltac:(lia) T2 (trl_le_bytes_ok _ _)).
      rewrite trl_le4_val by (apply Z.mod_pos_bound; lia). apply Zmod_mod. }
    replace (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (m_hold N =? i_total (m_s m) mod 2 ^ 32)) with false.
    2:{ rewrite Hhold, Tt. rewrite (Znumtheory.Zmod_div_mod (2 ^ 32) (2 ^ 64)); [rewrite Z.eqb_refl, andb_false_r; reflexivity | lia | lia |].
        exists (2 ^ 32). reflexivity. }
    apply (trl_done G pos inp ob flush m0); [| reflexivity | trl_cbn; exact Ho].
    constructor; unfold m_mode, m_left; trl_cbn.
    + exact K1.
    + apply trl_at_mk_done; [apply trl_hold0; lia | reflexivity |].
      unfold at_done. refine (conj Ao (conj Al (conj _ eq_refl))). lia.
    + apply (trl_glob G (m_s m)); auto; try rewrite Hm; cbv; discriminate.
    + intros Hc. exfalso. exact (trl_DONE_lt Hc).
    + apply trl_chk_mk; [right; reflexivity | | | exact Pre]; trl_cbn; rewrite (trl_produced_gzip G h), Ao by auto; auto.
    + rewrite trl_after by auto. exact K6.
    + rewrite trl_after by auto. exact K7.
    + rewrite Hr. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CHECK, wrapped: after NEEDBITS(32) and the check update, the compare and LENGTH                *)

Lemma trl_is_bytes l : Forall byte_ok l -> Zlib.proof.adler32.Bytes.is_bytes l.
Proof.
  intros F. unfold Zlib.proof.adler32.Bytes.is_bytes. eapply Forall_impl; [|exact F].
  intros b Hb. unfold byte_ok in Hb. split; [lia|]. change (b <= 255). lia.
Qed.

Lemma trl_not_after_raw G md : wrapped G = false -> after_check G md = false.
Proof. intros W. unfold after_check. rewrite W. reflexivity. Qed.

Lemma trl_check_tail (K: dkit_stmt) G pos inp ob flush m0 M :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) -> wrapped G = true ->
  m_inp M = inp -> 0 <= m_nx M <= Zlength inp ->
  hold_ok G (pos + m_nx M) (m_hold M) (m_bits M) -> m_bits M = 32 -> 8 * (pos + m_nx M) - 32 = endpos G ->
  ob ++ m_ow M = full G -> i_last (m_s M) = 1 -> i_mode (m_s M) = CHECK -> glob_ok G (m_s M) ->
  i_check (m_s M) = chkv G (produced G (full G)) -> i_total (m_s M) = Zlength (produced G (full G)) mod 2 ^ 64 ->
  m_tout M = Zlength (produced G (full G)) mod 2 ^ 64 -> m_out M = m_left M -> m_ret M = Z_OK -> m_leave M = 0 ->
  m_ow M = m_ow m0 -> (exists d', ob = dc_hist G ++ d') ->
  dstep_post G pos inp ob flush m0
    (if negb (Z.land (i_wrap (m_s M)) 4 =? 0) &&
        negb ((if i_flags (m_s M) =? 0 then swap32 (m_hold M) else m_hold M) =? i_check (m_s M))
     then IBrk (set_bad M M_dcheck) else c_LENGTH (set_mode (initbits M) LENGTH)).
Proof.
  intros D Hp Hl Hi Wr Mi Mn Mh Mb Mq Mo Ml Mm Mg Mc Mt Mtout Mout Mr Mv Mow Pre.
  destruct (trl_wrap G _ D Mg) as [_ Hw]. specialize (Hw Wr).
  assert (Hw0: i_wrap (m_s M) <> 0) by (intros E; rewrite E in Hw; apply Hw; reflexivity).
  destruct (trl_flags G _ Mg) as [Hz Hg]; try (rewrite Mm; cbv; discriminate).
  pose proof (proj1 (proj2 Mh)) as Mc'.
  destruct Mh as (_ & _ & Mhv). rewrite Mb in Mhv.
  pose proof (trl_endpos_nonneg G) as Ep.
  unfold wrapped in Wr. destruct (dc_w G) as [|wb fl did|h] eqn:W; try discriminate.
  - (* zlib *)
    rewrite (Hz wb fl did eq_refl). cbn [Z.eqb].
    destruct (trl_trail_zlib G K wb fl did D W) as (E8 & Es & Esl & T).
    assert (Hv: m_hold M = trl_le (be_bytes (ref_adler32 1 (produced G (full G))) 4)).
    { rewrite Mhv. replace (8 * (pos + m_nx M) - 32) with (8 * (endpos G / 8)) by lia.
      replace (8 * (pos + m_nx M)) with (8 * (endpos G / 8) + 32) by lia.
      apply trl_bits32; [apply Z.div_pos; lia | lia | exact T | apply trl_be_bytes_ok]. }
    assert (Va: adler_valid (ref_adler32 1 (produced G (full G))))
      by (apply ref_adler32_valid; unfold adler_valid, adler_lo, adler_hi, ADLER_BASE; cbv; repeat split; congruence).
    rewrite Hv, trl_be4_swap by (destruct Va; lia).
    unfold chkv in Mc. rewrite W in Mc. rewrite Mc, Z.eqb_refl, andb_false_r.
    unfold c_LENGTH. cbv beta zeta. trl_cbn. rewrite (Hz wb fl did eq_refl). cbn [Z.eqb]. rewrite andb_false_r.
    apply (trl_done G pos inp ob flush m0); [| reflexivity | trl_cbn; exact Mow].
    constructor; unfold m_mode, m_left; trl_cbn.
    + exact Mi.
    + apply trl_at_mk_done; [apply trl_hold0; lia | reflexivity |].
      unfold at_done. refine (conj Mo (conj Ml (conj _ eq_refl))). lia.
    + apply (trl_glob G (m_s M)); auto; try rewrite Mm; cbv; discriminate.
    + intros Hc. exfalso. exact (trl_DONE_lt Hc).
    + apply trl_chk_mk; [right; reflexivity | | | exact Pre]; trl_cbn; rewrite Mo; auto.
      unfold chkv. rewrite W. exact Mc.
    + rewrite trl_after by (auto; unfold wrapped; rewrite W; reflexivity).
      rewrite Mo. exact Mtout.
    + rewrite trl_after by (auto; unfold wrapped; rewrite W; reflexivity). exact Mout.
    + rewrite Mr, Mv. reflexivity.
  - (* gzip *)
    rewrite (trl_produced_gzip G h) in Mc, Mt, Mtout by auto.
    specialize (Hg h eq_refl). destruct (i_flags (m_s M) =? 0) eqn:Ef; [apply Z.eqb_eq in Ef; contradiction|].
    destruct (trl_trail_gzip G K h D W) as (E8 & Es & Esl & T1 & T2).
    assert (Hv: m_hold M = trl_le (le_bytes (ref_crc32 0 (full G)) 4)).
    { rewrite Mhv. replace (8 * (pos + m_nx M) - 32) with (8 * (endpos G / 8)) by lia.
      replace (8 * (pos + m_nx M)) with (8 * (endpos G / 8) + 32) by lia.
      apply trl_bits32; [apply Z.div_pos; lia | lia | exact T1 | apply trl_le_bytes_ok]. }
    pose proof (Zlib.proof.crc32.Combine.ref_crc32_range 0 (full G) (trl_is_bytes _ (trl_full_bytes G D))) as Rc.
    unfold Zlib.proof.crc32.GF2.is32 in Rc.
    rewrite Hv, trl_le4_val, Z.mod_small by lia.
    unfold chkv in Mc. rewrite W in Mc. rewrite Mc, Z.eqb_refl, andb_false_r.
    assert (Wr': wrapped G = true) by (unfold wrapped; rewrite W; reflexivity).
    apply (trl_length K G pos inp ob flush m0 _ h); auto; trl_cbn; auto; try lia.
    constructor; unfold m_mode, m_left; trl_cbn.
    + exact Mi.
    + apply trl_at_mk_length; [apply trl_hold0; lia | reflexivity |].
      unfold at_length. refine (conj Mo (conj Ml (conj _ (conj eq_refl (conj _ (ex_intro _ h W)))))); lia.
    + apply (trl_glob G (m_s M)); auto; try rewrite Mm; cbv; discriminate.
    + intros Hc. exfalso. exact (trl_LENGTH_lt Hc).
    + apply trl_chk_mk; [left; reflexivity | | | exact Pre]; trl_cbn; rewrite (trl_produced_gzip G h), Mo by auto; auto.
      unfold chkv. rewrite W. exact Mc.
    + rewrite trl_after by auto. rewrite (trl_produced_gzip G h), Mo by auto. exact Mtout.
    + rewrite trl_after by auto. exact Mout.
    + rewrite Mr, Mv. reflexivity.
    + rewrite Mi. lia.
Qed.

(* CHECK after NEEDBITS(32): the state before the compare *)
Definition trl_m5 (m: mst) : mst :=
    let out := u32 (m_out m - m_left m) in
    let m := set_m_tout m (u64 (m_tout m + out)) in
    let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
    let m := if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
               let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                          (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
               set_m_adler (upd_s m (fun s => set_i_check s c)) c
             else m in
    set_m_out m (m_left m).

Definition trl_tail (M: mst) : iout :=
  if negb (Z.land (i_wrap (m_s M)) 4 =? 0) &&
     negb ((if i_flags (m_s M) =? 0 then swap32 (m_hold M) else m_hold M) =? i_check (m_s M))
  then IBrk (set_bad M M_dcheck) else c_LENGTH (set_mode (initbits M) LENGTH).

Lemma trl_check_eq m : c_CHECK m =
  if negb (i_wrap (m_s m) =? 0) then
    (let m1 := needbits 32 m in if m_leave m1 =? 1 then IBrk m1 else trl_tail (trl_m5 m1))
  else c_LENGTH (set_mode m LENGTH).
Proof. reflexivity. Qed.

Lemma trl_m5_fields m :
  let out := u32 (m_out m - m_left m) in
  let M := trl_m5 m in
  m_inp M = m_inp m /\ m_nx M = m_nx m /\ m_hold M = m_hold m /\ m_bits M = m_bits m /\ m_ow M = m_ow m /\
  m_aout M = m_aout m /\ m_leave M = m_leave m /\ m_ret M = m_ret m /\ m_out M = m_left M /\
  m_tout M = u64 (m_tout m + out) /\
  i_mode (m_s M) = i_mode (m_s m) /\ i_last (m_s M) = i_last (m_s m) /\ i_wrap (m_s M) = i_wrap (m_s m) /\
  i_head (m_s M) = i_head (m_s m) /\ i_wbits (m_s M) = i_wbits (m_s m) /\ i_flags (m_s M) = i_flags (m_s m) /\
  i_total (m_s M) = u64 (i_total (m_s m) + out) /\
  i_check (m_s M) = (if negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0) then
                       update_check (i_flags (m_s m)) (i_check (m_s m))
                         (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m))
                     else i_check (m_s m)).
Proof.
  unfold trl_m5. cbv zeta. unfold m_left. trl_cbn.
  match goal with |- context [if ?c then _ else _] => destruct c end; trl_cbn;
    repeat match goal with |- _ /\ _ => split end; reflexivity.
Qed.

Lemma trl_adler1 : adler_valid 1.
Proof. unfold adler_valid, adler_lo, adler_hi, ADLER_BASE. cbv. repeat split; congruence. Qed.

Lemma trl_update G flags ob ow : wrapped G = true -> Forall byte_ok (ob ++ ow) ->
  (forall wb fl did, dc_w G = WZlib wb fl did -> flags = 0) -> (forall h, dc_w G = WGzip h -> flags <> 0) ->
  update_check flags (chkv G ob) ow = chkv G (ob ++ ow).
Proof.
  intros Wr F Hz Hg. unfold update_check, chkv. unfold wrapped in Wr.
  destruct (dc_w G) as [|wb fl did|h] eqn:W; try discriminate.
  - rewrite (Hz wb fl did eq_refl), Z.eqb_refl.
    rewrite adler32_z_val_ref by (apply ref_adler32_valid, trl_adler1).
    apply ref_adler32_app, trl_adler1.
  - specialize (Hg h eq_refl). destruct (flags =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. apply trl_is_bytes.
    apply Forall_app in F. apply F.
Qed.

Lemma trl_wrapped_place G (K: dkit_stmt) : dctx_ok G -> wrapped G = true ->
  endpos G = 8 * (endpos G / 8) /\ endpos G / 8 + 4 <= slen G /\ slen G <= Zlength (dc_src G).
Proof.
  intros D Wr. unfold wrapped in Wr. destruct (dc_w G) as [|wb fl did|h] eqn:W; try discriminate.
  - destruct (trl_trail_zlib G K wb fl did D W) as (A & B & C & _). lia.
  - destruct (trl_trail_gzip G K h D W) as (A & B & C & _). lia.
Qed.

Lemma trl_check_wr (K: dkit_stmt) G pos inp ob flush m :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> m_mode m = CHECK -> wrapped G = true ->
  dstep_post G pos inp ob flush m (c_CHECK m).
Proof.
  intros D Hp Hl Hi Kd Mw Hv Hm Wr.
  pose proof (mw_nx _ (mwf3_mwf _ Mw)) as Hn. pose proof (mw_ow _ (mwf3_mwf _ Mw)) as [How _].
  pose proof (mw_aout _ (mwf3_mwf _ Mw)) as Hao.
  destruct Kd as [K1 K2 K3 K4 K5 K6 K7 K8].
  unfold m_mode, m_left in *.
  destruct (trl_at_get _ _ _ _ _ _ K2) as (Hh & AC & _). specialize (AC Hm).
  destruct AC as (Ao & Al & Aq & A8 & Ab & Ax).
  destruct (trl_wrap G _ D K3) as [_ Hw]. specialize (Hw Wr).
  assert (Hw0: i_wrap (m_s m) <> 0) by (intros E; rewrite E in Hw; apply Hw; reflexivity).
  destruct (trl_flags G _ K3) as [Hz Hg]; try (rewrite Hm; cbv; discriminate).
  destruct (trl_chk_get_check G _ ob (m_ow m) K5 Wr Hm) as [Ck Tt].
  pose proof (trl_chk_pre G _ ob (m_ow m) K5 Wr (or_introl Hm)) as Pre.
  rewrite trl_not_after in K6, K7 by auto.
  assert (Hr: m_ret m = Z_OK) by (rewrite K8, Hm, Hv; reflexivity).
  destruct (trl_wrapped_place G K D Wr) as (E8 & Es & Esl).
  rewrite trl_check_eq.
  replace (negb (i_wrap (m_s m) =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; auto).
  cbv beta zeta.
  unfold needbits. rewrite (trl_needbits_frame 4 32 m).
  assert (Bs: bytes_ok (dc_src G)) by apply D.
  assert (I1: pos + Zlength (m_inp m) <= Zlength (dc_src G)) by (rewrite K1; lia).
  assert (I2: m_inp m = sublist pos (pos + Zlength (m_inp m)) (dc_src G)) by (rewrite K1; exact Hi).
  pose proof (proj1 Hh) as Hb0.
  assert (I3: 32 - m_bits m <= 8 * Z.of_nat 4) by (change (8 * Z.of_nat 4) with 32; lia).
  assert (I4: 0 <= m_bits m <= 32) by lia.
  destruct (trl_needbits_f G pos K 4 m Bs Hp I1 I2 Hn Hh A8 I4 I3 Hv) as (N1 & N2 & N3 & N4 & N5 & N6).
  set (N := needbits_f 4 32 m) in *.
  rewrite K1 in N5, N6.
  pose proof (proj1 (proj2 N2)) as Nc.
  destruct N6 as [(L1 & L2 & L3) | (L1 & L2)].
  - cbn [m_leave trl_nb set_m_leave]. rewrite L1. cbn [Z.eqb Pos.eqb].
    unfold dstep_post. split; [|split].
    + constructor; unfold m_mode, m_left; trl_cbn.
      * exact K1.
      * apply trl_at_mk_check; auto. unfold at_check.
        refine (conj Ao (conj Al (conj _ (conj N4 (conj _ _))))); [lia | lia | congruence].
      * exact K3.
      * exact K4.
      * exact K5.
      * rewrite trl_not_after by auto. exact K6.
      * rewrite trl_not_after by auto. exact K7.
      * rewrite Hm, Hr. reflexivity.
    + exists []. trl_cbn. rewrite app_nil_r. reflexivity.
    + intros _. right; left. trl_cbn. split; lia.
  - cbn [m_leave trl_nb set_m_leave]. rewrite L1. cbn [Z.eqb Pos.eqb].
    destruct (trl_m5_fields (trl_nb m (m_nx N) (m_hold N) (m_bits N) 0)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 &
                                    F15 & F16 & F17 & F18).
    cbv zeta in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18.
    unfold m_left in F10, F17, F18.
    cbn [trl_nb m_inp m_nx m_hold m_bits m_ow m_aout m_leave m_ret m_out m_tout m_s set_m_leave set_m_bits
         set_m_hold set_m_nx] in F1, F2, F3, F4, F5, F6, F7, F8, F10, F11, F12, F13, F14, F15, F16, F17, F18.
    assert (Out: u32 (m_out m - (m_aout m - Zlength (m_ow m))) = Zlength (m_ow m)).
    { rewrite K7. unfold u32. rewrite Z.mod_small; [lia|]. pose proof (Zlength_nonneg (m_ow m)).
      change compcert.lib.Integers.Int.max_signed with 2147483647 in Hao. lia. }
    rewrite Out in F10, F17, F18.
    set (M := trl_m5 (trl_nb m (m_nx N) (m_hold N) (m_bits N) 0)) in *.
    assert (A1: m_inp M = inp) by congruence.
    assert (A2: 0 <= m_nx M <= Zlength inp) by (rewrite F2; lia).
    assert (A3: hold_ok G (pos + m_nx M) (m_hold M) (m_bits M)) by (rewrite F2, F3, F4; exact N2).
    assert (A4: m_bits M = 32) by congruence.
    assert (A5: 8 * (pos + m_nx M) - 32 = endpos G) by (rewrite F2; lia).
    assert (A6: ob ++ m_ow M = full G) by (rewrite F5; exact Ao).
    assert (A7: i_last (m_s M) = 1) by congruence.
    assert (A8': i_mode (m_s M) = CHECK) by congruence.
    assert (A9: glob_ok G (m_s M))
      by (apply (trl_glob G (m_s m)); auto; try congruence; try rewrite F11; try rewrite Hm; cbv; discriminate).
    assert (A10: i_check (m_s M) = chkv G (produced G (full G))).
    { rewrite F18, Ck, <- Ao.
      destruct (Zlength (m_ow m) =? 0) eqn:Eo.
      - apply Z.eqb_eq, Zlength_nil_inv in Eo. rewrite Eo, app_nil_r, andb_false_r. reflexivity.
      - rewrite andb_true_r. replace (negb (Z.land (i_wrap (m_s m)) 4 =? 0)) with true
          by (symmetry; apply negb_true_iff, Z.eqb_neq; auto).
        rewrite Z.sub_diag, sublist_same by lia.
        rewrite (trl_produced_app G ob (m_ow m) Pre). apply trl_update; auto.
        rewrite <- (trl_produced_app G ob (m_ow m) Pre), Ao. apply trl_produced_bytes, trl_full_bytes, D. }
    assert (A11: i_total (m_s M) = Zlength (produced G (full G)) mod 2 ^ 64)
      by (rewrite F17, Tt, <- Ao, (trl_produced_app G ob (m_ow m) Pre), Zlength_app; unfold u64; rewrite Zplus_mod_idemp_l; reflexivity).
    assert (A12: m_tout M = Zlength (produced G (full G)) mod 2 ^ 64)
      by (rewrite F10, K6, <- Ao, (trl_produced_app G ob (m_ow m) Pre), Zlength_app; unfold u64; rewrite Zplus_mod_idemp_l; reflexivity).
    assert (A13: m_ret M = Z_OK) by congruence.
    exact (trl_check_tail K G pos inp ob flush m M D Hp Hl Hi Wr A1 A2 A3 A4 A5 A6 A7 A8' A9 A10 A11 A12 F9 A13 F7 F5 Pre).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CHECK, raw: straight to LENGTH and DONE                                                        *)

Lemma trl_check_raw (K: dkit_stmt) G pos inp ob flush m :
  dctx_ok G -> Kd G pos inp ob m -> m_leave m = 0 -> m_mode m = CHECK -> dc_w G = WRaw -> m_bits m = 0 ->
  dstep_post G pos inp ob flush m (c_CHECK m).
Proof.
  intros D Kd Hv Hm W Hb.
  destruct Kd as [K1 K2 K3 K4 K5 K6 K7 K8].
  unfold m_mode, m_left in *.
  destruct (trl_at_get _ _ _ _ _ _ K2) as (Hh & AC & _). specialize (AC Hm).
  destruct AC as (Ao & Al & Aq & A8 & Ab & Ax).
  assert (Wr: wrapped G = false) by (unfold wrapped; rewrite W; reflexivity).
  destruct (trl_wrap G _ D K3) as [Hw _]. specialize (Hw Wr).
  assert (Hr: m_ret m = Z_OK) by (rewrite K8, Hm, Hv; reflexivity).
  pose proof (trl_slen_raw G K D W) as Es.
  unfold c_CHECK. rewrite Hw. cbn [Z.eqb negb].
  unfold c_LENGTH. cbv beta zeta. trl_cbn. rewrite Hw. cbn [Z.eqb negb andb].
  apply (trl_done G pos inp ob flush m); [| reflexivity | reflexivity].
  constructor; unfold m_mode, m_left; trl_cbn.
  - exact K1.
  - apply trl_at_mk_done; [exact Hh | reflexivity |].
    unfold at_done. refine (conj Ao (conj Al (conj _ Hb))). lia.
  - apply (trl_glob G (m_s m)); auto; try rewrite Hm; cbv; discriminate.
  - intros Hc. exfalso. exact (trl_DONE_lt Hc).
  - unfold chk_ok. intros E. rewrite Wr in E. discriminate.
  - rewrite trl_not_after_raw by auto. rewrite trl_not_after_raw in K6 by auto. exact K6.
  - rewrite trl_not_after_raw by auto. rewrite trl_not_after_raw in K7 by auto. exact K7.
  - rewrite Hr, Hv. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The group, given the two facts of the invariant: raw at CHECK has an empty bit buffer, LENGTH  *)
(* is a loop head only for gzip                                                                   *)

Lemma trl_group_of (K: dkit_stmt)
  (RawCheck: forall G s q b out, at_check G s q b out -> wrapped G = false -> b = 0)
  (GzLength: forall G s q b out, at_length G s q b out -> exists h, dc_w G = WGzip h) :
  group_ok md_trl.
Proof.
  intros G pos inp ob flush m D Hp Hl Hi Kd Mw Hv Hmd.
  destruct Hmd as [Hm|[Hm|Hm]].
  - replace (stepf2 _ _ _ m) with (c_CHECK m) by (unfold stepf2, step2; rewrite Hm; reflexivity).
    destruct (wrapped G) eqn:Wr.
    + apply trl_check_wr; auto.
    + assert (W: dc_w G = WRaw) by (unfold wrapped in Wr; destruct (dc_w G); congruence).
      apply trl_check_raw; auto.
      destruct (trl_at_get _ _ _ _ _ _ (kd_at _ _ _ _ _ Kd)) as (_ & AC & _).
      exact (RawCheck _ _ _ _ _ (AC Hm) Wr).
  - replace (stepf2 _ _ _ m) with (c_LENGTH m) by (unfold stepf2, step2; rewrite Hm; reflexivity).
    destruct (trl_at_get _ _ _ _ _ _ (kd_at _ _ _ _ _ Kd)) as (_ & _ & AL).
    destruct (GzLength _ _ _ _ _ (AL Hm)) as [h W].
    apply (trl_length K G pos inp ob flush m m h); auto. apply (mw_nx _ (mwf3_mwf _ Mw)).
  - replace (stepf2 _ _ _ m) with (c_DONE m) by (unfold stepf2, step2; rewrite Hm; reflexivity).
    apply trl_done; auto.
Qed.

Lemma group_trl : dkit_stmt -> group_ok md_trl.
Proof.
  intros K. apply (trl_group_of K).
  - intros G s q b out A W. apply A, W.
  - intros G s q b out A. apply A.
Qed.

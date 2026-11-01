(* Part of the decode theory: the kit (bit buffer, layout of the input).  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Bits                                                                                           *)

Lemma dkit_bval_app : forall l1 l2, bval (l1 ++ l2) = bval l1 + 2 ^ Zlength l1 * bval l2.
Proof.
  induction l1 as [|b r IH]; intros l2; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia). lia.
Qed.

Lemma dkit_bval_bound : forall l, 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma dkit_bits_le_len : forall v n, 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma dkit_bits_le_bval : forall l, bits_le (bval l) (Zlength l) = l.
Proof.
  intros l. unfold bits_le. rewrite ZtoNat_Zlength.
  induction l as [|b r IH]; [reflexivity|].
  simpl length. cbn [seq map]. rewrite <- seq_shift, map_map. cbn [bval]. f_equal.
  - destruct b; simpl.
    + rewrite Z.add_comm. apply Z.testbit_odd_0.
    + rewrite Z.add_0_l. apply Z.testbit_even_0.
  - rewrite <- IH at 2. apply map_ext. intros i.
    rewrite Nat2Z.inj_succ. destruct b; simpl.
    + rewrite Z.add_comm. apply Z.testbit_odd_succ. lia.
    + rewrite Z.add_0_l. apply Z.testbit_even_succ. lia.
Qed.

Lemma dkit_bval_byte : forall b, 0 <= b < 256 -> bval (bits_le b 8) = b.
Proof.
  intros b Hb.
  assert (H: forallb (fun b => bval (bits_le b 8) =? b) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H b). rewrite Z.eqb_eq in H. apply H.
  replace b with (Z.of_nat (Z.to_nat b)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma dkit_bytes_bits_app : forall l1 l2, bytes_bits (l1 ++ l2) = bytes_bits l1 ++ bytes_bits l2.
Proof. intros. unfold bytes_bits. apply flat_map_app. Qed.

Lemma dkit_bytes_bits_len : forall l, Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity|].
  change (bytes_bits (b :: r)) with (bits_le b 8 ++ bytes_bits r). rewrite Zlength_app, IH, dkit_bits_le_len, Zlength_cons by lia. lia.
Qed.

(* the middle part of a concatenation *)
Lemma dkit_sublist_mid : forall {A} (X E Y: list A),
  sublist (Zlength X) (Zlength X + Zlength E) (X ++ E ++ Y) = E.
Proof.
  intros. rewrite sublist_app2 by (pose proof (Zlength_nonneg X); lia).
  rewrite sublist_app1 by (pose proof (Zlength_nonneg E); lia).
  apply sublist_same; lia.
Qed.

Lemma dkit_pack_aux : forall bs n n0 s, Zlength bs = 8 * n -> (s + n0 <= Z.to_nat n)%nat ->
  bytes_bits (map (fun k => bval (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) (seq s n0)) =
  sublist (8 * Z.of_nat s) (8 * Z.of_nat (s + n0)) bs.
Proof.
  intros bs n n0. induction n0 as [|n0 IH]; intros s Hl Hs.
  - rewrite Nat.add_0_r, sublist_nil. reflexivity.
  - cbn [seq map].
    match goal with |- bytes_bits (?x :: ?r) = _ => change (bytes_bits (x :: r)) with (bits_le x 8 ++ bytes_bits r) end.
    rewrite IH by lia.
    set (L := sublist (8 * Z.of_nat s) (8 * Z.of_nat s + 8) bs).
    assert (HL: Zlength L = 8) by (unfold L; rewrite Zlength_sublist; lia).
    pose proof (dkit_bits_le_bval L) as HB. rewrite HL in HB. rewrite HB. unfold L.
    replace (8 * Z.of_nat (S s)) with (8 * Z.of_nat s + 8) by lia.
    replace (S s + n0)%nat with (s + S n0)%nat by lia.
    apply sublist_rejoin; lia.
Qed.

Lemma dkit_pack_bits : forall bs, Zlength bs mod 8 = 0 -> bytes_bits (pack bs) = bs.
Proof.
  intros bs H. unfold pack. pose proof (Zlength_nonneg bs).
  set (n := Zlength bs / 8).
  assert (Hn: Zlength bs = 8 * n) by (unfold n; pose proof (Z.div_mod (Zlength bs) 8 ltac:(lia)); lia).
  replace ((Zlength bs + 7) / 8) with n.
  2: { rewrite Hn. replace (8 * n + 7) with (7 + n * 8) by ring. rewrite Z.div_add by lia. reflexivity. }
  rewrite (dkit_pack_aux bs n (Z.to_nat n) 0) by lia.
  apply sublist_same; lia.
Qed.

Lemma dkit_pack_len : forall bs, Zlength (pack bs) = (Zlength bs + 7) / 8.
Proof.
  intros. unfold pack. rewrite Zlength_map, Zlength_correct, seq_length.
  pose proof (Zlength_nonneg bs). rewrite Z2Nat.id; [lia|].
  apply Z.div_pos; lia.
Qed.

Lemma dkit_sublist_pre : forall {A} (E Y: list A), sublist 0 (Zlength E) (E ++ Y) = E.
Proof.
  intros. rewrite sublist_app1 by (pose proof (Zlength_nonneg E); lia). apply sublist_same; lia.
Qed.

Lemma dkit_bytes_bits_sublist : forall l a b, 0 <= a <= b -> b <= Zlength l ->
  sublist (8 * a) (8 * b) (bytes_bits l) = bytes_bits (sublist a b l).
Proof.
  intros l a b Ha Hb.
  rewrite <- (sublist_same 0 (Zlength l) l) at 1 by lia.
  rewrite <- (sublist_rejoin 0 a (Zlength l)) by lia.
  rewrite <- (sublist_rejoin a b (Zlength l)) by lia.
  rewrite !dkit_bytes_bits_app.
  replace (8 * a) with (Zlength (bytes_bits (sublist 0 a l))) by (rewrite dkit_bytes_bits_len, Zlength_sublist; lia).
  replace (8 * b) with (Zlength (bytes_bits (sublist 0 a l)) + Zlength (bytes_bits (sublist a b l)))
    by (rewrite !dkit_bytes_bits_len, !Zlength_sublist; lia).
  apply dkit_sublist_mid.
Qed.

Lemma dkit_bval_sub_bound : forall (l: list bool) lo hi, 0 <= lo <= hi -> hi <= Zlength l ->
  0 <= bval (sublist lo hi l) < 2 ^ (hi - lo).
Proof.
  intros. rewrite <- (Zlength_sublist lo hi l) by lia. apply dkit_bval_bound.
Qed.

Lemma dkit_pad8 : forall e, (e + pad8 e) mod 8 = 0 /\ 0 <= pad8 e < 8.
Proof.
  intros. unfold pad8. pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
  destruct (Z.eq_dec (e mod 8) 0) as [E|E].
  - rewrite E. replace ((8 - 0) mod 8) with 0 by reflexivity. rewrite Z.add_0_r, E. lia.
  - rewrite (Z.mod_small (8 - e mod 8) 8) by lia.
    replace (e + (8 - e mod 8)) with ((e / 8 + 1) * 8) by lia. rewrite Z.mod_mul by lia. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Blocks                                                                                         *)

Lemma dkit_enc_block_len : forall p f1 f2 b, Zlength (enc_block p f1 b) = Zlength (enc_block p f2 b).
Proof. intros. unfold enc_block. rewrite !Zlength_cons. reflexivity. Qed.

Lemma dkit_enc_blocks_cons : forall p b r,
  enc_blocks p (b :: r) =
  enc_block p (match r with [] => true | _ => false end) b ++
  enc_blocks (p + Zlength (enc_block p false b)) r.
Proof.
  intros. cbn [enc_blocks]. rewrite (dkit_enc_block_len p _ false). reflexivity.
Qed.

Lemma dkit_epos_split : forall k bs p, (k <= length bs)%nat ->
  exists A, enc_blocks p bs = A ++ enc_blocks (epos p bs k) (skipn k bs) /\ Zlength A = epos p bs k - p.
Proof.
  induction k as [|k IH]; intros bs p H.
  - exists []. assert (E: epos p bs 0 = p) by (destruct bs; reflexivity). rewrite E.
    split; [reflexivity|]. rewrite Zlength_nil. lia.
  - destruct bs as [|b r]; [simpl in H; lia|]. simpl in H.
    destruct (IH r (p + Zlength (enc_block p false b))) as [A [HA HL]]; [lia|].
    exists (enc_block p (match r with [] => true | _ => false end) b ++ A).
    cbn [epos skipn]. split.
    + rewrite dkit_enc_blocks_cons, HA, app_assoc. reflexivity.
    + rewrite Zlength_app, HL, (dkit_enc_block_len p _ false). lia.
Qed.

Lemma dkit_epos_S : forall k bs p d, (k < length bs)%nat ->
  epos p bs (S k) = epos p bs k + Zlength (enc_block (epos p bs k) false (nth k bs d)).
Proof.
  induction k as [|k IH]; intros bs p d H; destruct bs as [|b r]; simpl in H; try lia.
  - cbn [epos nth]. destruct r; reflexivity.
  - cbn [epos nth]. apply IH. lia.
Qed.

Lemma dkit_epos_end : forall bs p, epos p bs (length bs) = p + Zlength (enc_blocks p bs).
Proof.
  intros. destruct (dkit_epos_split (length bs) bs p) as [A [HA HL]]; [lia|].
  rewrite skipn_all in HA. cbn [enc_blocks] in HA. rewrite app_nil_r in HA. rewrite HA. lia.
Qed.

Lemma dkit_skipn_nth : forall {A} k (l: list A) d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction k as [|k IH]; intros l d H; destruct l as [|a l]; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma dkit_flag : forall {A} k (l: list A), (k < length l)%nat ->
  (match skipn (S k) l with [] => true | _ => false end) = Nat.eqb (S k) (length l).
Proof.
  intros A k l H. pose proof (skipn_length l (S k)) as HL.
  destruct (skipn (S k) l); simpl in HL; symmetry.
  - apply Nat.eqb_eq. lia.
  - apply Nat.eqb_neq. lia.
Qed.

Lemma dkit_enc_blocks_at : forall bs p k d, (k < length bs)%nat ->
  exists A B, enc_blocks p bs = A ++ enc_block (epos p bs k) (Nat.eqb (S k) (length bs)) (nth k bs d) ++ B /\
  Zlength A = epos p bs k - p.
Proof.
  intros bs p k d H.
  destruct (dkit_epos_split k bs p) as [A [HA HL]]; [lia|].
  rewrite (dkit_skipn_nth k bs d H), dkit_enc_blocks_cons, (dkit_flag k bs H) in HA.
  eexists A, _. split; [exact HA | exact HL].
Qed.

Lemma dkit_firstn_S : forall {A} n (l: list A) d, (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n as [|n IH]; intros l d H; destruct l as [|a l]; simpl in *; try lia; auto.
  f_equal. apply IH. lia.
Qed.

Lemma dkit_lz_ext : forall n dist out, exists r, lz_copy n dist out = out ++ r.
Proof.
  induction n as [|n IH]; intros dist out; cbn [lz_copy].
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IH dist (out ++ [Znth (Zlength out - dist) out])) as [r Hr].
    rewrite Hr, <- app_assoc. eexists; reflexivity.
Qed.

Lemma dkit_syms_ext : forall syms out, exists r, fold_left sym_data syms out = out ++ r.
Proof.
  induction syms as [|s syms IH]; intros out; cbn [fold_left].
  - exists []. rewrite app_nil_r. reflexivity.
  - assert (Hs: exists r, sym_data out s = out ++ r).
    { destruct s; cbn [sym_data]; [eexists; reflexivity | apply dkit_lz_ext]. }
    destruct Hs as [r1 H1]. destruct (IH (sym_data out s)) as [r2 H2].
    rewrite H2, H1, <- app_assoc. eexists; reflexivity.
Qed.

Lemma dkit_fold_ext : forall bs out, exists r, fold_left block_data bs out = out ++ r.
Proof.
  induction bs as [|b bs IH]; intros out; cbn [fold_left].
  - exists []. rewrite app_nil_r. reflexivity.
  - assert (Hb: exists r, block_data out b = out ++ r).
    { destruct b; cbn [block_data]; [eexists; reflexivity | apply dkit_syms_ext | apply dkit_syms_ext]. }
    destruct Hb as [r1 H1]. destruct (IH (block_data out b)) as [r2 H2].
    rewrite H2, H1, <- app_assoc. eexists; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream                                                                                     *)

Definition dkit_trl (w: wrapper) (d: list Z) : list Z :=
  match w with
  | WRaw => []
  | WZlib _ _ _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 d) 4
  | WGzip _ => le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 d) 4 ++ le_bytes (Zlength d mod 2 ^ 32) 4
  end.

Lemma dkit_stream_split : forall w hist bs,
  stream_bytes w hist bs = hdr_bytes w ++ deflate_bytes bs ++ dkit_trl w (data hist bs).
Proof.
  intros. unfold stream_bytes, hdr_bytes, dkit_trl. destruct w; cbn zeta.
  - rewrite app_nil_r. reflexivity.
  - rewrite <- !app_assoc. reflexivity.
  - reflexivity.
Qed.

Lemma dkit_src : forall G, dctx_ok G -> exists R,
  dc_src G = hdr_bytes (dc_w G) ++ deflate_bytes (dc_bs G) ++ dkit_trl (dc_w G) (data (dc_hist G) (dc_bs G)) ++ R.
Proof.
  intros G (_ & _ & _ & _ & Hs & _ & _ & Heq).
  exists (sublist (slen G) (Zlength (dc_src G)) (dc_src G)).
  rewrite <- (sublist_same 0 (Zlength (dc_src G)) (dc_src G)) at 1 by lia.
  assert (0 <= slen G) by (unfold slen; apply Zlength_nonneg).
  rewrite <- (sublist_rejoin 0 (slen G) (Zlength (dc_src G))) by lia.
  rewrite Heq, dkit_stream_split, <- !app_assoc. reflexivity.
Qed.

Lemma dkit_deflate_bits_len : forall bs,
  Zlength (deflate_bits bs) = Zlength (enc_blocks 0 bs) + pad8 (Zlength (enc_blocks 0 bs)) /\
  Zlength (deflate_bits bs) mod 8 = 0.
Proof.
  intros. unfold deflate_bits. rewrite Zlength_app. unfold zeros.
  pose proof (dkit_pad8 (Zlength (enc_blocks 0 bs))).
  rewrite Zlength_repeat by lia. lia.
Qed.

Lemma dkit_sbits : forall G, dctx_ok G -> exists R,
  sbits G = bytes_bits (hdr_bytes (dc_w G)) ++ deflate_bits (dc_bs G) ++ R.
Proof.
  intros G HG. destruct (dkit_src G HG) as [R HR].
  unfold sbits. rewrite HR, !dkit_bytes_bits_app. unfold deflate_bytes.
  rewrite dkit_pack_bits by apply dkit_deflate_bits_len.
  eexists. reflexivity.
Qed.

Lemma dkit_sbits_len : forall G, Zlength (sbits G) = 8 * Zlength (dc_src G).
Proof. intros. apply dkit_bytes_bits_len. Qed.

Lemma dkit_D0_len : forall G, D0 G = Zlength (bytes_bits (hdr_bytes (dc_w G))).
Proof. intros. unfold D0. rewrite dkit_bytes_bits_len. reflexivity. Qed.

Lemma dkit_div8 : forall L, L mod 8 = 0 -> (L + 7) / 8 = L / 8 /\ L = 8 * (L / 8).
Proof.
  intros L H. pose proof (Z.div_mod L 8 ltac:(lia)) as E. split; [|lia].
  rewrite E at 1. rewrite H. replace (8 * (L / 8) + 0 + 7) with (7 + L / 8 * 8) by ring.
  rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma dkit : dkit_stmt.
Proof.
  constructor.
  - (* dk_pull *)
    intros G c hold bits [Hb [Hc Hh]] Hlt H64 Hbytes.
    pose proof (dkit_sbits_len G) as HS.
    split; [lia | split; [lia |]].
    replace (8 * (c + 1) - (bits + 8)) with (8 * c - bits) by lia.
    rewrite (sublist_split (8 * c - bits) (8 * c) (8 * (c + 1))) by lia.
    rewrite dkit_bval_app, <- Hh, Zlength_sublist by lia.
    unfold sbits. rewrite dkit_bytes_bits_sublist by lia. rewrite sublist_len_1 by lia.
    change (bytes_bits [Znth c (dc_src G)]) with (bits_le (Znth c (dc_src G)) 8 ++ []).
    rewrite app_nil_r.
    assert (HB: 0 <= Znth c (dc_src G) <= 255).
    { pose proof (Forall_Znth _ (dc_src G) c ltac:(lia) Hbytes) as X. cbv beta in X.
      assert (compcert.lib.Integers.Byte.max_unsigned = 255) by reflexivity. lia. }
    rewrite dkit_bval_byte by lia.
    replace (8 * c - (8 * c - bits)) with bits by lia.
    pose proof (dkit_bval_sub_bound (sbits G) (8 * c - bits) (8 * c) ltac:(lia) ltac:(lia)) as X.
    rewrite <- Hh in X. replace (8 * c - (8 * c - bits)) with bits in X by lia.
    assert (P: 2 ^ (bits + 8) = 2 ^ bits * 256) by (rewrite Z.pow_add_r by lia; reflexivity).
    assert (P2: 2 ^ (bits + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    assert (P3: 2 ^ bits * Znth c (dc_src G) <= 2 ^ bits * 255) by (apply Z.mul_le_mono_nonneg_l; lia).
    rewrite Z.mod_small by nia. ring.
  - (* dk_bitsn *)
    intros G c hold bits n [Hb [Hc Hh]] Hn.
    pose proof (dkit_sbits_len G) as HS.
    rewrite Hh, (sublist_split (8 * c - bits) (8 * c - bits + n) (8 * c)) by lia.
    rewrite dkit_bval_app, Zlength_sublist by lia.
    replace (8 * c - bits + n - (8 * c - bits)) with n by lia.
    pose proof (dkit_bval_sub_bound (sbits G) (8 * c - bits) (8 * c - bits + n) ltac:(lia) ltac:(lia)) as X.
    replace (8 * c - bits + n - (8 * c - bits)) with n in X by lia.
    rewrite (Z.mul_comm (2 ^ n)), Z_mod_plus_full, Z.mod_small by lia. reflexivity.
  - (* dk_drop *)
    intros G c hold bits n [Hb [Hc Hh]] Hn.
    pose proof (dkit_sbits_len G) as HS.
    split; [lia | split; [lia |]].
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Hh, (sublist_split (8 * c - bits) (8 * c - bits + n) (8 * c)) by lia.
    rewrite dkit_bval_app, Zlength_sublist by lia.
    replace (8 * c - bits + n - (8 * c - bits)) with n by lia.
    pose proof (dkit_bval_sub_bound (sbits G) (8 * c - bits) (8 * c - bits + n) ltac:(lia) ltac:(lia)) as X.
    replace (8 * c - bits + n - (8 * c - bits)) with n in X by lia.
    rewrite (Z.mul_comm (2 ^ n)), Z.div_add by lia. rewrite (Z.div_small _ (2 ^ n)) by lia.
    replace (8 * c - (bits - n)) with (8 * c - bits + n) by lia. ring.
  - (* dk_hold_lt *)
    intros G c hold bits [Hb [Hc Hh]] _.
    pose proof (dkit_sbits_len G).
    pose proof (dkit_bval_sub_bound (sbits G) (8 * c - bits) (8 * c) ltac:(lia) ltac:(lia)) as X.
    rewrite <- Hh in X. replace (8 * c - (8 * c - bits)) with bits in X by lia. exact X.
  - (* dk_hdr *)
    intros G HG. destruct (dkit_sbits G HG) as [R HR]. rewrite HR, dkit_D0_len. apply dkit_sublist_pre.
  - (* dk_deflate *)
    intros G HG. destruct (dkit_sbits G HG) as [R HR]. rewrite HR. unfold endpos. rewrite dkit_D0_len.
    apply dkit_sublist_mid.
  - (* dk_blk *)
    intros G k HG Hk. unfold nblk in Hk. unfold bpos, blk, lastflag, nblk.
    assert (Hn: (Z.to_nat k < length (dc_bs G))%nat) by (rewrite <- ZtoNat_Zlength; apply Z2Nat.inj_lt; lia).
    replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by (rewrite Z2Nat.inj_add by lia; simpl; lia).
    rewrite (dkit_epos_S _ _ 0 (Stored []) Hn).
    replace (D0 G + epos 0 (dc_bs G) (Z.to_nat k) - D0 G) with (epos 0 (dc_bs G) (Z.to_nat k)) by ring.
    replace ((if k =? Zlength (dc_bs G) - 1 then 1 else 0) =? 1) with (Nat.eqb (S (Z.to_nat k)) (length (dc_bs G))).
    2: { rewrite <- ZtoNat_Zlength.
         destruct (Z.eqb_spec k (Zlength (dc_bs G) - 1));
         destruct (Nat.eqb_spec (S (Z.to_nat k)) (Z.to_nat (Zlength (dc_bs G)))); simpl; auto; lia. }
    rewrite (dkit_enc_block_len _ false (Nat.eqb (S (Z.to_nat k)) (length (dc_bs G)))). split; [ring|].
    destruct (dkit_sbits G HG) as [R HR].
    destruct (dkit_enc_blocks_at (dc_bs G) 0 (Z.to_nat k) (Stored []) Hn) as [A [B [HE HA]]].
    replace (D0 G + (epos 0 (dc_bs G) (Z.to_nat k) +
              Zlength (enc_block (epos 0 (dc_bs G) (Z.to_nat k)) (S (Z.to_nat k) =? length (dc_bs G))%nat
                 (nth (Z.to_nat k) (dc_bs G) (Stored [])))))
      with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ A) +
              Zlength (enc_block (epos 0 (dc_bs G) (Z.to_nat k)) (S (Z.to_nat k) =? length (dc_bs G))%nat
                 (nth (Z.to_nat k) (dc_bs G) (Stored []))))
      by (rewrite Zlength_app, HA, dkit_D0_len; ring).
    replace (D0 G + epos 0 (dc_bs G) (Z.to_nat k)) with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ A))
      by (rewrite Zlength_app, HA, dkit_D0_len; ring).
    rewrite HR. unfold deflate_bits. rewrite HE. rewrite <- !app_assoc. rewrite (app_assoc (bytes_bits _) A).
    apply dkit_sublist_mid.
  - (* dk_bpos0 *)
    intros. unfold bpos. assert (E: epos 0 (dc_bs G) 0 = 0) by (destruct (dc_bs G); reflexivity).
    change (Z.to_nat 0) with O. lia.
  - (* dk_end *)
    intros G HG. unfold endpos, bpos, nblk. rewrite ZtoNat_Zlength, dkit_epos_end.
    destruct (dkit_deflate_bits_len (dc_bs G)) as [HL _].
    assert (Hpad: pad8 (D0 G + (0 + Zlength (enc_blocks 0 (dc_bs G)))) = pad8 (Zlength (enc_blocks 0 (dc_bs G)))).
    { unfold pad8, D0. f_equal. f_equal. rewrite Z.add_0_l.
      rewrite (Z.add_comm (8 * _)), (Z.mul_comm 8), Z_mod_plus_full. reflexivity. }
    split.
    + rewrite HL, Hpad. ring.
    + destruct (dkit_sbits G HG) as [R HR]. rewrite HR. unfold deflate_bits. rewrite Hpad.
      rewrite <- app_assoc, app_assoc.
      replace (D0 G + Zlength (enc_blocks 0 (dc_bs G) ++ zeros (pad8 (Zlength (enc_blocks 0 (dc_bs G))))))
        with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ enc_blocks 0 (dc_bs G)) +
              Zlength (zeros (pad8 (Zlength (enc_blocks 0 (dc_bs G))))))
        by (rewrite !Zlength_app, dkit_D0_len; ring).
      replace (D0 G + (0 + Zlength (enc_blocks 0 (dc_bs G))))
        with (Zlength (bytes_bits (hdr_bytes (dc_w G)) ++ enc_blocks 0 (dc_bs G)))
        by (rewrite !Zlength_app, dkit_D0_len; ring).
      apply dkit_sublist_mid.
  - (* dk_D0 *)
    intros. unfold D0. rewrite Z.mul_comm. apply Z.mod_mul. lia.
  - (* dk_slen *)
    intros G HG. destruct (dkit_deflate_bits_len (dc_bs G)) as [HL HM].
    assert (HE: endpos G = 8 * (Zlength (hdr_bytes (dc_w G)) + Zlength (deflate_bytes (dc_bs G)))).
    { unfold endpos, D0, deflate_bytes. rewrite dkit_pack_len.
      destruct (dkit_div8 _ HM) as [E1 E2]. rewrite E1. rewrite E2 at 1. ring. }
    assert (Ht: forall d, Zlength (dkit_trl (dc_w G) d) = trl_len (dc_w G)).
    { intros d. unfold dkit_trl, trl_len, be_bytes, le_bytes.
      destruct (dc_w G); rewrite ?Zlength_app, ?Zlength_rev, ?Zlength_map; reflexivity. }
    unfold slen. rewrite dkit_stream_split, !Zlength_app, Ht, HE. ring.
  - (* dk_trailer *)
    intros G HG. destruct (dkit_deflate_bits_len (dc_bs G)) as [HL HM].
    assert (HE: endpos G = 8 * (Zlength (hdr_bytes (dc_w G)) + Zlength (deflate_bytes (dc_bs G)))).
    { unfold endpos, D0, deflate_bytes. rewrite dkit_pack_len.
      destruct (dkit_div8 _ HM) as [E1 E2]. rewrite E1. rewrite E2 at 1. ring. }
    split.
    + rewrite HE, Z.mul_comm. apply Z.mod_mul. lia.
    + rewrite HE, Z.mul_comm, Z.div_mul by lia.
      destruct (dkit_src G HG) as [R HR].
      assert (Hs: slen G = Zlength (hdr_bytes (dc_w G)) + Zlength (deflate_bytes (dc_bs G)) +
                           Zlength (dkit_trl (dc_w G) (data (dc_hist G) (dc_bs G))))
        by (unfold slen; rewrite dkit_stream_split, !Zlength_app; ring).
      rewrite Hs, HR, app_assoc.
      replace (Zlength (hdr_bytes (dc_w G)) + Zlength (deflate_bytes (dc_bs G)))
        with (Zlength (hdr_bytes (dc_w G) ++ deflate_bytes (dc_bs G))) by (rewrite Zlength_app; ring).
      rewrite dkit_sublist_mid.
      unfold dkit_trl, produced, full, data. destruct (dc_w G); reflexivity.
  - (* dk_outk *)
    intros G k Hk. unfold nblk in Hk. unfold outk, blk, expand.
    assert (Hn: (Z.to_nat k < length (dc_bs G))%nat) by (rewrite <- ZtoNat_Zlength; apply Z2Nat.inj_lt; lia).
    replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by (rewrite Z2Nat.inj_add by lia; simpl; lia).
    rewrite (dkit_firstn_S _ _ (Stored []) Hn), fold_left_app. reflexivity.
  - (* dk_outk0 *)
    intros. reflexivity.
  - (* dk_full *)
    intros. unfold outk, full, nblk. rewrite ZtoNat_Zlength, firstn_all. reflexivity.
  - (* dk_full_len *)
    intros G k Hk. unfold full, outk, expand.
    assert (Hf: fold_left block_data (dc_bs G) (dc_hist G) =
                fold_left block_data (skipn (Z.to_nat k) (dc_bs G))
                  (fold_left block_data (firstn (Z.to_nat k) (dc_bs G)) (dc_hist G)))
      by (rewrite <- fold_left_app, firstn_skipn; reflexivity).
    rewrite Hf.
    destruct (dkit_fold_ext (skipn (Z.to_nat k) (dc_bs G))
                (fold_left block_data (firstn (Z.to_nat k) (dc_bs G)) (dc_hist G))) as [r Hr].
    rewrite Hr. split; [rewrite Zlength_app; pose proof (Zlength_nonneg r); lia | eexists; reflexivity].
  - (* dk_produced *)
    intros. unfold produced. rewrite sublist_app2 by (pose proof (Zlength_nonneg (dc_hist G)); lia).
    rewrite Zlength_app. apply sublist_same; lia.
Qed.

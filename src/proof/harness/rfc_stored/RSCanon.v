(* Law rfc_stored: the stream the harness builds is, but for the padding bits of the stored blocks' first
   bytes, the RFC 1950/1951/1952 stream of Format.v (stream_bytes) of the data cut into stored blocks.

   `rs_ctx` is the decode theory's context (rfc1951/DecodeDefs.v) of the CANONICAL stream (zero padding,
   Format.enc_block); `rs_pad_rel G src` says that src (the harness's buffer) differs from that context's
   source only in the high five bits of the blocks' first bytes (inflate drops them: STORED's BYTEBITS). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Format.
Require Import Zlib.proof.rfc1951.DecodeDefs.
Require Export Zlib.proof.harness.rfc_stored.RSModel.
Require Import Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.DecType Zlib.proof.rfc1951.DecTrl
               Zlib.proof.rfc1951.DecHdr.
Import ListNotations.
Local Open Scope Z_scope.

(* the canonical stream's context: wrapper, window bits of the stream, no history, the stored blocks,
   inflateInit2's windowBits, the buffer with zero padding *)
Definition rs_ctx (wr window c: Z) (s0 lens d: list Z) : dctx :=
  DCtx (rs_wrapper wr c s0) (rs_wb wr window c) [] (rs_bs lens d) (rs_iw wr window)
       (rs_src wr c s0 (repeat 0 (length lens)) lens d).

(* every block is stored *)
Definition rs_stored_only (G: dctx) : Prop := Forall (fun b => exists l, b = Stored l) (dc_bs G).

(* src is the context's source but for the padding of the blocks' first bytes: same length, and every byte
   is the source's or the first byte of block k, with the same three low bits (BFINAL, BTYPE) *)
Definition rs_pad_rel (G: dctx) (src: list Z) : Prop :=
  Zlength src = Zlength (dc_src G) /\ bytes_ok src /\
  forall i, 0 <= i < Zlength src ->
    Znth i src = Znth i (dc_src G) \/
    (exists k, 0 <= k < nblk G /\ 8 * i = bpos G k /\
       Znth i src mod 8 = Znth i (dc_src G) mod 8 /\ 0 <= Znth i (dc_src G) < 8).

(* ---------------------------------------------------------------------------------------------- *)
(* The blocks as byte lists                                                                       *)

(* the harness's constraints on the block lengths *)
Definition rsc_lens_ok (lens d: list Z) : Prop :=
  Forall (fun l => 0 <= l <= 65535) lens /\ fold_right Z.add 0 lens = Zlength d.

Lemma rsc_sum_nonneg lens : Forall (fun l => 0 <= l <= 65535) lens -> 0 <= fold_right Z.add 0 lens.
Proof. induction 1; cbn [fold_right]; lia. Qed.

(* the first block and the rest of the data *)
Lemma rsc_lens_cons l r d : rsc_lens_ok (l :: r) d ->
  0 <= l <= 65535 /\ l <= Zlength d /\ Zlength (sublist 0 l d) = l /\
  rsc_lens_ok r (sublist l (Zlength d) d).
Proof.
  intros [F S]. inversion F as [|x y Hl Fr]; subst. cbn [fold_right] in S.
  pose proof (rsc_sum_nonneg r Fr).
  repeat split; try lia.
  - rewrite Zlength_sublist; lia.
  - exact Fr.
  - rewrite Zlength_sublist; lia.
Qed.

Lemma rsc_block_len pad last ch : Zlength (rs_block pad last ch) = 5 + Zlength ch.
Proof. unfold rs_block. rewrite Zlength_app. reflexivity. Qed.

Lemma rsc_blocks_len lens : forall pads d, rsc_lens_ok lens d ->
  Zlength (rs_blocks pads lens d) = 5 * Zlength lens + Zlength d.
Proof.
  induction lens as [|l r IH]; intros pads d H.
  - destruct H as [_ S]. cbn in S |- *. rewrite <- S. reflexivity.
  - destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
    cbn [rs_blocks]. rewrite Zlength_app, rsc_block_len, Hc, IH by exact Hr.
    rewrite Zlength_cons, Zlength_sublist by lia. lia.
Qed.

Lemma rsc_chunks_concat lens : forall d, rsc_lens_ok lens d -> concat (rs_chunks lens d) = d.
Proof.
  induction lens as [|l r IH]; intros d H.
  - destruct H as [_ S]. cbn in S |- *. symmetry. apply Zlength_nil_inv. lia.
  - destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
    cbn [rs_chunks concat]. rewrite IH by exact Hr.
    rewrite sublist_rejoin, sublist_same by lia. reflexivity.
Qed.

Lemma rsc_chunks_len lens d : Zlength (rs_chunks lens d) = Zlength lens.
Proof.
  revert d. induction lens as [|l r IH]; intros d; [reflexivity|].
  cbn [rs_chunks]. rewrite !Zlength_cons, IH. reflexivity.
Qed.

(* the first byte of a block, with any padding byte: the same three low bits as with zero padding *)
Definition rsc_pad_chk : bool :=
  forallb (fun p => (Z.lor (Z.land p 248) 1 mod 8 =? 1) && (Z.lor (Z.land p 248) 0 mod 8 =? 0) &&
                    (0 <=? Z.lor (Z.land p 248) 1) && (Z.lor (Z.land p 248) 1 <? 256) &&
                    (0 <=? Z.lor (Z.land p 248) 0) && (Z.lor (Z.land p 248) 0 <? 256))
          (map Z.of_nat (seq 0 256)).

Lemma rsc_pad_chk_true : rsc_pad_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsc_pad_byte p (f: bool) : 0 <= p < 256 ->
  Z.lor (Z.land p 248) (if f then 1 else 0) mod 8 = (if f then 1 else 0) /\
  0 <= Z.lor (Z.land p 248) (if f then 1 else 0) < 256.
Proof.
  intros Hp. pose proof rsc_pad_chk_true as C. unfold rsc_pad_chk in C. rewrite forallb_forall in C.
  specialize (C p).
  assert (I : In p (map Z.of_nat (seq 0 256))).
  { replace p with (Z.of_nat (Z.to_nat p)) by lia. apply in_map, in_seq. lia. }
  specialize (C I). rewrite !andb_true_iff, !Z.eqb_eq, !Z.leb_le, !Z.ltb_lt in C.
  destruct f; lia.
Qed.

Lemma rsc_zero_byte (f: bool) : Z.lor (Z.land 0 248) (if f then 1 else 0) = (if f then 1 else 0).
Proof. destruct f; reflexivity. Qed.

(* the blocks with the padding bytes pads differ from the ones with zero padding only at the blocks' first
   bytes (positions rs_bpos from p), in their five high bits *)
Lemma rsc_blocks_diff lens : forall pads zs d p, rsc_lens_ok lens d -> rs_bytes pads ->
  Forall (fun x => x = 0) zs ->
  forall i, 0 <= i < Zlength (rs_blocks pads lens d) ->
  Znth i (rs_blocks pads lens d) = Znth i (rs_blocks zs lens d) \/
  exists k, (k < length lens)%nat /\ p + i = nth k (rs_bpos p lens) 0 /\
    Znth i (rs_blocks pads lens d) mod 8 = Znth i (rs_blocks zs lens d) mod 8 /\
    0 <= Znth i (rs_blocks zs lens d) < 8.
Proof.
  induction lens as [|l r IH]; intros pads zs d p H Bp Z0 i Hi.
  - cbn in Hi. lia.
  - destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
    cbn [rs_blocks] in Hi |- *.
    rewrite Zlength_app, rsc_block_len, Hc in Hi.
    set (f := match r with [] => true | _ => false end).
    destruct (Z_lt_ge_dec i (5 + l)) as [Lt|Ge].
    + rewrite !app_Znth1 by (rewrite rsc_block_len; lia).
      destruct (Z.eq_dec i 0) as [->|Ne].
      * right. exists O. split; [cbn; lia|]. split; [cbn; lia|].
        unfold rs_block. cbn [app]. rewrite !Znth_0_cons.
        assert (Hz : hd 0 zs = 0) by (destruct Z0; [reflexivity|cbn; assumption]).
        assert (Hp : 0 <= hd 0 pads < 256).
        { destruct Bp as [|x y Bx _]; cbn; [lia|]. unfold byte_ok in Bx. lia. }
        rewrite Hz, rsc_zero_byte. pose proof (rsc_pad_byte (hd 0 pads) f Hp) as [E _].
        rewrite E. destruct f; cbn; lia.
      * left. unfold rs_block. cbn [app]. rewrite Znth_pos_cons by lia. symmetry. rewrite Znth_pos_cons by lia. reflexivity.
    + rewrite !app_Znth2 by (rewrite rsc_block_len; lia). rewrite !rsc_block_len, Hc.
      assert (Bt : rs_bytes (tl pads)) by (destruct Bp; cbn; [constructor|assumption]).
      assert (Zt : Forall (fun x => x = 0) (tl zs)) by (destruct Z0; cbn; [constructor|assumption]).
      assert (Hi' : 0 <= i - (5 + l) < Zlength (rs_blocks (tl pads) r (sublist l (Zlength d) d))) by lia.
      destruct (IH (tl pads) (tl zs) _ (p + 5 + l) Hr Bt Zt _ Hi') as [E|(k & Hk & Ep & E)].
      * left. exact E.
      * right. exists (S k). split; [cbn; lia|]. split; [cbn [rs_bpos nth]; lia|]. exact E.
Qed.

Lemma rsc_bytes_repeat0 n : rs_bytes (repeat 0 n).
Proof. unfold rs_bytes. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold byte_ok. lia. Qed.

Lemma rsc_repeat0 n : Forall (fun x => x = 0) (repeat 0 n).
Proof. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. exact Hx. Qed.

Lemma rsc_bytes_ok l : rs_bytes l -> bytes_ok l.
Proof.
  unfold rs_bytes, bytes_ok. apply Forall_impl. intros a Ha. unfold byte_ok in Ha.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma rsc_ok_bytes l : bytes_ok l -> rs_bytes l.
Proof.
  unfold rs_bytes, bytes_ok. apply Forall_impl. intros a Ha. unfold byte_ok.
  change compcert.lib.Integers.Byte.max_unsigned with 255 in Ha. lia.
Qed.

(* the blocks are bytes *)
Lemma rsc_blocks_bytes lens : forall pads d, rsc_lens_ok lens d -> rs_bytes pads -> rs_bytes d ->
  rs_bytes (rs_blocks pads lens d).
Proof.
  induction lens as [|l r IH]; intros pads d H Bp Bd; [constructor|].
  destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
  cbn [rs_blocks]. unfold rs_bytes. apply Forall_app. split.
  - unfold rs_block. rewrite Hc. apply Forall_app. split.
    + assert (Hp : 0 <= hd 0 pads < 256).
      { destruct Bp as [|x y Bx _]; cbn; [lia|]. unfold byte_ok in Bx. lia. }
      pose proof (rsc_pad_byte (hd 0 pads) match r with [] => true | _ => false end Hp) as [_ B].
      repeat (apply Forall_cons; [unfold byte_ok; first [exact B | apply Z.mod_pos_bound; lia |
        split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]] |]).
      apply Forall_nil.
    + apply Forall_sublist, Bd.
  - apply IH; auto.
    + destruct Bp; cbn; [constructor|assumption].
    + apply Forall_sublist, Bd.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit encoding of stored blocks at byte boundaries                                           *)

Lemma rsc_bits16 v : bits_le v 16 = bits_le (v mod 256) 8 ++ bits_le (v / 256) 8.
Proof.
  unfold bits_le. change (seq 0 (Z.to_nat 16)) with (seq 0 8 ++ seq 8 8). rewrite map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. change 256 with (2 ^ 8).
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - change (seq 8 8) with (map (fun i => i + 8)%nat (seq 0 8)). rewrite map_map. apply map_ext_in.
    intros i Hi. apply in_seq in Hi. change 256 with (2 ^ 8).
    rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma rsc_bytes_bits_cons x l : bytes_bits (x :: l) = bits_le x 8 ++ bytes_bits l.
Proof. reflexivity. Qed.

(* a stored block at a byte boundary, with zero padding, is the bits of its bytes *)
Lemma rsc_enc_stored p f b : p mod 8 = 0 -> enc_block p f (Stored b) = bytes_bits (rs_block 0 f b).
Proof.
  intros Hp. unfold enc_block, rs_block. rewrite rsc_zero_byte.
  assert (P : pad8 (p + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia).
  rewrite P. cbn [app]. rewrite !rsc_bytes_bits_cons, !rsc_bits16.
  assert (F : bits_le (if f then 1 else 0) 8 = f :: [false; false] ++ zeros 5) by (destruct f; reflexivity).
  rewrite F. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma rsc_last_flag r d :
  match map Stored (rs_chunks r d) with [] => true | _ => false end = match r with [] => true | _ => false end.
Proof. destruct r; reflexivity. Qed.

(* the canonical blocks from a byte boundary are the bits of rs_blocks with zero padding *)
Lemma rsc_enc_blocks lens : forall zs d p, rsc_lens_ok lens d -> Forall (fun x => x = 0) zs -> p mod 8 = 0 ->
  enc_blocks p (rs_bs lens d) = bytes_bits (rs_blocks zs lens d).
Proof.
  induction lens as [|l r IH]; intros zs d p H Z0 Hp; [reflexivity|].
  destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
  unfold rs_bs. cbn [rs_chunks map enc_blocks rs_blocks]. rewrite rsc_last_flag.
  assert (Hz : hd 0 zs = 0) by (destruct Z0; [reflexivity|cbn; assumption]).
  rewrite Hz, rsc_enc_stored, dt_bytes_bits_app by exact Hp. f_equal.
  apply IH; auto.
  - destruct Z0; cbn; [constructor|assumption].
  - rewrite dt_bytes_bits_len, Z.mul_comm, Z.mod_add by lia. exact Hp.
Qed.

(* the position of block k *)
Lemma rsc_epos lens : forall d p k, rsc_lens_ok lens d -> (k < length lens)%nat ->
  epos (8 * p) (rs_bs lens d) k = 8 * nth k (rs_bpos p lens) 0.
Proof.
  induction lens as [|l r IH]; intros d p k H Hk; [cbn in Hk; lia|].
  destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
  destruct k as [|k]; [reflexivity|].
  unfold rs_bs. cbn [rs_chunks map epos rs_bpos nth].
  rewrite dt_stored_len, Hc.
  assert (P : pad8 (8 * p + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia).
  rewrite P. replace (8 * p + (3 + 5 + 32 + 8 * l)) with (8 * (p + 5 + l)) by lia.
  apply IH; auto. cbn in Hk. lia.
Qed.

(* pack undoes bytes_bits *)
Lemma rsc_pack l : rs_bytes l -> pack (bytes_bits l) = l.
Proof.
  intros B. apply dt_bytes_bits_inj; [|apply rsc_bytes_ok, B|].
  - unfold bytes_ok, pack. apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as (k & <- & Hk). apply in_seq in Hk.
    rewrite dt_bytes_bits_len in Hk. pose proof (Zlength_nonneg l).
    replace ((8 * Zlength l + 7) / 8) with (Zlength l) in Hk
      by (apply Z.div_unique with (r := 7); lia).
    pose proof (dkit_bval_sub_bound (bytes_bits l) (8 * Z.of_nat k) (8 * Z.of_nat k + 8)) as Bd.
    rewrite dt_bytes_bits_len in Bd. replace (8 * Z.of_nat k + 8 - 8 * Z.of_nat k) with 8 in Bd by lia.
    change compcert.lib.Integers.Byte.max_unsigned with 255. change (2 ^ 8) with 256 in Bd.
    specialize (Bd ltac:(lia) ltac:(lia)). lia.
  - apply dkit_pack_bits. rewrite dt_bytes_bits_len, Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* the deflate bytes of the canonical blocks *)
Lemma rsc_deflate lens d : rsc_lens_ok lens d -> rs_bytes d ->
  deflate_bytes (rs_bs lens d) = rs_blocks (repeat 0 (length lens)) lens d.
Proof.
  intros H Bd. unfold deflate_bytes, deflate_bits.
  rewrite (rsc_enc_blocks lens (repeat 0 (length lens)) d 0 H (rsc_repeat0 _)) by reflexivity.
  rewrite dt_bytes_bits_len.
  assert (P : forall x, pad8 (8 * x) = 0) by (intros; unfold pad8; Z.to_euclidean_division_equations; lia).
  rewrite P. change (zeros 0) with (@nil bool). rewrite app_nil_r.
  apply rsc_pack, rsc_blocks_bytes; auto. apply rsc_bytes_repeat0.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The data, the header and the trailer                                                          *)

Lemma rsc_expand cs : forall out, fold_left block_data (map Stored cs) out = out ++ concat cs.
Proof.
  induction cs as [|x r IH]; intros out; cbn [map fold_left concat block_data].
  - rewrite app_nil_r. reflexivity.
  - rewrite IH, app_assoc. reflexivity.
Qed.

Lemma rsc_full lens d : rsc_lens_ok lens d -> expand [] (rs_bs lens d) = d.
Proof. intros H. unfold expand, rs_bs. rewrite rsc_expand, rsc_chunks_concat by exact H. reflexivity. Qed.

Lemma rsc_data lens d : rsc_lens_ok lens d -> data [] (rs_bs lens d) = d.
Proof.
  intros H. unfold data. rewrite rsc_full by exact H. rewrite Zlength_nil. apply sublist_same; lia.
Qed.

(* four bytes, little-endian *)
Lemma rsc_le4 a b c e : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= e < 256 ->
  le_bytes (a + 256 * b + 65536 * c + 16777216 * e) 4 = [a; b; c; e].
Proof.
  intros Ha Hb Hc He. rewrite trl_le_bytes4.
  set (v := a + 256 * b + 65536 * c + 16777216 * e).
  assert (D1 : v / 256 = b + 256 * c + 65536 * e) by (symmetry; apply Z.div_unique with (r := a); unfold v; lia).
  assert (D2 : v / 65536 = c + 256 * e) by (symmetry; apply Z.div_unique with (r := a + 256 * b); unfold v; lia).
  assert (D3 : v / 16777216 = e) by (symmetry; apply Z.div_unique with (r := a + 256 * b + 65536 * c); unfold v; lia).
  rewrite D1, D2, D3. f_equal; [|f_equal; [|f_equal; [|f_equal]]].
  - symmetry. apply Z.mod_unique with (q := b + 256 * c + 65536 * e); unfold v; lia.
  - symmetry. apply Z.mod_unique with (q := c + 256 * e); lia.
  - symmetry. apply Z.mod_unique with (q := e); lia.
  - apply Z.mod_small. lia.
Qed.

Lemma rsc_land1 x : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  pose proof (Z.land_ones x 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. change (2 ^ 1) with 2 in E.
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(* the gzip header the harness writes *)
Definition rsc_gzh (s0: list Z) : gzhdr :=
  GzHdr (Z.land (Znth 3 s0) 1 =? 1)
        (Znth 4 s0 + 256 * Znth 5 s0 + 65536 * Znth 6 s0 + 16777216 * Znth 7 s0)
        (Znth 8 s0) (Znth 9 s0) None None None false.

Lemma rsc_gz s0 : 10 <= Zlength s0 -> rs_bytes s0 ->
  gz_bytes (rsc_gzh s0) = [31; 139; 8; Z.land (Znth 3 s0) 1] ++ sublist 4 10 s0 /\ gz_ok (rsc_gzh s0) /\
  gz_simple (rsc_gzh s0).
Proof.
  intros L B.
  do 10 (destruct s0 as [|? s0]; [rewrite Zlength_nil in L; lia | rewrite Zlength_cons in L]).
  unfold rs_bytes in B. repeat match goal with H: Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
  unfold byte_ok in *. unfold rsc_gzh, Znth. cbn [Z.ltb Z.compare Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth].
  repeat match goal with |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); [lia|] end.
  split; [|split].
  - unfold gz_bytes, gz_bytes0, gz_flg. cbn [gz_hcrc gz_text gz_mtime gz_xfl gz_os gz_extra gz_name gz_comment].
    rewrite rsc_le4 by lia. cbn [app]. unfold sublist. cbn. do 3 f_equal.
    destruct (rsc_land1 z2) as [E|E]; rewrite E; reflexivity.
  - unfold gz_ok. cbn [gz_mtime gz_xfl gz_os gz_extra gz_name gz_comment]. unfold byte_ok.
    repeat split; try lia.
  - repeat split.
Qed.

(* the wrapper: its header is the harness's, its trailer too, and it is a valid wrapper *)
Lemma rsc_wrap wr window c s0 : 0 <= wr <= 2 -> 8 <= window <= 15 -> (wr = 1 -> 0 <= c <= window - 8) ->
  rs_hl wr + 5 <= Zlength s0 -> rs_bytes s0 ->
  hdr_bytes (rs_wrapper wr c s0) = rs_hdr wr c s0 /\ Zlength (rs_hdr wr c s0) = rs_hl wr /\
  rs_bytes (rs_hdr wr c s0) /\
  (forall d, dkit_trl (rs_wrapper wr c s0) d = rs_trl wr d) /\
  wrapper_ok (rs_wrapper wr c s0) [] /\ 8 <= rs_wb wr window c <= 15 /\
  (match rs_wrapper wr c s0 with WZlib wb' _ _ => wb' = rs_wb wr window c | _ => True end) /\
  (forall h, rs_wrapper wr c s0 = WGzip h -> gz_simple h).
Proof.
  intros Hwr Hwin Hc L B.
  assert (W : wr = 0 \/ wr = 1 \/ wr = 2) by lia.
  destruct W as [ -> | [ -> | -> ] ].
  - unfold rs_wb. cbn [Z.eqb]. repeat split; try reflexivity; try lia; try constructor;
      match goal with E: rs_wrapper 0 c s0 = WGzip _ |- _ => discriminate E end.
  - specialize (Hc eq_refl). cbn in L.
    assert (B1 : 0 <= Znth 1 s0 < 256) by (apply (Forall_Znth (fun b => 0 <= b < 256) s0 1); [lia | exact B]).
    assert (F : 0 <= Z.shiftr (Znth 1 s0) 6 <= 3).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
      split; [apply Z.div_pos; lia|]. assert (Znth 1 s0 / 64 < 4) by (apply Z.div_lt_upper_bound; lia). lia. }
    unfold rs_wrapper, rs_hdr, rs_hl, rs_wb, rs_trl, dkit_trl, hdr_bytes. cbn [Z.eqb Pos.eqb].
    repeat split; try lia; try match goal with E: _ = WGzip _ |- _ => discriminate E end.
    unfold rs_bytes, zlib_hdr. cbv zeta.
    set (fl := Z.shiftr (Znth 1 s0) 6) in *.
    pose proof (Z.mod_pos_bound (31 - (((c + 8 - 8) * 16 + 8) * 256 + (fl * 64 + 0)) mod 31) 31 ltac:(lia)).
    repeat constructor; unfold byte_ok; lia.
  - cbn in L. destruct (rsc_gz s0 ltac:(lia) B) as (G1 & G2 & G3).
    assert (E : rs_wrapper 2 c s0 = WGzip (rsc_gzh s0)) by reflexivity. rewrite E.
    unfold rs_hdr, rs_hl, rs_wb, rs_trl, dkit_trl, hdr_bytes. cbn [Z.eqb Pos.eqb].
    split; [exact G1|]. split; [rewrite Zlength_app, Zlength_sublist by lia; reflexivity|].
    split.
    { unfold rs_bytes. apply Forall_app. split; [|apply Forall_sublist, B].
      pose proof (rsc_land1 (Znth 3 s0)). repeat constructor; unfold byte_ok; lia. }
    split; [intros; reflexivity|]. split; [split; [exact G2|reflexivity]|]. split; [lia|]. split; [exact I|].
    intros h E'. inversion E'. subst. exact G3.
Qed.

(* the canonical blocks are well-formed stored blocks *)
Lemma rsc_blocks_ok lens : forall wmax out d, rsc_lens_ok lens d -> rs_bytes d -> blocks_ok wmax out (rs_bs lens d).
Proof.
  induction lens as [|l r IH]; intros wmax out d H Bd; [exact I|].
  destruct (rsc_lens_cons l r d H) as (Hl & Hd & Hc & Hr).
  unfold rs_bs. cbn [rs_chunks map blocks_ok block_ok]. split; [split|].
  - lia.
  - apply Forall_sublist, Bd.
  - apply IH; auto. apply Forall_sublist, Bd.
Qed.

(* the buffer: header, blocks, trailer, the rest of s0, by position *)
Lemma rsc_src_at wr c s0 pads lens d i : 0 <= Zlength (rs_hdr wr c s0) ->
  Znth i (rs_src wr c s0 pads lens d) =
  if i <? Zlength (rs_hdr wr c s0) then Znth i (rs_hdr wr c s0)
  else if i <? Zlength (rs_hdr wr c s0) + Zlength (rs_blocks pads lens d)
  then Znth (i - Zlength (rs_hdr wr c s0)) (rs_blocks pads lens d)
  else Znth (i - Zlength (rs_hdr wr c s0) - Zlength (rs_blocks pads lens d))
         (rs_trl wr d ++ sublist (rs_slen wr lens d) (Zlength s0) s0).
Proof.
  intros _. unfold rs_src.
  destruct (Z.ltb_spec i (Zlength (rs_hdr wr c s0))); [apply app_Znth1; lia|].
  rewrite app_Znth2 by lia.
  destruct (Z.ltb_spec i (Zlength (rs_hdr wr c s0) + Zlength (rs_blocks pads lens d))).
  - apply app_Znth1. lia.
  - rewrite app_Znth2 by lia. f_equal; lia.
Qed.

(* the canonical context is a valid stream of the data, and inflateInit2's windowBits accept it (zlib: the
   header's window, CINFO + 8, is at most inflate's) *)
Lemma rs_canon wr window c s0 lens d :
  rs_ok wr window c s0 lens d ->
  let G := rs_ctx wr window c s0 lens d in
  stream_ok (dc_w G) (dc_wb G) [] (dc_bs G) /\ rs_stored_only G /\
  (forall h, dc_w G = WGzip h -> gz_simple h) /\
  slen G = rs_slen wr lens d /\ Zlength (dc_src G) = Zlength s0 /\ bytes_ok (dc_src G) /\
  sublist 0 (slen G) (dc_src G) = stream_bytes (dc_w G) [] (dc_bs G) /\
  full G = d /\ nblk G = Zlength lens /\
  (wr = 0 -> dc_w G = WRaw /\ dc_iw G = - dc_wb G) /\
  (wr = 1 -> (exists fl, dc_w G = WZlib (dc_wb G) fl None) /\ dc_iw G = window /\ dc_wb G <= window) /\
  (wr = 2 -> (exists h, dc_w G = WGzip h) /\ dc_iw G = 16 + dc_wb G) /\
  (* the harness's buffer (its padding bytes are s0's) is the canonical one up to the padding *)
  (forall pads, Zlength pads = Zlength lens -> rs_bytes pads -> rs_pad_rel G (rs_src wr c s0 pads lens d)).
Proof.
  intros (Hwr & Hwin & Hc & Hne & Hlens & Hsum & Hslen & Bs0 & Bd). cbv zeta.
  assert (HL : rsc_lens_ok lens d) by (split; assumption).
  pose proof (Zlength_nonneg d) as Hd0.
  assert (Hn1 : 1 <= Zlength lens) by (destruct lens; [contradiction|rewrite Zlength_cons; pose proof (Zlength_nonneg lens); lia]).
  assert (Htl : 0 <= rs_tl wr) by (unfold rs_tl; destruct (wr =? 1); [|destruct (wr =? 2)]; lia).
  assert (Hhl : 0 <= rs_hl wr) by (unfold rs_hl; destruct (wr =? 1); [|destruct (wr =? 2)]; lia).
  pose proof Hslen as Hslen'. unfold rs_slen in Hslen'.
  destruct (rsc_wrap wr window c s0 Hwr Hwin Hc ltac:(lia) Bs0) as (Wh & Wl & Wb & Wt & Wok & Wwb & Wz & Wg).
  assert (Htrl : Zlength (rs_trl wr d) = rs_tl wr /\ rs_bytes (rs_trl wr d)).
  { unfold rs_trl, rs_tl. destruct (wr =? 1); [|destruct (wr =? 2)].
    - rewrite trl_be_bytes_len by lia. split; [reflexivity|]. apply trl_be_bytes_ok.
    - rewrite Zlength_app, !trl_le_bytes_len by lia. split; [reflexivity|].
      apply Forall_app. split; apply trl_le_bytes_ok.
    - split; [reflexivity|constructor]. }
  destruct Htrl as [Tl Tb].
  set (z := repeat 0 (length lens)).
  assert (Hst : stream_bytes (rs_wrapper wr c s0) [] (rs_bs lens d) = rs_hdr wr c s0 ++ rs_blocks z lens d ++ rs_trl wr d)
    by (rewrite dkit_stream_split, Wh, rsc_data, Wt, rsc_deflate by assumption; reflexivity).
  assert (Hstl : Zlength (stream_bytes (rs_wrapper wr c s0) [] (rs_bs lens d)) = rs_slen wr lens d)
    by (rewrite Hst, !Zlength_app, Wl, rsc_blocks_len, Tl by exact HL; unfold rs_slen; lia).
  assert (Hsrc : rs_src wr c s0 z lens d =
                 stream_bytes (rs_wrapper wr c s0) [] (rs_bs lens d) ++ sublist (rs_slen wr lens d) (Zlength s0) s0)
    by (unfold rs_src; rewrite Hst, <- !app_assoc; reflexivity).
  assert (Hsl0 : 0 <= rs_slen wr lens d) by (unfold rs_slen; lia).
  (* the buffer with any padding bytes *)
  assert (Lsrc : forall pads, Zlength (rs_src wr c s0 pads lens d) = Zlength s0).
  { intros pads. unfold rs_src. rewrite !Zlength_app, Wl, rsc_blocks_len, Tl, Zlength_sublist by (auto; lia).
    unfold rs_slen. lia. }
  assert (Bsrc : forall pads, rs_bytes pads -> rs_bytes (rs_src wr c s0 pads lens d)).
  { intros pads Bp. unfold rs_src, rs_bytes. rewrite !Forall_app.
    split; [exact Wb|]. split; [apply rsc_blocks_bytes; auto|]. split; [exact Tb|]. apply Forall_sublist, Bs0. }
  unfold rs_ctx, slen, full, nblk, bpos, D0, rs_stored_only, rs_pad_rel.
  cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src]. fold z.
  split; [|split; [|split; [exact Wg|split; [exact Hstl|split; [apply Lsrc|split]]]]].
  - split; [exact Wwb|]. split; [exact Wok|]. split; [exact Wz|]. split; [|split; [constructor|]].
    + unfold rs_bs. destruct lens; [contradiction|discriminate].
    + apply rsc_blocks_ok; auto.
  - unfold rs_bs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (ch & <- & _). eauto.
  - apply rsc_bytes_ok, Bsrc, rsc_bytes_repeat0.
  - split; [rewrite Hsrc; apply dkit_sublist_pre|].
    split; [apply rsc_full, HL|].
    split; [unfold rs_bs; rewrite Zlength_map; apply rsc_chunks_len|].
    split; [intros ->; split; reflexivity|].
    split; [intros ->; unfold rs_wrapper, rs_wb, rs_iw; cbn [Z.eqb Pos.eqb];
            split; [eexists; reflexivity|split; [reflexivity|specialize (Hc eq_refl); lia]]|].
    split; [intros ->; split; [eexists; reflexivity|reflexivity]|].
    (* the padding *)
    intros pads Hp Bp. split; [rewrite !Lsrc; reflexivity|]. split; [apply rsc_bytes_ok, Bsrc, Bp|].
    intros i Hi. rewrite Lsrc in Hi.
    rewrite !rsc_src_at by lia. rewrite !(rsc_blocks_len lens pads d HL), !(rsc_blocks_len lens z d HL).
    destruct (Z.ltb_spec i (Zlength (rs_hdr wr c s0))); [left; reflexivity|].
    destruct (Z.ltb_spec i (Zlength (rs_hdr wr c s0) + (5 * Zlength lens + Zlength d))); [|left; reflexivity].
    assert (Hi' : 0 <= i - Zlength (rs_hdr wr c s0) < Zlength (rs_blocks pads lens d))
      by (rewrite (rsc_blocks_len lens pads d HL); lia).
    destruct (rsc_blocks_diff lens pads z d 0 HL Bp (rsc_repeat0 _) _ Hi') as [E|(k & Hk & Ep & E)];
      [left; exact E|right].
    unfold nblk, bpos, D0. cbn [dc_bs dc_w].
    exists (Z.of_nat k). split; [unfold rs_bs; rewrite Zlength_map, rsc_chunks_len, Zlength_correct; lia|]. split; [|exact E].
    rewrite Nat2Z.id, Wh, Wl.
    pose proof (rsc_epos lens d 0 k HL Hk) as Ee. rewrite Z.mul_0_r in Ee. rewrite Ee. lia.
Qed.

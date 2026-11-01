(* Law rfc_stored, main: statements 22-24, adler32_z(1, data, data_len), crc32_z(0, data, data_len) and the
   trailer loop: the buffer is RSModel.rs_src (rs_C -> rs_D). *)
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

(* the malloc token of a byte object, moved from the crc32 unit's compspecs to the law's *)
Lemma rs_tok_c sh n q:
  @malloc_token Zlib.units.Crc32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_crc32). reflexivity. Qed.

(* `(unsigned char) (x >> k)` for a 64-bit x and a shift k <= 56: the 8 bits of x from bit k *)
Lemma rs_byte x k: 0 <= k <= 56 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.Z_mod_modulus x)
    (Int64.Z_mod_modulus k))))) = Int.repr (Z.shiftr x k mod 256).
Proof.
  intros Hk. rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small k) by (change Int64.modulus with (2 ^ 64); lia).
  apply Int.same_bits_eq; intros j Hj.
  rewrite Int.bits_zero_ext by lia. rewrite Int.testbit_repr by auto.
  change 256 with (2 ^ 8). change Int64.modulus with (2 ^ 64).
  destruct (zlt j 8).
  - rewrite Int.bits_zero_ext by lia. destruct (zlt j 8); [ | lia]. rewrite Int.testbit_repr by auto.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia.
    rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* the trailer area of the buffer after i rounds of the trailer loop (T0: its initial bytes, |T0| = rs_tl wr):
   zlib: the first i bytes of ADLER32 (MSB first); gzip: the first i bytes of CRC32 and of ISIZE (LSB first) *)
Definition rs_tw (wr A C N: Z) (T0: list Z) (i: Z) : list Z :=
  if wr =? 1 then sublist 0 i (Zlib.proof.rfc1951.Format.be_bytes A 4) ++ sublist i 4 T0
  else if wr =? 2 then
    sublist 0 i (Zlib.proof.rfc1951.Format.le_bytes C 4) ++ sublist i 4 T0 ++
    sublist 0 i (Zlib.proof.rfc1951.Format.le_bytes N 4) ++ sublist (4 + i) 8 T0
  else T0.

(* the bytes of a 32-bit field, LSB first (le_bytes) and MSB first (be_bytes) *)
Lemma rs_le4_nth v i: 0 <= i < 4 -> Znth i (Zlib.proof.rfc1951.Format.le_bytes v 4) = Z.shiftr v (8 * i) mod 256.
Proof. intros Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as E by lia. destruct E as [E|[E|[E|E]]]; subst; reflexivity. Qed.

Lemma rs_be4_nth v i: 0 <= i < 4 -> Znth i (Zlib.proof.rfc1951.Format.be_bytes v 4) = Z.shiftr v (24 - 8 * i) mod 256.
Proof. intros Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as E by lia. destruct E as [E|[E|[E|E]]]; subst; reflexivity. Qed.

Lemma rs_le4_len v: Zlength (Zlib.proof.rfc1951.Format.le_bytes v 4) = 4.
Proof. reflexivity. Qed.
Lemma rs_be4_len v: Zlength (Zlib.proof.rfc1951.Format.be_bytes v 4) = 4.
Proof. reflexivity. Qed.

(* byte i < 4 of a 64-bit value is byte i of its low 32 bits (ISIZE = data_len mod 2^32) *)
Lemma rs_byte32 x i: 0 <= i < 4 -> Z.shiftr (x mod 2 ^ 32) (8 * i) mod 256 = Z.shiftr x (8 * i) mod 256.
Proof.
  intros Hi. change 256 with (2 ^ 8). apply Z.bits_inj'; intros j Hj.
  destruct (zlt j 8).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia.
    reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* one round of the zlib trailer loop *)
Lemma rs_tw_step1 A C N T0 i: 0 <= i < 4 -> Zlength T0 = 4 ->
  upd_Znth i (rs_tw 1 A C N T0 i) (Z.shiftr A (24 - 8 * i) mod 256) = rs_tw 1 A C N T0 (i + 1).
Proof.
  intros Hi HT. unfold rs_tw; simpl. rewrite <- rs_be4_nth by lia.
  pose proof (rs_be4_len A). list_solve.
Qed.

(* one round of the gzip trailer loop *)
Lemma rs_tw_step2 A C N T0 i: 0 <= i < 4 -> Zlength T0 = 8 ->
  upd_Znth (4 + i) (upd_Znth i (rs_tw 2 A C N T0 i) (Z.shiftr C (8 * i) mod 256)) (Z.shiftr N (8 * i) mod 256) =
  rs_tw 2 A C N T0 (i + 1).
Proof.
  intros Hi HT. unfold rs_tw; simpl. rewrite <- !rs_le4_nth by lia.
  pose proof (rs_le4_len C). pose proof (rs_le4_len N). list_solve.
Qed.

(* a store into the middle part of the buffer *)
Lemma rs_upd_mid (P X R: list Z) j v: 0 <= j < Zlength X ->
  upd_Znth (Zlength P + j) (bytes_rep (P ++ X ++ R)) (Vint (Int.repr v)) = bytes_rep (P ++ upd_Znth j X v ++ R).
Proof. intros Hj. unfold bytes_rep. list_solve. Qed.

Lemma rs_tw_len wr A C N T0 i: 0 <= i <= 4 -> Zlength T0 = rs_tl wr -> Zlength (rs_tw wr A C N T0 i) = rs_tl wr.
Proof.
  intros Hi HT. unfold rs_tw, rs_tl in *.
  destruct (wr =? 1); [ | destruct (wr =? 2)]; auto.
  - pose proof (rs_be4_len A). list_solve.
  - pose proof (rs_le4_len C). pose proof (rs_le4_len N). list_solve.
Qed.

(* the trailer area before the loop and after its four rounds *)
Lemma rs_tw0 wr A C N T0: Zlength T0 = rs_tl wr -> rs_tw wr A C N T0 0 = T0.
Proof.
  intros HT. unfold rs_tw, rs_tl in *. destruct (wr =? 1); [ | destruct (wr =? 2)]; auto; list_solve.
Qed.

Lemma rs_tw4 wr d T0: 0 <= wr <= 2 -> Zlength T0 = rs_tl wr ->
  rs_tw wr (Zlib.proof.adler32.Model.ref_adler32 1 d) (ref_crc32 0 d) (Zlength d mod 2 ^ 32) T0 4 = rs_trl wr d.
Proof.
  intros Hw HT. unfold rs_tw, rs_trl, rs_tl in *.
  destruct (Z.eqb_spec wr 1); [ | destruct (Z.eqb_spec wr 2)].
  - pose proof (rs_be4_len (Zlib.proof.adler32.Model.ref_adler32 1 d)). list_solve.
  - pose proof (rs_le4_len (ref_crc32 0 d)). pose proof (rs_le4_len (Zlength d mod 2 ^ 32)). list_solve.
  - list_solve.
Qed.

(* the lengths of the header and of the blocks *)
Lemma rs_hdr_len wr c s0: rs_hl wr <= Zlength s0 -> Zlength (rs_hdr wr c s0) = rs_hl wr.
Proof.
  intros Hs. unfold rs_hdr, rs_hl in *.
  destruct (wr =? 1); [reflexivity | destruct (wr =? 2); [ | reflexivity]].
  rewrite Zlength_app, Zlength_sublist by lia. reflexivity.
Qed.

Lemma rs_block_len pad last ch: Zlength (rs_block pad last ch) = 5 + Zlength ch.
Proof. unfold rs_block. rewrite Zlength_app. reflexivity. Qed.

Lemma rs_blocks_len lens: forall pads d, Forall (fun l => 0 <= l <= 65535) lens ->
  fold_right Z.add 0 lens = Zlength d -> Zlength (rs_blocks pads lens d) = 5 * Zlength lens + Zlength d.
Proof.
  induction lens as [|l r IH]; intros pads d F S.
  - cbn in S |- *. rewrite <- S. reflexivity.
  - inversion F as [|x y Hl Fr]; subst. cbn [fold_right] in S.
    assert (0 <= fold_right Z.add 0 r) by (clear - Fr; induction Fr; cbn [fold_right]; lia).
    cbn [rs_blocks]. rewrite Zlength_app, rs_block_len, IH by (auto; rewrite Zlength_sublist; lia).
    rewrite Zlength_cons, !Zlength_sublist by lia. lia.
Qed.

Lemma seg_trl_ok {Espec: OracleKind} gv vs vwb n nb na wr window stp s0 dp d op ep c lens:
  rs_A_facts n nb na wr window stp s0 dp d op -> rs_c_ok wr window c -> rs_lens_ok nb n lens ->
  semax Delta_m (rs_D gv vs vwb n nb na wr window stp s0 dp d op ep c lens) rs_seg25 POST_B ->
  semax Delta_m (rs_C gv vs vwb n nb na wr window stp s0 dp d op ep c lens) rs_seg22 POST_B.
Proof.
  intros F Hc Hl K.
  unfold rs_C, rs_seg22, Delta_m, Gmain_k, POST_B, POST_m. simplify_func_tycontext. abbreviate_semax.
  destruct F as (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & Pst & Pdp & Pop).
  assert (Bd': is_bytes d) by (eapply Forall_impl; [ | exact Bd]; intros b Hb; hnf in Hb |- *; rep_lia).
  rewrite <- (rs_bytes_a Ews n (bytes_rep d) dp), <- (rs_tok_a Ews n dp).
  forward_call (1, dp, n, false, Ews, dp, 0, n, bytes_rep d, d, true, Ews).
  { unfold cbuf_ok. repeat split; auto; try lia. all: try (rewrite isptr_offset_val_zero; auto).
    rewrite sublist_same; auto; rewrite ?Zlength_bytes_rep; lia. }
  rewrite (rs_bytes_a Ews n (bytes_rep d) dp), (rs_tok_a Ews n dp).
  rewrite <- (rs_bytes_c Ews n (bytes_rep d) dp), <- (rs_tok_c Ews n dp).
  forward_call (0, dp, n, false, Ews, dp, 0, n, bytes_rep d, d, true, Ews, gv, Ers).
  { unfold cbuf_ok. repeat split; auto; try lia. all: try (rewrite isptr_offset_val_zero; auto).
    rewrite sublist_same; auto; rewrite ?Zlength_bytes_rep; lia. }
  rewrite (rs_bytes_c Ews n (bytes_rep d) dp), (rs_tok_c Ews n dp).
  rewrite Zlib.proof.adler32.Model.adler32_z_val_ref
    by (unfold Zlib.proof.adler32.Model.adler_valid; split; [lia | split; reflexivity]).
  destruct Hl as (Hne & Hln & Hlf & Hsum).
  assert (Htl: 0 <= rs_tl wr <= 8) by (unfold rs_tl; destruct (wr =? 1); [ | destruct (wr =? 2)]; lia).
  pose proof (rs_hdr_len wr c s0 ltac:(lia)) as Hhl.
  pose proof (rs_blocks_len lens (rs_pads wr s0 lens) d Hlf ltac:(lia)) as Hbl.
  assert (Hhl0: 0 <= rs_hl wr) by (unfold rs_hl; destruct (wr =? 1); [ | destruct (wr =? 2)]; lia).
  set (A := Zlib.proof.adler32.Model.ref_adler32 1 d). set (C := ref_crc32 0 d). set (N := Zlength d mod 2 ^ 32).
  set (at_ := rs_hl wr + 5 * nb + n).
  set (P := rs_hdr wr c s0 ++ rs_blocks (rs_pads wr s0 lens) lens d).
  set (T0 := sublist at_ (at_ + rs_tl wr) s0). set (R := sublist (at_ + rs_tl wr) (Zlength s0) s0).
  assert (HP: Zlength P = at_) by (subst P at_; rewrite Zlength_app; lia).
  assert (HT0: Zlength T0 = rs_tl wr) by (subst T0 at_; rewrite Zlength_sublist; lia).
  assert (EB: rs_hdr wr c s0 ++ rs_blocks (rs_pads wr s0 lens) lens d ++ sublist at_ (Zlength s0) s0 =
              P ++ rs_tw wr A C N T0 0 ++ R).
  { rewrite rs_tw0 by auto. subst P T0 R. rewrite (sublist_split at_ (at_ + rs_tl wr)) by lia.
    rewrite <- app_assoc. reflexivity. }
  assert (EF: rs_src wr c s0 (rs_pads wr s0 lens) lens d = P ++ rs_tw wr A C N T0 4 ++ R).
  { subst A C N. rewrite rs_tw4 by auto. unfold rs_src. subst P R.
    replace (rs_slen wr lens d) with (at_ + rs_tl wr) by (unfold rs_slen; subst at_; lia).
    rewrite <- app_assoc. reflexivity. }
  assert (Hs: Zlength s0 = at_ + rs_tl wr + na) by (subst at_; lia).
  rewrite EB; clear EB.
  clearbody A C at_ P T0 R.
  forward_for_simple_bound 4 (EX i: Z,
   PROP ( )
   LOCAL (temp _crc (Vlong (Int64.repr C)); temp _adler (Vlong (Int64.repr A));
   temp _at (Vlong (Int64.repr at_));
   temp _data_len (Vlong (Int64.repr n));
   temp _blocks (Vlong (Int64.repr nb)); temp _after (Vlong (Int64.repr na));
   temp _wrapper (Vint (Int.repr wr)); temp _window (Vint (Int.repr window));
   temp _head_len (Vlong (Int64.repr (rs_hl wr)));
   temp _trailer_len (Vlong (Int64.repr (rs_tl wr)));
   temp _stream_len (Vlong (Int64.repr (Zlength s0)));
   temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
   lvar _window_bits (tarray tint 3) vwb;
   lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
   SEP (Zlib.proof.crc32.Spec.crc_table_at Ers gv; malloc_token Ews (tarray tuchar n) dp;
   data_at Ews (tarray tuchar n) (bytes_rep d) dp;
   data_at_ Tsh (tarray tint 3) vwb;
   data_at_ Tsh (Tstruct _z_stream_s noattr) vs; mem_mgr gv;
   zfuncs gv; tables_rep Ers gv; version_lit gv; rs_hversion_lit gv;
   malloc_token Ews (tarray tuchar (Zlength s0)) stp;
   data_at Ews (tarray tuchar (Zlength s0))
     (bytes_rep (P ++ rs_tw wr A C N T0 i ++ R)) stp;
   malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d)).
  { entailer!. }
  { assert (wr = 0 \/ wr = 1 \/ wr = 2) as Ew by lia.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS; apply semax_if_seq.
    destruct Ew as [Ew|[Ew|Ew]]; subst wr.
    - forward_if. { exfalso; lia. }
      forward_if. { exfalso; lia. }
      forward. entailer!.
    - forward_if.
      + forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
        { entailer!. change (rs_tl 1) with 4 in *. pose proof (Zlength_nonneg P). lia. }
        rewrite mul_repr, sub_repr, Int.unsigned_repr by rep_lia.
        rewrite rs_byte by lia. rewrite <- HP, rs_upd_mid by (rewrite rs_tw_len by lia; change (rs_tl 1) with 4; lia).
        rewrite rs_tw_step1 by (auto; lia).
        forward_if. { exfalso. discriminate. }
        forward. entailer!.
      + exfalso; auto.
    - forward_if. { exfalso; lia. }
      forward_if; [ | exfalso; auto].
      forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      { entailer!. change (rs_tl 2) with 8 in *. pose proof (Zlength_nonneg P). lia. }
      rewrite mul_repr, Int.unsigned_repr by rep_lia.
      rewrite rs_byte by lia. rewrite <- HP, rs_upd_mid by (rewrite rs_tw_len by lia; change (rs_tl 2) with 8; lia).
      forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
      { entailer!. change (rs_tl 2) with 8 in *. pose proof (Zlength_nonneg P). lia. }
      rewrite mul_repr, Int.unsigned_repr by rep_lia. rewrite rs_byte by lia.
      replace (Zlength P + 4 + i) with (Zlength P + (4 + i)) by lia.
      assert (Lt: Zlength (rs_tw 2 A C N T0 i) = 8) by (rewrite rs_tw_len by lia; reflexivity).
      rewrite rs_upd_mid by (rewrite upd_Znth_Zlength by lia; lia).
      subst n. rewrite <- (rs_byte32 (Zlength d) i) by lia. change (Zlength d mod 2 ^ 32) with N.
      rewrite rs_tw_step2 by (auto; lia).
      entailer!. }
  rewrite <- EF.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply K ].
  unfold rs_D. entailer!.
Qed.

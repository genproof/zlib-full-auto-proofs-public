(* Law inflate_decode, main: the end-of-block code after the symbol loop. *)
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
(* Helpers                                                                                        *)

Lemma eob_bits_le_mod16 c l : 0 <= l <= 16 -> bits_le (c mod 65536) l = bits_le c l.
Proof.
  intros Hl. unfold bits_le. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  change 65536 with (2 ^ 16). apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma eob_canon_send lens s : 0 <= Znth s lens <= 15 -> Znth s lens <> 0 ->
  bits_msb (canon_val lens s) (Znth s lens) = send_sym lens s.
Proof.
  intros Hl Hn. unfold canon_val, send_sym, bits_msb. destruct (Z.eqb_spec (Znth s lens) 0); [contradiction | ].
  rewrite eob_bits_le_mod16 by lia. reflexivity.
Qed.

Lemma eob_bits_last last : last = 0 \/ last = 1 -> bits_le last 1 = [last =? 1].
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma eob_canon_vals_nth lens i : 0 <= i < Zlength lens -> Znth i (canon_vals lens) = canon_val lens i.
Proof.
  intros Hi. unfold canon_vals.
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; rewrite Zlength_correct in Hi; lia).
  rewrite <- (Z2Nat.id i) at 2 by lia. f_equal. f_equal.
  unfold Znth. destruct (Z_lt_dec i 0); [lia | ].
  rewrite seq_nth; [lia | rewrite Zlength_correct in Hi; lia].
Qed.

Lemma eob_sub_nth {A} {d: Inhabitant A} (l: list A) n i : 0 <= i < n -> n <= Zlength l ->
  Znth i l = Znth i (sublist 0 n l).
Proof. intros. rewrite Znth_sublist by lia. f_equal; lia. Qed.

(* 8 bytes of room (the harness's gp_assume) give room for 57 bits *)
Lemma eob_room8 B cap k : 0 <= k <= 57 -> Zlength B / 8 + 8 <= cap -> cap <= Int.max_unsigned -> bw_room B cap k.
Proof.
  intros Hk Hr Hc. unfold bw_room. split; [lia | split; [ | lia]].
  pose proof (Zlength_nonneg B). pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  set (q := Zlength B / 8) in *. set (r := Zlength B mod 8) in *.
  assert ((Zlength B + k + 7) / 8 < q + 9); [ | lia].
  apply Z.div_lt_upper_bound; lia.
Qed.

Ltac abs_sizes :=
  set (N0 := 262144) in *; set (N1 := 262145) in *; set (N2 := 524288) in *;
  assert (HN0: 262144 <= N0 <= 262144) by (unfold N0; lia);
  assert (HN1: 262145 <= N1 <= 262145) by (unfold N1; lia);
  assert (HN2: 524288 <= N2 <= 524288) by (unfold N2; lia);
  clearbody N0 N1 N2.
Ltac rest_sizes :=
  match goal with N0: Z, N1: Z, N2: Z, HN0: 262144 <= ?N0 <= 262144, HN1: 262145 <= ?N1 <= 262145,
                  HN2: 524288 <= ?N2 <= 524288 |- _ =>
    assert (N0 = 262144) by lia; assert (N1 = 262145) by lia; assert (N2 = 524288) by lia; subst N0 N1 N2
  end.

Ltac xcontra := exfalso; match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end.

Lemma id_eob_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr
    bs ls isbz last hk llc lcc dcc (R: ret_assert) :
  blk_hyps wrap wb flevel isel datap srcp isbp bs ls isbz last -> hk_ok hk -> hk_arrays_ok hk llc lcc dcc ->
  semax Delta_id
    (sym_post gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last hk llc lcc dcc)
    seg_eob
    (overridePost (blk_done gv vw vll vlc vdc vs vosn wrap wb flevel isel datap srcp isbp Fr bs ls isbz last) R).
Proof.
  intros HH Hk Ha. destruct R as [Rn Rb Rc Rr].
  unfold sym_post. Intros syms dcont.
  unfold seg_eob, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  rename H into Hsyms. rename H0 into Hdata. rename H1 into Hroom.
  destruct hk as [ | nlen ndist cl toks]; cbv [hk_dyn hk_nlen hk_ndist hk_ll hk_dl hk_bits] in *.
  - forward_if.
    { xcontra. }
    set (B := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++ [true; false] ++
              flat_map (send_one fixed_ll fixed_dl) syms) in *.
    forward_call (Tsh, Ews, B, 524288, srcp, vw, 256).
    { apply eob_room8; [lia | exact Hroom | rep_lia]. }
    assert (EB: B ++ send_sym fixed_ll 256 =
                enc_bits (id_wrapper wrap wb flevel) bs ++ enc_block (Zlength (enc_nf 0 bs)) (last =? 1) (Fixed syms)).
    { subst B. destruct HH as (_ & _ & _ & _ & _ & _ & _ & Hl & _). rewrite eob_bits_last by exact Hl.
      unfold enc_block, send_syms. rewrite <- !app_assoc. reflexivity. }
    rewrite EB. clearbody B. unfold blk_done. Exists (Fixed syms) dcont llc lcc dcc. entailer!.
    destruct Ha as [Hc _]. simpl. auto.
  - forward_if.
    2: { inv H. }
    destruct Ha as [Hc (Hll & Hlc & Hdc)].
    pose proof Hk as (Hnl & Hnd & Hcl & Hclr & Hclc & Htoks & Hlen & Hllok & Hdlok).
    set (LL := dyn_ll nlen toks) in *.
    assert (HLL: Zlength LL = nlen) by (unfold LL, dyn_ll; rewrite Zlength_sublist; lia).
    assert (E1: Znth 256 lcc = Vint (Int.repr (canon_val LL 256))).
    { rewrite (eob_sub_nth lcc nlen 256) by (destruct Hc as (? & ? & ?); lia). rewrite Hlc.
      unfold zvals. rewrite Znth_map by (unfold canon_vals; rewrite Zlength_map, Zlength_correct, seq_length;
                                          rewrite Zlength_correct in HLL; lia).
      rewrite eob_canon_vals_nth by lia. reflexivity. }
    assert (E2: Znth 256 llc = Vint (Int.repr (Znth 256 LL))).
    { rewrite (eob_sub_nth llc (nlen + ndist) 256) by (destruct Hc as (? & ? & ?); lia). rewrite Hll.
      unfold zvals. rewrite Znth_map by lia. unfold LL, dyn_ll. rewrite <- eob_sub_nth by lia. reflexivity. }
    destruct Hllok as (Hlok & H256 & _).
    assert (R256: 0 <= Znth 256 LL <= 15).
    { unfold lens_ok in Hlok. rewrite Forall_Znth in Hlok. apply (Hlok 256). lia. }
    assert (RC: 0 <= canon_val LL 256 < 65536).
    { unfold canon_val. destruct (Znth 256 LL =? 0); [lia | apply Z.mod_pos_bound; lia]. }
    change (@Znth val Inhabitant_val 256 lcc) with (@Znth val Vundef 256 lcc) in E1.
    change (@Znth val Inhabitant_val 256 llc) with (@Znth val Vundef 256 llc) in E2.
    abs_sizes.
    forward.
    1: (entailer!; rewrite E1; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
    forward.
    1: (entailer!; rewrite E2; simpl; rewrite Int.unsigned_repr by rep_lia; rep_lia).
    rest_sizes. rewrite E1, E2.
    set (B := enc_bits (id_wrapper wrap wb flevel) bs ++ bits_le last 1 ++
              ([false; true] ++ dyn_hdr_bits nlen ndist cl toks) ++
              flat_map (send_one LL (dyn_dl nlen ndist toks)) syms) in *.
    forward_call (Tsh, Ews, B, 524288, srcp, vw, canon_val LL 256, Znth 256 LL).
    { apply eob_room8; [lia | exact Hroom | rep_lia]. }
    rewrite eob_canon_send by auto.
    assert (EB: B ++ send_sym LL 256 =
                enc_bits (id_wrapper wrap wb flevel) bs ++
                enc_block (Zlength (enc_nf 0 bs)) (last =? 1) (Dynamic nlen ndist cl toks syms)).
    { subst B. destruct HH as (_ & _ & _ & _ & _ & _ & _ & Hl & _). rewrite eob_bits_last by exact Hl.
      unfold enc_block, send_syms, dyn_hdr_bits. fold LL. rewrite <- !app_assoc. reflexivity. }
    rewrite EB. clearbody B. unfold blk_done. Exists (Dynamic nlen ndist cl toks syms) dcont llc lcc dcc.
    entailer!.
    destruct Hk as (_ & _ & _ & _ & _ & _ & _ & Hllok & _).
    simpl. fold LL. rewrite Hcl.
    refine (conj Hnl (conj Hnd (conj _ (conj Hclr (conj Hclc (conj Htoks (conj Hlen (conj Hllok
              (conj Hdlok Hsyms))))))))). lia.
Qed.

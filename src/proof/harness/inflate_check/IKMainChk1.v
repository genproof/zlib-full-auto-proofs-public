(* Law inflate_check, main: the check `if (raw) gp_assert(s.adler == adler0); else if (tout != 0) { the header
   bytes; s.adler == rc (gzip) or ra (zlib) }` (IKMainKit.v seg_L2 up to seg_L3); then seg_L3 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit.
Local Open Scope logic.

Lemma c1_znth src i: 0 <= i < Zlength src ->
  forall d: val, @Znth val d i (bytes_rep src) = Vint (Int.repr (Znth i src)).
Proof.
  intros R d. unfold bytes_rep, Znth. rewrite !if_false by lia.
  rewrite nth_map' with (d' := 0); [reflexivity | ]. rewrite Zlength_correct in R. lia.
Qed.

Lemma c1_byte src i: bytes_ok src -> 0 <= i < Zlength src -> 0 <= Znth i src <= Byte.max_unsigned.
Proof. intros B R. unfold bytes_ok in B. eapply Forall_Znth in B; eauto. Qed.

Lemma c1_shr b: 0 <= b <= 255 -> Z.shiftr b 4 <= 7 ->
  Int.lt (Int.repr 7) (Int.shr (Int.repr b) (Int.repr 4)) = false.
Proof.
  intros R S. unfold Int.shr. rewrite Int.signed_repr by rep_lia. rewrite (Int.unsigned_repr 4) by rep_lia.
  assert (0 <= Z.shiftr b 4) by (apply Z.shiftr_nonneg; lia).
  unfold Int.lt. rewrite !Int.signed_repr by rep_lia. destruct (zlt 7 (Z.shiftr b 4)); auto; lia.
Qed.

Lemma c1_lor b0 b1: 0 <= b1 < 256 -> Z.lor (b0 * 256) b1 = b0 * 256 + b1.
Proof.
  intros R.
  assert (L: Z.land (b0 * 256) b1 = 0).
  { assert (E: b1 = Z.land b1 (Z.ones 8)) by (rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
    rewrite E, (Z.land_comm b1), Z.land_assoc, (Z.land_ones (b0 * 256)) by lia.
    change (2 ^ 8) with 256. rewrite Z_mod_mult. apply Z.land_0_l. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma c1_hdr b0 b1: 0 <= b0 <= 255 -> 0 <= b1 <= 255 ->
  Int.modu (Int.or (Int.shl (Int.repr b0) (Int.repr 8)) (Int.repr b1)) (Int.repr 31) =
  Int.repr ((b0 * 256 + b1) mod 31).
Proof.
  intros R0 R1. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite or_repr, c1_lor by lia.
  unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma chk1_ok {Espec: OracleKind} gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest
    (Post: ret_assert) :
  ik_mid_facts w srcp src adler0 pos' out' r z' ->
  semax Delta_m (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest) seg_L3 Post ->
  semax Delta_m (ik_mid gv vs vosn w srcp src adler0 pos' out' r stop ibp obp z' sp Rest) seg_L2 Post.
Proof.
  intros MF HL3.
  destruct MF as (Hw & Hpos & Hn & Hsrc & Psrc & Had0 & Hout & Hz & Hr & Hraw & Hhdr & Hchk & Hend).
  destruct Post as [Pn Pb Pc Pr].
  unfold ik_mid, seg_L2. unfold ik_tup.
  abbreviate_semax.
  ifsame.
  { (* raw *)
    assert (w < 0) by (unfold ik_raw in *; destruct (w <? 0) eqn:E; [apply Z.ltb_lt in E; lia | contradiction]).
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite Hraw by lia. simpl. rewrite Int64.eq_true. reflexivity. }
    entailer!. }
  { assert (Hw0: 0 <= w) by (unfold ik_raw in *; destruct (w <? 0) eqn:E; [discriminate | apply Z.ltb_ge in E; lia]).
    ifsame.
    { assert (Hne: out' <> []) by (intro E; subst out'; apply H0; reflexivity).
      specialize (Hhdr Hw0 Hne). specialize (Hchk Hw0 (or_introl Hne)).
      unfold ik_hdr, ik_chk in *.
      destruct (ik_gz w src) eqn:G.
      { assert (Egz: ik_gzv w src = 1) by (unfold ik_gzv; rewrite G, (proj2 (Z.leb_le 0 w) Hw0); reflexivity).
        destruct Hhdr as (G4 & G0 & G1 & G2 & G3).
        assert (B0: forall d: val, @Znth val d 0 (bytes_rep src) = Vint (Int.repr 31)) by (intros; rewrite c1_znth by lia; rewrite G0; reflexivity).
        assert (B1: forall d: val, @Znth val d 1 (bytes_rep src) = Vint (Int.repr 139)) by (intros; rewrite c1_znth by lia; rewrite G1; reflexivity).
        assert (B2: forall d: val, @Znth val d 2 (bytes_rep src) = Vint (Int.repr 8)) by (intros; rewrite c1_znth by lia; rewrite G2; reflexivity).
        assert (B3: forall d: val, @Znth val d 3 (bytes_rep src) = Vint (Int.repr (Znth 3 src))) by (intros; rewrite c1_znth by lia; reflexivity).
        pose proof (c1_byte src 3 Hsrc ltac:(lia)) as R3.
        ifsame.
        2: { exfalso. rewrite Egz in *. apply Int.one_not_zero. assumption. }
        forward.
        { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite B0.
        ifpost _t'20 (Int.repr 1).
        { forward. { entailer!. rewrite B1. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite B1. forward. entailer!. }
        { exfalso. congruence. }
        ifpost _t'21 (Int.repr 1).
        { forward. { entailer!. rewrite B2. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite B2. forward. entailer!. }
        { exfalso. apply Int.one_not_zero. assumption. }
        ifpost _t'22 (Int.repr 1).
        { forward. { entailer!. rewrite B3. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite B3. forward. entailer!. rewrite G3. reflexivity. }
        { exfalso. apply Int.one_not_zero. assumption. }
        gpa.
        forward.
        forward_call (Int.repr 1).
        { entailer!. rewrite Hchk. simpl. rewrite Int64.eq_true. reflexivity. }
        entailer!. }
      { assert (Egz: ik_gzv w src = 0) by (unfold ik_gzv; rewrite G, (proj2 (Z.leb_le 0 w) Hw0); reflexivity).
        destruct Hhdr as (G4 & G0 & G1 & G2).
        pose proof (c1_byte src 0 Hsrc ltac:(lia)) as R0.
        pose proof (c1_byte src 1 Hsrc ltac:(lia)) as R1.
        assert (B0: forall d: val, @Znth val d 0 (bytes_rep src) = Vint (Int.repr (Znth 0 src))) by (intros; rewrite c1_znth by lia; reflexivity).
        assert (B1: forall d: val, @Znth val d 1 (bytes_rep src) = Vint (Int.repr (Znth 1 src))) by (intros; rewrite c1_znth by lia; reflexivity).
        ifsame.
        { exfalso. rewrite Egz in *. apply H1. reflexivity. }
        forward.
        { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite B0.
        ifpost _t'23 (Int.repr 1).
        { forward. { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite B0. forward. entailer!. rewrite c1_shr by rep_lia. reflexivity. }
        { exfalso. rewrite and_repr, G0 in *. contradiction. }
        gpa.
        forward. { entailer!. rewrite B0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        forward. { entailer!. rewrite B1. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite B0, B1.
        forward_call (Int.repr 1).
        { entailer!. rewrite c1_hdr by rep_lia. rewrite G2. reflexivity. }
        forward.
        forward_call (Int.repr 1).
        { entailer!. rewrite Hchk. simpl. rewrite Int64.eq_true. reflexivity. }
        entailer!. } }
    { forward. entailer!. } }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate. exact HL3.
Qed.

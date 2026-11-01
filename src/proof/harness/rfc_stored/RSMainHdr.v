(* Law rfc_stored, main: statements 17-18, the header written over s0 (zlib: CMF = CINFO << 4 | 8 with CINFO
   chosen by upto(window - 8), FLG = s0's FLEVEL bits with FCHECK; gzip: ID1 ID2 CM, FLG = s0's FTEXT bit) is
   RSModel.rs_hdr (rs_A -> rs_B). *)
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

(* statement 17 (the zlib header), statement 18 (the gzip header) *)
Definition rs_hdr_s17 : statement :=
  ltac:(let x := eval cbv [rs_seg17] in rs_seg17 in match x with Ssequence ?a _ => exact a end).
Definition rs_hdr_s18 : statement :=
  ltac:(let x := eval cbv [rs_seg17] in rs_seg17 in match x with Ssequence _ (Ssequence ?a _) => exact a end).

Lemma rs_seg17_eq : rs_seg17 = Ssequence rs_hdr_s17 (Ssequence rs_hdr_s18 rs_seg19).
Proof. reflexivity. Qed.

Local Open Scope Z_scope.

(* a byte stored into / loaded from an array of bytes *)
Lemma rs_upd_bytes i l x v: x = Int.repr v -> upd_Znth i (bytes_rep l) (Vint x) = bytes_rep (upd_Znth i l v).
Proof. intros ->. apply (upd_Znth_map (fun b => Vint (Int.repr b))). Qed.

Lemma rs_znth_bytes i l: 0 <= i < Zlength l -> Znth i (bytes_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold bytes_rep. rewrite Znth_map by auto. reflexivity. Qed.

(* a boolean property checked on 0 .. n - 1 holds on that range *)
Lemma rs_check_range (P: Z -> bool) n:
  forallb P (map Z.of_nat (seq 0 n)) = true -> forall x, 0 <= x < Z.of_nat n -> P x = true.
Proof.
  intros H x Hx. rewrite forallb_forall in H. replace x with (Z.of_nat (Z.to_nat x)) by lia.
  apply H, in_map, in_seq. lia.
Qed.

(* FLG's FLEVEL bits: b & 0xc0 = FLEVEL * 64 with FLEVEL = b >> 6 *)
Lemma rs_land192 b: 0 <= b < 256 -> Z.land b 192 = Z.shiftr b 6 * 64.
Proof.
  intros Hb. apply Z.eqb_eq. revert b Hb.
  apply (rs_check_range (fun b => Z.land b 192 =? Z.shiftr b 6 * 64) 256). vm_compute. reflexivity.
Qed.

Lemma rs_shiftr6 b: 0 <= b < 256 -> 0 <= Z.shiftr b 6 <= 3.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
  assert (b / 64 < 4) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos b 64). lia.
Qed.

(* (unsigned char) (b & 0xc0) *)
Lemma rs_and192 b: 0 <= b < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.and (Int.repr b) (Int.repr 192))) = Int.repr (Z.shiftr b 6 * 64).
Proof.
  intros Hb. pose proof (rs_shiftr6 b Hb). rewrite <- rs_land192 by auto.
  unfold Int.and. rewrite !(Int.unsigned_repr b), !(Int.unsigned_repr 192) by rep_lia.
  rewrite rs_land192 by auto. destruct (rs_shiftr6 b Hb) as [K0 K3]. revert K0 K3.
  generalize (Z.shiftr b 6). intros k K0 K3.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as Hk by lia. repeat destruct Hk as [-> | Hk]; try reflexivity.
  subst k; reflexivity.
Qed.

(* the gzip FLG's FTEXT bit: b & 1, stored as an unsigned char *)
Lemma rs_and1 b: 0 <= b < 256 -> Int.zero_ext 8 (Int.and (Int.repr b) (Int.repr 1)) = Int.repr (Z.land b 1).
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  pose proof (rs_land1_range b). assert (Z.land b 1 = 0 \/ Z.land b 1 = 1) as [-> | ->] by lia; reflexivity.
Qed.

(* FLG with FCHECK: (unsigned char) (flg0 + (31 - (cmf * 256 + flg0) % 31) % 31) in C's int arithmetic, for
   CMF = CINFO * 16 + 8 (CINFO <= 7) and FLG0 = FLEVEL * 64 (FLEVEL <= 3) *)
Lemma rs_fcheck ci fl: 0 <= ci <= 7 -> 0 <= fl <= 3 ->
  let cmf := ci * 16 + 8 in let flg0 := fl * 64 in
  Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr flg0) (Int.mods (Int.sub (Int.repr 31)
    (Int.mods (Int.add (Int.mul (Int.repr cmf) (Int.repr 256)) (Int.repr flg0)) (Int.repr 31))) (Int.repr 31)))) =
  Int.repr (flg0 + (31 - (cmf * 256 + flg0) mod 31) mod 31).
Proof.
  intros Hc Hf.
  assert (ci = 0 \/ ci = 1 \/ ci = 2 \/ ci = 3 \/ ci = 4 \/ ci = 5 \/ ci = 6 \/ ci = 7) as Ec by lia.
  assert (fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3) as Ef by lia.
  repeat destruct Ec as [-> | Ec]; try (subst ci);
    repeat destruct Ef as [-> | Ef]; try (subst fl); reflexivity.
Qed.

(* the first two and the first four bytes overwritten *)
Lemma rs_upd2 (l: list Z) a b: 2 <= Zlength l -> upd_Znth 1 (upd_Znth 0 l a) b = [a; b] ++ sublist 2 (Zlength l) l.
Proof. intros. list_solve. Qed.

Lemma rs_upd4 (l: list Z) a b c e: 4 <= Zlength l ->
  upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 l a) b) c) e = [a; b; c; e] ++ sublist 4 (Zlength l) l.
Proof. intros. list_solve. Qed.

Local Open Scope logic.

(* rs_A with the stream object holding the bytes l (of s0's length) *)
Definition rs_Al (gv: globals) (vs vwb: val) (n nb na wr window: Z) (stp: val) (s0: list Z) (dp: val) (d: list Z)
    (op ep: val) (l: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _data_len (Vlong (Int64.repr n)); temp _blocks (Vlong (Int64.repr nb));
         temp _after (Vlong (Int64.repr na)); temp _wrapper (Vint (Int.repr wr));
         temp _window (Vint (Int.repr window)); temp _head_len (Vlong (Int64.repr (rs_hl wr)));
         temp _trailer_len (Vlong (Int64.repr (rs_tl wr))); temp _stream_len (Vlong (Int64.repr (Zlength s0)));
         temp _stream stp; temp _data dp; temp _out op; temp _expected ep;
         lvar _window_bits (tarray tint 3) vwb; lvar _strm (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at_ Tsh (tarray tint 3) vwb; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; Zlib.proof.crc32.Spec.crc_table_at Ers gv; version_lit gv;
       rs_hversion_lit gv;
       malloc_token Ews (tarray tuchar (Zlength s0)) stp;
       data_at Ews (tarray tuchar (Zlength s0)) (bytes_rep l) stp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep d) dp;
       malloc_token Ews (tarray tuchar n) op; data_at_ Ews (tarray tuchar n) op; rs_copy ep n d).

Lemma rs_A_Al gv vs vwb n nb na wr window stp s0 dp d op ep:
  rs_A gv vs vwb n nb na wr window stp s0 dp d op ep = rs_Al gv vs vwb n nb na wr window stp s0 dp d op ep s0.
Proof. reflexivity. Qed.

Lemma rs_B_Al gv vs vwb n nb na wr window stp s0 dp d op ep c:
  rs_B gv vs vwb n nb na wr window stp s0 dp d op ep c =
  rs_Al gv vs vwb n nb na wr window stp s0 dp d op ep (rs_hdr wr c s0 ++ sublist (rs_hl wr) (Zlength s0) s0).
Proof. reflexivity. Qed.

Lemma seg_hdr_ok {Espec: OracleKind} gv vs vwb n nb na wr window stp s0 dp d op ep:
  rs_A_facts n nb na wr window stp s0 dp d op ->
  (forall c, rs_c_ok wr window c ->
     semax Delta_m (rs_B gv vs vwb n nb na wr window stp s0 dp d op ep c) rs_seg19 POST_B) ->
  semax Delta_m (rs_A gv vs vwb n nb na wr window stp s0 dp d op ep) rs_seg17 POST_B.
Proof.
  intros F K. pose proof F as (Hn & Hnb & Hna & Hwr & Hw & Hs0 & Hd & Bs & Bd & Ps & Pd & Po).
  rewrite rs_A_Al, rs_seg17_eq. unfold rs_hdr_s17, rs_hdr_s18.
  destruct (Z.eq_dec wr 1) as [E1 | N1]; [ | destruct (Z.eq_dec wr 2) as [E2 | N2]].
  - subst wr. unfold rs_Al at 1. simpl rs_hl. simpl rs_tl.
    forward_if (EX c: Z, !! (0 <= c <= window - 8) &&
      (rs_Al gv vs vwb n nb na 1 window stp s0 dp d op ep (rs_hdr 1 c s0 ++ sublist 2 (Zlength s0) s0))).
    + forward_call (window - 8).
      Intros c. assert (L7: 7 <= Zlength s0) by (unfold rs_hl, rs_tl in Hs0; simpl in Hs0; lia).
      assert (B0: 0 <= Znth 0 s0 < 256) by (apply (proj1 (Forall_Znth _ _) Bs 0); lia).
      assert (B1: 0 <= Znth 1 s0 < 256) by (apply (proj1 (Forall_Znth _ _) Bs 1); lia).
      forward. erewrite (rs_upd_bytes 0 s0 _ (c * 16 + 8)).
      2:{ assert (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7) as Hc by lia.
          repeat destruct Hc as [-> | Hc]; try reflexivity; subst c; reflexivity. }
      assert (Z1: Zlength (upd_Znth 0 s0 (c*16+8)) = Zlength s0) by list_solve.
      assert (Z2: Znth 1 (upd_Znth 0 s0 (c*16+8)) = Znth 1 s0) by list_solve.
      forward.
      1:{ rewrite rs_znth_bytes, Z2 by lia. entailer!. rep_lia. }
      rewrite rs_znth_bytes, Z2 by lia.
      forward. erewrite (rs_upd_bytes 1 _ _ (Z.shiftr (Znth 1 s0) 6 * 64)) by (apply rs_and192; lia).
      rewrite rs_upd2 by lia. pose proof (rs_shiftr6 _ B1) as Bf.
      set (cmf := c * 16 + 8). set (flg0 := (Z.shiftr (Znth 1 s0) 6 * 64)%Z). set (r := sublist 2 (Zlength s0) s0).
      assert (R0: 0 <= cmf <= 120) by lia. assert (R1: 0 <= flg0 <= 192) by lia.
      forward; try (entailer!; rep_lia).
      forward; try (entailer!; rep_lia).
      forward; try (entailer!; rep_lia).
      forward.
      1:{ entailer!. assert (M: Int.repr 31 <> Int.mone) by (intros X; apply (f_equal Int.unsigned) in X;
            vm_compute in X; discriminate).
          split; [tauto | split; [ | tauto]].
          unfold Int.mods. rewrite (Int.signed_repr (cmf * 256 + flg0)), (Int.signed_repr 31) by rep_lia.
          rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound (cmf * 256 + flg0) 31 ltac:(lia)).
          rewrite Int.signed_repr by rep_lia. rep_lia. }
      erewrite rs_upd_bytes by (apply (rs_fcheck c (Z.shiftr (Znth 1 s0) 6)); lia).
      assert (Hh: upd_Znth 1 ([cmf; flg0] ++ r) (flg0 + (31 - (cmf * 256 + flg0) mod 31) mod 31) =
                  rs_hdr 1 c s0 ++ r).
      { unfold rs_hdr, Zlib.proof.rfc1951.Format.zlib_hdr. simpl. replace ((c + 8 - 8) * 16 + 8) with cmf by (unfold cmf; lia).
        rewrite Z.add_0_r. fold flg0. list_solve. }
      change (Z.shiftr (Znth 1 s0) 6 * 64)%Z with flg0. change (c * 16 + 8)%Z with cmf. rewrite Hh.
      Exists c. unfold rs_Al. entailer!.
    + contradiction.
    + Intros c. unfold rs_Al. apply semax_extract_prop; intros Hc.
      let P := eval unfold rs_Al in
        (rs_Al gv vs vwb n nb na 1 window stp s0 dp d op ep (rs_hdr 1 c s0 ++ sublist 2 (Zlength s0) s0)) in
      forward_if P.
      * discriminate.
      * forward. unfold POST_B. destruct (overridePost FF POST_m). apply ENTAIL_refl.
      * eapply semax_pre; [ | apply (K c); intros _; lia ]. apply ENTAIL_refl.
  - subst wr. unfold rs_Al at 1.
    let P := eval unfold rs_Al in (rs_Al gv vs vwb n nb na 2 window stp s0 dp d op ep s0) in forward_if P.
    + discriminate.
    + forward. unfold POST_B. destruct (overridePost FF POST_m). apply ENTAIL_refl.
    + let P := eval unfold rs_Al in
        (rs_Al gv vs vwb n nb na 2 window stp s0 dp d op ep (rs_hdr 2 0 s0 ++ sublist 10 (Zlength s0) s0)) in
      forward_if P.
      * assert (L15: 15 <= Zlength s0) by (unfold rs_hl, rs_tl in Hs0; simpl in Hs0; lia).
        assert (B3: 0 <= Znth 3 s0 < 256) by (apply (proj1 (Forall_Znth _ _) Bs 3); lia).
        forward. erewrite (rs_upd_bytes 0 s0 _ 31) by reflexivity.
        forward. erewrite (rs_upd_bytes 1 _ _ 139) by reflexivity.
        forward. erewrite (rs_upd_bytes 2 _ _ 8) by reflexivity.
        assert (Z3: Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 s0 31) 139) 8) = Znth 3 s0) by list_solve.
        forward; rewrite ?rs_znth_bytes, ?Z3 by list_solve; try (entailer!; rep_lia).
        forward.
        erewrite (rs_upd_bytes 3 _ _ (Z.land (Znth 3 s0) 1)) by (apply rs_and1; lia).
        rewrite rs_upd4 by lia.
        replace ([31; 139; 8; Z.land (Znth 3 s0) 1] ++ sublist 4 (Zlength s0) s0)
          with (rs_hdr 2 0 s0 ++ sublist 10 (Zlength s0) s0)
          by (unfold rs_hdr; simpl; rewrite sublist_rejoin by lia; reflexivity).
        unfold POST_B. destruct (overridePost FF POST_m). cbn [tycontext.RA_normal]. entailer!.
      * contradiction.
      * eapply semax_pre; [ | apply (K 0); intros E; lia ]. apply ENTAIL_refl.
  - assert (wr = 0) by lia. subst wr. unfold rs_Al at 1.
    let P := eval unfold rs_Al in (rs_Al gv vs vwb n nb na 0 window stp s0 dp d op ep s0) in forward_if P.
    + discriminate.
    + forward. unfold POST_B. destruct (overridePost FF POST_m). apply ENTAIL_refl.
    + let P := eval unfold rs_Al in (rs_Al gv vs vwb n nb na 0 window stp s0 dp d op ep s0) in forward_if P.
      * discriminate.
      * forward. unfold POST_B. destruct (overridePost FF POST_m). apply ENTAIL_refl.
      * eapply semax_pre; [ | apply (K 0); intros E; lia ].
        rewrite rs_B_Al. replace (rs_hdr 0 0 s0 ++ sublist (rs_hl 0) (Zlength s0) s0) with s0
          by (unfold rs_hdr, rs_hl; simpl; rewrite sublist_same by lia; reflexivity).
        apply ENTAIL_refl.
Qed.

(* Law inflate_codes, main, branch `op >= 24`, part B (MainInfKit.v): `if (r == Z_NEED_DICT) { the asserts }`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.harness.inflate_codes.MainInfKit.

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Lemma mi_land32 b: Z.land b 32 <> 0 -> Int.eq (Int.repr (Z.land b 32)) (Int.repr 0) = false.
Proof.
  intros Hb. apply Int.eq_false. intro X. apply (f_equal Int.unsigned) in X. rewrite !Int.unsigned_repr_eq in X.
  replace (Z.land b 32 mod Int.modulus) with (Z.land b 32) in X.
  - change (0 mod Int.modulus) with 0 in X. contradiction.
  - change Int.modulus with (2 ^ 32). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma mi_B_ok {Espec: OracleKind} gv vs vo vosn vb vdl w srcp src pos final indict ain aout flush innull outnull
    stop ibp obp r z' sp Rest (Post: ret_assert) :
  mi_facts w src pos final indict ain aout flush innull outnull r z' -> isptr srcp ->
  semax Delta_m
    (mi_pre_B gv vs vo vosn vb vdl w srcp src pos final indict ain aout innull outnull stop ibp obp r z' sp Rest)
    seg_inf_B
    (overridePost
       (mi_pre_B gv vs vo vosn vb vdl w srcp src pos final indict ain aout innull outnull stop ibp obp r z' sp Rest)
       Post).
Proof.
  intros MF Psrc.
  unfold mi_facts in MF. cbv zeta in MF.
  destruct MF as (Hw & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hfl & Hin & Hout & Hfr & Hidr & Hz' & Hcode & Hai & Hao
                  & Hbad & Hok & Hbuf & Hdata & Hfin & Hnd).
  unfold mi_pre_B, seg_inf_B, mi_tup.
  destruct Post as [Pn Pb Pc Pr]. unfold overridePost.
  ifsame.
  { assert (Hr: -5 <= r <= 2).
    { unfold code_okb in Hcode. repeat rewrite orb_true_iff in Hcode.
      repeat match goal with H: _ \/ _ |- _ => destruct H end; apply Z.eqb_eq in H0; subst; cbv; split; congruence. }
    assert (r = Z_NEED_DICT) by (apply repr_inj_signed in H; [exact H | rep_lia | rep_lia]).
    destruct (Hnd H0) as (Hzo & Hpu & Hb1 & Had & Hid). clear Hnd.
    rewrite Hzo. gpa.
    forward_call (Int.repr 1). { entailer!. rewrite Hpu. reflexivity. }
    assert (Hn6: 6 <= Zlength src) by lia.
    assert (Hb1r := is_bytes_Znth src 1 Hsb ltac:(lia)).
    forward.
    { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite Znth_bytes_rep by lia.
    forward_call (Int.repr 1).
    { entailer!. rewrite mi_land32 by exact Hb1. reflexivity. }
    rewrite <- (bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
    forward_call (offset_val 2 srcp, Ews, srcp, 2, Zlength src, bytes_rep src, sublist 2 6 src).
    { unfold cbuf_ok. split3; [reflexivity | auto with share | ]. split3; [lia | lia | ].
      split3; [rewrite Zlength_sublist by lia; lia | apply is_bytes_sublist; auto | apply sublist_bytes_rep]. }
    try rewrite (bytes_adler_cs Ews (Zlength src) (bytes_rep src) srcp).
    forward.
    rewrite <- Had.
    forward_call (Int.repr 1).
    { entailer!. rewrite Int64.eq_true. reflexivity. }
    destruct Hidr as [I0|I1]; subst indict.
    - ifsame.
      { exfalso. match goal with X: Int.repr 0 <> Int.zero |- _ => apply X; reflexivity end. }
      { forward. entailer!. }
      rewrite Hzo. entailer!.
    - destruct (Hid ltac:(lia)) as [U M]. rewrite U, M.
      ifsame.
      { ifpost _t'48 (Int.repr 1).
        { forward. entailer!. }
        { exfalso. lia. }
        gpa. entailer!. }
      { exfalso. match goal with X: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact X end. }
      rewrite Hzo; try rewrite U; try rewrite M. entailer!. }
  { forward. entailer!. }
Qed.

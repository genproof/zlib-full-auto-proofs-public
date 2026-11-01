(* Law inflate_header, main: the checks of the loop body other than the gz_header's fields (IHMainKit.v):
   chk_ok (L18 .. L19): `if (reserved || badcrc) gp_assert(r != Z_STREAM_END); else gp_assert(r != Z_DATA_ERROR);`
   and `if (reserved && r == Z_DATA_ERROR) gp_assert(h.done == 0);`; fin_ok (L21 .. L25): `if (r == Z_STREAM_END)
   { h.done == 1; pos == total; s.total_out == 0 }`, the three free()s, `if (stop == 0) break;`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.

Lemma ih_int_neq r c: Int.min_signed <= r <= Int.max_signed -> Int.min_signed <= c <= Int.max_signed -> r <> c ->
  Int.eq (Int.repr r) (Int.repr c) = false.
Proof. intros. apply Int.eq_false. intro E. apply repr_inj_signed in E; auto. Qed.

Lemma ih_int_eq r: Int.eq (Int.repr r) (Int.repr r) = true.
Proof. apply Int.eq_true. Qed.

Ltac ih_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Ltac ih_infeas_eq := match goal with H: Int.eq _ _ = true |- _ => apply Int.same_if_eq in H end;
  match goal with H: Int.repr _ = Int.repr _ |- _ => apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end.

Lemma chk_ok {Espec: OracleKind} I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs
    (Post: ret_assert):
  ih_mid_facts I V g b P h0 H pos pos' ain r z' L' aout stop ibp obp q inb cont bs ->
  semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL20 Post ->
  semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL18 Post.
Proof.
  intros MF HK.
  pose proof MF as MF'.
  destruct MF' as (G & Hpost & Hne & Hpos' & Hpos & Hpa & Hz & HLv & HLok & _).
  pose proof G as G'. destruct G' as (CF & F53 & _).
  destruct Hpost as (Hr & Hai & Hrs1 & Hrs2 & Hrsv & Hdone & Hend & HI').
  assert (Hhd: i_head (l_s L') = true) by (apply (proj1 (ihf_live I CF g (b_w b) h0 _ z' L' (HI' Hne)))).
  destruct HLok as (Hhp & Hhs & Hxb & Hnb & Hcb).
  destruct Post as [Pn Pb Pc Pr].
  unfold ih_mid in HK |- *.
  set (src := ih_src g) in *. clearbody src.
  destruct V as [vs vh vxs vns vcs vosn]; simpl v_s_ in *; simpl v_h_ in *; simpl v_xs_ in *; simpl v_ns_ in *;
    simpl v_cs_ in *; simpl v_osn_ in *.
  rewrite (ih_head_mem_eq L' Hhd) in HK |- *. rewrite Hhp, Hhs in HK |- *.
  assert (Hrr: Int.min_signed <= r <= Int.max_signed) by (unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR in Hr; rep_lia).
  unfold segL18, Delta_m, Gmain; simplify_func_tycontext; abbreviate_semax.
  Intros.
  ifpost _t'53 (Int.repr (b2z (orb (ih_reserved g) (ih_badcrc g)))).
  { forward. entailer!. destruct (ih_reserved g), (ih_badcrc g); simpl in *; try reflexivity; ih_infeas. }
  { forward. entailer!. destruct (ih_reserved g), (ih_badcrc g); simpl in *; try reflexivity; ih_infeas. }
  ifsame.
  { assert (E1: orb (ih_reserved g) (ih_badcrc g) = true) by (destruct (orb (ih_reserved g) (ih_badcrc g)); [reflexivity | ih_infeas]).
    forward_call (Int.repr 1).
    { entailer!. rewrite (ih_int_neq r 1) by (auto; rep_lia || (apply Hrs1; auto)). reflexivity. }
    entailer!. }
  { assert (E1: orb (ih_reserved g) (ih_badcrc g) = false) by (destruct (orb (ih_reserved g) (ih_badcrc g)); [ih_infeas | reflexivity]).
    forward_call (Int.repr 1).
    { entailer!. change (Z.opp 3) with (-3); rewrite (ih_int_neq r (- 3)) by (auto; rep_lia || (apply Hrs2; auto)). reflexivity. }
    entailer!. }
  ifpost _t'54 (Int.repr (b2z (andb (ih_reserved g) (r =? - 3)))).
  { destruct (ih_reserved g); simpl in *; [ | ih_infeas].
    forward. entailer!. unfold b2z. destruct (Z.eqb_spec r (- 3)).
    { subst r. rewrite ih_int_eq. reflexivity. }
    { change (Z.opp 3) with (-3); rewrite (ih_int_neq r (- 3)) by (auto; rep_lia). reflexivity. } }
  { destruct (ih_reserved g); simpl in *; [ ih_infeas | ].
    forward. entailer!. }
  ifsame.
  { assert (Er: ih_reserved g = true /\ r = - 3).
    { destruct (ih_reserved g), (Z.eqb_spec r (- 3)); simpl in *; auto; ih_infeas. }
    destruct Er as [Er Er3].
    assert (Hd0: h_done (l_h L') = 0) by (apply Hrsv; auto).
    unfold ih_htup. forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Hd0. reflexivity. }
    entailer!. }
  { forward. entailer!. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | exact HK ].
  entailer!.
Qed.

Lemma fin_ok {Espec: OracleKind} I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs:
  ih_mid_facts I V g b P h0 H pos pos' ain r z' L' aout stop ibp obp q inb cont bs ->
  semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL21
    (ih_PL (ih_inv I gv V g b P h0 H Fr)).
Proof.
  intros MF.
  pose proof MF as MF'.
  destruct MF' as (G & Hpost & Hne & Hpos' & Hpos & Hpa & Hz & HLv & HLok & Hain & Haout & Hinb & Hcont & Hbs &
                   Hst & Pib & Pob & Pq).
  pose proof G as G'. destruct G' as (CF & F53 & _).
  destruct Hpost as (Hr & Hai & Hrs1 & Hrs2 & Hrsv & Hdone & Hend & HI').
  specialize (HI' Hne).
  assert (Hhd: i_head (l_s L') = true) by (apply (proj1 (ihf_live I CF g (b_w b) h0 _ z' L' HI'))).
  pose proof HLok as HLok'. destruct HLok' as (Hhp & Hhs & Hxb & Hnb & Hcb).
  unfold ih_mid, ih_PL, ih_inv, ih_at.
  set (src := ih_src g) in *. clearbody src.
  destruct V as [vs vh vxs vns vcs vosn]; simpl v_s_ in *; simpl v_h_ in *; simpl v_xs_ in *; simpl v_ns_ in *;
    simpl v_cs_ in *; simpl v_osn_ in *.
  rewrite (ih_head_mem_eq L' Hhd), Hhp, Hhs.
  rewrite (ih_istream_unfold gv Tsh vs z' L').
  assert (Hrr: Int.min_signed <= r <= Int.max_signed) by (unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END, Z_DATA_ERROR, Z_MEM_ERROR in Hr; rep_lia).
  unfold segL21, Delta_m, Gmain, POST_b, POST_m; simplify_func_tycontext; abbreviate_semax.
  Intros.
  ifsame.
  { assert (Hr1: r = 1) by (first [assumption | ih_infeas_eq]).
    destruct (Hend Hr1) as (Hd1 & Hend' & Htout).
    unfold ih_htup. forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Hd1. reflexivity. }
    forward_call (Int.repr 1).
    { entailer!. rewrite Hend', ih_int_eq. reflexivity. }
    unfold ih_tup. forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Htout. reflexivity. }
    entailer!. }
  { forward. entailer!. }
  forward_call (tarray tuchar ain, ibp, gv).
  { rewrite if_false by (destruct ibp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar ain) inb ibp). cancel. }
  forward_call (tarray tuchar aout, obp, gv).
  { rewrite if_false by (destruct obp; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) cont obp). cancel. }
  forward.
  forward_call (tarray tuchar aout, q, gv).
  { rewrite if_false by (destruct q; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar aout) (bytes_rep bs) q). cancel. }
  sep_apply (ih_istream_fold gv Tsh vs z' L'); auto.
  assert (Hp2: 0 <= pos' <= Zlength src) by lia.
  forward_if.
  { forward. Exists pos' z' L'. rewrite (ih_head_mem_eq L' Hhd), Hhp, Hhs. subst pos'. entailer!. }
  { forward. Exists pos' z' L'. rewrite (ih_head_mem_eq L' Hhd), Hhp, Hhs. subst pos'. entailer!. }
Qed.

(* Law inflate_header, main: the check of the gz_header once inflate() set done (IHMainKit.v segL20, position
   L20): `if (h.done != 0) { done == 1; text, time, xflags, os, hcrc; extra_len and field_ok(h.extra, xs, xmax,
   xf, xlen) or extra == Z_NULL; the same for name and comment }` (ih_done_ok of IHFacts.v, field_ok_spec of
   IHHelpers.v); then segL21 (given). *)
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

Lemma ih_int_eq r: Int.eq (Int.repr r) (Int.repr r) = true.
Proof. apply Int.eq_true. Qed.

Lemma ih_flb_zero flg bit: 0 <= flg <= 255 -> 0 <= bit <= 255 ->
  (Int.and (Int.repr flg) (Int.repr bit) = Int.zero <-> flb flg bit = false).
Proof.
  intros Hf Hb. unfold flb, Int.and. rewrite !Int.unsigned_repr by rep_lia.
  assert (L0: 0 <= Z.land flg bit) by (apply Z.land_nonneg; lia).
  assert (L1: Z.land flg bit < 2 ^ 8).
  { assert (M: Z.land flg bit = Z.land flg bit mod 2 ^ 8).
    { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite (Z.land_ones bit 8) by lia.
      rewrite Z.mod_small by lia. reflexivity. }
    rewrite M. apply Z.mod_pos_bound. lia. }
  destruct (Z.eqb_spec (Z.land flg bit) 0) as [E|E]; simpl.
  - rewrite E. split; auto.
  - split; [intros R | discriminate]. exfalso. apply E.
    apply repr_inj_unsigned in R; rep_lia.
Qed.

Ltac flbs := repeat match goal with
  | H: Int.and (Int.repr ?f) (Int.repr ?b) = Int.zero |- _ =>
      apply ih_flb_zero in H; [ | rep_lia | rep_lia]
  | H: Int.and (Int.repr ?f) (Int.repr ?b) <> Int.zero |- _ =>
      let E := fresh "E" in assert (E: flb f b = true) by
        (destruct (flb f b) eqn:E'; [reflexivity | apply ih_flb_zero in E'; [contradiction | rep_lia | rep_lia]]);
      clear H
  end.

Lemma ih_land_int f b: 0 <= f <= 255 -> 0 <= b <= 255 ->
  Int.and (Int.repr f) (Int.repr b) = Int.repr (Z.land f b).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma ih_hcrc_int f: 0 <= f <= 255 ->
  Int.and (Int.shr (Int.repr f) (Int.repr 1)) (Int.repr 1) = Int.repr (Z.land (Z.shiftr f 1) 1).
Proof.
  intros. unfold Int.shr, Int.and. rewrite Int.signed_repr by rep_lia.
  rewrite (Int.unsigned_repr 1) by rep_lia. change (Int.unsigned (Int.repr 1)) with 1.
  rewrite Int.unsigned_repr; [reflexivity | ].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  split; [apply Z.div_pos; lia | ]. assert (f / 2 <= f) by (apply Z.div_le_upper_bound; lia). rep_lia.
Qed.

Lemma field_okb_fbuf b0 f: field_okb (fbuf b0 f) b0 f = true.
Proof.
  unfold field_okb, fbuf.
  set (k := Z.min (Zlength f) (Zlength b0)).
  assert (Hk: 0 <= k <= Zlength f /\ k <= Zlength b0) by (subst k; pose proof (Zlength_nonneg f); pose proof (Zlength_nonneg b0); lia).
  assert (Hl: Zlength (sublist 0 k f ++ sublist k (Zlength b0) b0) = Zlength b0) by (rewrite Zlength_app, !Zlength_sublist; lia).
  rewrite Hl.
  replace (Z.min (Zlength f) (Zlength b0)) with k by reflexivity.
  rewrite sublist0_app1, sublist_sublist00, sublist_app2 by (rewrite ?Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. replace (k - (k - 0)) with 0 by lia. replace (Zlength b0 - (k - 0)) with (Zlength b0 - k) by lia.
  rewrite sublist_sublist by lia. replace (0 + k) with k by lia. replace (Zlength b0 - k + k) with (Zlength b0) by lia.
  destruct (list_eq_dec Z.eq_dec _ _) as [_ | C]; [ | exfalso; apply C; reflexivity].
  destruct (list_eq_dec Z.eq_dec _ _) as [_ | C]; [ reflexivity | exfalso; apply C; reflexivity].
Qed.

Lemma ih_hbuf_nn b m c: isptr b -> ih_hbuf b m c = data_at Ews (tarray tuchar m) (bytes_rep c) b.
Proof. intros Pb. unfold ih_hbuf. rewrite if_false; auto. destruct b; try contradiction; discriminate. Qed.

Lemma ih_hrest_nn bp q m bs: isptr bp ->
  ih_hrest bp q m bs = malloc_token Ews (tarray tuchar m) q * data_at Ews (tarray tuchar m) (bytes_rep bs) q *
                       (if zeq m 0 then emp else malloc_token Ews (tarray tuchar m) bp).
Proof. intros Pb. unfold ih_hrest. rewrite if_false; auto. destruct bp; try contradiction; discriminate. Qed.

Lemma done_ok {Espec: OracleKind} I gv V g b P h0 H Fr pos pos' ain r z' L' aout stop ibp obp q inb cont bs
    (Post: ret_assert):
  ih_mid_facts I V g b P h0 H pos pos' ain r z' L' aout stop ibp obp q inb cont bs ->
  semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL21 Post ->
  semax Delta_m (ih_mid gv V g b P h0 H Fr pos' r z' L' ain aout stop ibp obp q inb cont bs) segL20 Post.
Proof.
  intros MF HK.
  pose proof MF as MF'.
  destruct MF' as (G & Hpost & Hne & Hpos' & Hpos & Hpa & Hz & HLv & HLok & _).
  pose proof G as G'. destruct G' as (CF & F53 & Hwok & Hw16 & Hh0 & Ex0 & En0 & Ec0 & Exp0 & Enp0 & Ecp0 &
    Hxn0 & Hxn1 & Hnn0 & Hnn1 & Hcn0 & Hcn1).
  destruct Hpost as (Hr & Hai & Hrs1 & Hrs2 & Hrsv & Hdone & Hend & HI').
  destruct (ihf_live I CF g (b_w b) h0 _ z' L' (HI' Hne)) as (Hhd & Ex & En & Ec).
  destruct HLok as (Hhp & Hhs & Hxb & Hnb & Hcb).
  destruct Post as [Pn Pb Pc Pr].
  unfold ih_mid in HK |- *.
  set (src := ih_src g) in *. clearbody src.
  destruct V as [vs vh vxs vns vcs vosn]; simpl v_s_ in *; simpl v_h_ in *; simpl v_xs_ in *; simpl v_ns_ in *;
    simpl v_cs_ in *; simpl v_osn_ in *.
  rewrite (ih_head_mem_eq L' Hhd) in HK |- *. rewrite Hhp, Hhs, Hxb, Hnb, Hcb in HK |- *.
  unfold segL20, Delta_m, Gmain; simplify_func_tycontext; abbreviate_semax.
  Intros.
  assert (Hhw: hwf (l_h L')) by (destruct HLv as (_ & _ & _ & Hw & _); exact Hw).
  pose proof Hhw as Hhw'.
  destruct F53 as (Hg & Hwr & Hxm & Hnm & Hcm & Hxu & Hnu & Hcu & Psrc & Pxf & Pnf & Pcf).
  destruct Hhw as [_ _ _ _ _ _ _ _ [Hlx Hbx] [Hln Hbn] [Hlc Hbc] _ _].
  destruct Hh0 as [_ _ _ _ _ _ _ _ [Hlx0 Hbx0] [Hln0 Hbn0] [Hlc0 Hbc0] _ _].
  rewrite Ex in Hlx. rewrite En in Hln. rewrite Ec in Hlc.
  rewrite Ex0 in Hlx0. rewrite En0 in Hln0. rewrite Ec0 in Hlc0.
  set (hL := l_h L') in *. clearbody hL.
  rewrite Ex, En, Ec, Ex0, En0, Ec0 in *.
  unfold ih_htup. forward.
  ifsame.
  { assert (Hd: h_done hL <> 0).
    { intro E. rewrite E in *. contradiction. }
    destruct (Hdone Hne Hd) as (Hd1 & Htx & Htm & Hxf & Hos & Hhc & HX & HN & HC).
    forward.
    forward_call (Int.repr 1).
    { entailer!. rewrite Hd1. reflexivity. }
    destruct Hg as (Hf & Hm & Hxl & Hol & Hxn & Hxb' & Hnn & Hnb' & Hcn & Hcb' & Hdl).
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite Htx, ih_int_eq. reflexivity. }
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite Htm, Int64.eq_true. reflexivity. }
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite Hxf, ih_int_eq. reflexivity. }
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite Hos, ih_int_eq. reflexivity. }
    forward. forward_call (Int.repr 1).
    { entailer!. rewrite ih_hcrc_int by lia. rewrite Hhc, ih_int_eq. reflexivity. }
    (* the extra field *)
    ifsame.
    { flbs. change (fl g 4) with (flb (g_flg g) 4) in HX. rewrite E in HX.
      destruct HX as (HXl & HXp & HXb).
      forward. forward_call (Int.repr 1).
      { entailer!. rewrite HXl, ih_int_eq. reflexivity. }
      ifsame.
      { assert (Hn: b_xnul b <> 0) by (intro Z0; rewrite Z0 in *; contradiction).
        assert (Hp0: h_xp h0 = true) by (rewrite Exp0; destruct (Z.eqb_spec (b_xnul b) 0); [contradiction | reflexivity]).
        rewrite Hp0 in HXp. specialize (HXb Hp0).
        destruct (Hxn1 Hn) as (Pxb & Pxq).
        rewrite HXp.
        rewrite (ih_hbuf_nn (h_xb H)), (ih_hrest_nn (h_xb H)) by auto.
        Intros.
        forward. forward.
        rewrite <- Hlx.
        forward_call (h_xb H, Ews, h_xbuf hL, h_xq H, Ews, h_xbuf h0, p_xf P, Ews, g_xf g).
        forward_call (Int.repr 1).
        { entailer!. rewrite HXb, field_okb_fbuf. reflexivity. }
        rewrite Hlx, (ih_hbuf_nn (h_xb H)), (ih_hrest_nn (h_xb H)), HXp by auto.
        entailer!. }
      { forward. entailer!. }
      entailer!. }
    { flbs. change (fl g 4) with (flb (g_flg g) 4) in HX.
      match goal with Hf4: flb _ 4 = false |- _ => rewrite Hf4 in HX end.
      rewrite HX. forward. forward_call (Int.repr 1).
      rewrite HX. entailer!. }
    (* the name *)
    assert (Bn: is_bytes (g_nf g ++ [0])).
    { unfold is_bytes. apply Forall_app. split; [ | repeat constructor; rep_lia].
      eapply Forall_impl; [ | exact Hnb']. simpl. intros. rep_lia. }
    assert (Bc: is_bytes (g_cf g ++ [0])).
    { unfold is_bytes. apply Forall_app. split; [ | repeat constructor; rep_lia].
      eapply Forall_impl; [ | exact Hcb']. simpl. intros. rep_lia. }
    ifsame.
    { flbs. change (fl g 8) with (flb (g_flg g) 8) in HN.
      match goal with Ef: flb _ 8 = true |- _ => rewrite Ef in HN end.
      destruct HN as (HNp & HNb).
      ifsame.
      { assert (Hn: b_nnul b <> 0) by (intro Z0; rewrite Z0 in *; contradiction).
        assert (Hp0: h_np h0 = true) by (rewrite Enp0; destruct (Z.eqb_spec (b_nnul b) 0); [contradiction | reflexivity]).
        rewrite Hp0 in HNp. specialize (HNb Hp0).
        destruct (Hnn1 Hn) as (Pb1 & Pq1).
        rewrite HNp.
        rewrite (ih_hbuf_nn (h_nb H)), (ih_hrest_nn (h_nb H)) by auto.
        Intros.
        forward. forward.
        rewrite <- Hln.
        replace (Zlength (g_nf g) + 1) with (Zlength (g_nf g ++ [0])) by list_solve.
        forward_call (h_nb H, Ews, h_nbuf hL, h_nq H, Ews, h_nbuf h0, p_nf P, Ews, g_nf g ++ [0]).
        { entailer!. replace (Zlength (g_nf g ++ [0])) with (Zlength (g_nf g) + 1) by list_solve. reflexivity. }
        { rewrite Zlength_app, Zlength_cons, Zlength_nil. rep_lia. }
        forward_call (Int.repr 1).
        { entailer!. rewrite HNb, field_okb_fbuf. reflexivity. }
        rewrite Hln, (ih_hbuf_nn (h_nb H)), (ih_hrest_nn (h_nb H)), HNp by auto.
        replace (Zlength (g_nf g ++ [0])) with (Zlength (g_nf g) + 1) by list_solve.
        entailer!. }
      { forward. entailer!. } }
    { flbs. change (fl g 8) with (flb (g_flg g) 8) in HN.
      match goal with Ef: flb _ 8 = false |- _ => rewrite Ef in HN end.
      rewrite HN. forward. forward_call (Int.repr 1).
      rewrite HN. entailer!. }
    (* the comment *)
    ifsame.
    { flbs. change (fl g 16) with (flb (g_flg g) 16) in HC.
      match goal with Ef: flb _ 16 = true |- _ => rewrite Ef in HC end.
      destruct HC as (HCp & HCb).
      ifsame.
      { assert (Hn: b_cnul b <> 0) by (intro Z0; rewrite Z0 in *; contradiction).
        assert (Hp0: h_cp h0 = true) by (rewrite Ecp0; destruct (Z.eqb_spec (b_cnul b) 0); [contradiction | reflexivity]).
        rewrite Hp0 in HCp. specialize (HCb Hp0).
        destruct (Hcn1 Hn) as (Pb1 & Pq1).
        rewrite HCp.
        rewrite (ih_hbuf_nn (h_cb H)), (ih_hrest_nn (h_cb H)) by auto.
        Intros.
        forward. forward.
        rewrite <- Hlc.
        replace (Zlength (g_cf g) + 1) with (Zlength (g_cf g ++ [0])) by list_solve.
        forward_call (h_cb H, Ews, h_cbuf hL, h_cq H, Ews, h_cbuf h0, p_cf P, Ews, g_cf g ++ [0]).
        { entailer!. replace (Zlength (g_cf g ++ [0])) with (Zlength (g_cf g) + 1) by list_solve. reflexivity. }
        { rewrite Zlength_app, Zlength_cons, Zlength_nil. rep_lia. }
        forward_call (Int.repr 1).
        { entailer!. rewrite HCb, field_okb_fbuf. reflexivity. }
        rewrite Hlc, (ih_hbuf_nn (h_cb H)), (ih_hrest_nn (h_cb H)), HCp by auto.
        replace (Zlength (g_cf g ++ [0])) with (Zlength (g_cf g) + 1) by list_solve.
        entailer!. }
      { forward. entailer!. } }
    { flbs. change (fl g 16) with (flb (g_flg g) 16) in HC.
      match goal with Ef: flb _ 16 = false |- _ => rewrite Ef in HC end.
      rewrite HC. forward. forward_call (Int.repr 1).
      rewrite HC. entailer!. }
    entailer!. }
  { forward. entailer!. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | exact HK ].
  entailer!.
Qed.

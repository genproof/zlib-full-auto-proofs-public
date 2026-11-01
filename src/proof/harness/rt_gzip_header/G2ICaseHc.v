(* Law rt_gzip_header on the round-2 harness, inflate side: the header case HCRC (c_HCRC), the end of the header,
   adapted from law inflate_header's IHTCaseHc.v.  The header CRC deflate wrote is right (g_delta = 0), so the
   case always ends at TYPE (or leaves the call before, out of input). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the gz_header once HCRC is done *)
Lemma g2h_done g h0 h v :
  h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hcf g h0 h ->
  v = Z.land (Z.shiftr (g_flg g) 1) 1 ->
  ih_done_ok g h0 (set_h_done (set_h_hcrc h v) 1).
Proof.
  unfold hT, hM, hO, hxf, hnf, hcf, ih_done_ok. intros _ T M [X O] XF NF CF ->. cbn.
  repeat split; auto.
Qed.

Lemma g2c_hcrc : g2c_hcrc_stmt.
Proof.
  intros KIT g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E|E Pr B F Rs Ck Dn Ht Hm Ho Hx Hn Hc La|E]; try solve [ihk_nomode].
  pose proof (g2k_flg g G) as FR.
  destruct (proj1 (k2_bits KIT) (g_flg g) FR) as (_ & _ & _ & F512 & _ & _ & _ & _ & F9).
  pose proof (l2_ord _ _ LY) as ORD.
  destruct (g2k_lay_src g src LY) as (XS & NH & NH10).
  pose proof (g2k_badcrc g G) as BC.
  pose proof (jc2_wrap _ _ _ _ Kc) as W6.
  pose proof (jc2_head _ _ _ _ Kc) as HD.
  unfold c_HCRC. cbv beta zeta.
  rewrite F, F512.
  destruct (fl g 2) eqn:F2.
  - (* FHCRC: NEEDBITS(16) *)
    replace (negb (Z.land (g_flg g) 2 =? 0)) with true by (unfold fl in F2; rewrite F2; reflexivity).
    destruct X as (X0 & X1 & X2).
    destruct B as [Bb Bh].
    assert (NH2: ih_nh g = ih_nc g + 2) by (unfold ih_nh; rewrite F2; reflexivity).
    destruct (k2_nb KIT src inp pos (ih_nc g) 16 m (l2_bytes _ _ LY) X0 X1 X2 Ki Kn
                ltac:(lia) ltac:(lia) ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
      as (nx' & lv' & EN & R & C).
    rewrite EN. ihk_red.
    change ((16 + 7) / 8) with 2 in C.
    destruct C as [(-> & -> & C) | (-> & C)].
    + (* out of input *)
      rewrite Z.eqb_refl. cbn [ok_out2].
      g2k_km K.
      * right. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite E. unfold HCRC, Zlib.proof.inflate.Model.TYPE. lia.
      * g2k_jc.
      * apply J2_HCRC; auto; try lia. rewrite F2; lia. split; reflexivity.
      * exact Ks.
    + rewrite L0. cbn [Z.eqb].
      rewrite W6, (Ck F2). cbn [Z.land Z.eqb negb andb].
      rewrite C. rewrite (l2_hc _ _ LY F2), BC. cbn [negb].
      rewrite HD. ihk_red.
      cbn [ok_out2].
      eapply (g2k_km _ _ _ _ _ _ _ _ _ _ K); ihk_red;
        [reflexivity | lia | exact Kw | reflexivity | reflexivity | exact Kt | exact Kr | reflexivity
        | reflexivity | reflexivity | reflexivity | unfold lrange; rep_lia
        | left; first [exact L0 | reflexivity] | | | g2k_swf].
      * eapply g2k_jc; [exact Kc | ..]; reflexivity.
      * apply J2_TYPE; ihk_red; auto; try lia.
        apply g2h_done; auto. unfold fg in F. rewrite F, F9. reflexivity.
  - (* no FHCRC *)
    replace (negb (Z.land (g_flg g) 2 =? 0)) with false by (unfold fl in F2; rewrite F2; reflexivity).
    destruct B as [Bb Bh].
    assert (Pe: pos + m_nx m = ih_nc g) by lia.
    assert (NH0: ih_nh g = ih_nc g) by (unfold ih_nh; rewrite F2; lia).
    rewrite HD. ihk_red.
    cbn [ok_out2].
    eapply (g2k_km _ _ _ _ _ _ _ _ _ _ K); ihk_red;
      [reflexivity | lia | exact Kw | reflexivity | reflexivity | exact Kt | exact Kr | reflexivity
      | reflexivity | reflexivity | reflexivity | unfold lrange; rep_lia
        | left; first [exact L0 | reflexivity] | | | g2k_swf].
    + eapply g2k_jc; [exact Kc | ..]; reflexivity.
    + apply J2_TYPE; ihk_red; auto.
      * lia.
      * rewrite Bh, Pe, sublist_nil. reflexivity.
      * lia.
      * apply g2h_done; auto. unfold fg in F. rewrite F, F9. reflexivity.
Qed.

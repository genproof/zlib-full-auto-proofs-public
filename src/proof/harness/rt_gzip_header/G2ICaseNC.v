(* Law rt_gzip_header on the round-2 harness, inflate side: the header cases NAME and COMMENT (c_NAME2,
   c_COMMENT2), adapted from law inflate_header's IHTCaseNC.v *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma g2c_name : g2c_name_stmt.
Proof.
  intros KIT CN g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E Pne Plt Ho Bi Ln Fg Rs Ck Dn Ht Hm Hos Hxf Hnk Hc La|E|E|E];
    try solve [ihk_nomode].
  pose proof (g2k_flg g G) as FR.
  destruct (proj1 (k2_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & _ & F2048 & _).
  pose proof X as (X0 & X1 & X2).
  pose proof (l2_bytes _ _ LY) as LB.
  pose proof Fg as Fg'. unfold fg in Fg'.
  pose proof (l2_ord _ _ LY) as (O1 & O2 & O3 & O4).
  destruct (g2k_lay_src g src LY) as (XS & NH & NH10).
  pose proof HW as (_ & _ & _ & _ & _ & _ & NM & _ & _ & [NBL _] & _).
  unfold c_NAME2. cbv zeta. rewrite Fg', F2048.
  (* fin: the comment *)
  assert (FIN: forall m', m_inp m' = m_inp m -> m_nx m <= m_nx m' <= Zlength inp -> m_ow m' = [] ->
                m_out m' = m_out m -> m_aout m' = m_aout m -> m_tout m' = 0 -> m_ret m' = Z_OK ->
                m_in m' = m_in m -> m_tin m' = m_tin m -> m_snx m' = m_snx m -> m_sow m' = m_sow m ->
                m_adler m' = m_adler m -> m_leave m' = 0 -> Jc2 wb h0 (m_s m') (m_h m') -> swf (m_s m') ->
                pos + m_nx m' = ih_nn g -> m_hold m' = 0 -> m_bits m' = 0 -> ck2 g src (m_s m') (ih_nn g) ->
                h_done (m_h m') = 0 -> hT g (m_h m') -> hM g (m_h m') -> hO g (m_h m') -> hxf g h0 (m_h m') ->
                hnf g h0 (m_h m') -> hc0 h0 (m_h m') -> i_last (m_s m') = 0 ->
                i_flags (m_s m') = i_flags (m_s m) ->
                ok_out2 g src h0 wb pos inp aout tin
                  (c_COMMENT2 (set_mode (upd_s m' (fun s => set_i_length s 0)) COMMENT))).
  { intros m' I' N' W' U' A' T' R' Ii' Ti' S' Sw' D' L' C' SW' P' H' B' CK' Dn' T'' M' O' XF' NF' CC' LA' FL'.
    apply CN; [exact G | exact HW | exact LY | exact X | | ihk_red; exact L' | reflexivity].
    eapply (g2k_km_ad _ _ _ _ _ _ _ _ _ _ K); ihk_red; try assumption.
    - left; exact L'.
    - eapply g2k_jc; [exact C' | ..]; ihk_red; reflexivity.
    - pose proof HW as (_ & _ & _ & _ & _ & _ & _ & CM & _).
      apply J2_COMMENT; [reflexivity | lia | right; exact P' | exact H' | exact B'
                       | cbn [i_length set_i_mode set_i_length]; rewrite P', Z.sub_diag; destruct (h_cp h0); lia
                       | unfold fg in *; ihk_red; rewrite FL'; exact Fg' | exact Rs
                       | unfold ck2 in *; ihk_red; rewrite P'; exact CK' | exact Dn' | exact T'' | exact M'
                       | exact O' | exact XF' | exact NF' | | exact LA' ].
      unfold hck, hc0 in *. rewrite P', Z.sub_diag, sublist_nil, ihk_fbuf_nil. destruct CC' as [N1 N2].
      split; [exact N1 | intros _; exact N2].
    - g2k_swf. }
  destruct (fl g 8) eqn:F8.
  - (* FNAME *)
    replace (negb (Z.land (g_flg g) 8 =? 0)) with true by (unfold fl in F8; rewrite F8; reflexivity).
    cbv iota.
    set (f := g_nf g ++ [0]) in *.
    assert (NN: ih_nn g = ih_ne g + Zlength f) by (unfold ih_nn, f; rewrite F8, Zlength_app; cbn; lia).
    assert (Ef: sublist (ih_ne g) (ih_ne g + Zlength f) src = f) by (rewrite <- NN; apply (l2_nf _ _ LY F8)).
    destruct (ihk_field (g_nf g) ltac:(unfold g2h_ok in G; tauto)) as (Fl & Fz & Fnz). fold f in Fl, Fz, Fnz.
    set (j := pos + m_nx m - ih_ne g) in *.
    assert (Ej: j = pos + m_nx m - ih_ne g) by reflexivity. clearbody j.
    assert (Jr: 0 <= j < Zlength f) by lia.
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + (* no input: leave *)
      cbn [ok_out2]. g2k_km K.
      * right. unfold m_have in H0. rewrite Ki in H0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite E. unfold NAME, Zlib.proof.inflate.Model.TYPE. lia.
      * g2k_jc.
      * apply J2_NAME; auto; rewrite <- Ej; auto.
      * exact Ks.
    + rewrite (jc2_head _ _ _ _ Kc), (jc2_nmax _ _ _ _ Kc). cbn [andb].
      destruct Hnk as [NP NB]. rewrite NP.
      rewrite <- NBL.
      replace (i_length (m_s m)) with (if h_np h0 then Z.min j (Zlength (h_nbuf h0)) else 0)
        by (rewrite Ln, NBL, Ej; reflexivity).
      assert (Hv: 0 < m_have m) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (BY: forall i, 0 <= i < Z.min (m_have m) (Zlength f - j) ->
                    Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (j + i) f).
      { intros i I. rewrite Ki.
        rewrite (ihk_bytes src inp f pos (m_nx m) (ih_ne g) i X2 X0 X1 Ef)
          by (unfold m_have in *; rewrite Ki in *; lia).
        f_equal; lia. }
      rewrite (k2_zstr KIT f _ (h_nbuf (m_h m)) (h_nbuf h0) j (m_have m) (h_np h0) (Z.to_nat (m_have m))
                 Fl Fz Fnz Jr Hv (Nat.le_refl _) BY NB).
      set (c := Z.min (m_have m) (Zlength f - j)) in *.
      assert (Ec: c = Z.min (m_have m) (Zlength f - j)) by reflexivity. clearbody c.
      assert (Cr: 0 < c <= Zlength inp - m_nx m /\ j + c <= Zlength f)
        by (unfold m_have in *; rewrite Ki in *; lia).
      assert (IB: inbytes m c = sublist (pos + m_nx m) (pos + m_nx m + c) src).
      { unfold inbytes. rewrite Ki.
        destruct (k2_in KIT src inp pos (m_nx m) c X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        exact S. }
      rewrite IB.
      rewrite (g2k_crc_if KIT g); [| exact FR | exact Fg' | apply (jc2_wrap _ _ _ _ Kc)].
      assert (CK: ck2 g src (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) src)) else m_s m) (pos + m_nx m + c)).
      { unfold ck2 in *. intros F2. rewrite F2. cbn [i_check set_i_check]. rewrite (Ck F2).
        apply (k2_crc KIT); [exact LB | lia | lia]. }
      assert (LN: urange (if h_np h0 then Z.min (j + c) (Zlength (h_nbuf h0)) else 0))
        by (unfold urange; destruct (h_np h0); rep_lia).
      unfold hT, hM, hO, hc0 in *.
      assert (ZB: (Znth (j + c - 1) f = 0 /\ j + c = Zlength f) \/
                  (Znth (j + c - 1) f <> 0 /\ j + c < Zlength f)).
      { destruct (Z.eq_dec (j + c) (Zlength f)) as [JC|JC].
        - left. split; [rewrite JC; exact Fz | exact JC].
        - right. split; [apply Fnz; lia | lia]. }
      destruct ZB as [(Z0 & JC) | (Z0 & JC)].
      * rewrite Z0. cbn [Z.eqb negb].
        destruct (fl g 2) eqn:F2; ihk_red; apply FIN.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck2 _ _ _ _ => unfold ck2 in *; intros F; specialize (CK F); ihk_red; rewrite CK;
                            f_equal; f_equal; lia
        | |- hnf _ _ _ => unfold hnf; rewrite F8; cbn [h_np h_nbuf set_h_nbuf]; split; [exact NP|];
            intros XP; rewrite XP, JC, sublist_same by lia; reflexivity
        | |- Jc2 _ _ _ _ => g2k_jc
        | |- swf _ => g2k_swf
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | _ => first [assumption | reflexivity | lia]
        end.
      * replace (Znth (j + c - 1) f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0). cbn [negb].
        assert (NX: m_nx m + c = Zlength inp) by (unfold m_have in *; rewrite Ki in *; lia).
        destruct (fl g 2) eqn:F2; ihk_red; cbn [ok_out2]; g2k_km K.
        all: try (right; split; [reflexivity|]; split; [exact NX|]; split; [lia|];
                  rewrite E; unfold NAME, Zlib.proof.inflate.Model.TYPE; lia).
        all: try g2k_jc.
        all: try g2k_swf.
        all: apply J2_NAME.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck2 _ _ _ _ => unfold ck2 in *; intros F; specialize (CK F); ihk_red; rewrite CK;
                            f_equal; f_equal; lia
        | |- hnk _ _ _ _ => unfold hnk; cbn [h_np h_nbuf set_h_nbuf]; split; [exact NP|];
            intros XP; rewrite XP; f_equal; f_equal; lia
        | |- _ \/ _ => left; lia
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | |- (if ?b then _ else _) = _ => destruct b; [rewrite NBL; f_equal; lia | reflexivity]
        | _ => first [assumption | reflexivity | lia]
        end.
  - (* no FNAME *)
    replace (negb (Z.land (g_flg g) 8 =? 0)) with false by (unfold fl in F8; rewrite F8; reflexivity).
    cbv iota.
    assert (NN: ih_nn g = ih_ne g) by (unfold ih_nn; rewrite F8; lia).
    rewrite (jc2_head _ _ _ _ Kc).
    apply FIN.
    all: ihk_red.
    all: try lazymatch goal with
         | |- ck2 _ _ _ _ => unfold ck2 in *; intros F2; rewrite (Ck F2);
                             replace (pos + m_nx m) with (ih_nn g) by lia; reflexivity
         | |- hnf _ _ _ => unfold hnf; rewrite F8; reflexivity
         | |- Jc2 _ _ _ _ => g2k_jc
         | |- hc0 _ _ => unfold hc0 in *; ihk_red; exact Hc
         | _ => first [assumption | reflexivity | lia]
         end.
Qed.

Lemma g2c_comment : g2c_comment_stmt.
Proof.
  intros KIT CN g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E Pnn Plt Ho Bi Ln Fg Rs Ck Dn Ht Hm Hos Hxf Hnf Hck La|E|E];
    try solve [ihk_nomode].
  pose proof (g2k_flg g G) as FR.
  destruct (proj1 (k2_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & _ & _ & F4096 & _).
  pose proof X as (X0 & X1 & X2).
  pose proof (l2_bytes _ _ LY) as LB.
  pose proof Fg as Fg'. unfold fg in Fg'.
  pose proof (l2_ord _ _ LY) as (O1 & O2 & O3 & O4).
  destruct (g2k_lay_src g src LY) as (XS & NH & NH10).
  pose proof HW as (_ & _ & _ & _ & _ & _ & _ & CM & _ & _ & [CBL _] & _).
  unfold c_COMMENT2. cbv zeta. rewrite Fg', F4096.
  (* fin: the header CRC *)
  assert (FIN: forall m', m_inp m' = m_inp m -> m_nx m <= m_nx m' <= Zlength inp -> m_ow m' = [] ->
                m_out m' = m_out m -> m_aout m' = m_aout m -> m_tout m' = 0 -> m_ret m' = Z_OK ->
                m_in m' = m_in m -> m_tin m' = m_tin m -> m_snx m' = m_snx m -> m_sow m' = m_sow m ->
                m_adler m' = m_adler m -> m_leave m' = 0 -> Jc2 wb h0 (m_s m') (m_h m') -> swf (m_s m') ->
                pos + m_nx m' = ih_nc g -> m_hold m' = 0 -> m_bits m' = 0 -> ck2 g src (m_s m') (ih_nc g) ->
                h_done (m_h m') = 0 -> hT g (m_h m') -> hM g (m_h m') -> hO g (m_h m') -> hxf g h0 (m_h m') ->
                hnf g h0 (m_h m') -> hcf g h0 (m_h m') -> i_last (m_s m') = 0 ->
                i_flags (m_s m') = i_flags (m_s m) ->
                ok_out2 g src h0 wb pos inp aout tin (c_HCRC (set_mode m' HCRC))).
  { intros m' I' N' W' U' A' T' R' Ii' Ti' S' Sw' D' L' C' SW' P' H' B' CK' Dn' T'' M' O' XF' NF' CF' LA' FL'.
    apply CN; [exact G | exact HW | exact LY | exact X | | ihk_red; exact L' | reflexivity].
    eapply (g2k_km_ad _ _ _ _ _ _ _ _ _ _ K); ihk_red; try assumption.
    - left; exact L'.
    - eapply g2k_jc; [exact C' | ..]; ihk_red; reflexivity.
    - apply J2_HCRC; [reflexivity | destruct (fl g 2); lia | rewrite P', H', B'; apply g2k_bb0
                     | unfold fg in *; ihk_red; rewrite FL'; exact Fg' | exact Rs
                     | unfold ck2 in *; ihk_red; exact CK' | exact Dn' | exact T'' | exact M'
                     | exact O' | exact XF' | exact NF' | exact CF' | exact LA' ].
    - g2k_swf. }
  destruct (fl g 16) eqn:F16.
  - (* FCOMMENT *)
    replace (negb (Z.land (g_flg g) 16 =? 0)) with true by (unfold fl in F16; rewrite F16; reflexivity).
    cbv iota.
    set (f := g_cf g ++ [0]) in *.
    assert (NC: ih_nc g = ih_nn g + Zlength f) by (unfold ih_nc, f; rewrite F16, Zlength_app; cbn; lia).
    assert (Ef: sublist (ih_nn g) (ih_nn g + Zlength f) src = f) by (rewrite <- NC; apply (l2_cf _ _ LY F16)).
    destruct (ihk_field (g_cf g) ltac:(unfold g2h_ok in G; tauto)) as (Fl & Fz & Fnz). fold f in Fl, Fz, Fnz.
    set (j := pos + m_nx m - ih_nn g) in *.
    assert (Ej: j = pos + m_nx m - ih_nn g) by reflexivity. clearbody j.
    assert (Jr: 0 <= j < Zlength f) by lia.
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + (* no input: leave *)
      cbn [ok_out2]. g2k_km K.
      * right. unfold m_have in H0. rewrite Ki in H0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite E. unfold COMMENT, Zlib.proof.inflate.Model.TYPE. lia.
      * g2k_jc.
      * apply J2_COMMENT; auto; rewrite <- Ej; auto.
      * exact Ks.
    + rewrite (jc2_head _ _ _ _ Kc), (jc2_cmax _ _ _ _ Kc). cbn [andb].
      destruct Hck as [CP CB]. rewrite CP.
      rewrite <- CBL.
      replace (i_length (m_s m)) with (if h_cp h0 then Z.min j (Zlength (h_cbuf h0)) else 0)
        by (rewrite Ln, CBL, Ej; reflexivity).
      assert (Hv: 0 < m_have m) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (BY: forall i, 0 <= i < Z.min (m_have m) (Zlength f - j) ->
                    Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (j + i) f).
      { intros i I. rewrite Ki.
        rewrite (ihk_bytes src inp f pos (m_nx m) (ih_nn g) i X2 X0 X1 Ef)
          by (unfold m_have in *; rewrite Ki in *; lia).
        f_equal; lia. }
      rewrite (k2_zstr KIT f _ (h_cbuf (m_h m)) (h_cbuf h0) j (m_have m) (h_cp h0) (Z.to_nat (m_have m))
                 Fl Fz Fnz Jr Hv (Nat.le_refl _) BY CB).
      set (c := Z.min (m_have m) (Zlength f - j)) in *.
      assert (Ec: c = Z.min (m_have m) (Zlength f - j)) by reflexivity. clearbody c.
      assert (Cr: 0 < c <= Zlength inp - m_nx m /\ j + c <= Zlength f)
        by (unfold m_have in *; rewrite Ki in *; lia).
      assert (IB: inbytes m c = sublist (pos + m_nx m) (pos + m_nx m + c) src).
      { unfold inbytes. rewrite Ki.
        destruct (k2_in KIT src inp pos (m_nx m) c X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        exact S. }
      rewrite IB.
      rewrite (g2k_crc_if KIT g); [| exact FR | exact Fg' | apply (jc2_wrap _ _ _ _ Kc)].
      assert (CK: ck2 g src (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) src)) else m_s m) (pos + m_nx m + c)).
      { unfold ck2 in *. intros F2. rewrite F2. cbn [i_check set_i_check]. rewrite (Ck F2).
        apply (k2_crc KIT); [exact LB | lia | lia]. }
      assert (LN: urange (if h_cp h0 then Z.min (j + c) (Zlength (h_cbuf h0)) else 0))
        by (unfold urange; destruct (h_cp h0); rep_lia).
      unfold hT, hM, hO in *.
      assert (ZB: (Znth (j + c - 1) f = 0 /\ j + c = Zlength f) \/
                  (Znth (j + c - 1) f <> 0 /\ j + c < Zlength f)).
      { destruct (Z.eq_dec (j + c) (Zlength f)) as [JC|JC].
        - left. split; [rewrite JC; exact Fz | exact JC].
        - right. split; [apply Fnz; lia | lia]. }
      destruct ZB as [(Z0 & JC) | (Z0 & JC)].
      * rewrite Z0. cbn [Z.eqb negb].
        destruct (fl g 2) eqn:F2; ihk_red; apply FIN.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck2 _ _ _ _ => unfold ck2 in *; intros F; specialize (CK F); ihk_red; rewrite CK;
                            f_equal; f_equal; lia
        | |- hcf _ _ _ => unfold hcf; rewrite F16; cbn [h_cp h_cbuf set_h_cbuf]; split; [exact CP|];
            intros XP; rewrite XP, JC, sublist_same by lia; reflexivity
        | |- Jc2 _ _ _ _ => g2k_jc
        | |- swf _ => g2k_swf
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | |- hnf _ _ _ => unfold hnf in *; ihk_red; exact Hnf
        | _ => first [assumption | reflexivity | lia]
        end.
      * replace (Znth (j + c - 1) f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0). cbn [negb].
        assert (NX: m_nx m + c = Zlength inp) by (unfold m_have in *; rewrite Ki in *; lia).
        destruct (fl g 2) eqn:F2; ihk_red; cbn [ok_out2]; g2k_km K.
        all: try (right; split; [reflexivity|]; split; [exact NX|]; split; [lia|];
                  rewrite E; unfold COMMENT, Zlib.proof.inflate.Model.TYPE; lia).
        all: try g2k_jc.
        all: try g2k_swf.
        all: apply J2_COMMENT.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck2 _ _ _ _ => unfold ck2 in *; intros F; specialize (CK F); ihk_red; rewrite CK;
                            f_equal; f_equal; lia
        | |- hck _ _ _ _ => unfold hck; cbn [h_cp h_cbuf set_h_cbuf]; split; [exact CP|];
            intros XP; rewrite XP; f_equal; f_equal; lia
        | |- _ \/ _ => left; lia
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | |- hnf _ _ _ => unfold hnf in *; ihk_red; exact Hnf
        | |- (if ?b then _ else _) = _ => destruct b; [rewrite CBL; f_equal; lia | reflexivity]
        | _ => first [assumption | reflexivity | lia]
        end.
  - (* no FCOMMENT *)
    replace (negb (Z.land (g_flg g) 16 =? 0)) with false by (unfold fl in F16; rewrite F16; reflexivity).
    cbv iota.
    assert (NC: ih_nc g = ih_nn g) by (unfold ih_nc; rewrite F16; lia).
    rewrite (jc2_head _ _ _ _ Kc).
    apply FIN.
    all: ihk_red.
    all: try lazymatch goal with
         | |- ck2 _ _ _ _ => unfold ck2 in *; intros F2; rewrite (Ck F2);
                             replace (pos + m_nx m) with (ih_nc g) by lia; reflexivity
         | |- hcf _ _ _ => unfold hcf; rewrite F16; reflexivity
         | |- Jc2 _ _ _ _ => g2k_jc
         | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
         | |- hnf _ _ _ => unfold hnf in *; ihk_red; exact Hnf
         | |- hT _ _ => unfold hT in *; ihk_red; exact Ht
         | |- hM _ _ => unfold hM in *; ihk_red; exact Hm
         | |- hO _ _ => unfold hO in *; ihk_red; exact Hos
         | _ => first [assumption | reflexivity | lia]
         end.
Qed.

(* the two cases, for G2ICases.v *)
Lemma g2c_nc : g2c_name_stmt /\ g2c_comment_stmt.
Proof. exact (conj g2c_name g2c_comment). Qed.

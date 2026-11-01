(* Law inflate_header, theory part: cases NAME, COMMENT (c_NAME2, c_COMMENT2) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Zlib.proof.harness.inflate_header.IHTCaseKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ihc_name : ihc_name_stmt.
Proof.
  intros KIT CN g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihk_lay_src g LY) as [LS XS].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m NAME); auto; unfold NAME, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E Pne Plt Ho Bi Ln Fg Rs Ck Dn Ht Hm Hos Hxf Hnk Hc La|E|E|E|E|E|E|E|E|E];
    try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  destruct (proj1 (k_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & _ & F2048 & _).
  pose proof X as (X0 & X1 & X2).
  pose proof Fg as Fg'. unfold fg in Fg'.
  pose proof (ly_ord _ LY) as (O1 & O2 & O3 & O4).
  pose proof (hw_nbuf _ HW) as [NBL _].
  unfold c_NAME2. cbv zeta. rewrite Fg', F2048.
  (* fin: the comment *)
  assert (FIN: forall m', m_inp m' = inp -> 0 <= m_nx m' <= Zlength inp -> m_ow m' = [] -> m_out m' = m_aout m' ->
                m_tout m' = 0 -> m_ret m' = Z_OK -> Jc h0 (m_s m') (m_h m') -> m_leave m' = 0 -> i_mode (m_s m') = NAME ->
                pos + m_nx m' = ih_nn g -> m_hold m' = 0 -> m_bits m' = 0 -> ck g (m_s m') (ih_nn g) ->
                h_done (m_h m') = 0 -> hT g (m_h m') -> hM g (m_h m') -> hO g (m_h m') -> hxf g h0 (m_h m') ->
                hnf g h0 (m_h m') -> hc0 h0 (m_h m') -> i_last (m_s m') = 0 -> i_flags (m_s m') = i_flags (m_s m) ->
                ok_out g h0 pos inp (c_COMMENT2 (set_mode (upd_s m' (fun s => set_i_length s 0)) COMMENT))).
  { intros m' Ki' Kn' Kw' Ko' Kt' Rok' Kc' L' E' P' H' B' C' D' T' M' O' XF' NF' CC' LA' FL'.
    apply CN; [exact G | exact HW | exact X | | exact L' | reflexivity].
    constructor; ihk_red; [exact Ki' | lia | exact Kw' | exact Ko' | exact Kt' | left; exact Rok' | left; exact L'
                          | eapply ihk_jc; [exact Kc' | ..]; reflexivity | ].
    pose proof (hw_comm_max _ HW) as CM.
    apply J_COMMENT; [reflexivity | lia | right; exact P' | exact H' | exact B'
                     | cbn [i_length set_i_mode set_i_length]; rewrite P', Z.sub_diag; destruct (h_cp h0); lia
                     | unfold fg in *; ihk_red; rewrite FL'; exact Fg' | exact Rs
                     | unfold ck in *; ihk_red; rewrite P'; exact C' | exact D' | exact T' | exact M' | exact O'
                     | exact XF' | exact NF' | | exact LA' ].
    unfold hck, hc0 in *. rewrite P', Z.sub_diag, sublist_nil, ihk_fbuf_nil. destruct CC' as [N1 N2].
    split; [exact N1 | intros _; exact N2]. }
  destruct (fl g 8) eqn:F8.
  - (* FNAME *)
    replace (negb (Z.land (g_flg g) 8 =? 0)) with true by (unfold fl in F8; rewrite F8; reflexivity).
    cbv iota.
    set (f := g_nf g ++ [0]) in *.
    assert (NN: ih_nn g = ih_ne g + Zlength f) by (unfold ih_nn, f; rewrite F8, Zlength_app; cbn; lia).
    assert (Ef: sublist (ih_ne g) (ih_ne g + Zlength f) (ih_src g) = f) by (rewrite <- NN; apply (ly_nf _ LY F8)).
    destruct (ihk_field (g_nf g) ltac:(unfold ih_ok in G; tauto)) as (Fl & Fz & Fnz). fold f in Fl, Fz, Fnz.
    set (j := pos + m_nx m - ih_ne g) in *.
    assert (Ej: j = pos + m_nx m - ih_ne g) by reflexivity. clearbody j.
    assert (Jr: 0 <= j < Zlength f) by lia.
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + (* no input: leave *)
      cbn [ok_out]. constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok
                                          | right; reflexivity | ihk_jc | ].
      apply J_NAME; auto; rewrite <- Ej; auto.
    + rewrite (jc_head _ _ _ Kc), (jc_nmax _ _ _ Kc). cbn [andb].
      destruct Hnk as [NP NB]. rewrite NP.
      rewrite <- NBL.
      replace (i_length (m_s m)) with (if h_np h0 then Z.min j (Zlength (h_nbuf h0)) else 0)
        by (rewrite Ln, NBL, Ej; reflexivity).
      assert (Hv: 0 < m_have m) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (BY: forall i, 0 <= i < Z.min (m_have m) (Zlength f - j) ->
                    Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (j + i) f).
      { intros i I. rewrite Ki.
        rewrite (ihk_bytes (ih_src g) inp f pos (m_nx m) (ih_ne g) i X2 X0 X1 Ef)
          by (unfold m_have in *; rewrite Ki in *; lia).
        f_equal; lia. }
      rewrite (k_zstr KIT f _ (h_nbuf (m_h m)) (h_nbuf h0) j (m_have m) (h_np h0) (Z.to_nat (m_have m))
                 Fl Fz Fnz Jr Hv (Nat.le_refl _) BY NB).
      set (c := Z.min (m_have m) (Zlength f - j)) in *.
      assert (Ec: c = Z.min (m_have m) (Zlength f - j)) by reflexivity. clearbody c.
      assert (Cr: 0 < c <= Zlength inp - m_nx m /\ j + c <= Zlength f) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (IB: inbytes m c = sublist (pos + m_nx m) (pos + m_nx m + c) (ih_src g)).
      { unfold inbytes. rewrite Ki.
        destruct (k_in KIT (ih_src g) inp pos (m_nx m) c X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        exact S. }
      rewrite IB.
      rewrite (ihk_crc_if KIT g); [| exact FR | exact Fg' | apply (jc_wrap _ _ _ Kc)].
      assert (CK: ck g (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) (ih_src g))) else m_s m) (pos + m_nx m + c)).
      { unfold ck in *. intros F2. rewrite F2. cbn [i_check set_i_check]. rewrite (Ck F2).
        apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia]. }
      unfold hT, hM, hO, hc0 in *.
      assert (ZB: (Znth (j + c - 1) f = 0 /\ j + c = Zlength f) \/ (Znth (j + c - 1) f <> 0 /\ j + c < Zlength f)).
      { destruct (Z.eq_dec (j + c) (Zlength f)) as [JC|JC].
        - left. split; [rewrite JC; exact Fz | exact JC].
        - right. split; [apply Fnz; lia | lia]. }
      destruct ZB as [(Z0 & JC) | (Z0 & JC)].
      * rewrite Z0. cbn [Z.eqb negb].
        destruct (fl g 2) eqn:F2; ihk_red; apply FIN.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck _ _ _ => unfold ck in *; intros F; specialize (CK F); ihk_red; rewrite CK; f_equal; f_equal; lia
        | |- hnf _ _ _ => unfold hnf; rewrite F8; cbn [h_np h_nbuf set_h_nbuf]; split; [exact NP|];
            intros XP; rewrite XP, JC, sublist_same by lia; reflexivity
        | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
        | |- _ \/ _ => first [left; assumption | left; reflexivity | right; reflexivity]
        | |- J _ _ _ _ _ _ _ => fail
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | _ => first [assumption | reflexivity | lia]
        end.
      * replace (Znth (j + c - 1) f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0). cbn [negb].
        destruct (fl g 2) eqn:F2; ihk_red; cbn [ok_out]; constructor.
        all: ihk_red.
        all: try (lazymatch goal with |- J _ _ _ _ _ _ _ => apply J_NAME end).
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck _ _ _ => unfold ck in *; intros F; specialize (CK F); ihk_red; rewrite CK; f_equal; f_equal; lia
        | |- hnk _ _ _ _ => unfold hnk; cbn [h_np h_nbuf set_h_nbuf]; split; [exact NP|];
            intros XP; rewrite XP; f_equal; f_equal; lia
        | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
        | |- _ \/ _ => first [left; lia | left; assumption | left; reflexivity | right; reflexivity]
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | |- (if ?b then _ else _) = _ => destruct b; [rewrite NBL; f_equal; lia | reflexivity]
        | _ => first [assumption | reflexivity | lia]
        end.
  - (* no FNAME *)
    replace (negb (Z.land (g_flg g) 8 =? 0)) with false by (unfold fl in F8; rewrite F8; reflexivity).
    cbv iota.
    assert (NN: ih_nn g = ih_ne g) by (unfold ih_nn; rewrite F8; lia).
    rewrite (jc_head _ _ _ Kc).
    apply FIN.
    all: ihk_red.
    all: try lazymatch goal with
         | |- ck _ _ _ => unfold ck in *; intros F2; rewrite (Ck F2); replace (pos + m_nx m) with (ih_nn g) by lia; reflexivity
         | |- hnf _ _ _ => unfold hnf; rewrite F8; reflexivity
         | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
         | |- _ \/ _ => first [left; assumption | left; reflexivity | right; reflexivity]
         | |- J _ _ _ _ _ _ _ => apply J_NAME; auto
         | |- hc0 _ _ => unfold hc0 in *; ihk_red; exact Hc
         | _ => first [assumption | reflexivity | lia]
         end.
Qed.

Lemma ihc_comment : ihc_comment_stmt.
Proof.
  intros KIT CN g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY. destruct (ihk_lay_src g LY) as [LS XS].
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK) by (apply (ihk_ret m COMMENT); auto; unfold COMMENT, DONE, BAD; lia).
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E|E|E Pnn Plt Ho Bi Ln Fg Rs Ck Dn Ht Hm Hos Hxf Hnf Hck La|E|E|E|E|E|E|E|E];
    try solve [ihk_nomode].
  pose proof (ihk_flg g G) as FR.
  destruct (proj1 (k_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & _ & _ & F4096 & _).
  pose proof X as (X0 & X1 & X2).
  pose proof Fg as Fg'. unfold fg in Fg'.
  pose proof (ly_ord _ LY) as (O1 & O2 & O3 & O4).
  pose proof (hw_cbuf _ HW) as [CBL _].
  unfold c_COMMENT2. cbv zeta. rewrite Fg', F4096.
  (* fin: the header CRC *)
  assert (FIN: forall m', m_inp m' = inp -> 0 <= m_nx m' <= Zlength inp -> m_ow m' = [] -> m_out m' = m_aout m' ->
                m_tout m' = 0 -> m_ret m' = Z_OK -> Jc h0 (m_s m') (m_h m') -> m_leave m' = 0 ->
                pos + m_nx m' = ih_nc g -> m_hold m' = 0 -> m_bits m' = 0 -> ck g (m_s m') (ih_nc g) ->
                h_done (m_h m') = 0 -> hT g (m_h m') -> hM g (m_h m') -> hO g (m_h m') -> hxf g h0 (m_h m') ->
                hnf g h0 (m_h m') -> hcf g h0 (m_h m') -> i_last (m_s m') = 0 -> i_flags (m_s m') = i_flags (m_s m) ->
                ok_out g h0 pos inp (c_HCRC (set_mode m' HCRC))).
  { intros m' Ki' Kn' Kw' Ko' Kt' Rok' Kc' L' P' H' B' C' D' T' M' O' XF' NF' CF' LA' FL'.
    apply CN; [exact G | exact HW | exact X | | exact L' | reflexivity].
    constructor; ihk_red; [exact Ki' | lia | exact Kw' | exact Ko' | exact Kt' | left; exact Rok' | left; exact L'
                          | eapply ihk_jc; [exact Kc' | ..]; reflexivity | ].
    apply J_HCRC; [reflexivity | destruct (fl g 2); lia | rewrite P', H', B'; apply ihk_bb0
                  | unfold fg in *; ihk_red; rewrite FL'; exact Fg' | exact Rs
                  | unfold ck in *; ihk_red; exact C' | exact D' | exact T' | exact M' | exact O'
                  | exact XF' | exact NF' | exact CF' | exact LA' ]. }
  destruct (fl g 16) eqn:F16.
  - (* FCOMMENT *)
    replace (negb (Z.land (g_flg g) 16 =? 0)) with true by (unfold fl in F16; rewrite F16; reflexivity).
    cbv iota.
    set (f := g_cf g ++ [0]) in *.
    assert (NC: ih_nc g = ih_nn g + Zlength f) by (unfold ih_nc, f; rewrite F16, Zlength_app; cbn; lia).
    assert (Ef: sublist (ih_nn g) (ih_nn g + Zlength f) (ih_src g) = f) by (rewrite <- NC; apply (ly_cf _ LY F16)).
    destruct (ihk_field (g_cf g) ltac:(unfold ih_ok in G; tauto)) as (Fl & Fz & Fnz). fold f in Fl, Fz, Fnz.
    set (j := pos + m_nx m - ih_nn g) in *.
    assert (Ej: j = pos + m_nx m - ih_nn g) by reflexivity. clearbody j.
    assert (Jr: 0 <= j < Zlength f) by lia.
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + (* no input: leave *)
      cbn [ok_out]. constructor; ihk_red; [exact Ki | lia | exact Kw | exact Ko | exact Kt | left; exact Rok
                                          | right; reflexivity | ihk_jc | ].
      apply J_COMMENT; auto; rewrite <- Ej; auto.
    + rewrite (jc_head _ _ _ Kc), (jc_cmax _ _ _ Kc). cbn [andb].
      destruct Hck as [CP CB]. rewrite CP.
      rewrite <- CBL.
      replace (i_length (m_s m)) with (if h_cp h0 then Z.min j (Zlength (h_cbuf h0)) else 0)
        by (rewrite Ln, CBL, Ej; reflexivity).
      assert (Hv: 0 < m_have m) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (BY: forall i, 0 <= i < Z.min (m_have m) (Zlength f - j) ->
                    Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (j + i) f).
      { intros i I. rewrite Ki.
        rewrite (ihk_bytes (ih_src g) inp f pos (m_nx m) (ih_nn g) i X2 X0 X1 Ef)
          by (unfold m_have in *; rewrite Ki in *; lia).
        f_equal; lia. }
      rewrite (k_zstr KIT f _ (h_cbuf (m_h m)) (h_cbuf h0) j (m_have m) (h_cp h0) (Z.to_nat (m_have m))
                 Fl Fz Fnz Jr Hv (Nat.le_refl _) BY CB).
      set (c := Z.min (m_have m) (Zlength f - j)) in *.
      assert (Ec: c = Z.min (m_have m) (Zlength f - j)) by reflexivity. clearbody c.
      assert (Cr: 0 < c <= Zlength inp - m_nx m /\ j + c <= Zlength f) by (unfold m_have in *; rewrite Ki in *; lia).
      assert (IB: inbytes m c = sublist (pos + m_nx m) (pos + m_nx m + c) (ih_src g)).
      { unfold inbytes. rewrite Ki.
        destruct (k_in KIT (ih_src g) inp pos (m_nx m) c X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        exact S. }
      rewrite IB.
      rewrite (ihk_crc_if KIT g); [| exact FR | exact Fg' | apply (jc_wrap _ _ _ Kc)].
      assert (CK: ck g (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) (ih_src g))) else m_s m) (pos + m_nx m + c)).
      { unfold ck in *. intros F2. rewrite F2. cbn [i_check set_i_check]. rewrite (Ck F2).
        apply (k_crc KIT); [apply (ly_bytes _ LY) | lia | lia]. }
      unfold hT, hM, hO in *.
      assert (ZB: (Znth (j + c - 1) f = 0 /\ j + c = Zlength f) \/ (Znth (j + c - 1) f <> 0 /\ j + c < Zlength f)).
      { destruct (Z.eq_dec (j + c) (Zlength f)) as [JC|JC].
        - left. split; [rewrite JC; exact Fz | exact JC].
        - right. split; [apply Fnz; lia | lia]. }
      destruct ZB as [(Z0 & JC) | (Z0 & JC)].
      * rewrite Z0. cbn [Z.eqb negb].
        destruct (fl g 2) eqn:F2; ihk_red; apply FIN.
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck _ _ _ => unfold ck in *; intros F; specialize (CK F); ihk_red; rewrite CK; f_equal; f_equal; lia
        | |- hcf _ _ _ => unfold hcf; rewrite F16; cbn [h_cp h_cbuf set_h_cbuf]; split; [exact CP|];
            intros XP; rewrite XP, JC, sublist_same by lia; reflexivity
        | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
        | |- _ \/ _ => first [left; assumption | left; reflexivity | right; reflexivity]
        | |- fg _ _ => unfold fg in *; ihk_red; assumption
        | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
        | |- hnf _ _ _ => unfold hnf in *; ihk_red; exact Hnf
        | _ => first [assumption | reflexivity | lia]
        end.
      * replace (Znth (j + c - 1) f =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0). cbn [negb].
        destruct (fl g 2) eqn:F2; ihk_red; cbn [ok_out]; constructor.
        all: ihk_red.
        all: try (lazymatch goal with |- J _ _ _ _ _ _ _ => apply J_COMMENT end).
        all: ihk_red.
        all: try lazymatch goal with
        | |- ck _ _ _ => unfold ck in *; intros F; specialize (CK F); ihk_red; rewrite CK; f_equal; f_equal; lia
        | |- hck _ _ _ _ => unfold hck; cbn [h_cp h_cbuf set_h_cbuf]; split; [exact CP|];
            intros XP; rewrite XP; f_equal; f_equal; lia
        | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
        | |- _ \/ _ => first [left; lia | left; assumption | left; reflexivity | right; reflexivity]
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
    rewrite (jc_head _ _ _ Kc).
    apply FIN.
    all: ihk_red.
    all: try lazymatch goal with
         | |- ck _ _ _ => unfold ck in *; intros F2; rewrite (Ck F2); replace (pos + m_nx m) with (ih_nc g) by lia; reflexivity
         | |- hcf _ _ _ => unfold hcf; rewrite F16; reflexivity
         | |- Jc _ _ _ => eapply ihk_jc; [exact Kc | ..]; ihk_red; reflexivity
         | |- hxf _ _ _ => unfold hxf in *; ihk_red; exact Hxf
         | |- hnf _ _ _ => unfold hnf in *; ihk_red; exact Hnf
         | |- hT _ _ => unfold hT in *; ihk_red; exact Ht
         | |- hM _ _ => unfold hM in *; ihk_red; exact Hm
         | |- hO _ _ => unfold hO in *; ihk_red; exact Hos
         | _ => first [assumption | reflexivity | lia]
         end.
Qed.


Lemma ihc_nc : ihc_name_stmt /\ ihc_comment_stmt.
Proof. exact (conj ihc_name ihc_comment). Qed.

(* Law rt_gzip_header on the round-2 harness, inflate side: the header case EXTRA (c_EXTRA2), adapted from law
   inflate_header's IHTCaseEx.v *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2ICaseKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the extra field's buffer after one chunk of c bytes (j stored before); the buffer has extra_max bytes
   (RTH8Spec.hwf8), the field at most 65535 *)
Lemma g2x_buf (KIT: g2_kit) g h0 h j c :
  fl g 4 = true -> hwf8 h0 -> h_extra_max h = h_extra_max h0 -> hxk g h0 j h ->
  0 <= j -> 0 < c -> j + c <= Zlength (g_xf g) -> Zlength (g_xf g) <= 65535 ->
  hxk g h0 (j + c)
    (if (h_xp h && (j <? h_extra_max h))%bool then
       set_h_xbuf h (put_bytes (h_xbuf h) j
         (sublist j (j + (if h_extra_max h <? u32 (j + c) then h_extra_max h - j else c)) (g_xf g)))
     else h).
Proof.
  intros F4 HW XM Hx J C JC XL. unfold hxk in *. rewrite F4 in *. destruct Hx as (Xl & Xp & Xb).
  destruct HW as (_ & _ & _ & _ & _ & _ & _ & _ & [XB _] & _).
  destruct (k2_put KIT (h_xbuf h0) (g_xf g) j c J C JC XL) as [P1 P2].
  rewrite XM, Xp.
  destruct (h_xp h0) eqn:XP; cbn [andb].
  - destruct (Z.ltb_spec j (h_extra_max h0)) as [L|L]; cbn [h_extra_len h_xp h_xbuf set_h_xbuf].
    + split; [exact Xl|]. split; [exact Xp|]. intros _. rewrite (Xb eq_refl), <- XB.
      apply P1. lia.
    + split; [exact Xl|]. split; [exact Xp|]. intros _. rewrite (Xb eq_refl). apply P2. lia.
  - split; [exact Xl|]. split; [exact Xp|]. intros D; discriminate.
Qed.

Lemma g2c_extra : g2c_extra_stmt.
Proof.
  intros KIT CN g src h0 wb pos inp aout tin m G HW LY X K L0 MD.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks Kf].
  unfold m_mode in MD.
  destruct Kj as [E|E|E|E|E|E Pr Ho Bi Ln Fg Rs Ck Dn Ht Hm Hos Hx Hn Hc La|E|E|E|E];
    try solve [ihk_nomode].
  pose proof (g2k_flg g G) as FR.
  destruct (proj1 (k2_bits KIT) (g_flg g) FR) as (_ & _ & _ & _ & F1024 & _).
  assert (XL: Zlength (g_xf g) <= 65535) by (destruct G as (_ & _ & _ & _ & _ & XL & _); exact XL).
  pose proof HW as (_ & _ & _ & _ & _ & _ & NM & _).
  pose proof X as (X0 & X1 & X2).
  pose proof Fg as Fg'. unfold fg in Fg'.
  pose proof (l2_ord _ _ LY) as (O1 & O2 & O3 & O4).
  unfold c_EXTRA2. cbv zeta. rewrite Fg', F1024.
  (* fin: the name *)
  assert (FIN: forall m', Km2 g src h0 wb pos inp aout tin m' -> m_leave m' = 0 ->
                pos + m_nx m' = ih_ne g -> m_hold m' = 0 -> m_bits m' = 0 -> ck2 g src (m_s m') (ih_ne g) ->
                h_done (m_h m') = 0 -> hT g (m_h m') -> hM g (m_h m') -> hO g (m_h m') -> hxf g h0 (m_h m') ->
                hn0 h0 (m_h m') -> hc0 h0 (m_h m') -> i_last (m_s m') = 0 -> i_flags (m_s m') = i_flags (m_s m) ->
                ok_out2 g src h0 wb pos inp aout tin
                  (c_NAME2 (set_mode (upd_s m' (fun s => set_i_length s 0)) NAME))).
  { intros m' K' L' P' H' B' C' D' T' M' O' XF' N' CC' LA' FL'.
    pose proof K' as [Ki' Kn' Kw' Ko' Kt' Kr' Kl' Kc' Kj' Ks' Kf'].
    apply CN; [exact G | exact HW | exact LY | exact X | | exact L' | reflexivity].
    g2k_km K'.
    - left; exact L'.
    - g2k_jc.
    - apply J2_NAME; [reflexivity | lia | right; exact P' | exact H' | exact B'
                     | cbn [i_length set_i_mode set_i_length]; rewrite P', Z.sub_diag; destruct (h_np h0); lia
                     | unfold fg in *; ihk_red; rewrite FL'; exact Fg' | exact Rs
                     | unfold ck2 in *; ihk_red; rewrite P'; exact C' | exact D' | exact T' | exact M' | exact O'
                     | exact XF' | | exact CC' | exact LA' ].
      unfold hnk, hn0 in *. rewrite P', Z.sub_diag, sublist_nil, ihk_fbuf_nil. destruct N' as [N1 N2].
      split; [exact N1 | intros _; exact N2].
    - g2k_swf. }
  destruct (fl g 4) eqn:F4.
  - (* FEXTRA *)
    replace (negb (Z.land (g_flg g) 4 =? 0)) with true by (unfold fl in F4; rewrite F4; reflexivity).
    assert (NE: ih_ne g = 12 + Zlength (g_xf g)) by (unfold ih_ne; rewrite F4; lia).
    assert (XS12: ih_xs g = 12) by (unfold ih_xs; rewrite F4; reflexivity).
    specialize (Ln eq_refl).
    pose proof Hx as Hx0. unfold hxk in Hx0. rewrite F4 in Hx0. destruct Hx0 as (Xl & Xp & Xb).
    set (j := pos + m_nx m - 12) in *.
    assert (Ej: j = pos + m_nx m - 12) by reflexivity. clearbody j.
    assert (Jr: 0 <= j <= Zlength (g_xf g)) by lia.
    destruct (Z.eqb_spec (Z.min (i_length (m_s m)) (m_have m)) 0) as [C0|C0]; cbn [negb].
    + (* nothing to copy *)
      destruct (Z.eqb_spec (i_length (m_s m)) 0) as [LZ|LZ]; cbn [negb].
      * apply FIN; auto; try lia.
        all: lazymatch goal with
             | |- ck2 _ _ _ _ => unfold ck2 in *; intros F2; rewrite (Ck F2);
                                 replace (pos + m_nx m) with (ih_ne g) by lia; reflexivity
             | |- hxf _ _ _ => unfold hxf; rewrite F4; split; [exact Xl|]; split; [exact Xp|]; intros XP;
                 rewrite (Xb XP), XS12; f_equal; rewrite sublist_same; auto; lia
             end.
      * cbn [ok_out2]. unfold m_have in C0. rewrite Ki in C0.
        g2k_km K.
        -- right. split; [reflexivity|]. split; [lia|]. split; [lia|].
           rewrite E. unfold EXTRA, Zlib.proof.inflate.Model.TYPE. lia.
        -- g2k_jc.
        -- apply J2_EXTRA; auto.
        -- exact Ks.
    + (* a chunk of c bytes *)
      set (c := Z.min (i_length (m_s m)) (m_have m)) in *.
      assert (Ec: c = Z.min (i_length (m_s m)) (m_have m)) by reflexivity. clearbody c.
      assert (Cr: 0 < c <= Zlength inp - m_nx m /\ c <= i_length (m_s m))
        by (rewrite Ec; unfold m_have in *; rewrite Ki in *; lia).
      assert (U: u32 (h_extra_len (m_h m) - i_length (m_s m)) = j)
        by (rewrite Xl, Ln, NE; unfold u32; rewrite Z.mod_small; lia).
      rewrite U, (jc2_head _ _ _ _ Kc). cbn [andb].
      (* the bytes read are the field's *)
      assert (IN: forall n, 0 <= n <= c -> inbytes m n = sublist j (j + n) (g_xf g)).
      { intros n Nn. unfold inbytes. rewrite Ki.
        destruct (k2_in KIT src inp pos (m_nx m) n X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        rewrite S. replace (pos + m_nx m) with (12 + j) by lia.
        replace (12 + j + n) with (12 + (j + n)) by lia.
        apply (ihk_sub _ _ 12 (Zlength (g_xf g))); [rewrite <- NE; apply (l2_xf _ _ LY F4) | lia | lia | lia]. }
      set (n := if h_extra_max (m_h m) <? u32 (j + c) then h_extra_max (m_h m) - j else c) in *.
      set (h1 := if (h_xp (m_h m) && (j <? h_extra_max (m_h m)))%bool
                 then set_h_xbuf (m_h m) (put_bytes (h_xbuf (m_h m)) j (inbytes m n)) else m_h m).
      assert (Em1: (if (h_xp (m_h m) && (j <? h_extra_max (m_h m)))%bool
                    then upd_h m (fun h => set_h_xbuf h (put_bytes (h_xbuf h) j (inbytes m n))) else m)
                   = set_m_h m h1)
        by (unfold h1; destruct (_ && _)%bool; [reflexivity | destruct m; reflexivity]).
      rewrite Em1. clear Em1.
      assert (H1: hxk g h0 (j + c) h1 /\ h_done h1 = h_done (m_h m) /\ h_text h1 = h_text (m_h m) /\
                  h_time h1 = h_time (m_h m) /\ h_xflags h1 = h_xflags (m_h m) /\
                  h_os h1 = h_os (m_h m) /\ h_np h1 = h_np (m_h m) /\ h_nbuf h1 = h_nbuf (m_h m) /\
                  h_cp h1 = h_cp (m_h m) /\ h_cbuf h1 = h_cbuf (m_h m) /\
                  h_extra_max h1 = h_extra_max (m_h m) /\ h_name_max h1 = h_name_max (m_h m) /\
                  h_comm_max h1 = h_comm_max (m_h m)).
      { pose proof (g2x_buf KIT g h0 (m_h m) j c F4 HW (jc2_xmax _ _ _ _ Kc)
                     ltac:(rewrite XS12, <- Ej in Hx; exact Hx) ltac:(lia) ltac:(lia) ltac:(lia) XL) as XB.
        unfold h1. fold n in XB.
        destruct (h_xp (m_h m) && (j <? h_extra_max (m_h m)))%bool eqn:XC.
        - apply andb_true_iff in XC. destruct XC as [_ XC]. apply Z.ltb_lt in XC.
          assert (Uj: u32 (j + c) = j + c) by (unfold u32; apply Z.mod_small; lia).
          rewrite (IN n) by (unfold n; rewrite Uj; destruct (Z.ltb_spec (h_extra_max (m_h m)) (j + c)); lia).
          split; [exact XB|]. cbn. repeat split.
        - split; [exact XB|]. repeat split. }
      clearbody h1. clear n.
      destruct H1 as (Hx1 & D1 & T1' & M1' & XF1 & OS1 & NP1 & NB1 & CP1 & CB1 & XM1 & NM1 & CM1).
      assert (IB: inbytes (set_m_h m h1) c = sublist (pos + m_nx m) (pos + m_nx m + c) src).
      { unfold inbytes. cbn [m_nx m_inp set_m_h]. rewrite Ki.
        destruct (k2_in KIT src inp pos (m_nx m) c X0 X1 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as [S _].
        exact S. }
      rewrite IB.
      rewrite (g2k_crc_if KIT g); [| exact FR | ihk_red; exact Fg' | ihk_red; apply (jc2_wrap _ _ _ _ Kc)].
      assert (CB: is_bytes (sublist (pos + m_nx m) (pos + m_nx m + c) src))
        by (apply Forall_sublist; apply (l2_bytes _ _ LY)).
      assert (CK: ck2 g src (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) src)) else m_s m) (pos + m_nx m + c)).
      { unfold ck2 in *. intros F2. rewrite F2. cbn [i_check set_i_check]. rewrite (Ck F2).
        apply (k2_crc KIT); [apply (l2_bytes _ _ LY) | lia | lia]. }
      assert (SW: swf (if fl g 2 then set_i_check (m_s m) (ref_crc32 (i_check (m_s m))
                        (sublist (pos + m_nx m) (pos + m_nx m + c) src)) else m_s m)).
      { destruct (fl g 2); [apply g2k_swf_check; [exact Ks | apply g2k_crc_lrange; exact CB] | exact Ks]. }
      unfold m_have in Ec. rewrite Ki in Ec.
      unfold hT, hM, hO, hn0, hc0 in *.
      destruct (fl g 2) eqn:F2; ihk_red;
      (destruct (Z.eqb_spec (i_length (m_s m) - c) 0) as [LZ|LZ]; cbn [negb];
       [ apply FIN | cbn [ok_out2] ]); ihk_red.
      all: try (lazymatch goal with |- Km2 _ _ _ _ _ _ _ _ _ => g2k_km K end).
      all: ihk_red.
      all: try (lazymatch goal with |- J2 _ _ _ _ _ _ _ _ => apply J2_EXTRA end).
      all: ihk_red.
      all: try lazymatch goal with
      | |- ck2 _ _ _ _ => unfold ck2 in *; intros F; specialize (CK F); ihk_red; rewrite CK; f_equal; f_equal; lia
      | |- hxf _ _ _ =>
          unfold hxf; rewrite F4; unfold hxk in Hx1; rewrite F4 in Hx1; destruct Hx1 as (A1 & A2 & A3);
          split; [exact A1|]; split; [exact A2|]; intros XP; rewrite (A3 XP); f_equal; apply sublist_same; lia
      | |- hxk _ _ _ _ => rewrite XS12; replace (pos + (m_nx m + c) - 12) with (j + c) by lia; exact Hx1
      | |- Jc2 _ _ _ _ => eapply g2k_jc; [exact Kc | ..]; ihk_red; congruence
      | |- swf _ => apply g2k_swf_length; [exact SW | unfold urange; rep_lia]
      | |- _ \/ _ =>
          first [ left; assumption | left; reflexivity
                | right; split; [reflexivity|]; split; [lia|]; split; [lia|];
                  rewrite E; unfold EXTRA, Zlib.proof.inflate.Model.TYPE; lia ]
      | |- fg _ _ => unfold fg in *; ihk_red; assumption
      | |- hO _ _ => unfold hO; rewrite XF1, OS1; exact Hos
      | |- hn0 _ _ => unfold hn0; rewrite NP1, NB1; exact Hn
      | |- hc0 _ _ => unfold hc0; rewrite CP1, CB1; exact Hc
      | _ => first [assumption | reflexivity | lia | congruence | intros; lia | tauto]
      end.
  - (* no FEXTRA *)
    assert (NE: ih_ne g = 10) by (unfold ih_ne; rewrite F4; lia).
    assert (XS10: ih_xs g = 10) by (unfold ih_xs; rewrite F4; reflexivity).
    replace (negb (Z.land (g_flg g) 4 =? 0)) with false by (unfold fl in F4; rewrite F4; reflexivity).
    cbv iota.
    apply FIN; auto; try lia.
    all: lazymatch goal with
         | |- ck2 _ _ _ _ => unfold ck2 in *; intros F2; rewrite (Ck F2);
                             replace (pos + m_nx m) with (ih_ne g) by lia; reflexivity
         | |- hxf _ _ _ => unfold hxf; unfold hxk in Hx; rewrite F4 in *; exact Hx
         end.
Qed.

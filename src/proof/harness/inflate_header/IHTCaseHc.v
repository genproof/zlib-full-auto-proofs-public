(* Law inflate_header, theory part: case HCRC (c_HCRC) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Import ListNotations.
Local Open Scope Z_scope.

Ltac ihh_red :=
  unfold m_mode, m_have in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       upd_s upd_h set_mode set_leave set_bad initbits
       i_mode i_wrap i_head i_length i_flags i_check i_last i_wsize i_total
       set_i_mode set_i_check set_i_length set_i_flags
       h_done h_hcrc h_text h_time h_xflags h_os h_xp h_extra_len h_xbuf h_np h_nbuf h_cp h_cbuf
       h_extra_max h_name_max h_comm_max set_h_done set_h_hcrc] in *.

Lemma ihh_jc h0 s h v : Jc h0 s h -> Jc h0 s (set_h_done (set_h_hcrc h v) 1).
Proof. intros [A B C D E F G]. constructor; cbn; auto. Qed.

Lemma ihh_jc_s h0 s h md c : Jc h0 s h -> Jc h0 (set_i_check (set_i_mode s md) c) h.
Proof. intros [A B C D E F G]. constructor; cbn; auto. Qed.

Lemma ihh_jc_m h0 s h md : Jc h0 s h -> Jc h0 (set_i_mode s md) h.
Proof. intros [A B C D E F G]. constructor; cbn; auto. Qed.

Lemma ihh_done g h0 h v :
  h_done h = 0 -> hT g h -> hM g h -> hO g h -> hxf g h0 h -> hnf g h0 h -> hcf g h0 h ->
  v = Z.land (Z.shiftr (g_flg g) 1) 1 ->
  ih_done_ok g h0 (set_h_done (set_h_hcrc h v) 1).
Proof.
  unfold hT, hM, hO, hxf, hnf, hcf, ih_done_ok. intros _ T M [X O] XF NF CF ->. cbn.
  repeat split; auto.
Qed.

Lemma ihc_hc : ihc_hcrc_stmt.
Proof.
  intros KIT g h0 pos inp m G HW X K L0 MD.
  pose proof (k_lay KIT g G) as LY.
  pose proof K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj].
  assert (Rok: m_ret m = Z_OK).
  { destruct Kr as [R|[(_ & D)|(_ & D)]]; auto; rewrite MD in D; unfold HCRC, DONE, BAD in D; lia. }
  destruct Kj as [E ? ? ? ? ? ? ? ?|E|E|E|E|E|E|E| E Pr B F Rs Ck Dn Ht Hm Ho Hx Hn Hc La |E|E|E|E|E|E|E];
    try solve [exfalso; repeat match goal with H: _ \/ _ |- _ => destruct H end; unfold m_mode in MD;
      rewrite MD in *; unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
        Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD in *; lia].
  destruct (proj1 (k_bits KIT) (g_flg g) ltac:(unfold ih_ok in G; lia)) as (_ & _ & _ & F512 & _ & _ & _ & _ & F9).
  unfold c_HCRC. cbv beta zeta.
  rewrite F, F512.
  destruct (fl g 2) eqn:F2.
  - (* FHCRC: NEEDBITS(16) *)
    replace (negb (Z.land (g_flg g) 2 =? 0)) with true by (unfold fl in F2; rewrite F2; reflexivity).
    destruct X as (X0 & X1 & X2).
    destruct B as [Bb Bh].
    destruct (k_nb KIT (ih_src g) inp pos (ih_nc g) 16 m (ly_bytes _ LY) X0 X1 X2 Ki Kn
                ltac:(lia) ltac:(pose proof (ly_ord _ LY); unfold ih_xs in *; destruct (fl g 4); lia)
                ltac:(change ((16 + 7) / 8) with 2; lia) Bb Bh)
      as (nx' & lv' & EN & R & C).
    rewrite EN. ihh_red.
    change ((16 + 7) / 8) with 2 in C.
    destruct C as [(-> & -> & C) | (-> & C)].
    + (* out of input *)
      rewrite Z.eqb_refl. cbn [ok_out].
      constructor; ihh_red; auto; try lia.
      apply J_HCRC; auto; try lia. rewrite F2; lia. split; reflexivity.
    + rewrite L0. cbn [Z.eqb].
      assert (W4: negb (Z.land (i_wrap (m_s m)) 4 =? 0) = true)
        by (destruct (jc_wrap _ _ _ Kc) as [W|[W|[W|W]]]; rewrite W; reflexivity).
      rewrite W4, (Ck F2). cbn [andb].
      rewrite C. rewrite (ly_hc _ LY F2).
      destruct (ih_badcrc g) eqn:BC; cbn [negb].
      * (* wrong header CRC *)
        cbn [ok_out]. constructor; ihh_red; auto; try lia.
        -- apply ihh_jc_m; auto.
        -- apply J_BAD; ihh_red; auto. rewrite BC, orb_true_r. reflexivity.
      * (* done *)
        rewrite (jc_head _ _ _ Kc). ihh_red.
        cbn [ok_out]. constructor; ihh_red; auto; try lia.
        -- apply ihh_jc_s, ihh_jc; auto.
        -- apply J_TYPE; ihh_red; auto.
           ++ left. split; [unfold ih_nh; rewrite F2; lia | exact La].
           ++ apply ihh_done; auto. unfold fg in F. rewrite F, F9. reflexivity.
  - (* no FHCRC *)
    replace (negb (Z.land (g_flg g) 2 =? 0)) with false by (unfold fl in F2; rewrite F2; reflexivity).
    destruct B as [Bb Bh].
    assert (Pe: pos + m_nx m = ih_nc g) by lia.
    rewrite (jc_head _ _ _ Kc). ihh_red.
    cbn [ok_out]. constructor; ihh_red; auto; try lia.
    + apply ihh_jc_s, ihh_jc; auto.
    + apply J_TYPE; ihh_red; auto.
      * left. split; [unfold ih_nh; rewrite F2; lia | exact La].
      * rewrite Bh, Pe, sublist_nil. reflexivity.
      * lia.
      * unfold ih_badcrc. rewrite F2. reflexivity.
      * apply ihh_done; auto. unfold fg in F. rewrite F, F9. reflexivity.
Qed.

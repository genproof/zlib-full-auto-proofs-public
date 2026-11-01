(** * deflate_slow: after the loop and the pending literal (S_tail): s->insert, FLUSH_BLOCK(s, 1) / FLUSH_BLOCK(s, 0)
    and the returns. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.SlowKit.
Require Import Zlib.proof.deflate.SlowPost.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.
Local Strategy opaque [loop loop2].

Lemma slow_tail_part {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (gv : globals) (flush : Z) (z : strm) (r : dstate * strm * bstate) (s7 : dstate) (z1 : strm) (msgv1 : val) :
  Int.min_signed <= flush <= Int.max_signed ->
  c_deflate_tail (set_insert_end s7) z1 flush = Some r ->
  out_grow z z1 ->
  Zlength rest = z_avail_out z ->
  semax Delta_sl
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s7 z1 p pin pout ish (rest_after z z1 rest) msgv1 gv; deflate_globals gv))
    S_tail (slow_fpost z r p pin pout ish rest gv).
Proof.
  intros H H0 H2 Hrest. assert (Ha : True) by exact I.
  cbv [S_tail SL ssub f_deflate_slow fn_body].
  slow_open_post.
    assert_PROP (dstate_ranges s7) as Hr7 by (unfold dfull, dstate_at; entailer!).
    unfold dfull, dstate_at. Intros. unfold match_at. Intros.
    assert (0 <= d_strstart s7 <= Int.max_unsigned) by drange.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'26 (vi (if d_strstart s7 <? MIN_MATCH - 1 then d_strstart s7
                                                   else MIN_MATCH - 1)) :: L) (SEPx S))) end.
    { forward. forward. entailer!. rewrite (proj2 (Z.ltb_lt _ _)) by (unfold MIN_MATCH; lia). reflexivity. }
    { forward. entailer!. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold MIN_MATCH; lia). reflexivity. }
      forward.
      set (s8 := set_insert_end s7) in H0.
      assert (Hr8 : dstate_ranges s8)
        by (subst s8; unfold set_insert_end; destruct (d_strstart s7 <? MIN_MATCH - 1) eqn:?;
            [apply Z.ltb_lt in Heqb | apply Z.ltb_ge in Heqb]; dranges_tac Hr7; unfold MIN_MATCH in *; lia).
      pre_dfull s8 z1 p pin pout ish (rest_after z z1 rest) msgv1 gv.
      { (subst s8; unfold set_insert_end; dfull_close_entail). }
      clearbody s8.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx ((flush <> Z_FINISH) :: P) (LOCALx L (SEPx S))) end.
      + (* flush == Z_FINISH: FLUSH_BLOCK(s, 1); return finish_done; *)
        unfold c_deflate_tail in H0. try subst flush. unfold Z_FINISH in H0. cbn [Z.eqb Pos.eqb] in H0.
        inv_bind H0. destruct x as [[s5 z5] r5]. rename Ha0 into Hfb.
        unfold c_flush_block in Hfb. inv_bind Hfb. destruct x as [s6 z6]. rename Ha0 into Hfbo.
        fbo_pre Hfbo.
        1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
          f5_tac; fb_tail_if;
          lazymatch goal with
          | |- semax _ _ Sskip _ => forward; entailer!; f5_b2z0
          | |- semax _ _ (Ssequence (Sset _ _) _) _ => (* return finish_started *)
              f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r; clear H0;
              forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
          | |- _ => (* return finish_done *)
              Intros; f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r;
              clear H0; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
          end).
        1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
          f5_tac; fb_tail_if;
          lazymatch goal with
          | |- semax _ _ Sskip _ => forward; entailer!; f5_b2z0
          | |- semax _ _ (Ssequence (Sset _ _) _) _ => (* return finish_started *)
              f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r; clear H0;
              forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
          | |- _ => (* return finish_done *)
              Intros; f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r;
              clear H0; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
          end).
      + forward. entailer!.
      + (* if (s->sym_next) FLUSH_BLOCK(s, 0); return block_done; *)
        Intros. unfold c_deflate_tail in H0.
        match type of H0 with context [flush =? ?k] =>
          rewrite (proj2 (Z.eqb_neq flush k) ltac:(assumption)) in H0 end.
        assert_PROP (0 <= tr_sym_next (d_tr s8) <= Int.max_unsigned) as Hsn
          by (sep_apply (dfull_sym_range s8 z1 p pin pout ish (rest_after z z1 rest) msgv1 gv); entailer!).
        sep_apply (dfull_sym_peek s8 z1 p pin pout ish (rest_after z z1 rest) msgv1 gv). Intros.
        forward.
        sep_apply (wand_frame_elim (@field_at DCS.CS Ews t_ds (DOT _sym_next) (vi (tr_sym_next (d_tr s8))) (p_s p))
                     (dfull s8 z1 p pin pout ish (rest_after z z1 rest) msgv1 gv)).
        forward_if (EX s' : dstate, EX z' : strm, EX m' : val,
          PROP (r = (s', z', block_done); out_grow z z')
          LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
          SEP (dfull s' z' p pin pout ish (rest_after z z' rest) m' gv; deflate_globals gv)).
        * (* sym_next <> 0: FLUSH_BLOCK(s, 0) *)
          assert (Esn : tr_sym_next (d_tr s8) <> 0).
          { intro E. match goal with Hn : Int.repr _ <> _ |- _ => apply Hn; rewrite E; reflexivity end. }
          unfold d_sym_next in H0. rewrite (proj2 (Z.eqb_neq _ _) Esn) in H0. cbn [negb] in H0.
          inv_bind H0. destruct x as [[s5 z5] r5]. rename Ha0 into Hfb.
          unfold c_flush_block in Hfb. inv_bind Hfb. destruct x as [s6 z6]. rename Ha0 into Hfbo.
          fbo_pre Hfbo.
          1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
            f5_tac; forward_if;
            f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r; clear H0;
            lazymatch goal with
            | |- semax _ _ Sskip _ => forward; Exists s6 z6 msgv1; entailer!; eapply out_grow_trans; eauto
            | |- _ => forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
            end).
          1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
            f5_tac; forward_if;
            f5_case Hfb; inversion Hfb; subst s5 z5 r5; clear Hfb; cbn in H0; inversion H0; subst r; clear H0;
            lazymatch goal with
            | |- semax _ _ Sskip _ => forward; Exists s6 z6 msgv1; entailer!; eapply out_grow_trans; eauto
            | |- _ => forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv1; entailer!
            end).
        * (* sym_next = 0 *)
          assert (Esn : tr_sym_next (d_tr s8) = 0).
          { match goal with Hz : Int.repr _ = ?zz |- _ =>
              change zz with (Int.repr 0) in Hz; apply repr_eq_u32 in Hz; [exact Hz|lia|rep_lia] end. }
          unfold d_sym_next in H0. rewrite Esn in H0. cbn in H0. inversion H0; subst r; clear H0.
          forward. Exists s8 z1 msgv1. entailer!.
        * Intros s' z' m'. forward. try subst r. unfold dfull_post. cbn [fst snd]. Exists m'. entailer!.
Qed.

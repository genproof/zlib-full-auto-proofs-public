(** * deflate_slow: the literal branch after _tr_tally_lit (S_litrest): FLUSH_BLOCK_ONLY, strstart++, lookahead--,
    the avail_out test. *)
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

Lemma slow_litrest_part {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (gv : globals) (flush : Z) (z : strm) (r : dstate * strm * bstate) (s1 : dstate) (z1 : strm) (rx : option bstate)
    (X : option (dstate * strm * bstate)) (s' : dstate) (z' : strm) (o : (dstate * strm) + dexit)
    (s5 s6 : dstate) (z2 z6 : strm) (msgv2 : val) (bf : bool) :
  Int.min_signed <= flush <= Int.max_signed ->
  Zlength rest = z_avail_out z ->
  match rx with Some r0 => Some (s1, z1, r0) | None => X end = Some r ->
  runs (dsl_body flush) (s', z') (s1, z1, rx) ->
  dsl_body flush (s', z') = Some o ->
  (if bf then c_flush_block_only s5 z2 0 else Some (s5, z2)) = Some (s6, z6) ->
  (let s := set_d_strstart s6 (u32 (d_strstart s6 + 1)) in
   let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
   if z_avail_out z6 =? 0 then Some (inr (s, z6, Some need_more)) else Some (inl (s, z6))) = Some o ->
  out_grow z z2 ->
  semax Delta_sl
    (PROP () LOCAL (temp _bflush (vi (Z.b2z bf)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s5 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv; deflate_globals gv))
    S_litrest (slow_lpost flush s1 z1 rx z r p pin pout ish rest gv).
Proof.
  intros H Hrest H0 Hrun Hbody Hfo Ho Hgrow2. cbv zeta in Ho. assert (Ha : True) by exact I.
  cbv [S_litrest SL ssub f_deflate_slow fn_body].
  slow_open_post.
           match goal with |- semax _ (PROPx ?P (LOCALx ?L _)) _ _ =>
             forward_if (PROPx (out_grow z2 z6 :: P) (LOCALx L
               (SEPx [dfull s6 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv; deflate_globals gv]))) end.
           ++ (* FLUSH_BLOCK_ONLY(s, 0) *)
              subst bf. rename Hfo into Hfbo.
              fbo_pre Hfbo.
              1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
                           entailer!).
              1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
                           entailer!).
           ++ subst bf.
              inversion Hfo; subst s6 z6. forward. entailer!. apply out_grow_refl.
           ++ (* s->strstart++; s->lookahead--; if (s->strm->avail_out == 0) return need_more; *)
              Intros.
              assert_PROP (dstate_ranges s6) as Hr6 by (unfold dfull, dstate_at; entailer!).
              unfold dfull, dstate_at. Intros. unfold match_at. Intros.
              assert (0 <= d_strstart s6 <= Int.max_unsigned) by drange.
              assert (0 <= d_lookahead s6 <= Int.max_unsigned) by drange.
              forward. forward. forward. forward.
              set (s8 := set_d_lookahead (set_d_strstart s6 (u32 (d_strstart s6 + 1)))
                           (u32 (d_lookahead (set_d_strstart s6 (u32 (d_strstart s6 + 1))) - 1))) in Ho.
              assert (Hr8 : dstate_ranges s8) by (subst s8; dranges_tac Hr6).
              pre_dfull s8 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv.
              { (subst s8; dfull_close_entail). }
              clearbody s8.
              sep_apply (dfull_f5_open s8 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv). Intros.
              forward. forward.
              forward_if.
              ** (* avail_out == 0: return need_more *)
                 assert (Ea : z_avail_out z6 = 0) by repr_eq.
                 rewrite Ea in Ho. cbn in Ho. inversion Ho; subst o.
                 apply (runs_exit_eq _ _ _ _ Hrun) in Hbody. inversion Hbody; subst s1 z1 rx.
                 cbn in H0. inversion H0; subst r.
                 forward.
                 sep_apply (dfull_f5_close s8 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv); auto.
                 unfold dfull_post. cbn [fst snd]. Exists msgv2. entailer!.
              ** assert (Ea : z_avail_out z6 <> 0) by (intro E; rewrite E in *; contradiction).
                 rewrite (proj2 (Z.eqb_neq _ _) Ea) in Ho. inversion Ho; subst o.
                 apply (runs_step_eq _ _ _ _ Hrun) in Hbody.
                 forward.
                 sep_apply (dfull_f5_close s8 z6 p pin pout ish (rest_after z z6 rest) msgv2 gv); auto.
                 Exists s8 z6 msgv2. entailer!. eapply out_grow_trans; eauto.
Qed.

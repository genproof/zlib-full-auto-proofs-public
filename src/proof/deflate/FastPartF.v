(** * deflate_fast: [if (bflush) FLUSH_BLOCK(s, 0);] at the end of an iteration (FS_ifbf). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.FastKit.
Require Import Zlib.proof.deflate.FastTailKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.
Local Strategy opaque [loop loop2].

Lemma fast_ifbf_part {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (gv : globals) (flush : Z) (z : strm) (r : dstate * strm * bstate) (s1 : dstate) (z1 : strm) (rx : option bstate)
    (s' : dstate) (z' : strm) (o : (dstate * strm) + dexit) (s5 : dstate) (z2 : strm) (msgv2 : val) (bf : bool) :
  Int.min_signed <= flush <= Int.max_signed ->
  Zlength rest = z_avail_out z ->
  match rx with Some r0 => Some (s1, z1, r0) | None => c_deflate_tail (set_insert_end s1) z1 flush end = Some r ->
  runs (df_body flush) (s', z') (s1, z1, rx) ->
  df_body flush (s', z') = Some o ->
  c_bflush s5 z2 bf = Some o ->
  out_grow z z2 ->
  semax Delta_fast
    (fa (temp _bflush (vi (Z.b2z bf)) :: fa_base p flush gv) s5 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv)
    FS_ifbf (fast_lpost flush s1 z1 rx z r p pin pout ish rest gv).
Proof.
  intros H Hrest H0 Hrun Hbody Ho Hgrow2. assert (Ha : True) by exact I.
  cbv [FS_ifbf fs_last fs_ssub f_deflate_fast fn_body].
  fast_open_post.
        unfold fa, fa_base. destruct bf.
        -- unfold c_bflush in Ho. inv_bind Ho. destruct x as [[s7 z7] r7]. rename Ha0 into Hfb.
           unfold c_flush_block in Hfb. inv_bind Hfb. destruct x as [s6 z6]. rename Ha0 into Hfbo.
           forward_if; [| fa_contra].
           fbo_pre Hfbo.
           1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
        f5_tac; forward_if;
        f5_case Hfb; inversion Hfb; subst s7 z7 r7; clear Hfb; cbn in Ho; inversion Ho; subst o; clear Ho;
        lazymatch goal with
        | |- semax _ _ Sskip _ => (* continue *)
            apply (runs_step_eq _ _ _ _ Hrun) in Hbody;
            forward; Exists s6 z6 msgv2; entailer!; eapply out_grow_trans; eauto
        | |- _ => (* avail_out == 0: return need_more *)
            apply (runs_exit_eq _ _ _ _ Hrun) in Hbody; inversion Hbody; subst s1 z1 rx; clear Hbody;
            cbn in H0; inversion H0; subst r; clear H0;
            forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv2; entailer!
        end).
           1: (fbo_branch p pin pout ish gv z rest Hfbo fb_tt fb_kk fb_Hsome fb_Hnone fb_Hfp fb_Hwok fb_Hbs;
        f5_tac; forward_if;
        f5_case Hfb; inversion Hfb; subst s7 z7 r7; clear Hfb; cbn in Ho; inversion Ho; subst o; clear Ho;
        lazymatch goal with
        | |- semax _ _ Sskip _ => (* continue *)
            apply (runs_step_eq _ _ _ _ Hrun) in Hbody;
            forward; Exists s6 z6 msgv2; entailer!; eapply out_grow_trans; eauto
        | |- _ => (* avail_out == 0: return need_more *)
            apply (runs_exit_eq _ _ _ _ Hrun) in Hbody; inversion Hbody; subst s1 z1 rx; clear Hbody;
            cbn in H0; inversion H0; subst r; clear H0;
            forward; forward; unfold dfull_post; cbn [fst snd]; Exists msgv2; entailer!
        end).
        -- cbn in Ho. inversion Ho; subst o; clear Ho.
           apply (runs_step_eq _ _ _ _ Hrun) in Hbody.
           forward_if; [fa_contra |].
           forward.
           Exists s5 z2 msgv2. entailer!.
Qed.

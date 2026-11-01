(** * Body proof of deflateReset. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.

(** The level of a [dstream] normalised to 0, 1 or 2 (any other level means [dstate_at_d0], as 0). *)
Definition rs_norm (lvl : Z) : Z := if lvl =? 2 then 2 else if lvl =? 1 then 1 else 0.

Lemma rs_dstream_norm lvl os strmp ghp gv :
  dstream lvl os strmp ghp gv = dstream (rs_norm lvl) os strmp ghp gv.
Proof.
  unfold dstream, dstate_at', rs_norm.
  destruct (lvl =? 2); [reflexivity|]. destruct (lvl =? 1); reflexivity.
Qed.

Lemma rs_resetkeep_code s z s1 z1 ret :
  c_deflateResetKeep s z = Some (s1, z1, ret) -> ret = Z_OK \/ ret = Z_STREAM_ERROR.
Proof.
  unfold c_deflateResetKeep. destruct (bad_state s).
  { intro E; inv E; auto. }
  intro E. unfold bind in E.
  repeat match type of E with context [match ?x with _ => _ end] => destruct x end; inv E; auto.
Qed.

Lemma rs_lm_init_sizes s r : c_lm_init s = Some r -> dsizes s -> dsizes r.
Proof.
  unfold c_lm_init, c_clear_hash, guard, bind. intros E Hs.
  repeat match goal with H : context [match ?x with _ => _ end] |- _ => destruct x eqn:? end; try discriminate.
  inv E. match goal with H : Some (set_d_slid _ _) = Some _ |- _ => inv H end.
  unfold dsizes in *. dcbn. cbn [d_hash_size set_d_window_size] in Heqb0.
  rewrite andb_true_iff, Z.leb_le in Heqb0. rewrite Zlength_repeat by lia. tauto.
Qed.

Lemma rs_lm_init_tokens s r p : c_lm_init s = Some r -> dtokens r p = dtokens s p.
Proof.
  unfold c_lm_init, c_clear_hash, guard, bind. intros E.
  repeat match goal with H : context [match ?x with _ => _ end] |- _ => destruct x eqn:? end; try discriminate.
  inv E. match goal with H : Some (set_d_slid _ _) = Some _ |- _ => inv H end.
  reflexivity.
Qed.

(** lm_init's precondition from a state of level 1 or 2 (head[] forgotten). *)
Lemma rs_to_h0 l s p gv : l = 1 \/ l = 2 -> dstate_at' l s p gv |-- dstate_at_h0 s p gv.
Proof.
  intros [-> | ->]. { rewrite dstate_at'_1; auto. }
  rewrite dstate_at'_2. unfold dstate_at, dstate_at_h0, hash_at, hash_at_h0. Intros. entailer!.
Qed.

Lemma body_deflateReset : ob_deflateReset.
Proof.
  unfold ob_deflateReset. start_function.
  rewrite (rs_dstream_norm lvl).
  destruct os as [s|].
  2:{ cbn in H0. inv H0.
    forward_call (rs_norm lvl, @None dstate, strmp, ghp, nextin, ain, tin, nextout, aout, tout, msgv, msg, adler,
                  (@None dstate, zmk [] 0 ain tin aout tout adler msg, Z_STREAM_ERROR), gv).
    cbn [fst snd z_msg z_avail_in z_total_in z_avail_out z_total_out z_adler zmk]. Intros msgv'.
    forward_if (PROP () LOCAL (temp _ret (vi Z_STREAM_ERROR); gvars gv; temp _strm strmp)
       SEP (dstream (rs_norm lvl) None strmp ghp gv;
            api_fields strmp nextin ain tin nextout aout tout msgv' adler; deflate_globals gv)).
    discriminate. forward. apply ENTAIL_refl. forward.
    Exists msgv'. change (if Z_STREAM_ERROR =? Z_OK then 2 else lvl) with lvl. rewrite (rs_dstream_norm lvl).
    cbn [zmk z_msg z_avail_in z_total_in z_avail_out z_total_out z_adler]. entailer!. }
  set (z := zmk [] 0 ain tin aout tout adler msg) in *.
  destruct (c_deflateResetKeep s z) as [[[s1 z1] ret]|] eqn:Hk.
  2:{ unfold on_state, c_on_state, c_deflateReset in H0. rewrite Hk in H0. discriminate. }
  forward_call (rs_norm lvl, Some s, strmp, ghp, nextin, ain, tin, nextout, aout, tout, msgv, msg, adler,
                (Some s1, z1, ret), gv).
  { unfold on_state, c_on_state. fold z. rewrite Hk. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  unfold on_state, c_on_state, c_deflateReset in H0. rewrite Hk in H0. cbn [bind] in H0.
  destruct (rs_resetkeep_code _ _ _ _ _ Hk) as [-> | ->].
  - change (Z_OK =? Z_OK) with true in H0. cbv iota in H0.
    destruct (c_lm_init s1) as [s2|] eqn:Hl; cbn [bind] in H0; inv H0.
    change (if Z_OK =? Z_OK then Z.max (rs_norm lvl) 1 else rs_norm lvl) with (Z.max (rs_norm lvl) 1).
    forward_if (PROP () LOCAL (temp _ret (vi Z_OK); gvars gv; temp _strm strmp)
       SEP (dstream 2 (Some s2) strmp ghp gv;
            api_fields strmp nextin (z_avail_in z1) (z_total_in z1) nextout (z_avail_out z1) (z_total_out z1)
              msgv' (z_adler z1);
            deflate_globals gv)).
    + rewrite dstream_some_eq. Intros p.
      sep_apply (rs_to_h0 (Z.max (rs_norm lvl) 1) s1 p gv).
      { unfold rs_norm. destruct (lvl =? 2); [|destruct (lvl =? 1)]; lia. }
      assert_PROP (isptr (p_s p)). { unfold dstate_at_h0, stat_at. Intros. entailer!. }
      forward.
      forward_call (s1, p, s2, gv).
      rewrite <- (rs_lm_init_tokens _ _ p Hl), <- (dstate_at'_2 s2).
      sep_apply (dstream_some_fold 2 s2 p strmp ghp gv H2 H3 (rs_lm_init_sizes _ _ Hl H4)). entailer!.
    + contradiction.
    + forward. Exists msgv'. change (if Z_OK =? Z_OK then 2 else lvl) with 2. entailer!.
  - change (Z_STREAM_ERROR =? Z_OK) with false in H0 |- *. cbv iota in H0 |- *. cbn [bind] in H0. inv H0.
    forward_if (PROP () LOCAL (temp _ret (vi Z_STREAM_ERROR); gvars gv; temp _strm strmp)
       SEP (dstream (rs_norm lvl) (Some s1) strmp ghp gv;
            api_fields strmp nextin (z_avail_in z1) (z_total_in z1) nextout (z_avail_out z1) (z_total_out z1)
              msgv' (z_adler z1);
            deflate_globals gv)).
    + discriminate.
    + forward. apply ENTAIL_refl.
    + forward. Exists msgv'. change (if Z_STREAM_ERROR =? Z_OK then 2 else lvl) with lvl.
      rewrite (rs_dstream_norm lvl). entailer!.
Qed.

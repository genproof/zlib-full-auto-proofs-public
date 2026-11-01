(** * Body proofs of deflateTune, deflateSetHeader.
    v5: strm->next_in is in their specs; dcheck_some / dcheck_none take it from the field_at. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DSpec Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.deflate.ApiKit.

Lemma body_deflateTune : ob_deflateTune.
Proof.
  unfold ob_deflateTune. start_function.
  destruct os as [s|].
  2:{ cbn in H3. inv H3. dcheck_none strmp gv. forward_if; [forward; entailer! | discriminate]. }
  dcheck_some s strmp gv.
  cbn in H3. unfold c_deflateTune, bad_state, c_deflateStateCheck in H3. unfold c_deflateStateCheck.
  destruct (status_ok (d_status s)) eqn:Hst; cbn in H3.
  2:{ inv H3. forward_if; [forward; entailer! | discriminate]. }
  inv H3. forward_if; [contradiction|].
  rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2; unfold dstate_at. Intros. unfold cfg_at. Intros.
  forward. forward. forward. forward. forward. forward.
  rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2; unfold dstate_at. dsame s. unfold cfg_at. dcbn.
  rewrite !vi_u32. entailer!.
  pose proof (u32_range good); pose proof (u32_range lazy); pose proof (u32_range chain).
  unfold dstate_ranges in *; dcbn. unfold u32_ok, s32_ok in *. intuition rep_lia.
Qed.

Lemma body_deflateSetHeader : ob_deflateSetHeader.
Proof.
  unfold ob_deflateSetHeader. start_function.
  destruct os as [s|].
  2:{ cbn in H. inv H. dcheck_none strmp gv.
      forward_if (PROP () LOCAL (temp _t'2 (vi 1); gvars gv; temp _strm strmp; temp _head hp)
                  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 None strmp ghp gv; gzh_at Ews h hp xp np cp)).
      - forward. entailer!.
      - discriminate.
      - forward_if; [forward; entailer! | discriminate]. }
  dcheck_some s strmp gv.
  unfold on_state, c_on_state, c_deflateSetHeader, bad_state, c_deflateStateCheck in H |- *.
  destruct (status_ok (d_status s)) eqn:Hst; cbn in H.
  2:{ inv H.
      forward_if (PROP () LOCAL (temp _t'2 (vi 1); gvars gv; temp _strm strmp; temp _head hp)
                  SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 (Some s) strmp ghp gv; gzh_at Ews h hp xp np cp)).
      - forward. entailer!.
      - discriminate.
      - forward_if; [forward; entailer! | discriminate]. }
  forward_if (PROP () LOCAL (temp _t'2 (vi (if d_wrap s =? 2 then 0 else 1)); gvars gv;
                             temp _strm strmp; temp _head hp)
              SEP (@field_at DCS.CS Ews t_strm (DOT _next_in) ni strmp; dstream 2 (Some s) strmp ghp gv; gzh_at Ews h hp xp np cp)).
  - contradiction.
  - rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2; unfold dstate_at, stat_at. Intros.
    forward. forward. forward.
    entailer!.
    + assert (s32_ok (d_wrap s)) by (match goal with Hr : dstate_ranges s |- _ => drange Hr end).
      rewrite int_eq_s32 by (auto; unfold s32_ok; rep_lia). destruct (d_wrap s =? 2); reflexivity.
    + rewrite dstream_some_eq. Exists p. rewrite dstate_at'_2; unfold dstate_at, stat_at. entailer!.
  - destruct (d_wrap s =? 2) eqn:Hw; cbn in H; inv H.
    + forward_if; [contradiction|].
      rewrite dstream_some_eq. Intros p. rewrite dstate_at'_2; unfold dstate_at, stat_at. Intros.
      forward. forward. forward.
      rewrite dstream_some_eq.
      Exists (mkDP (p_strm p) (p_s p) (p_window p) (p_prev p) (p_head p) (p_pbuf p) hp).
      rewrite dstate_at'_2; unfold dstate_at. dsame2 s p. unfold stat_at. dcbn. cbn [p_gzhead p_s p_strm p_pbuf].
      entailer!.
    + forward_if; [forward; entailer! | discriminate].
Qed.

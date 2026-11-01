(* Part of the decode theory: the passes from LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* The parts: statements in DecDecDefs.v, proofs in DecDec*.v. *)
Require Import compcert.lib.Integers.
Require Import Zlib.proof.rfc1951.DecDecKd.
Require Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.rfc1951.DecDecCanon Zlib.proof.rfc1951.DecDecWalk Zlib.proof.rfc1951.DecDecLook
  Zlib.proof.rfc1951.DecDecNeed Zlib.proof.rfc1951.DecDecLay Zlib.proof.rfc1951.DecDecCopy
  Zlib.proof.rfc1951.DecDecTabs Zlib.proof.rfc1951.DecDecLit Zlib.proof.rfc1951.DecDecMatch
  Zlib.proof.rfc1951.DecDecDistext Zlib.proof.rfc1951.DecDecDist Zlib.proof.rfc1951.DecDecLenext
  Zlib.proof.rfc1951.DecDecLen.

Lemma dd_dw m : mwf3 m -> md_dec (m_mode m) -> dw m.
Proof.
  intros [W _] Hmd.
  destruct (Zlib.proof.inflate.Inv.md_tables _ (Zlib.proof.inflate.Inv.mw_md _ W) Hmd) as [T1 T2].
  pose proof (Zlib.proof.inflate.Inv.mw_nx _ W) as N. pose proof (Zlib.proof.inflate.Inv.mw_ow _ W) as [O _].
  pose proof (Zlib.proof.inflate.Inv.mw_aout _ W) as A.
  split; [exact T1|]. split; [exact T2|]. split; [exact N|].
  split; [change Int.max_signed with (2 ^ 31 - 1) in A; lia|].
  exact (proj1 (proj1 (Zlib.proof.inflate.Inv.sw_wnext _ (Zlib.proof.inflate.Inv.mw_s _ W)))).
Qed.

Lemma dd_mwf3_len m : mwf3 m -> m_mode m = LEN_ -> mwf3 (set_mode m LEN).
Proof.
  intros [W S] Hmd.
  assert (Dm : decode_mode (m_mode m)) by (unfold decode_mode; tauto).
  split.
  - apply Zlib.proof.inflate.MwfLemmas.mwf_set_mode; auto;
      try (unfold LEN, LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST, HEAD, SYNC; intros; lia).
    + intros _. apply (Zlib.proof.inflate.Inv.md_tables _ (Zlib.proof.inflate.Inv.mw_md _ W) Dm).
    + left. apply (Zlib.proof.inflate.Inv.mwf_out_eq _ W); rewrite Hmd; unfold LEN_, LENGTH, DONE, BAD; lia.
  - destruct S as [S1 S2 S3 S4]. constructor; cbn [set_mode upd_s m_s set_m_s i_mode set_i_mode].
    + unfold LEN, HEAD; intros; lia.
    + intros _. exact (S2 Dm).
    + unfold LEN, LENEXT; intros; lia.
    + unfold LEN, DISTEXT; intros; lia.
Qed.

Lemma group_dec : dkit_stmt -> dfast_stmt -> group_ok md_dec.
Proof.
  intros DK DF G pos inp ob flush m Gok Hp Hpi Hinp K W Hl Hmd.
  assert (Ctx : in_ctx G pos inp) by (split; auto).
  assert (D : dw m) by (apply dd_dw; auto).
  pose proof (lay_ok DK) as LAY. pose proof tabs_ok as TB. pose proof copy_ok as CP.
  pose proof (need_ok DK) as ND. pose proof (dcode_ok DK (walk_ok canon_ok)) as DC.
  pose proof (pass_match LAY CP) as P_match.
  pose proof (pass_distext DK LAY TB ND P_match) as P_distext.
  pose proof (pass_dist LAY TB DC P_distext) as P_dist.
  pose proof (pass_lenext DK LAY TB ND P_dist) as P_lenext.
  pose proof (pass_len DF LAY TB DC P_lenext) as P_len.
  pose proof (pass_lit LAY) as P_lit.
  pose proof Hmd as Hmd0. unfold md_dec in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 _ _ _ m) with (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) (set_mode m LEN))
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    assert (K' : Kd G pos inp ob (set_mode m LEN)).
    { apply kd_tr with m; auto; try reflexivity.
      - unfold set_mode, upd_s. sf_auto.
      - right. cbn. unfold md_dec; tauto.
      - destruct (at_mode_len_e _ _ _ _ _ _ (kd_at _ _ _ _ _ K) (or_introl Hmd)) as [H A].
        apply at_mode_len_i; [exact H|right; reflexivity|].
        destruct A as (k & j & ll & dl & syms & p0 & IH & R).
        exists k, j, ll, dl, syms, p0. split; [|exact R].
        apply in_huff_tr with (m_s m); [unfold set_mode, upd_s; sf_auto|exact IH]. }
    exact (P_len G pos inp ob flush (set_mode m LEN) Ctx K' (dd_mwf3_len m W Hmd)
             (dw_tr m _ D ltac:(unfold set_mode, upd_s; sf_auto) eq_refl (proj1 (proj2 (proj2 D)))
                eq_refl (proj1 (proj1 (proj2 (proj2 (proj2 D))))))
             Hl eq_refl).
  - replace (stepf2 _ _ _ m) with (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list) m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_len G pos inp ob flush m Ctx K W D Hl Hmd).
  - replace (stepf2 _ _ _ m) with (c_LENEXT lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_lenext G pos inp ob flush m Ctx K D Hl Hmd).
  - replace (stepf2 _ _ _ m) with (c_DIST lenfix_list distfix_list m)
      by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_dist G pos inp ob flush m Ctx K D Hl Hmd).
  - replace (stepf2 _ _ _ m) with (c_DISTEXT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_distext G pos inp ob flush m Ctx K D Hl Hmd).
  - replace (stepf2 _ _ _ m) with (c_MATCH m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_match G pos inp ob flush m Ctx K D Hl Hmd).
  - replace (stepf2 _ _ _ m) with (c_LIT m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    exact (P_lit G pos inp ob flush m Ctx K D Hl Hmd).
Qed.

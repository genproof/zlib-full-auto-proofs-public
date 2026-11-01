(* One pass of the switch keeps out_inv, the window flag and win_inv5 (Body5Parts.v stepf_inv5_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Import Zlib.proof.inflate_api.StepInv5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* HEAD: wbits is set (non-zero) on every path that leaves HEAD except to BAD; nothing is written *)
Lemma c_HEAD_inv5 m : m_mode m = HEAD -> out_inv m -> win_inv5 (m_s m) ->
  match c_HEAD2 m with
  | IBrk m' => out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.
Proof.
  intros Hm (O1 & O2 & O3) (W1 & W2).
  unfold c_HEAD2. hsplit; unfold out_inv, win_inv5; hcbn; autorewrite with wi.
  all: assert (Hw: m_ow m = []) by auto; unfold m_left, m_mode in *; autorewrite with wi in *;
       rewrite ?Hw in *; rewrite ?Zlength_nil in *.
  all: repeat match goal with |- context [if ?c then _ else _] => let E := fresh "F" in destruct c eqn:E end.
  all: repeat match goal with
       | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
       end.
  all: try match goal with |- context [?x mod 16] => pose proof (Z.mod_pos_bound x 16 ltac:(lia)) end.
  all: wmodes.
  all: split; [split; [lia | split; [lia | auto]] | split; [reflexivity | ]].
  all: split; intros A; try (intros B); try (destruct (W1 A)); try (destruct (W2 A B));
       try (split; [auto|]); try tauto; try lia.
Qed.

(* the modes a failed stream rests in: the pass changes neither the state nor the output *)
Lemma stepf2_rest flush m : m_mode m = BAD \/ m_mode m = SYNC \/ m_mode m = MEM ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => m_s m' = m_s m /\ m_ow m' = m_ow m /\ m_out m' = m_out m /\ m_aout m' = m_aout m
  | IRet _ m' => m_s m' = m_s m
  end.
Proof.
  intros [H|[H|H]]; unfold stepf2, step2; rewrite H; cbv beta iota zeta; wmodes; cbn -[c_BAD];
    try reflexivity.
  unfold c_BAD; cbn; auto.
Qed.

Lemma stepf_inv5 : stepf_inv5_stmt.
Proof.
  intros flush m Hmwf Hlv Hout Hwin.
  destruct (Z.eq_dec (m_mode m) HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply c_HEAD_inv5; auto.
  - destruct Hwin as [W1 W2].
    destruct (Z.eq_dec (i_wbits (m_s m)) 0) as [Hz|Hz].
    + destruct (W1 Hz) as [Hw Hn]. destruct (W2 Hz (land3_wrap _ Hw)) as [Hf Hmd].
      assert (Hr: m_mode m = BAD \/ m_mode m = SYNC \/ m_mode m = MEM)
        by (unfold m_mode; destruct Hmd as [Hmd|Hmd]; [contradiction|tauto]).
      pose proof (stepf2_rest flush m Hr) as R.
      destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
      * destruct R as (R1 & R2 & R3 & R4). unfold out_inv, m_left, m_mode in *. rewrite R1, R2, R3, R4.
        split; [exact Hout|]. split; [reflexivity|]. split; auto.
      * rewrite R. split; [reflexivity|]. split; auto.
    + pose proof (stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
      assert (V: forall s, i_wbits s = i_wbits (m_s m) -> win_inv5 s)
        by (intros s E; split; intros Z; rewrite E in Z; contradiction).
      destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
        unfold wgood, wrel in G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      * split; [|split; [exact G1 | apply V; exact G2]].
        unfold out_inv, m_left, m_mode in *. destruct Hout as (O1 & O2 & O3).
        split; [lia|]. split; [lia|]. intros; contradiction.
      * split; [exact G1 | apply V; exact G2].
Qed.

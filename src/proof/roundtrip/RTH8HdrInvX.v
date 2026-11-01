(* One pass of the switch from a header mode with a header of any buffer sizes keeps the loop's invariants
   (the conclusion of RTH8W.hdr8_inv_stmt), provided the copy of case EXTRA does not wrap in 32 bits
   (RTH8HdrKit.xsafe), which the header invariant gives (round 1's RTH8HdrInv2.v, from
   RTHSpec.hinv6; here RTH9AHdrInv.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH8W.
Require Zlib.proof.roundtrip.RTH8HdrKit.
Require Zlib.proof.inflate.Step5Mwf.
Require Zlib.proof.inflate_api.Body5HdrKit.
Require Zlib.proof.inflate_api.Body5StepInv.
Require Zlib.proof.inflate_api.StepInv5Kit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module K := Zlib.proof.roundtrip.RTH8HdrKit.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3_8 is RTH8HdrKit's mwf3x8                                                                  *)

Lemma hwf_hcanon: forall h, hwf (hcanon h).
Proof.
  intros h. unfold hcanon, cz.
  destruct (h_extra_max h =? 0), (h_name_max h =? 0), (h_comm_max h =? 0);
  constructor; cbn; unfold srange, lrange, urange; try rep_lia; split; try reflexivity; repeat constructor; rep_lia.
Qed.

Lemma hwf8_r: forall h, hwf8 h -> K.hwf8r h.
Proof.
  intros h (A & B & C & D & E & X & N & M & XB & NB & CB & HC & DN). constructor; auto.
Qed.

Lemma hwf8_of_r: forall h, K.hwf8r h -> hwf8 h.
Proof. intros h []. unfold hwf8. tauto. Qed.

Lemma mwf3_8_x: forall m, mwf3_8 m -> K.mwf3x8 m.
Proof.
  intros m [W H]. apply K.m38_of with (hcanon (m_h m)); [| apply hwf8_r; exact H].
  apply Zlib.proof.inflate.Step5Mwf.mwf3x_iff. exact W.
Qed.

Lemma mwf3_8_of_x: forall m, K.mwf3x8 m -> mwf3_8 m.
Proof.
  intros m W. split; [| apply hwf8_of_r; exact (K.mw8_h _ (K.m8_w _ W))].
  apply Zlib.proof.inflate.Step5Mwf.mwf3x_iff. apply K.m38_to; [exact W | apply hwf_hcanon].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* out_inv and win_inv5 (Body5StepInv.stepf_inv5, whose proof does not use mwf3)                   *)

Lemma stepf2_inv5_any : forall flush m, out_inv m -> win_inv5 (m_s m) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.
Proof.
  intros flush m Hout Hwin.
  destruct (Z.eq_dec (m_mode m) IM.HEAD) as [Hh|Hh].
  - replace (stepf2 flush lenfix_list distfix_list m) with (c_HEAD2 m)
      by (unfold stepf2, step2; rewrite Hh; reflexivity).
    apply Zlib.proof.inflate_api.Body5StepInv.c_HEAD_inv5; auto.
  - destruct Hwin as [W1 W2].
    destruct (Z.eq_dec (i_wbits (m_s m)) 0) as [Hz|Hz].
    + destruct (W1 Hz) as [Hw Hn]. destruct (W2 Hz (land3_wrap _ Hw)) as [Hf Hmd].
      assert (Hr: m_mode m = IM.BAD \/ m_mode m = IM.SYNC \/ m_mode m = IM.MEM)
        by (unfold m_mode; destruct Hmd as [Hmd|Hmd]; [contradiction|tauto]).
      pose proof (Zlib.proof.inflate_api.Body5StepInv.stepf2_rest flush m Hr) as R.
      destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
      * destruct R as (R1 & R2 & R3 & R4). unfold out_inv, m_left, m_mode in *. rewrite R1, R2, R3, R4.
        split; [exact Hout|]. split; [reflexivity|]. split; auto.
      * rewrite R. split; [reflexivity|]. split; auto.
    + pose proof (Zlib.proof.inflate_api.StepInv5Kit.stepf2_wgood flush lenfix_list distfix_list m Hh) as G.
      assert (V: forall s, i_wbits s = i_wbits (m_s m) -> win_inv5 s)
        by (intros s E; split; intros Z; rewrite E in Z; contradiction).
      destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
        unfold Zlib.proof.inflate_api.StepInv5Kit.wgood, Zlib.proof.inflate_api.StepInv5Kit.wrel in G;
        destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
      * split; [|split; [exact G1 | apply V; exact G2]].
        unfold out_inv, m_left, m_mode in *. destruct Hout as (O1 & O2 & O3).
        split; [lia|]. split; [lia|]. intros; contradiction.
      * split; [exact G1 | apply V; exact G2].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the pass, given that the copy of case EXTRA does not wrap                                       *)

Lemma hdr8_inv_xsafe : forall flush m, mwf3_8 m -> m_leave m = 0 -> hdr_mode (m_mode m) = true ->
  out_inv m -> win_inv5 (m_s m) ->
  (m_mode m = IM.EXTRA -> negb (Z.land (i_flags (m_s m)) 1024 =? 0) = true -> K.xsafe m) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => mwf3_8 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
               out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => mwf3_8 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
                 i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.
Proof.
  intros flush m W L HM O V XS.
  assert (HM': IM.HEAD <= m_mode m <= IM.HCRC)
    by (unfold hdr_mode in HM; apply andb_prop in HM; destruct HM as [A B];
        apply Z.leb_le in A; apply Z.leb_le in B; lia).
  pose proof (K.stepf2_hdr8 flush m (mwf3_8_x m W) L HM' XS) as S.
  pose proof (stepf2_inv5_any flush m O V) as I.
  pose proof (Zlib.proof.inflate_api.Body5HdrKit.stepf2_hrel flush lenfix_list distfix_list m) as H.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    cbn [Zlib.proof.inflate.StepInv.iout_ok] in S;
    unfold Zlib.proof.inflate_api.Body5HdrKit.hrel in H; destruct H as (H1 & H2 & H3 & H4 & H5 & _);
    (split; [apply mwf3_8_of_x; exact S |]); (split; [unfold hdr_same; auto |]); (split; [exact H1 |]);
    tauto.
Qed.

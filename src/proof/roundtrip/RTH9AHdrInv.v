(* One pass of inflate's switch from a header mode, for a wide machine with a header of any buffer sizes
   (RTH9AKit.hdr9_inv_stmt): round 1's RTH8W2.hdr8_inv2_stmt with the wide invariant RTH9HDefs.mwf3_9.

   mwf3_9 is RTH9AHdrKit.mwf3hW8 ([mwf3_9_h], [mwf3_9_of_h]), which the header cases keep (RTH9AHdrKit.stepf2_hdrW8)
   when the copy of case EXTRA does not wrap in 32 bits; RTHSpec.hinv6 gives that ([xsafe_of_hinv6]).  The loop's
   other invariants (out_inv, the window, the header's presence and sizes, the input) are those of RTH8HdrInvX.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Zlib.proof.roundtrip.RTH9AHdrKit.
Require Zlib.proof.roundtrip.RTH8HdrKit.
Require Zlib.proof.roundtrip.RTH8HdrInvX.
Require Zlib.proof.inflate.StepW.
Require Zlib.proof.inflate_api.Body5HdrKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module H := Zlib.proof.roundtrip.RTH9AHdrKit.
Module X := Zlib.proof.roundtrip.RTH8HdrInvX.

(* mwf3_9 is the kit's mwf3hW8 *)
Lemma mwf3_9_h: forall m, mwf3_9 m -> H.mwf3hW8 m.
Proof.
  intros m [(W & S & HW) H8]. constructor.
  - apply H.mW8_of with (hcanon (m_h m)); [exact W | apply X.hwf8_r; exact H8].
  - apply Zlib.proof.inflate.Step3Kit.xwf3_ext with (mcanon m); [reflexivity |].
    apply Zlib.proof.inflate.StepW.swf3_xwf3. exact S.
  - exact HW.
Qed.

Lemma mwf3_9_of_h: forall m, H.mwf3hW8 m -> mwf3_9 m.
Proof.
  intros m [W Xw HW]. split.
  - split; [apply H.mW8_to; [exact W | apply X.hwf_hcanon] | split; [| exact HW]].
    apply (Zlib.proof.inflate.StepW.xwf3_swf3 (mcanon m)).
    apply Zlib.proof.inflate.Step3Kit.xwf3_ext with m; [reflexivity | exact Xw].
  - apply X.hwf8_of_r. exact (H.mW8_h _ W).
Qed.

(* In EXTRA, hinv6 bounds state->length by the header's extra_len, a uInt: the copy of case EXTRA does not wrap. *)
Lemma xsafe_of_hinv6 : forall m, mwf3_9 m -> m_mode m = IM.EXTRA ->
  (i_head (m_s m) = true -> hinv6 (m_s m) (m_h m)) -> Zlib.proof.roundtrip.RTH8HdrKit.xsafe m.
Proof.
  intros m [_ H8] ME HI. unfold Zlib.proof.roundtrip.RTH8HdrKit.xsafe. intros HD XP _.
  destruct (HI HD) as (_ & _ & XE & _). specialize (XE ME XP).
  destruct H8 as (_ & _ & _ & _ & XL & _). unfold urange in XL.
  unfold u32. rewrite Z.mod_small by rep_lia. lia.
Qed.

Lemma hdr9_inv : hdr9_inv_stmt.
Proof.
  intros flush m W L HM O V HI.
  assert (HM': IM.HEAD <= m_mode m <= IM.HCRC)
    by (unfold hdr_mode in HM; apply andb_prop in HM; destruct HM as [A B];
        apply Z.leb_le in A; apply Z.leb_le in B; lia).
  pose proof (H.stepf2_hdrW8 flush m (mwf3_9_h m W) L HM' (fun ME _ => xsafe_of_hinv6 m W ME HI)) as S.
  pose proof (X.stepf2_inv5_any flush m O V) as I.
  pose proof (Zlib.proof.inflate_api.Body5HdrKit.stepf2_hrel flush lenfix_list distfix_list m) as Hr.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    cbn [Zlib.proof.inflate.StepInv.iout_ok] in S;
    unfold Zlib.proof.inflate_api.Body5HdrKit.hrel in Hr; destruct Hr as (H1 & H2 & H3 & H4 & H5 & _);
    (split; [apply mwf3_9_of_h; exact S |]); (split; [unfold hdr_same; auto |]); (split; [exact H1 |]);
    tauto.
Qed.

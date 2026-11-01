(* RT-I, part rti_hkeep: a pass of inflate()'s switch (Model2.stepf2) from a mode after the header
   (TYPE .. DONE: the decode theory's groups md_type, md_tab, md_dec, md_trl) does not change the application's
   gz_header (m_h): only the header modes write it.  Template: rfc1951/DecCallWkeepKit.v (the same per-case
   traversal for the window fields). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.rfc1951.DecodeDefs.
Require Zlib.proof.roundtrip.RTIHKeepKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rti_hkeep : forall flush m,
  md_type (m_mode m) \/ md_tab (m_mode m) \/ md_dec (m_mode m) \/ md_trl (m_mode m) ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => m_h m' = m_h m | IRet _ m' => m_h m' = m_h m end.
Proof.
  intros flush m HM.
  change (RTIHKeepKit.hkgood m (stepf2 flush lenfix_list distfix_list m)).
  assert (NH: forall c, (c =? HEAD) = true \/ (c =? FLAGS) = true \/ (c =? TIME) = true \/ (c =? OS) = true \/
                (c =? EXLEN) = true \/ (c =? EXTRA) = true \/ (c =? NAME) = true \/ (c =? COMMENT) = true \/
                (c =? HCRC) = true \/ (c =? DICTID) = true \/ (c =? DICT) = true -> c = m_mode m -> False).
  { intros c HC ->. unfold md_type, md_tab, md_dec, md_trl in HM.
    repeat destruct HM as [HM|HM]; rewrite HM in HC; vm_compute in HC;
      repeat destruct HC as [HC|HC]; discriminate HC. }
  unfold stepf2, step2.
  Ltac nhd NH := let E := fresh "E" in
    match goal with |- context [if ?c =? ?k then _ else _] =>
      destruct (c =? k) eqn:E; [exfalso; apply (NH c); [tauto|reflexivity]|] end.
  do 11 nhd NH.
  destruct (m_mode m =? Zlib.proof.inflate.Model.TYPE); [apply RTIHKeepKit.c_TYPE_hk|].
  destruct (m_mode m =? TYPEDO); [apply RTIHKeepKit.c_TYPEDO_hk|].
  destruct (m_mode m =? STORED); [apply RTIHKeepKit.c_STORED_hk|].
  destruct (m_mode m =? COPY_); [apply RTIHKeepKit.c_COPY__hk|].
  destruct (m_mode m =? COPY); [apply RTIHKeepKit.c_COPY_hk|].
  destruct (m_mode m =? TABLE); [apply RTIHKeepKit.c_TABLE_hk|].
  destruct (m_mode m =? LENLENS); [apply RTIHKeepKit.c_LENLENS_hk|].
  destruct (m_mode m =? CODELENS); [apply RTIHKeepKit.c_CODELENS_hk|].
  destruct (m_mode m =? LEN_); [apply RTIHKeepKit.c_LEN__hk|].
  destruct (m_mode m =? LEN); [apply RTIHKeepKit.c_LEN_hk|].
  destruct (m_mode m =? LENEXT); [apply RTIHKeepKit.c_LENEXT_hk|].
  destruct (m_mode m =? DIST); [apply RTIHKeepKit.c_DIST_hk|].
  destruct (m_mode m =? DISTEXT); [apply RTIHKeepKit.c_DISTEXT_hk|].
  destruct (m_mode m =? MATCH); [apply RTIHKeepKit.c_MATCH_hk|].
  destruct (m_mode m =? LIT); [apply RTIHKeepKit.c_LIT_hk|].
  destruct (m_mode m =? CHECK); [apply RTIHKeepKit.c_CHECK_hk|].
  destruct (m_mode m =? LENGTH); [apply RTIHKeepKit.c_LENGTH_hk|].
  destruct (m_mode m =? DONE); [apply RTIHKeepKit.c_DONE_hk|].
  destruct (m_mode m =? BAD); [apply RTIHKeepKit.c_BAD_hk|].
  destruct (m_mode m =? MEM); exact (RTIHKeepKit.hkrel_refl m).
Qed.

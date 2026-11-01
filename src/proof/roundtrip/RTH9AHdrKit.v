(* The header cases of Model2.v (HEAD .. HCRC) on WIDE machines (inputs and output spaces of up to 2^32-1 bytes)
   with an application header whose buffers have any uInt size.

   StepWHeader.v proves the header cases for the wide invariant InvW.mwfW, whose header invariant hwf caps
   extra_max / name_max / comm_max at 65536; RTH8HdrKit.v proves them for the narrow invariant with the header
   invariant RTH8HdrKit.hwf8r (these three sizes any uInt).  This file does both at once: [mwfW8] is mwfW with
   hwf8r, and [mwfxW8], [mwf3xW8], [mwf3hW8] are StepWHeader's mwfxW, mwf3xW, mwf3hW over it.  The facts that do
   not read the header are moved between mwfW8 and mwfW through any header with hwf ([mW8_of], [mW8_to]).

   The copy into the extra buffer (case EXTRA) tests `len + copy > extra_max` in 32 bits (len = extra_len - length,
   copy <= length): with extra_max close to 2^32 the sum may wrap, so [EXTRAW8_ok] takes RTH8HdrKit.xsafe (the sum
   does not wrap) for a machine that starts in EXTRA; EXLEN gives it to the machine it hands to EXTRA (len = 0). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Step3Header.
Require Import Zlib.proof.inflate.StepWHeader.
Require Import Zlib.proof.inflate.Steps2.
Require Zlib.proof.roundtrip.RTH8HdrKit.
Import ListNotations.
Local Open Scope Z_scope.

Module K := Zlib.proof.roundtrip.RTH8HdrKit.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant                                                                                  *)

Record mwfW8 (m: mst) : Prop := {
  mW8_md : modewf (m_s m);
  mW8_s : swf (m_s m);
  mW8_h : K.hwf8r (m_h m);
  mW8_inp : Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m);
  mW8_aout : 0 <= m_aout m <= Int.max_unsigned;
  mW8_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mW8_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mW8_hold : lrange (m_hold m);
  mW8_bits : 0 <= m_bits m <= 39;
  mW8_in : m_in m = Zlength (m_inp m);
  mW8_out : urange (m_out m);
  mW8_ret : -5 <= m_ret m <= 2;
  mW8_leave : 0 <= m_leave m <= 1;
  mW8_adler : lrange (m_adler m);
  mW8_tin : lrange (m_tin m);
  mW8_tout : lrange (m_tout m);
  mW8_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mW8_sow : 0 <= m_sow m <= Zlength (m_ow m);
  mW8_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

Record mwfxW8 (m: mst) : Prop := { mxW8_w : mwfW8 m; mxW8_x : xwf3 m }.
Record mwf3xW8 (m: mst) : Prop := { m3xW8_w : mwfW8 m; m3xW8_x : xwf3 m; m3xW8_n : nohdr m }.
Record mwf3hW8 (m: mst) : Prop := { m3hW8_w : mwfW8 m; m3hW8_x : xwf3 m; m3hW8_h : hdrW m }.

Lemma xW8_x: forall m, mwf3xW8 m -> mwfxW8 m.
Proof. intros m [W X N]. constructor; auto. Qed.

Lemma hW8_x: forall m, mwf3hW8 m -> mwfxW8 m.
Proof. intros m [W X H]. constructor; auto. Qed.

Lemma mwf3xW8_hW: forall m, mwf3xW8 m -> mwf3hW8 m.
Proof. intros m [W X N]. constructor; auto. apply nohdr_hdrW; auto. Qed.

Lemma iout_xW8_hW: forall o, iout_ok mwf3xW8 o -> iout_ok mwf3hW8 o.
Proof. intros o. destruct o; simpl; apply mwf3xW8_hW. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwfW8 and mwfW: the same facts but the header's                                                *)

Lemma mW8_of: forall m h, mwfW (set_m_h m h) -> K.hwf8r (m_h m) -> mwfW8 m.
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mW8_to: forall m h, mwfW8 m -> hwf h -> mwfW (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

(* an update that does not read the header keeps the header-free facts *)
Lemma mW8_lift: forall m m',
  (mwfW (set_m_h m K.hzero) -> mwfW (set_m_h m' K.hzero)) -> m_h m' = m_h m -> mwfW8 m -> mwfW8 m'.
Proof.
  intros m m' F E W. apply mW8_of with K.hzero; [apply F; apply mW8_to; auto; apply K.hwf_hzero |].
  rewrite E. apply (mW8_h _ W).
Qed.

Lemma mwfW8_needbits: forall n m, mwfW8 m -> n <= 32 -> mwfW8 (needbits n m).
Proof.
  intros n m W N. apply mW8_lift with m; [| apply needbits_f_h | exact W].
  intros W0. unfold needbits. rewrite <- K.needbits_f_set_h. apply mwfW_needbits; auto.
Qed.

Lemma mwfW8_set_leave: forall m, mwfW8 m -> mwfW8 (set_leave m).
Proof.
  intros m W. apply mW8_lift with m; [| reflexivity | exact W].
  intros W0. exact (mwfW_set_leave _ W0).
Qed.

Lemma mwf3xW8_needbits: forall n m, mwf3xW8 m -> n <= 32 -> mwf3xW8 (needbits n m).
Proof.
  intros n m [W X N] H. constructor; [apply mwfW8_needbits; auto | |].
  - apply xwf3_ext with m; [symmetry; apply needbits_s | exact X].
  - apply nohdr_ext with m; [exact N | apply needbits_s].
Qed.

Lemma mwf3xW8_set_leave: forall m, mwf3xW8 m -> mwf3xW8 (set_leave m).
Proof.
  intros m [W X N]. constructor; [apply mwfW8_set_leave; auto | |].
  - apply xwf3_ext with m; [reflexivity | exact X].
  - apply nohdr_ext with m; [exact N | reflexivity].
Qed.

Lemma mwf3hW8_set_leave: forall m, mwf3hW8 m -> mwf3hW8 (set_leave m).
Proof.
  intros m [W X H]. constructor; [apply mwfW8_set_leave; auto | apply xwf3_ext with m; auto | exact H].
Qed.

Lemma mwf3xW8_set_bad_x: forall m e, mwfxW8 m -> mwf3xW8 (set_bad m e).
Proof.
  intros m e [W X].
  assert (Y: mwf3xW (set_bad (set_m_h m K.hzero) e))
    by (apply mwf3xW_set_bad_x; constructor; [apply mW8_to; auto; apply K.hwf_hzero |
                                             apply xwf3_ext with m; auto]).
  destruct Y as [Y1 Y2 Y3]. constructor.
  - apply mW8_of with K.hzero; [exact Y1 | apply (mW8_h _ W)].
  - apply xwf3_ext with (set_bad (set_m_h m K.hzero) e); [reflexivity | exact Y2].
  - exact Y3.
Qed.

Lemma mwf3xW8_set_bad: forall m e, mwf3xW8 m -> mwf3xW8 (set_bad m e).
Proof. intros m e W. apply mwf3xW8_set_bad_x, xW8_x, W. Qed.

Lemma needbits_okW8: forall n m,
  mwfW8 m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

Lemma needbits_allW8: forall n m, mwf3xW8 m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  mwf3xW8 (needbits n m) /\ m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m) /\
  m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof.
  intros n m W L N E. destruct (needbits_okW8 n m (m3xW8_w _ W) L N E) as [B1 L1].
  split; [apply mwf3xW8_needbits; auto |]. split; [auto |]. split; [auto |].
  split; [apply needbits_s | apply needbits_f_h].
Qed.

(* NEEDBITS(n) from fewer than n bits keeps the bit buffer free of bits above its count (StepWHeader.needbits_hb) *)
Lemma needbits_hbW8: forall n m, mwfW8 m -> n <= 32 -> m_hold m < 2 ^ m_bits m -> m_bits m < n ->
  m_hold (needbits n m) < 2 ^ m_bits (needbits n m) /\ m_bits (needbits n m) < n + 8 /\
  (m_leave (needbits n m) = 1 -> m_leave m = 1 \/ m_bits (needbits n m) < n).
Proof.
  intros n m W N H B. pose proof (mW8_to m K.hzero W K.hwf_hzero) as W0.
  pose proof (needbits_hb n (set_m_h m K.hzero) W0 N H B) as R.
  unfold needbits in *. rewrite K.needbits_f_set_h in R. exact R.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the machines the cases build                                                                   *)

Lemma mwfxW8_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> K.hwf8r (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m -> mwfxW8 m.
Proof.
  intros m HM S H XW. intros. constructor.
  - constructor; auto. apply modewf_hdr; auto.
  - unfold m_mode in HM. unfold HEAD, TYPEDO in HM.
    constructor; auto; unfold m_mode, decode_mode;
    unfold LENEXT, DIST, DISTEXT, MATCH, LIT, LEN, LEN_; intros E; exfalso; lia.
Qed.

Lemma mwf3xW8_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> K.hwf8r (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m ->
  i_mode (m_s m) <> EXLEN /\ i_mode (m_s m) <> EXTRA -> mwf3xW8 m.
Proof. intros. assert (Y: mwfxW8 m) by (apply mwfxW8_of; auto). destruct Y as [W X]. constructor; auto. Qed.

Lemma mwf3hW8_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> K.hwf8r (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m ->
  (i_mode (m_s m) = EXLEN -> m_bits m < 16 /\ m_hold m < 2 ^ m_bits m) ->
  (i_mode (m_s m) = EXTRA -> i_length (m_s m) <= Int.max_signed) -> mwf3hW8 m.
Proof.
  intros. assert (Y: mwfxW8 m) by (apply mwfxW8_of; auto). destruct Y as [W X]. constructor; auto. split; auto.
Qed.

Lemma mwfxW8_out: forall m, mwfxW8 m -> HEAD <= m_mode m <= TYPEDO -> m_out m = m_aout m.
Proof.
  intros m W HM. destruct (mW8_outeq _ (mxW8_w _ W)) as [E | [E | [E | E]]]; auto;
  exfalso; rewrite E in HM; unfold HEAD, TYPEDO, LENGTH, DONE, BAD in *; lia.
Qed.

Lemma inbytes_bytesW8: forall m n, mwfW8 m -> is_bytes (inbytes m n).
Proof. intros m n W. unfold inbytes. apply Forall_sublist. apply (mW8_inp _ W). Qed.

(* the facts of a machine m1 in a header mode *)
Ltac baseW8 W1 HM :=
  let Y := fresh "Y" in
  first [ (pose proof W1 as Y; match type of Y with mwfxW8 _ => idtac end)
        | pose proof (xW8_x _ W1) as Y | pose proof (hW8_x _ W1) as Y ];
  let O := fresh "O" in pose proof (mwfxW8_out _ Y HM) as O;
  let X := fresh "X" in pose proof (x3_head _ (mxW8_x _ Y)) as X;
  let WB := fresh "WB" in pose proof (sw_wbits _ (mW8_s _ (mxW8_w _ Y))) as WB;
  let V := fresh "V" in pose proof (mxW8_w _ Y) as V; destruct V as [_ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  clear Y; repeat match goal with H: _ /\ _ |- _ => destruct H end.

Ltac swW8 := repeat match goal with
  | |- swf (set_i_mode _ _) => apply swf_set_mode
  | |- swf (set_i_check _ _) => apply swf_check
  | |- swf (set_i_flags _ _) => apply swf_flags
  | |- swf (set_i_dmax _ _) => apply swf_dmax
  | |- swf (set_i_length _ _) => apply swf_length
  | |- swf (set_i_hold _ _) => apply swf_hold
  | |- swf (set_i_bits _ _) => apply swf_bits
  | |- swf (set_i_wbits _ _) => apply swf_wbits
  | |- K.hwf8r (set_h_text _ _) => apply K.hwf8_text
  | |- K.hwf8r (set_h_time _ _) => apply K.hwf8_time
  | |- K.hwf8r (set_h_xflags _ _) => apply K.hwf8_xflags
  | |- K.hwf8r (set_h_os _ _) => apply K.hwf8_os
  | |- K.hwf8r (set_h_extra_len _ _) => apply K.hwf8_extra_len
  | |- K.hwf8r (set_h_hcrc _ _) => apply K.hwf8_hcrc
  | |- K.hwf8r (set_h_done _ _) => apply K.hwf8_done
  | |- K.hwf8r (set_h_xp _ _) => apply K.hwf8_xp
  | |- K.hwf8r (set_h_np _ _) => apply K.hwf8_np
  | |- K.hwf8r (set_h_cp _ _) => apply K.hwf8_cp
  | |- K.hwf8r (set_h_xbuf _ _) => apply K.hwf8_xbuf
  | |- K.hwf8r (set_h_nbuf _ _) => apply K.hwf8_nbuf
  | |- K.hwf8r (set_h_cbuf _ _) => apply K.hwf8_cbuf
  end.

Ltac finW8 W1 HM := rewrite ?crc_if_eq; apply mwf3xW8_of; unfold m_mode; simpl; split_ifs; simpl; baseW8 W1 HM;
  swW8; try leaf; try nh.
Ltac finxW8 W1 HM := rewrite ?crc_if_eq; apply mwfxW8_of; unfold m_mode; simpl; split_ifs; simpl; baseW8 W1 HM;
  swW8; try leaf.
Ltac finhW8 W1 HM := rewrite ?crc_if_eq; apply mwf3hW8_of; unfold m_mode; simpl; split_ifs; simpl; baseW8 W1 HM;
  swW8; try leaf.

Ltac nbW8 n m W L :=
  let m1 := fresh "m1" in let E := fresh "E" in let NL := fresh "NL" in
  remember (needbits n m) as m1 eqn:E; cbv beta zeta;
  destruct (Z.eqb_spec (m_leave m1) 1) as [?|NL];
  [simpl; subst m1; first [apply mwf3xW8_needbits | apply mwf3xW8_hW, mwf3xW8_needbits]; auto; lia |];
  let W1 := fresh "W1" in let L1 := fresh "L1" in let B1 := fresh "B1" in
  let S1 := fresh "S1" in let H1 := fresh "H1" in
  destruct (needbits_allW8 n m W L ltac:(lia) ltac:(subst m1; exact NL)) as (W1 & L1 & B1 & S1 & H1);
  rewrite <- E in W1, L1, B1, S1, H1; clear E NL.

Ltac goW8 OK W HM := apply OK; [finW8 W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity].

(* ---------------------------------------------------------------------------------------------- *)
(* the cases                                                                                     *)

Definition okW8_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3xW8 m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3xW8 (f m).

(* FLAGS, TIME, OS start outside EXLEN / EXTRA and may stop in them *)
Definition okhW8_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3xW8 m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3hW8 (f m).

Lemma HCRCW8_ok : okW8_at HCRC c_HCRC.
Proof.
  intros m W L M. unfold c_HCRC.
  destruct (negb (Z.land (i_flags (m_s m)) 512 =? 0)) eqn:F.
  - nbW8 16 m W L.
    destruct (andb _ _); simpl; [apply mwf3xW8_set_bad; auto |].
    assert (HM: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    destruct (i_head (m_s m1)) eqn:HD; finW8 W1 HM.
  - cbv beta zeta. simpl.
    assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
    destruct (i_head (m_s m)) eqn:HD; finW8 W HM.
Qed.

Lemma COMMENTW8_ok : okW8_at COMMENT c_COMMENT2.
Proof.
  intros m W L M. unfold c_COMMENT2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3xW8_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3xW8_w _ W) as W0. pose proof (mW8_h _ W0) as HW. pose proof (mW8_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (i_head (m_s m) && h_cp (m_h m))%bool
                  (h_cbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mW8_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mW8_nx _ W0); lia. }
    { pose proof (mW8_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (K.h8_cbuf _ HW)). lia. }
    { apply (K.h8_cbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (K.h8_comm_max _ HW). pose proof (K.h8_cbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3xW8_set_leave. finW8 W HM.
    + goW8 HCRCW8_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; goW8 HCRCW8_ok W HM.
Qed.

Lemma NAMEW8_ok : okW8_at NAME c_NAME2.
Proof.
  intros m W L M. unfold c_NAME2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3xW8_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3xW8_w _ W) as W0. pose proof (mW8_h _ W0) as HW. pose proof (mW8_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_name_max (m_h m)) (i_head (m_s m) && h_np (m_h m))%bool
                  (h_nbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mW8_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mW8_nx _ W0); lia. }
    { pose proof (mW8_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (K.h8_nbuf _ HW)). lia. }
    { apply (K.h8_nbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (K.h8_name_max _ HW). pose proof (K.h8_nbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3xW8_set_leave. finW8 W HM.
    + goW8 COMMENTW8_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; goW8 COMMENTW8_ok W HM.
Qed.

(* the copy into the extra buffer: hdrW bounds the remaining length, xsafe says the 32-bit sum len + copy does not
   wrap *)
Lemma EXTRAW8_ok : forall m, mwfxW8 m -> m_leave m = 0 -> m_mode m = EXTRA ->
  (Z.land (i_flags (m_s m)) 1024 <> 0 -> i_length (m_s m) <= Int.max_signed) ->
  (negb (Z.land (i_flags (m_s m)) 1024 =? 0) = true -> K.xsafe m) -> iout_ok mwf3hW8 (c_EXTRA2 m).
Proof.
  intros m W L M XL XS. unfold c_EXTRA2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  assert (M': i_mode (m_s m) = EXTRA) by exact M.
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F; [| apply iout_xW8_hW; goW8 NAMEW8_ok W HM].
  specialize (XS eq_refl).
  assert (XL1: i_length (m_s m) <= Int.max_signed).
  { apply XL. intros E. rewrite E in F. discriminate. }
  clear XL.
  match goal with |- context [if negb (Z.min ?a ?b =? 0) then ?X else m] =>
    remember (if negb (Z.min a b =? 0) then X else m) as m2 eqn:E2 end.
  assert (W2: mwf3hW8 m2 /\ m_leave m2 = 0 /\ HEAD <= m_mode m2 <= TYPEDO).
  { subst m2. pose proof (mxW8_w _ W) as W0. pose proof (mW8_h _ W0) as HW. pose proof (mW8_s _ W0) as SW.
    pose proof (mW8_nx _ W0) as NX. pose proof (sw_length _ SW) as LN. pose proof (K.h8_extra_max _ HW) as XM.
    pose proof (K.h8_xbuf _ HW) as XB. pose proof (proj1 (mW8_inp _ W0)) as IN.
    unfold K.xsafe in XS. unfold m_have in *. unfold urange in *.
    remember (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)) as copy eqn:EC.
    assert (CP: 0 <= copy <= i_length (m_s m) /\ copy <= Zlength (m_inp m) - m_nx m) by (rewrite EC; lia).
    clear EC.
    destruct (negb (copy =? 0)).
    2:{ split; [| split; [auto | auto]]. constructor; [exact W0 | apply (mxW8_x _ W) |].
        split; intros HE; [exfalso; unfold m_mode in HE; rewrite M' in HE; unfold_modes; lia | intros _; exact XL1]. }
    remember (u32 (h_extra_len (m_h m) - i_length (m_s m))) as len eqn:EL.
    assert (LR: urange len) by (rewrite EL; apply u32_range). clear EL. unfold urange in LR.
    destruct (andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m))) eqn:C.
    + apply andb_prop in C; destruct C as [C0 C]; apply Z.ltb_lt in C.
      apply andb_prop in C0; destruct C0 as [C1 C2].
      specialize (XS C1 C2 C).
      remember (if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy)
        as n eqn:EN.
      assert (NR: 0 <= n <= copy /\ len + n <= h_extra_max (m_h m)).
      { rewrite EN. unfold u32. rewrite (Z.mod_small (len + copy)) by rep_lia.
        destruct (Z.ltb_spec (h_extra_max (m_h m)) (len + copy)); lia. }
      clear EN.
      assert (IB: Zlength (inbytes m n) = n) by (unfold inbytes; rewrite Zlength_sublist; lia).
      destruct (put_bytes_ok (h_xbuf (m_h m)) len (inbytes m n)) as [PB1 PB2]; [lia | lia |].
      rewrite (proj1 XB) in PB1.
      specialize (PB2 (proj2 XB) (inbytes_bytesW8 m n W0)).
      split.
      * finhW8 W HM.
        all: intros HE; [exfalso; rewrite M' in HE; unfold_modes; lia | lia].
      * rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto.
    + split.
      * finhW8 W HM.
        all: intros HE; [exfalso; rewrite M' in HE; unfold_modes; lia | lia].
      * rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto. }
  destruct W2 as (W2 & L2 & HM2).
  destruct (negb (i_length (m_s m2) =? 0));
    [simpl; apply mwf3hW8_set_leave; auto | apply iout_xW8_hW; goW8 NAMEW8_ok W2 HM2].
Qed.

(* EXLEN reads the extra length from 16 bits of a bit buffer holding fewer than 16 bits: below 2^23 *)
Lemma EXLENW8_ok : forall m, mwf3hW8 m -> m_leave m = 0 -> m_mode m = EXLEN -> iout_ok mwf3hW8 (c_EXLEN2 m).
Proof.
  intros m W L M. unfold c_EXLEN2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F.
  - destruct (proj1 (m3hW8_h _ W) M) as [B0 H0].
    destruct (needbits_hbW8 16 m (m3hW8_w _ W) ltac:(lia) H0 B0) as (HB1 & BB1 & LB1).
    remember (needbits 16 m) as m1 eqn:E. cbv beta zeta.
    assert (S1: m_s m1 = m_s m) by (subst m1; apply needbits_s).
    assert (W1: mwfxW8 m1).
    { constructor; [subst m1; apply mwfW8_needbits; [apply (m3hW8_w _ W) | lia] |
                    apply xwf3_ext with m; [symmetry; exact S1 | apply (m3hW8_x _ W)]]. }
    destruct (Z.eqb_spec (m_leave m1) 1) as [LV|NL].
    + (* the input ran out: m1 is still in EXLEN, with fewer than 16 bits *)
      simpl. constructor; [apply (mxW8_w _ W1) | apply (mxW8_x _ W1) |]. split; intros HE.
      * split; [destruct (LB1 LV) as [A|A]; [rewrite L in A; discriminate | exact A] | exact HB1].
      * exfalso. unfold m_mode in HE, M. rewrite S1, M in HE. unfold_modes; lia.
    + destruct (needbits_okW8 16 m (m3hW8_w _ W) L ltac:(lia) ltac:(subst m1; exact NL)) as [B1 L1].
      rewrite <- E in B1, L1.
      assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
      assert (HV: 0 <= m_hold m1 < 8388608).
      { pose proof (mW8_hold _ (mxW8_w _ W1)). unfold lrange in *. split; [lia|].
        change 8388608 with (2 ^ 23). apply Z.lt_le_trans with (2 ^ m_bits m1); [exact HB1 | apply Z.pow_le_mono_r; lia]. }
      clear E NL.
      apply EXTRAW8_ok; [finxW8 W1 HM1 | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity | |].
      * intros _. rewrite ?crc_if_eq. simpl. split_ifs; simpl; unfold u32; rewrite Z.mod_small by lia; rep_lia.
      * (* EXTRA starts with length = extra_len: len = 0 *)
        intros _. unfold K.xsafe. rewrite ?crc_if_eq. cbn.
        destruct (i_head (m_s m1)) eqn:HD; cbn; intros; try congruence.
        rewrite Z.sub_diag. pose proof (u32_range (m_hold m1)). unfold urange in *. change (u32 0) with 0.
        pose proof (Z.le_min_l (u32 (m_hold m1)) (Zlength (m_inp m1) - m_nx m1)). rep_lia.
  - cbv beta zeta.
    apply EXTRAW8_ok; [finxW8 W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity | |].
    + apply negb_false_iff, Z.eqb_eq in F. split_ifs; simpl; intros FF; contradiction.
    + intros E. exfalso. revert E. rewrite ?crc_if_eq. cbn. destruct (i_head (m_s m)); cbn; rewrite F; discriminate.
Qed.

Lemma OSW8_ok : okhW8_at OS c_OS2.
Proof.
  intros m W L M. unfold c_OS2. nbW8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  apply EXLENW8_ok; [| rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity].
  (* EXLEN starts with an empty bit buffer *)
  finhW8 W1 HM1. all: intros _; simpl; lia.
Qed.

Lemma TIMEW8_ok : okhW8_at TIME c_TIME2.
Proof.
  intros m W L M. unfold c_TIME2. nbW8 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  goW8 OSW8_ok W1 HM1.
Qed.

Lemma FLAGSW8_ok : okhW8_at FLAGS c_FLAGS2.
Proof.
  intros m W L M. unfold c_FLAGS2. nbW8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  destruct (negb (Z.land (s32 (m_hold m1)) 255 =? 8)); [simpl; apply mwf3xW8_hW, mwf3xW8_set_bad; finW8 W1 HM1 |].
  destruct (negb (Z.land (s32 (m_hold m1)) 57344 =? 0)); [simpl; apply mwf3xW8_hW, mwf3xW8_set_bad; finW8 W1 HM1 |].
  goW8 TIMEW8_ok W1 HM1.
Qed.

(* case HEAD with patch F7 (StepW.HEAD2_ok) *)
Lemma HEADW8_ok : okW8_at HEAD c_HEAD2.
Proof.
  intros m W L M. unfold c_HEAD2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_wrap (m_s m) =? 0) eqn:WR; [simpl; finW8 W HM |].
  nbW8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  assert (XW0: i_wbits (m_s m1) = 0 -> i_wsize (m_s m1) = 0).
  { intros Z0. apply (x3_head _ (m3xW8_x _ W1)); [unfold m_mode; rewrite S1; exact M | exact Z0 |].
    rewrite S1. apply Z.eqb_neq. exact WR. }
  destruct (andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)) eqn:GZ.
  { simpl. finW8 W1 HM1. }
  destruct (i_head (m_s m1)) eqn:HD; simpl.
  all: destruct (orb _ _); [simpl; apply mwf3xW8_set_bad; finW8 W1 HM1 |].
  all: destruct (negb (m_hold m1 mod 16 =? 8)); [simpl; apply mwf3xW8_set_bad; finW8 W1 HM1 |].
  all: remember (Z.shiftr (m_hold m1) 4 mod 16 + 8) as len eqn:EL.
  all: assert (LN: 8 <= len <= 23)
         by (rewrite EL; pose proof (Z.mod_pos_bound (Z.shiftr (m_hold m1) 4) 16); lia).
  all: clear EL.
  all: destruct (orb _ _) eqn:C; [simpl; apply mwf3xW8_set_bad; finW8 W1 HM1 |].
  all: apply orb_false_iff in C; destruct C as [C1 C2]; apply Z.ltb_ge in C1.
  all: assert (C3: len <= (if i_wbits (m_s m1) =? 0 then len else i_wbits (m_s m1)))
         by (destruct (Z.eqb_spec (i_wbits (m_s m1)) 0); [lia |];
             cbn [negb andb] in C2; apply Z.ltb_ge in C2; exact C2).
  all: clear C2.
  all: assert (P: 0 <= 2 ^ len <= 32768)
         by (split; [apply Z.pow_nonneg; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]).
  all: destruct (Z.land (Z.shiftr (m_hold m1) 4) 512 =? 0); simpl; finW8 W1 HM1.
Qed.

(* one pass of the switch from a header mode keeps mwf3hW8; a machine that starts in EXTRA with the extra field
   to read needs xsafe *)
Lemma stepf2_hdrW8 : forall flush m, mwf3hW8 m -> m_leave m = 0 -> HEAD <= m_mode m <= HCRC ->
  (m_mode m = EXTRA -> negb (Z.land (i_flags (m_s m)) 1024 =? 0) = true -> K.xsafe m) ->
  iout_ok mwf3hW8 (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros flush m W L HM XS.
  assert (XW: nohdr m -> mwf3xW8 m) by (intros N; destruct W; constructor; auto).
  assert (E: m_mode m = HEAD \/ m_mode m = FLAGS \/ m_mode m = TIME \/ m_mode m = OS \/ m_mode m = EXLEN \/
             m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/ m_mode m = HCRC)
    by (unfold_modes; unfold NAME, COMMENT, HCRC, FLAGS, TIME, OS, EXLEN, EXTRA in *; lia).
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]].
  - rewrite (stepf2_HEAD _ _ _ _ E). apply iout_xW8_hW, HEADW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_FLAGS _ _ _ _ E). apply FLAGSW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_TIME _ _ _ _ E). apply TIMEW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_OS _ _ _ _ E). apply OSW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_EXLEN _ _ _ _ E). apply EXLENW8_ok; auto.
  - rewrite (stepf2_EXTRA _ _ _ _ E). apply EXTRAW8_ok; auto.
    + apply hW8_x; auto.
    + apply (proj2 (m3hW8_h _ W)). exact E.
  - rewrite (stepf2_NAME _ _ _ _ E). apply iout_xW8_hW, NAMEW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_COMMENT _ _ _ _ E). apply iout_xW8_hW, COMMENTW8_ok; auto. apply XW; nohdr_md.
  - rewrite (stepf2_HCRC _ _ _ _ E). apply iout_xW8_hW, HCRCW8_ok; auto. apply XW; nohdr_md.
Qed.

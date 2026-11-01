(* The header cases FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT preserve the wide
   invariant.  NAME .. DICT preserve mwf3xW (StepWKit.v); DICT / DICTID fall into TYPE (hypothesis ok_TYPE,
   proved in StepWBlock.v).  FLAGS .. EXTRA may stop in EXLEN or EXTRA, where mwf3xW does not hold: they lead
   to mwf3hW, which has InvW.v's hdrW in place of nohdr.  hdrW is what makes the extra field's copy safe:
   EXLEN reads the field's length from 16 bits of a bit buffer that held fewer than 16 bits before (so the
   length is below 2^23), and EXTRA's test `len + copy > extra_max` then cannot wrap in 32 bits. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Step3Header.
Require Export Zlib.proof.inflate.StepWKit.
Require Export Zlib.proof.inflate.Model2.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.crc32.Combine.

Lemma inbytes_bytes: forall m n, mwfW m -> is_bytes (inbytes m n).
Proof. intros m n W. unfold inbytes. apply Forall_sublist. apply (mwW_inp _ W). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3xW in the header modes                                                                       *)

(* mwfW and xwf3: the part of the invariant the header cases rebuild for every machine *)
Record mwfxW (m: mst) : Prop := { mxW_w : mwfW m; mxW_x : xwf3 m }.

(* the invariant of the machines the cases FLAGS .. EXTRA return *)
Record mwf3hW (m: mst) : Prop := { m3H_w : mwfW m; m3H_x : xwf3 m; m3H_h : hdrW m }.

Lemma xW_x: forall m, mwf3xW m -> mwfxW m.
Proof. intros m [W X N]. constructor; auto. Qed.

Lemma hW_x: forall m, mwf3hW m -> mwfxW m.
Proof. intros m [W X H]. constructor; auto. Qed.

Lemma mwf3xW_hW: forall m, mwf3xW m -> mwf3hW m.
Proof. intros m [W X N]. constructor; auto. apply nohdr_hdrW; auto. Qed.

Lemma iout_xW_hW: forall o, iout_ok mwf3xW o -> iout_ok mwf3hW o.
Proof. intros o. destruct o; simpl; apply mwf3xW_hW. Qed.

Lemma mwfxW_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> hwf (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m -> mwfxW m.
Proof.
  intros m HM S H XW. intros. constructor.
  - constructor; auto. apply modewf_hdr; auto.
  - unfold m_mode in HM. unfold HEAD, TYPEDO in HM.
    constructor; auto; unfold m_mode, decode_mode;
    unfold LENEXT, DIST, DISTEXT, MATCH, LIT, LEN, LEN_; intros E; exfalso; lia.
Qed.

(* mwfxW_of's facts give mwf3xW outside EXLEN / EXTRA, and mwf3hW with hdrW's two facts *)
Lemma mwf3xW_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> hwf (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m ->
  i_mode (m_s m) <> EXLEN /\ i_mode (m_s m) <> EXTRA -> mwf3xW m.
Proof. intros. assert (Y: mwfxW m) by (apply mwfxW_of; auto). destruct Y as [W X]. constructor; auto. Qed.

Lemma mwf3hW_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> hwf (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_unsigned -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m ->
  (i_mode (m_s m) = EXLEN -> m_bits m < 16 /\ m_hold m < 2 ^ m_bits m) ->
  (i_mode (m_s m) = EXTRA -> i_length (m_s m) <= Int.max_signed) -> mwf3hW m.
Proof.
  intros. assert (Y: mwfxW m) by (apply mwfxW_of; auto). destruct Y as [W X]. constructor; auto. split; auto.
Qed.

Lemma mwfxW_out: forall m, mwfxW m -> HEAD <= m_mode m <= TYPEDO -> m_out m = m_aout m.
Proof.
  intros m W HM. apply mwfW_out_eq; [apply W | ..]; unfold HEAD, TYPEDO, LENGTH, DONE, BAD in *; lia.
Qed.

(* the machine is in a mode other than EXLEN, EXTRA: its mode is a constant, or that of the case's machine *)
Ltac nh := unfold m_mode in *;
  repeat match goal with H: m_s ?a = m_s ?b |- context [m_s ?a] => rewrite H end; unfold_modes; lia.

Lemma ok_needbits: forall n m (P: mst -> iout),
  mwf3xW m -> m_leave m = 0 -> n <= 32 ->
  (forall m1, mwf3xW m1 -> m_leave m1 = 0 -> n <= m_bits m1 -> m_s m1 = m_s m -> m_h m1 = m_h m ->
     iout_ok mwf3xW (P m1)) ->
  iout_ok mwf3xW (let m1 := needbits n m in if m_leave m1 =? 1 then IBrk m1 else P m1).
Proof.
  intros n m P W L N K. cbv zeta.
  pose proof (mwf3xW_needbits n m W N) as W1.
  destruct (Z.eqb_spec (m_leave (needbits n m)) 1) as [E | E]; [exact W1 |].
  destruct (needbits_ok n m (m3W_w _ W) L N E) as [B1 L1].
  apply K; auto. apply needbits_s. apply needbits_f_h.
Qed.


Lemma needbits_all: forall n m, mwf3xW m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  mwf3xW (needbits n m) /\ m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m) /\
  m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof.
  intros n m W L N E. destruct (needbits_ok n m (m3W_w _ W) L N E) as [B1 L1].
  split; [apply mwf3xW_needbits; auto |]. split; [auto |]. split; [auto |].
  split; [apply needbits_s | apply needbits_f_h].
Qed.

Lemma mwf3xW_set_bad_x: forall m e, mwfxW m -> mwf3xW (set_bad m e).
Proof.
  intros m e [W X]. constructor.
  - unfold set_bad. apply mwfW_set_mode_plain.
    + destruct W; constructor; simpl; auto.
    + unfold HEAD, BAD, SYNC; lia.
    + unfold BAD, LENLENS; lia.
    + unfold BAD, CODELENS; lia.
    + unfold decode_mode, BAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
    + auto.
  - constructor; unfold m_mode, decode_mode; simpl; intros E; exfalso;
      unfold BAD, HEAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
  - split; unfold m_mode; simpl; unfold BAD, EXLEN, EXTRA; lia.
Qed.

Lemma mwf3xW_set_bad: forall m e, mwf3xW m -> mwf3xW (set_bad m e).
Proof. intros m e W. apply mwf3xW_set_bad_x, xW_x, W. Qed.

(* the facts of a machine m1 in a header mode *)
Ltac base W1 HM :=
  let Y := fresh "Y" in
  first [ (pose proof W1 as Y; match type of Y with mwfxW _ => idtac end)
        | pose proof (xW_x _ W1) as Y | pose proof (hW_x _ W1) as Y ];
  let O := fresh "O" in pose proof (mwfxW_out _ Y HM) as O;
  let X := fresh "X" in pose proof (x3_head _ (mxW_x _ Y)) as X;
  let WB := fresh "WB" in pose proof (sw_wbits _ (mwW_s _ (mxW_w _ Y))) as WB;
  let V := fresh "V" in pose proof (mxW_w _ Y) as V; destruct V as [_ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  clear Y; repeat match goal with H: _ /\ _ |- _ => destruct H end.

(* mwf3xW of a machine built from m1 by the setters *)
Ltac split_ifs := repeat match goal with
  | |- context [if i_head ?x then _ else _] => destruct (i_head x)
  | |- context [if i_wbits ?x =? 0 then _ else _] => destruct (Z.eqb_spec (i_wbits x) 0)
  end.

Ltac fin2 W1 HM := rewrite ?crc_if_eq; apply mwf3xW_of; unfold m_mode; simpl; split_ifs; simpl; base W1 HM; sw;
  try leaf; try nh.

(* the same for mwfxW and mwf3hW (the hdrW facts of a machine in EXLEN are left to the caller) *)
Ltac fin2x W1 HM := rewrite ?crc_if_eq; apply mwfxW_of; unfold m_mode; simpl; split_ifs; simpl; base W1 HM; sw;
  try leaf.
Ltac fin2h W1 HM := rewrite ?crc_if_eq; apply mwf3hW_of; unfold m_mode; simpl; split_ifs; simpl; base W1 HM; sw;
  try leaf.


(* NEEDBITS(n) at the head of a case: the leave branch, then the facts of the result *)
Ltac nb n m W L :=
  let m1 := fresh "m1" in let E := fresh "E" in let NL := fresh "NL" in
  remember (needbits n m) as m1 eqn:E; cbv beta zeta;
  destruct (Z.eqb_spec (m_leave m1) 1) as [?|NL];
  [simpl; subst m1; first [apply mwf3xW_needbits | apply mwf3xW_hW, mwf3xW_needbits]; auto; lia |];
  let W1 := fresh "W1" in let L1 := fresh "L1" in let B1 := fresh "B1" in
  let S1 := fresh "S1" in let H1 := fresh "H1" in
  destruct (needbits_all n m W L ltac:(lia) ltac:(subst m1; exact NL)) as (W1 & L1 & B1 & S1 & H1);
  rewrite <- E in W1, L1, B1, S1, H1; clear E NL.


(* a case falling into the next case OK *)
Ltac go OK W HM := apply OK; [fin2 W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity].

Lemma HCRC_ok : ok_HCRC.
Proof.
  intros m W L M. unfold c_HCRC.
  destruct (negb (Z.land (i_flags (m_s m)) 512 =? 0)) eqn:F.
  - nb 16 m W L.
    destruct (andb _ _); simpl; [apply mwf3xW_set_bad; auto |].
    assert (HM: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    destruct (i_head (m_s m1)) eqn:HD; fin2 W1 HM.
  - cbv beta zeta. simpl.
    assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
    destruct (i_head (m_s m)) eqn:HD; fin2 W HM.
Qed.

Lemma DICT_ok : ok_TYPE -> ok_DICT.
Proof.
  intros T flush m W L M. unfold c_DICT.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_havedict (m_s m) =? 0).
  - simpl. unfold restore. fin2 W HM.
  - go (T flush) W HM.
Qed.

Lemma DICTID_ok : ok_TYPE -> ok_DICTID.
Proof.
  intros T flush m W L M. unfold c_DICTID. nb 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go (DICT_ok T flush) W1 HM1.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the header cases of Model2.v (c_FLAGS2 .. c_COMMENT2)                                           *)

Definition ok_NAME2 : Prop := ok_at NAME c_NAME2.
Definition ok_COMMENT2 : Prop := ok_at COMMENT c_COMMENT2.

(* FLAGS, TIME, OS start outside EXLEN / EXTRA and may stop in them *)
Definition okh_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3xW m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3hW (f m).
Definition ok_FLAGS2 : Prop := okh_at FLAGS c_FLAGS2.
Definition ok_TIME2 : Prop := okh_at TIME c_TIME2.
Definition ok_OS2 : Prop := okh_at OS c_OS2.
(* EXLEN starts with hdrW's bit buffer (fewer than 16 bits, nothing above them) *)
Definition ok_EXLEN2 : Prop :=
  forall m, mwf3hW m -> m_leave m = 0 -> m_mode m = EXLEN -> iout_ok mwf3hW (c_EXLEN2 m).
(* EXTRA needs its length bound only when the header has an extra field (else it skips to NAME) *)
Definition ok_EXTRA2 : Prop :=
  forall m, mwfxW m -> m_leave m = 0 -> m_mode m = EXTRA ->
    (Z.land (i_flags (m_s m)) 1024 <> 0 -> i_length (m_s m) <= Int.max_signed) -> iout_ok mwf3hW (c_EXTRA2 m).

Lemma mwf3hW_set_leave: forall m, mwf3hW m -> mwf3hW (set_leave m).
Proof.
  intros m [W X H]. constructor; [apply mwfW_set_leave; auto | apply xwf3_ext with m; auto | exact H].
Qed.

(* NEEDBITS(n) from fewer than n bits keeps the bit buffer free of bits above its count, ends with fewer than
   n + 8 bits, and with fewer than n bits when it runs out of input *)
Lemma needbits_f_ge: forall k n m, n <= m_bits m -> needbits_f k n m = m.
Proof. intros [|k] n m B; simpl; auto. destruct (Z.ltb_spec (m_bits m) n); [lia | auto]. Qed.

Lemma needbits_f_hb: forall k n m, mwfW m -> n <= 32 -> m_hold m < 2 ^ m_bits m -> m_bits m < n ->
  m_hold (needbits_f k n m) < 2 ^ m_bits (needbits_f k n m) /\ m_bits (needbits_f k n m) < n + 8 /\
  (m_leave (needbits_f k n m) = 1 -> m_leave m = 1 \/ m_bits (needbits_f k n m) < n).
Proof.
  induction k; intros n m W N H B; simpl.
  - split; [auto|]. split; [lia | auto].
  - destruct (Z.ltb_spec (m_bits m) n); [| lia].
    destruct (Z.eqb_spec (m_have m) 0).
    + simpl. split; [auto|]. split; [lia|]. intros _. right; auto.
    + pose proof (mwW_hold _ W) as HL. pose proof (mwW_bits _ W) as BR. pose proof (mwW_nx _ W) as NX.
      pose proof (proj2 (mwW_inp _ W)) as BY. unfold m_have in *. unfold lrange in HL.
      assert (Bb: 0 <= Znth (m_nx m) (m_inp m) <= 255).
      { assert (I: 0 <= m_nx m < Zlength (m_inp m)) by lia.
        pose proof (proj1 (Forall_Znth _ _) BY (m_nx m) I) as Z0. simpl in Z0. rep_lia. }
      assert (P0: 0 < 2 ^ m_bits m) by (apply Z.pow_pos_nonneg; lia).
      assert (P31: 2 ^ m_bits m <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
      assert (MB: Znth (m_nx m) (m_inp m) * 2 ^ m_bits m <= 255 * 2 ^ m_bits m)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hp: m_hold (pull m) = m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m).
      { unfold pull; simpl. unfold u64. rewrite Z.mod_small; [reflexivity|]. split; [nia|].
        change (2 ^ 31) with 2147483648 in P31. lia. }
      assert (Bp: m_bits (pull m) = m_bits m + 8) by (unfold pull; simpl; unfold u32; rewrite Z.mod_small; lia).
      assert (Wp: mwfW (pull m)) by (apply mwfW_pull; auto; lia).
      assert (Hq: m_hold (pull m) < 2 ^ m_bits (pull m)).
      { rewrite Hp, Bp, Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. }
      assert (Lp: m_leave (pull m) = m_leave m) by reflexivity.
      destruct (Z.ltb_spec (m_bits (pull m)) n).
      * destruct (IHk n (pull m) Wp N Hq H1) as (A1 & A2 & A3).
        split; [auto|]. split; [auto|]. intros LV. destruct (A3 LV) as [A|A]; [left; congruence | right; auto].
      * rewrite (needbits_f_ge k n (pull m)) by lia. split; [auto|]. split; [lia|]. intros LV. left; congruence.
Qed.

Lemma needbits_hb: forall n m, mwfW m -> n <= 32 -> m_hold m < 2 ^ m_bits m -> m_bits m < n ->
  m_hold (needbits n m) < 2 ^ m_bits (needbits n m) /\ m_bits (needbits n m) < n + 8 /\
  (m_leave (needbits n m) = 1 -> m_leave m = 1 \/ m_bits (needbits n m) < n).
Proof. intros. apply needbits_f_hb; auto. Qed.

Lemma COMMENT2_ok : ok_COMMENT2.
Proof.
  intros m W L M. unfold c_COMMENT2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3xW_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3W_w _ W) as W0. pose proof (mwW_h _ W0) as HW. pose proof (mwW_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (i_head (m_s m) && h_cp (m_h m))%bool
                  (h_cbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mwW_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mwW_nx _ W0); lia. }
    { pose proof (mwW_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_cbuf _ HW)). lia. }
    { apply (hw_cbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_comm_max _ HW). pose proof (hw_cbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3xW_set_leave. fin2 W HM.
    + go HCRC_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go HCRC_ok W HM.
Qed.

Lemma NAME2_ok : ok_NAME2.
Proof.
  intros m W L M. unfold c_NAME2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3xW_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3W_w _ W) as W0. pose proof (mwW_h _ W0) as HW. pose proof (mwW_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_name_max (m_h m)) (i_head (m_s m) && h_np (m_h m))%bool
                  (h_nbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mwW_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mwW_nx _ W0); lia. }
    { pose proof (mwW_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_nbuf _ HW)). lia. }
    { apply (hw_nbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_name_max _ HW). pose proof (hw_nbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3xW_set_leave. fin2 W HM.
    + go COMMENT2_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go COMMENT2_ok W HM.
Qed.

Lemma EXTRA2_ok : ok_EXTRA2.
Proof.
  intros m W L M XL. unfold c_EXTRA2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  assert (M': i_mode (m_s m) = EXTRA) by exact M.
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F; [| apply iout_xW_hW; go NAME2_ok W HM].
  assert (XL1: i_length (m_s m) <= Int.max_signed).
  { apply XL. intros E. rewrite E in F. discriminate. }
  clear XL.
  match goal with |- context [if negb (Z.min ?a ?b =? 0) then ?X else m] =>
    remember (if negb (Z.min a b =? 0) then X else m) as m2 eqn:E2 end.
  assert (W2: mwf3hW m2 /\ m_leave m2 = 0 /\ HEAD <= m_mode m2 <= TYPEDO).
  { subst m2. pose proof (mxW_w _ W) as W0. pose proof (mwW_h _ W0) as HW. pose proof (mwW_s _ W0) as SW.
    pose proof (mwW_nx _ W0) as NX. pose proof (sw_length _ SW) as LN. pose proof (hw_extra_max _ HW) as XM.
    pose proof (hw_xbuf _ HW) as XB. pose proof (proj1 (mwW_inp _ W0)) as IN. unfold m_have in *.
    unfold urange in *.
    remember (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)) as copy eqn:EC.
    assert (CP: 0 <= copy <= i_length (m_s m) /\ copy <= Zlength (m_inp m) - m_nx m) by (rewrite EC; lia).
    clear EC.
    destruct (negb (copy =? 0)).
    2:{ split; [| split; [auto | auto]]. constructor; [apply W | apply W |].
        split; intros HE; [exfalso; unfold m_mode in HE; rewrite M' in HE; unfold_modes; lia | intros _; exact XL1]. }
    remember (u32 (h_extra_len (m_h m) - i_length (m_s m))) as len eqn:EL.
    assert (LR: urange len) by (rewrite EL; apply u32_range). clear EL. unfold urange in LR.
    destruct (andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m))) eqn:C.
    + apply andb_prop in C; destruct C as [_ C]; apply Z.ltb_lt in C.
      remember (if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy)
        as n eqn:EN.
      (* the sum does not wrap: len < extra_max <= 65536 and copy <= the extra length <= 2^31 - 1 *)
      assert (NR: 0 <= n <= copy /\ len + n <= h_extra_max (m_h m)).
      { rewrite EN. unfold u32. rewrite (Z.mod_small (len + copy)) by rep_lia.
        destruct (Z.ltb_spec (h_extra_max (m_h m)) (len + copy)); lia. }
      clear EN.
      assert (IB: Zlength (inbytes m n) = n) by (unfold inbytes; rewrite Zlength_sublist; lia).
      destruct (put_bytes_ok (h_xbuf (m_h m)) len (inbytes m n)) as [PB1 PB2]; [lia | lia |].
      rewrite (proj1 XB) in PB1.
      specialize (PB2 (proj2 XB) (inbytes_bytes m n W0)).
      split.
      * fin2h W HM.
        all: intros HE; [exfalso; rewrite M' in HE; unfold_modes; lia | lia].
      * rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto.
    + split.
      * fin2h W HM.
        all: intros HE; [exfalso; rewrite M' in HE; unfold_modes; lia | lia].
      * rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto. }
  destruct W2 as (W2 & L2 & HM2).
  destruct (negb (i_length (m_s m2) =? 0)); [simpl; apply mwf3hW_set_leave; auto | apply iout_xW_hW; go NAME2_ok W2 HM2].
Qed.

Lemma EXLEN2_ok : ok_EXLEN2.
Proof.
  intros m W L M. unfold c_EXLEN2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F.
  - destruct (proj1 (m3H_h _ W) M) as [B0 H0].
    destruct (needbits_hb 16 m (m3H_w _ W) ltac:(lia) H0 B0) as (HB1 & BB1 & LB1).
    remember (needbits 16 m) as m1 eqn:E. cbv beta zeta.
    assert (S1: m_s m1 = m_s m) by (subst m1; apply needbits_s).
    assert (W1: mwfxW m1).
    { constructor; [subst m1; apply mwfW_needbits; [apply W | lia] | apply xwf3_ext with m; [symmetry; exact S1 | apply W]]. }
    destruct (Z.eqb_spec (m_leave m1) 1) as [LV|NL].
    + (* the input ran out: m1 is still in EXLEN, with fewer than 16 bits *)
      simpl. constructor; [apply W1 | apply W1 |]. split; intros HE.
      * split; [destruct (LB1 LV) as [A|A]; [rewrite L in A; discriminate | exact A] | exact HB1].
      * exfalso. unfold m_mode in HE, M. rewrite S1, M in HE. unfold_modes; lia.
    + destruct (needbits_ok 16 m (m3H_w _ W) L ltac:(lia) ltac:(subst m1; exact NL)) as [B1 L1].
      rewrite <- E in B1, L1.
      assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
      (* the length is the 16 to 23 bits of the bit buffer: below 2^23 *)
      assert (HV: 0 <= m_hold m1 < 8388608).
      { pose proof (mwW_hold _ (mxW_w _ W1)). unfold lrange in *. split; [lia|].
        change 8388608 with (2 ^ 23). apply Z.lt_le_trans with (2 ^ m_bits m1); [exact HB1 | apply Z.pow_le_mono_r; lia]. }
      clear E NL.
      apply EXTRA2_ok; [fin2x W1 HM1 | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity | ].
      intros _. rewrite ?crc_if_eq. simpl. split_ifs; simpl; unfold u32; rewrite Z.mod_small by lia; rep_lia.
  - cbv beta zeta. apply negb_false_iff, Z.eqb_eq in F.
    apply EXTRA2_ok; [fin2x W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity | ].
    split_ifs; simpl; intros FF; contradiction.
Qed.

Lemma OS2_ok : ok_OS2.
Proof.
  intros m W L M. unfold c_OS2. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  apply EXLEN2_ok; [| rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity].
  (* EXLEN starts with an empty bit buffer *)
  fin2h W1 HM1. all: intros _; simpl; lia.
Qed.

Lemma TIME2_ok : ok_TIME2.
Proof.
  intros m W L M. unfold c_TIME2. nb 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go OS2_ok W1 HM1.
Qed.

Lemma FLAGS2_ok : ok_FLAGS2.
Proof.
  intros m W L M. unfold c_FLAGS2. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  destruct (negb (Z.land (s32 (m_hold m1)) 255 =? 8)); [simpl; apply mwf3xW_hW, mwf3xW_set_bad; fin2 W1 HM1 |].
  destruct (negb (Z.land (s32 (m_hold m1)) 57344 =? 0)); [simpl; apply mwf3xW_hW, mwf3xW_set_bad; fin2 W1 HM1 |].
  go TIME2_ok W1 HM1.
Qed.

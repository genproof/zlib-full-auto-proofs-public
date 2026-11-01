(* The header cases of Model2.v (HEAD .. HCRC) with an application header whose buffers have any uInt size.

   Inv.v's mwf holds the header invariant hwf, which caps extra_max / name_max / comm_max at 65536.  [hwf8r] is
   hwf with these three bounds raised to Int.max_unsigned (RTH8Spec.hwf8 as a record), [mwf8] is mwf with hwf8r,
   and [mwf3x8] adds Step3Inv.v's xwf3 as mwf3x does.  The proofs of the header cases are those of Step3Header.v,
   Step5Header.v and Step5Mwf.v (HEAD2_ok) over mwf3x8; the facts of mwf that do not read the header are moved
   between mwf8 and mwf through any header with hwf ([mwf8_of_mwf], [mwf_of_mwf8]).

   Only the copy into the extra buffer (case EXTRA) needs more than the wider bounds: it tests
   `len + copy > extra_max` in 32 bits (len = extra_len - length, copy <= length), which wraps once extra_max may
   be close to 2^32.  [EXTRA8_ok] takes the fact that the sum does not wrap ([xsafe]) for a machine that starts in
   EXTRA; EXLEN gives it to the machine it hands to EXTRA (length = extra_len there). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate.Step5Header.
Require Import Zlib.proof.inflate.Steps2.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* the invariant                                                                                  *)

Record hwf8r (h: hstate) : Prop := {
  h8_text : srange (h_text h);
  h8_time : lrange (h_time h);
  h8_xflags : srange (h_xflags h);
  h8_os : srange (h_os h);
  h8_extra_len : urange (h_extra_len h);
  h8_extra_max : 0 <= h_extra_max h <= Int.max_unsigned;
  h8_name_max : 0 <= h_name_max h <= Int.max_unsigned;
  h8_comm_max : 0 <= h_comm_max h <= Int.max_unsigned;
  h8_xbuf : Zlength (h_xbuf h) = h_extra_max h /\ bytes_ok (h_xbuf h);
  h8_nbuf : Zlength (h_nbuf h) = h_name_max h /\ bytes_ok (h_nbuf h);
  h8_cbuf : Zlength (h_cbuf h) = h_comm_max h /\ bytes_ok (h_cbuf h);
  h8_hcrc : srange (h_hcrc h);
  h8_done : srange (h_done h) }.

Record mwf8 (m: mst) : Prop := {
  mw8_md : modewf (m_s m);
  mw8_s : swf (m_s m);
  mw8_h : hwf8r (m_h m);
  mw8_inp : Zlength (m_inp m) <= Int.max_signed /\ bytes_ok (m_inp m);
  mw8_aout : 0 <= m_aout m <= Int.max_signed;
  mw8_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mw8_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mw8_hold : lrange (m_hold m);
  mw8_bits : 0 <= m_bits m <= 39;
  mw8_in : m_in m = Zlength (m_inp m);
  mw8_out : urange (m_out m);
  mw8_ret : -5 <= m_ret m <= 2;
  mw8_leave : 0 <= m_leave m <= 1;
  mw8_adler : lrange (m_adler m);
  mw8_tin : lrange (m_tin m);
  mw8_tout : lrange (m_tout m);
  mw8_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mw8_sow : 0 <= m_sow m <= Zlength (m_ow m);
  mw8_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

Record mwf3x8 (m: mst) : Prop := { m8_w : mwf8 m; m8_x : xwf3 m }.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf8 and mwf: the same facts but the header's                                                  *)

Lemma mwf8_of_mwf: forall m h, mwf (set_m_h m h) -> hwf8r (m_h m) -> mwf8 m.
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma mwf_of_mwf8: forall m h, mwf8 m -> hwf h -> mwf (set_m_h m h).
Proof. intros m h W H. destruct W. constructor; cbn in *; auto. Qed.

Lemma m38_of: forall m h, mwf3x (set_m_h m h) -> hwf8r (m_h m) -> mwf3x8 m.
Proof.
  intros m h [W X] H. constructor; [apply mwf8_of_mwf with h; auto |].
  apply xwf3_ext with (set_m_h m h); [reflexivity | exact X].
Qed.

Lemma m38_to: forall m h, mwf3x8 m -> hwf h -> mwf3x (set_m_h m h).
Proof.
  intros m h [W X] H. constructor; [apply mwf_of_mwf8; auto |].
  apply xwf3_ext with m; [reflexivity | exact X].
Qed.

(* a header with hwf *)
Definition hzero : hstate := HS 0 0 0 0 false 0 0 [] false 0 [] false 0 [] 0 0.

Lemma hwf_hzero: hwf hzero.
Proof.
  constructor; cbn; unfold srange, lrange, urange; try rep_lia; split; try reflexivity; constructor.
Qed.

(* an update that does not read the header keeps the header-free facts *)
Lemma m38_lift: forall m m',
  (mwf3x (set_m_h m hzero) -> mwf3x (set_m_h m' hzero)) -> m_h m' = m_h m -> mwf3x8 m -> mwf3x8 m'.
Proof.
  intros m m' F E W. apply m38_of with hzero; [apply F; apply m38_to; auto; apply hwf_hzero |].
  rewrite E. apply (mw8_h _ (m8_w _ W)).
Qed.

Lemma needbits_f_set_h: forall k n m h, needbits_f k n (set_m_h m h) = set_m_h (needbits_f k n m) h.
Proof.
  induction k; intros n m h; [reflexivity |]. cbn [needbits_f].
  change (m_bits (set_m_h m h)) with (m_bits m). change (m_have (set_m_h m h)) with (m_have m).
  destruct (m_bits m <? n); [| reflexivity]. destruct (m_have m =? 0); [reflexivity |].
  change (pull (set_m_h m h)) with (set_m_h (pull m) h). apply IHk.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the kit of Step3Kit.v / Step3Header.v over mwf3x8                                              *)

Lemma mwf3x8_needbits: forall n m, mwf3x8 m -> n <= 32 -> mwf3x8 (needbits n m).
Proof.
  intros n m W N. apply m38_lift with m; [| apply needbits_f_h | exact W].
  intros W0. unfold needbits. rewrite <- needbits_f_set_h. apply mwf3x_needbits; auto.
Qed.

Lemma mwf3x8_set_leave: forall m, mwf3x8 m -> mwf3x8 (set_leave m).
Proof.
  intros m W. apply m38_lift with m; [| reflexivity | exact W].
  intros W0. exact (mwf3x_set_leave _ W0).
Qed.

Lemma mwf3x8_set_bad: forall m e, mwf3x8 m -> mwf3x8 (set_bad m e).
Proof.
  intros m e W. apply m38_lift with m; [| reflexivity | exact W].
  intros W0. exact (mwf3x_set_bad _ e W0).
Qed.

Lemma needbits_ok8: forall n m,
  mwf8 m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  n <= m_bits (needbits n m) /\ m_leave (needbits n m) = 0.
Proof. intros n m W L N E. apply needbits_f_ok; auto; try (destruct W; simpl; lia). Qed.

Lemma needbits_all8: forall n m, mwf3x8 m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  mwf3x8 (needbits n m) /\ m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m) /\
  m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof.
  intros n m W L N E. destruct (needbits_ok8 n m (m8_w _ W) L N E) as [B1 L1].
  split; [apply mwf3x8_needbits; auto |]. split; [auto |]. split; [auto |].
  split; [apply needbits_s | apply needbits_f_h].
Qed.

Lemma mwf3x8_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> hwf8r (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_signed /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_signed -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m -> mwf3x8 m.
Proof.
  intros m HM S H XW. intros. constructor.
  - constructor; auto. apply modewf_hdr; auto.
  - unfold m_mode in HM. unfold HEAD, TYPEDO in HM.
    constructor; auto; unfold m_mode, decode_mode;
    unfold LENEXT, DIST, DISTEXT, MATCH, LIT, LEN, LEN_; intros E; exfalso; lia.
Qed.

Lemma mwf3x8_out: forall m, mwf3x8 m -> HEAD <= m_mode m <= TYPEDO -> m_out m = m_aout m.
Proof.
  intros m W HM. destruct (mw8_outeq _ (m8_w _ W)) as [E | [E | [E | E]]]; auto;
  exfalso; rewrite E in HM; unfold HEAD, TYPEDO, LENGTH, DONE, BAD in *; lia.
Qed.

Lemma inbytes_bytes8: forall m n, mwf8 m -> is_bytes (inbytes m n).
Proof. intros m n W. unfold inbytes. apply Forall_sublist. apply (mw8_inp _ W). Qed.

Ltac hwf8_set := intros; match goal with H: hwf8r _ |- _ => destruct H end; constructor; simpl; auto.

Lemma hwf8_text: forall h v, hwf8r h -> srange v -> hwf8r (set_h_text h v). Proof. hwf8_set. Qed.
Lemma hwf8_time: forall h v, hwf8r h -> lrange v -> hwf8r (set_h_time h v). Proof. hwf8_set. Qed.
Lemma hwf8_xflags: forall h v, hwf8r h -> srange v -> hwf8r (set_h_xflags h v). Proof. hwf8_set. Qed.
Lemma hwf8_os: forall h v, hwf8r h -> srange v -> hwf8r (set_h_os h v). Proof. hwf8_set. Qed.
Lemma hwf8_extra_len: forall h v, hwf8r h -> urange v -> hwf8r (set_h_extra_len h v). Proof. hwf8_set. Qed.
Lemma hwf8_hcrc: forall h v, hwf8r h -> srange v -> hwf8r (set_h_hcrc h v). Proof. hwf8_set. Qed.
Lemma hwf8_done: forall h v, hwf8r h -> srange v -> hwf8r (set_h_done h v). Proof. hwf8_set. Qed.
Lemma hwf8_xp: forall h v, hwf8r h -> hwf8r (set_h_xp h v). Proof. hwf8_set. Qed.
Lemma hwf8_np: forall h v, hwf8r h -> hwf8r (set_h_np h v). Proof. hwf8_set. Qed.
Lemma hwf8_cp: forall h v, hwf8r h -> hwf8r (set_h_cp h v). Proof. hwf8_set. Qed.
Lemma hwf8_xbuf: forall h v, hwf8r h -> Zlength v = h_extra_max h -> bytes_ok v -> hwf8r (set_h_xbuf h v).
Proof. hwf8_set. Qed.
Lemma hwf8_nbuf: forall h v, hwf8r h -> Zlength v = h_name_max h -> bytes_ok v -> hwf8r (set_h_nbuf h v).
Proof. hwf8_set. Qed.
Lemma hwf8_cbuf: forall h v, hwf8r h -> Zlength v = h_comm_max h -> bytes_ok v -> hwf8r (set_h_cbuf h v).
Proof. hwf8_set. Qed.

(* the facts of a machine m1 in a header mode (Step3Header.v's base) *)
Ltac base8 W1 HM :=
  let O := fresh "O" in pose proof (mwf3x8_out _ W1 HM) as O;
  let X := fresh "X" in pose proof (x3_head _ (m8_x _ W1)) as X;
  let WB := fresh "WB" in pose proof (sw_wbits _ (mw8_s _ (m8_w _ W1))) as WB;
  let V := fresh "V" in pose proof (m8_w _ W1) as V; destruct V as [_ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  repeat match goal with H: _ /\ _ |- _ => destruct H end.

Ltac sw8 := repeat match goal with
  | |- swf (set_i_mode _ _) => apply swf_set_mode
  | |- swf (set_i_check _ _) => apply swf_check
  | |- swf (set_i_flags _ _) => apply swf_flags
  | |- swf (set_i_dmax _ _) => apply swf_dmax
  | |- swf (set_i_length _ _) => apply swf_length
  | |- swf (set_i_hold _ _) => apply swf_hold
  | |- swf (set_i_bits _ _) => apply swf_bits
  | |- swf (set_i_wbits _ _) => apply swf_wbits
  | |- hwf8r (set_h_text _ _) => apply hwf8_text
  | |- hwf8r (set_h_time _ _) => apply hwf8_time
  | |- hwf8r (set_h_xflags _ _) => apply hwf8_xflags
  | |- hwf8r (set_h_os _ _) => apply hwf8_os
  | |- hwf8r (set_h_extra_len _ _) => apply hwf8_extra_len
  | |- hwf8r (set_h_hcrc _ _) => apply hwf8_hcrc
  | |- hwf8r (set_h_done _ _) => apply hwf8_done
  | |- hwf8r (set_h_xp _ _) => apply hwf8_xp
  | |- hwf8r (set_h_np _ _) => apply hwf8_np
  | |- hwf8r (set_h_cp _ _) => apply hwf8_cp
  | |- hwf8r (set_h_xbuf _ _) => apply hwf8_xbuf
  | |- hwf8r (set_h_nbuf _ _) => apply hwf8_nbuf
  | |- hwf8r (set_h_cbuf _ _) => apply hwf8_cbuf
  end.

Ltac fin8 W1 HM :=
  rewrite ?crc_if_eq; apply mwf3x8_of; unfold m_mode; simpl; split_ifs; simpl; base8 W1 HM; sw8; try leaf.

Ltac nb8 n m W L :=
  let m1 := fresh "m1" in let E := fresh "E" in let NL := fresh "NL" in
  remember (needbits n m) as m1 eqn:E; cbv beta zeta;
  destruct (Z.eqb_spec (m_leave m1) 1) as [?|NL];
  [simpl; subst m1; apply mwf3x8_needbits; auto; lia |];
  let W1 := fresh "W1" in let L1 := fresh "L1" in let B1 := fresh "B1" in
  let S1 := fresh "S1" in let H1 := fresh "H1" in
  destruct (needbits_all8 n m W L ltac:(lia) ltac:(subst m1; exact NL)) as (W1 & L1 & B1 & S1 & H1);
  rewrite <- E in W1, L1, B1, S1, H1; clear E NL.

Ltac go8 OK W HM := apply OK; [fin8 W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity].

(* ---------------------------------------------------------------------------------------------- *)
(* the cases                                                                                     *)

Definition ok8_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3x8 m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3x8 (f m).

Lemma HCRC8_ok : ok8_at HCRC c_HCRC.
Proof.
  intros m W L M. unfold c_HCRC.
  destruct (negb (Z.land (i_flags (m_s m)) 512 =? 0)) eqn:F.
  - nb8 16 m W L.
    destruct (andb _ _); simpl; [apply mwf3x8_set_bad; auto |].
    assert (HM: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    destruct (i_head (m_s m1)) eqn:HD; fin8 W1 HM.
  - cbv beta zeta. simpl.
    assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
    destruct (i_head (m_s m)) eqn:HD; fin8 W HM.
Qed.

Lemma COMMENT8_ok : ok8_at COMMENT c_COMMENT2.
Proof.
  intros m W L M. unfold c_COMMENT2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x8_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m8_w _ W) as W0. pose proof (mw8_h _ W0) as HW. pose proof (mw8_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (i_head (m_s m) && h_cp (m_h m))%bool
                  (h_cbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw8_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw8_nx _ W0); lia. }
    { pose proof (mw8_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (h8_cbuf _ HW)). lia. }
    { apply (h8_cbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (h8_comm_max _ HW). pose proof (h8_cbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x8_set_leave. fin8 W HM.
    + go8 HCRC8_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go8 HCRC8_ok W HM.
Qed.

Lemma NAME8_ok : ok8_at NAME c_NAME2.
Proof.
  intros m W L M. unfold c_NAME2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x8_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m8_w _ W) as W0. pose proof (mw8_h _ W0) as HW. pose proof (mw8_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_name_max (m_h m)) (i_head (m_s m) && h_np (m_h m))%bool
                  (h_nbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw8_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw8_nx _ W0); lia. }
    { pose proof (mw8_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (h8_nbuf _ HW)). lia. }
    { apply (h8_nbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (h8_name_max _ HW). pose proof (h8_nbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x8_set_leave. fin8 W HM.
    + go8 COMMENT8_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go8 COMMENT8_ok W HM.
Qed.

(* the copy into the extra buffer: the 32-bit sum len + copy of case EXTRA does not wrap *)
Definition xsafe (m: mst) : Prop :=
  i_head (m_s m) = true -> h_xp (m_h m) = true ->
  u32 (h_extra_len (m_h m) - i_length (m_s m)) < h_extra_max (m_h m) ->
  u32 (h_extra_len (m_h m) - i_length (m_s m)) + Z.min (i_length (m_s m)) (m_have m) <= Int.max_unsigned.

Lemma EXTRA8_ok : forall m, mwf3x8 m -> m_leave m = 0 -> m_mode m = EXTRA ->
  (negb (Z.land (i_flags (m_s m)) 1024 =? 0) = true -> xsafe m) -> iout_ok mwf3x8 (c_EXTRA2 m).
Proof.
  intros m W L M XS. unfold c_EXTRA2. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F; [| go8 NAME8_ok W HM].
  specialize (XS eq_refl).
  match goal with |- context [if negb (Z.min ?a ?b =? 0) then ?X else m] =>
    remember (if negb (Z.min a b =? 0) then X else m) as m2 eqn:E2 end.
  assert (W2: mwf3x8 m2 /\ m_leave m2 = 0 /\ HEAD <= m_mode m2 <= TYPEDO).
  { subst m2. pose proof (m8_w _ W) as W0. pose proof (mw8_h _ W0) as HW. pose proof (mw8_s _ W0) as SW.
    pose proof (mw8_nx _ W0) as NX. pose proof (sw_length _ SW) as LN. pose proof (h8_extra_max _ HW) as XM.
    pose proof (h8_xbuf _ HW) as XB. pose proof (proj1 (mw8_inp _ W0)) as IN. unfold xsafe in XS. unfold m_have in *.
    unfold urange in *.
    remember (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)) as copy eqn:EC.
    assert (CP: 0 <= copy <= i_length (m_s m) /\ copy <= Zlength (m_inp m) - m_nx m) by (rewrite EC; lia).
    clear EC.
    destruct (negb (copy =? 0)); [| split; [auto | split; [auto | auto]]].
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
      specialize (PB2 (proj2 XB) (inbytes_bytes8 m n W0)).
      split; [fin8 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto.
    + split; [fin8 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto. }
  destruct W2 as (W2 & L2 & HM2).
  destruct (negb (i_length (m_s m2) =? 0)); [simpl; apply mwf3x8_set_leave; auto | go8 NAME8_ok W2 HM2].
Qed.

Lemma EXLEN8_ok : ok8_at EXLEN c_EXLEN2.
Proof.
  intros m W L M. unfold c_EXLEN2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F.
  - nb8 16 m W L.
    assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    apply EXTRA8_ok; [fin8 W1 HM1 | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity |].
    (* EXTRA starts with length = extra_len: len = 0 *)
    intros _. unfold xsafe. rewrite ?crc_if_eq. cbn.
    destruct (i_head (m_s m1)) eqn:HD; cbn; intros; try congruence.
    rewrite Z.sub_diag. pose proof (u32_range (m_hold m1)). unfold urange in *. change (u32 0) with 0. rep_lia.
  - cbv beta zeta. apply EXTRA8_ok; [fin8 W HM | rewrite ?crc_if_eq; simpl; split_ifs; simpl; assumption | reflexivity |].
    intros E. exfalso. revert E. rewrite ?crc_if_eq. cbn. destruct (i_head (m_s m)); cbn; rewrite F; discriminate.
Qed.

Lemma OS8_ok : ok8_at OS c_OS2.
Proof.
  intros m W L M. unfold c_OS2. nb8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go8 EXLEN8_ok W1 HM1.
Qed.

Lemma TIME8_ok : ok8_at TIME c_TIME2.
Proof.
  intros m W L M. unfold c_TIME2. nb8 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go8 OS8_ok W1 HM1.
Qed.

Lemma FLAGS8_ok : ok8_at FLAGS c_FLAGS2.
Proof.
  intros m W L M. unfold c_FLAGS2. nb8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  destruct (negb (Z.land (s32 (m_hold m1)) 255 =? 8)); [simpl; apply mwf3x8_set_bad; fin8 W1 HM1 |].
  destruct (negb (Z.land (s32 (m_hold m1)) 57344 =? 0)); [simpl; apply mwf3x8_set_bad; fin8 W1 HM1 |].
  go8 TIME8_ok W1 HM1.
Qed.

(* case HEAD with patch F7 (Step5Mwf.HEAD2_ok) *)
Lemma HEAD8_ok : ok8_at HEAD c_HEAD2.
Proof.
  intros m W L M. unfold c_HEAD2.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_wrap (m_s m) =? 0) eqn:WR; [simpl; fin8 W HM |].
  nb8 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  assert (XW0: i_wbits (m_s m1) = 0 -> i_wsize (m_s m1) = 0).
  { intros Z0. apply (x3_head _ (m8_x _ W1)); [unfold m_mode; rewrite S1; exact M | exact Z0 |].
    rewrite S1. apply Z.eqb_neq. exact WR. }
  destruct (andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)) eqn:GZ.
  { simpl. fin8 W1 HM1. }
  destruct (i_head (m_s m1)) eqn:HD; simpl.
  all: destruct (orb _ _); [simpl; apply mwf3x8_set_bad; fin8 W1 HM1 |].
  all: destruct (negb (m_hold m1 mod 16 =? 8)); [simpl; apply mwf3x8_set_bad; fin8 W1 HM1 |].
  all: remember (Z.shiftr (m_hold m1) 4 mod 16 + 8) as len eqn:EL.
  all: assert (LN: 8 <= len <= 23)
         by (rewrite EL; pose proof (Z.mod_pos_bound (Z.shiftr (m_hold m1) 4) 16); lia).
  all: clear EL.
  all: destruct (orb _ _) eqn:C; [simpl; apply mwf3x8_set_bad; fin8 W1 HM1 |].
  all: apply orb_false_iff in C; destruct C as [C1 C2]; apply Z.ltb_ge in C1.
  all: assert (C3: len <= (if i_wbits (m_s m1) =? 0 then len else i_wbits (m_s m1)))
         by (destruct (Z.eqb_spec (i_wbits (m_s m1)) 0); [lia |];
             cbn [negb andb] in C2; apply Z.ltb_ge in C2; exact C2).
  all: clear C2.
  all: assert (P: 0 <= 2 ^ len <= 32768)
         by (split; [apply Z.pow_nonneg; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]).
  all: destruct (Z.land (Z.shiftr (m_hold m1) 4) 512 =? 0); simpl; fin8 W1 HM1.
Qed.

(* one pass of the switch from a header mode keeps mwf3x8; a machine that starts in EXTRA with the extra field
   to read needs xsafe *)
Lemma stepf2_hdr8 : forall flush m, mwf3x8 m -> m_leave m = 0 -> HEAD <= m_mode m <= HCRC ->
  (m_mode m = EXTRA -> negb (Z.land (i_flags (m_s m)) 1024 =? 0) = true -> xsafe m) ->
  iout_ok mwf3x8 (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros flush m W L HM XS.
  assert (E: m_mode m = HEAD \/ m_mode m = FLAGS \/ m_mode m = TIME \/ m_mode m = OS \/ m_mode m = EXLEN \/
             m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT \/ m_mode m = HCRC)
    by (unfold_modes; unfold NAME, COMMENT, HCRC, FLAGS, TIME, OS, EXLEN, EXTRA in *; lia).
  destruct E as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]].
  - rewrite (stepf2_HEAD _ _ _ _ E). apply HEAD8_ok; auto.
  - rewrite (stepf2_FLAGS _ _ _ _ E). apply FLAGS8_ok; auto.
  - rewrite (stepf2_TIME _ _ _ _ E). apply TIME8_ok; auto.
  - rewrite (stepf2_OS _ _ _ _ E). apply OS8_ok; auto.
  - rewrite (stepf2_EXLEN _ _ _ _ E). apply EXLEN8_ok; auto.
  - rewrite (stepf2_EXTRA _ _ _ _ E). apply EXTRA8_ok; auto.
  - rewrite (stepf2_NAME _ _ _ _ E). apply NAME8_ok; auto.
  - rewrite (stepf2_COMMENT _ _ _ _ E). apply COMMENT8_ok; auto.
  - rewrite (stepf2_HCRC _ _ _ _ E). apply HCRC8_ok; auto.
Qed.

(* The header cases HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT preserve
   mwf3x (ICStep3Stmts.v).  DICT / DICTID fall into TYPE (hypothesis ok_TYPE, proved in ICStep3Block.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_codes.ICStep3Stmts.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.crc32.Combine.

(* ---------------------------------------------------------------------------------------------- *)
(* arithmetic                                                                                    *)

Lemma land_range: forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b H. split.
  - apply Z.land_nonneg; auto.
  - apply Zbits.Ztestbit_le; auto. intros i _ T. rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma s32_range: forall x, srange (s32 x).
Proof.
  intros x. unfold s32, srange. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)).
  destruct (Z.ltb_spec (x mod 2^32) (2^31)); rep_lia.
Qed.

Lemma u32_range: forall x, urange (u32 x).
Proof. intros x. unfold u32, urange. pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). rep_lia. Qed.

Lemma u64_range: forall x, lrange (u64 x).
Proof. intros x. unfold u64, lrange. pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). rep_lia. Qed.

Lemma swap32_range: forall q, 0 <= q -> lrange (swap32 q).
Proof.
  intros q H. unfold swap32, lrange.
  rewrite !Z.shiftl_mul_pow2 by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr q 24) 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound q 256 ltac:(lia)).
  pose proof (land_range (Z.shiftr q 8) 65280 ltac:(lia)).
  pose proof (land_range q 65280 ltac:(lia)).
  rep_lia.
Qed.

Lemma byte_mod: forall x, 0 <= x mod 256 <= Byte.max_unsigned.
Proof. intros x. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). rep_lia. Qed.

Lemma hbytes2_bytes: forall h, is_bytes (hbytes2 h).
Proof. intros h. unfold hbytes2. repeat constructor; apply byte_mod. Qed.

Lemma hbytes4_bytes: forall h, is_bytes (hbytes4 h).
Proof. intros h. unfold hbytes4. repeat constructor; apply byte_mod. Qed.

Lemma inbytes_bytes: forall m n, mwf m -> is_bytes (inbytes m n).
Proof. intros m n W. unfold inbytes. apply Forall_sublist. apply (mw_inp _ W). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the setters of the state and of the header                                                    *)

Ltac swf_set := intros; match goal with H: swf _ |- _ => destruct H end; constructor; simpl; auto.

Lemma swf_check: forall s v, swf s -> lrange v -> swf (set_i_check s v). Proof. swf_set. Qed.
Lemma swf_flags: forall s v, swf s -> srange v -> swf (set_i_flags s v). Proof. swf_set. Qed.
Lemma swf_dmax: forall s v, swf s -> urange v -> swf (set_i_dmax s v). Proof. swf_set. Qed.
Lemma swf_length: forall s v, swf s -> urange v -> swf (set_i_length s v). Proof. swf_set. Qed.
Lemma swf_hold: forall s v, swf s -> lrange v -> swf (set_i_hold s v). Proof. swf_set. Qed.
Lemma swf_bits: forall s v, swf s -> 0 <= v <= 39 -> swf (set_i_bits s v). Proof. swf_set. Qed.
Lemma swf_wbits: forall s v, swf s -> 0 <= v <= 23 -> (i_wsize s = 0 \/ v = i_wbits s) ->
  swf (set_i_wbits s v).
Proof.
  intros s v S R C. destruct S; constructor; simpl; auto.
  destruct C as [C | C]; [left; auto | subst; auto].
Qed.

Ltac hwf_set := intros; match goal with H: hwf _ |- _ => destruct H end; constructor; simpl; auto.

Lemma hwf_text: forall h v, hwf h -> srange v -> hwf (set_h_text h v). Proof. hwf_set. Qed.
Lemma hwf_time: forall h v, hwf h -> lrange v -> hwf (set_h_time h v). Proof. hwf_set. Qed.
Lemma hwf_xflags: forall h v, hwf h -> srange v -> hwf (set_h_xflags h v). Proof. hwf_set. Qed.
Lemma hwf_os: forall h v, hwf h -> srange v -> hwf (set_h_os h v). Proof. hwf_set. Qed.
Lemma hwf_extra_len: forall h v, hwf h -> urange v -> hwf (set_h_extra_len h v). Proof. hwf_set. Qed.
Lemma hwf_hcrc: forall h v, hwf h -> srange v -> hwf (set_h_hcrc h v). Proof. hwf_set. Qed.
Lemma hwf_done: forall h v, hwf h -> srange v -> hwf (set_h_done h v). Proof. hwf_set. Qed.
Lemma hwf_xp: forall h v, hwf h -> hwf (set_h_xp h v). Proof. hwf_set. Qed.
Lemma hwf_np: forall h v, hwf h -> hwf (set_h_np h v). Proof. hwf_set. Qed.
Lemma hwf_cp: forall h v, hwf h -> hwf (set_h_cp h v). Proof. hwf_set. Qed.
Lemma hwf_xbuf: forall h v, hwf h -> Zlength v = h_extra_max h -> bytes_ok v -> hwf (set_h_xbuf h v).
Proof. hwf_set. Qed.
Lemma hwf_nbuf: forall h v, hwf h -> Zlength v = h_name_max h -> bytes_ok v -> hwf (set_h_nbuf h v).
Proof. hwf_set. Qed.
Lemma hwf_cbuf: forall h v, hwf h -> Zlength v = h_comm_max h -> bytes_ok v -> hwf (set_h_cbuf h v).
Proof. hwf_set. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* mwf3x in the header modes                                                                       *)

Lemma modewf_hdr: forall s, HEAD <= i_mode s <= TYPEDO -> modewf s.
Proof.
  intros s H. unfold HEAD, TYPEDO in H.
  constructor; repeat match goal with |- _ /\ _ => split end; unfold decode_mode; intros E;
  unfold LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in E; exfalso; lia.
Qed.

Lemma mwf3x_of: forall m,
  HEAD <= m_mode m <= TYPEDO -> swf (m_s m) -> hwf (m_h m) ->
  (m_mode m = HEAD -> i_wbits (m_s m) = 0 -> i_wrap (m_s m) <> 0 -> i_wsize (m_s m) = 0 /\ i_win (m_s m) = false) ->
  Zlength (m_inp m) <= Int.max_signed /\ bytes_ok (m_inp m) ->
  0 <= m_aout m <= Int.max_signed -> 0 <= m_nx m <= Zlength (m_inp m) ->
  Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m) -> lrange (m_hold m) -> 0 <= m_bits m <= 39 ->
  m_in m = Zlength (m_inp m) -> urange (m_out m) -> -5 <= m_ret m <= 2 -> 0 <= m_leave m <= 1 ->
  lrange (m_adler m) -> lrange (m_tin m) -> lrange (m_tout m) -> 0 <= m_snx m <= Zlength (m_inp m) ->
  0 <= m_sow m <= Zlength (m_ow m) -> m_out m = m_aout m -> mwf3x m.
Proof.
  intros m HM S H XW. intros. constructor.
  - constructor; auto. apply modewf_hdr; auto.
  - unfold m_mode in HM. unfold HEAD, TYPEDO in HM.
    constructor; auto; unfold m_mode, decode_mode;
    unfold LENEXT, DIST, DISTEXT, MATCH, LIT, LEN, LEN_; intros E; exfalso; lia.
Qed.

Lemma mwf3x_out: forall m, mwf3x m -> HEAD <= m_mode m <= TYPEDO -> m_out m = m_aout m.
Proof.
  intros m W HM. apply mwf_out_eq; [apply W | ..]; unfold HEAD, TYPEDO, LENGTH, DONE, BAD in *; lia.
Qed.

(* crc_if only changes the check *)
Definition crc_val (s: istate) (data: list Z) : Z :=
  if andb (negb (Z.land (i_flags s) 512 =? 0)) (negb (Z.land (i_wrap s) 4 =? 0))
  then ref_crc32 (i_check s) data else i_check s.
Arguments crc_val : simpl never.

Lemma crc_if_eq: forall m d, crc_if m d = set_m_s m (set_i_check (m_s m) (crc_val (m_s m) d)).
Proof.
  intros m d. unfold crc_if, crc_val, upd_s.
  destruct (andb _ _); [reflexivity |]. destruct m as [s]; destruct s; reflexivity.
Qed.

Lemma crc_val_range: forall s d, swf s -> is_bytes d -> lrange (crc_val s d).
Proof.
  intros s d W B. unfold crc_val. destruct (andb _ _).
  - pose proof (ref_crc32_range (i_check s) d B). unfold is32 in *. unfold lrange. rep_lia.
  - apply (sw_check _ W).
Qed.

Lemma ref_crc32_lrange: forall c d, is_bytes d -> lrange (ref_crc32 c d).
Proof. intros c d B. pose proof (ref_crc32_range c d B). unfold is32 in *. unfold lrange. rep_lia. Qed.

Lemma needbits_f_h: forall k n m, m_h (needbits_f k n m) = m_h m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma ok_needbits: forall n m (P: mst -> iout),
  mwf3x m -> m_leave m = 0 -> n <= 32 ->
  (forall m1, mwf3x m1 -> m_leave m1 = 0 -> n <= m_bits m1 -> m_s m1 = m_s m -> m_h m1 = m_h m ->
     iout_ok mwf3x (P m1)) ->
  iout_ok mwf3x (let m1 := needbits n m in if m_leave m1 =? 1 then IBrk m1 else P m1).
Proof.
  intros n m P W L N K. cbv zeta.
  pose proof (mwf3x_needbits n m W N) as W1.
  destruct (Z.eqb_spec (m_leave (needbits n m)) 1) as [E | E]; [exact W1 |].
  destruct (needbits_ok n m (m3_w _ W) L N E) as [B1 L1].
  apply K; auto. apply needbits_s. apply needbits_f_h.
Qed.


Lemma needbits_all: forall n m, mwf3x m -> m_leave m = 0 -> n <= 32 -> m_leave (needbits n m) <> 1 ->
  mwf3x (needbits n m) /\ m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m) /\
  m_s (needbits n m) = m_s m /\ m_h (needbits n m) = m_h m.
Proof.
  intros n m W L N E. destruct (needbits_ok n m (m3_w _ W) L N E) as [B1 L1].
  split; [apply mwf3x_needbits; auto |]. split; [auto |]. split; [auto |].
  split; [apply needbits_s | apply needbits_f_h].
Qed.

Lemma mwf3x_set_bad: forall m e, mwf3x m -> mwf3x (set_bad m e).
Proof.
  intros m e W. unfold set_bad. apply mwf3x_set_mode_plain.
  - apply mwf3x_intro with m; [| apply W | reflexivity]. destruct (m3_w _ W); constructor; simpl; auto.
  - unfold HEAD, BAD, SYNC; lia.
  - unfold BAD, LENLENS; lia.
  - unfold BAD, CODELENS; lia.
  - unfold decode_mode, BAD, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia.
  - auto.
Qed.


Ltac unfold_modes := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT, Model.TYPE,
  TYPEDO, SYNC, BAD in *.

(* the facts of a machine m1 in a header mode *)
Ltac base W1 HM :=
  let O := fresh "O" in pose proof (mwf3x_out _ W1 HM) as O;
  let X := fresh "X" in pose proof (x3_head _ (m3_x _ W1)) as X;
  let WB := fresh "WB" in pose proof (sw_wbits _ (mw_s _ (m3_w _ W1))) as WB;
  let V := fresh "V" in pose proof (m3_w _ W1) as V; destruct V as [_ ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?];
  repeat match goal with H: _ /\ _ |- _ => destruct H end.

Ltac sw := repeat match goal with
  | |- swf (set_i_mode _ _) => apply swf_set_mode
  | |- swf (set_i_check _ _) => apply swf_check
  | |- swf (set_i_flags _ _) => apply swf_flags
  | |- swf (set_i_dmax _ _) => apply swf_dmax
  | |- swf (set_i_length _ _) => apply swf_length
  | |- swf (set_i_hold _ _) => apply swf_hold
  | |- swf (set_i_bits _ _) => apply swf_bits
  | |- swf (set_i_wbits _ _) => apply swf_wbits
  | |- hwf (set_h_text _ _) => apply hwf_text
  | |- hwf (set_h_time _ _) => apply hwf_time
  | |- hwf (set_h_xflags _ _) => apply hwf_xflags
  | |- hwf (set_h_os _ _) => apply hwf_os
  | |- hwf (set_h_extra_len _ _) => apply hwf_extra_len
  | |- hwf (set_h_hcrc _ _) => apply hwf_hcrc
  | |- hwf (set_h_done _ _) => apply hwf_done
  | |- hwf (set_h_xp _ _) => apply hwf_xp
  | |- hwf (set_h_np _ _) => apply hwf_np
  | |- hwf (set_h_cp _ _) => apply hwf_cp
  | |- hwf (set_h_xbuf _ _) => apply hwf_xbuf
  | |- hwf (set_h_nbuf _ _) => apply hwf_nbuf
  | |- hwf (set_h_cbuf _ _) => apply hwf_cbuf
  end.

Ltac cl := repeat match goal with H: _ |- _ => clear H end.

Ltac leaf := first [ assumption | reflexivity | (split; assumption)
  | apply u32_range | apply u64_range | apply s32_range
  | (apply swap32_range; unfold lrange in *; lia)
  | (apply ref_crc32_lrange; first [apply hbytes2_bytes | apply hbytes4_bytes])
  | (apply crc_val_range; [sw; leaf | first [apply hbytes2_bytes | apply hbytes4_bytes
                                              | apply Forall_sublist; assumption]])
  | (left; solve [auto]) | (intros ?HH; exfalso; revert HH; cl; unfold_modes; lia)
  | (apply Zshiftr_range; [assumption | lia])
  | (unfold u32; rewrite Z.mod_small by lia; lia) | (right; reflexivity) | (intros ?; discriminate)
  | (match goal with |- 0 <= Zlength ?l <= _ => pose proof (Zlength_nonneg l); lia end)
  | (cl; unfold lrange, urange, srange; unfold_modes; rep_lia)
  | (match goal with |- context [Z.land ?a ?b] =>
       let P := fresh in pose proof (land_range a b ltac:(lia)) as P; revert P; cl; intros P end;
     unfold lrange, urange, srange; rep_lia)
  | (unfold lrange, urange, srange in *; unfold_modes; rep_lia) ].

(* mwf3x of a machine built from m1 by the setters *)
Ltac split_ifs := repeat match goal with
  | |- context [if i_head ?x then _ else _] => destruct (i_head x)
  | |- context [if i_wbits ?x =? 0 then _ else _] => destruct (Z.eqb_spec (i_wbits x) 0)
  end.

Ltac fin2 W1 HM := rewrite ?crc_if_eq; apply mwf3x_of; unfold m_mode; simpl; split_ifs; simpl; base W1 HM; sw; try leaf.


(* NEEDBITS(n) at the head of a case: the leave branch, then the facts of the result *)
Ltac nb n m W L :=
  let m1 := fresh "m1" in let E := fresh "E" in let NL := fresh "NL" in
  remember (needbits n m) as m1 eqn:E; cbv beta zeta;
  destruct (Z.eqb_spec (m_leave m1) 1) as [?|NL];
  [simpl; subst m1; apply mwf3x_needbits; auto; lia |];
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
    destruct (andb _ _); simpl; [apply mwf3x_set_bad; auto |].
    assert (HM: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    destruct (i_head (m_s m1)) eqn:HD; fin2 W1 HM.
  - cbv beta zeta. simpl.
    assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
    destruct (i_head (m_s m)) eqn:HD; fin2 W HM.
Qed.

(* the do-while of NAME / COMMENT *)
Lemma zstr_f_ok: forall k bytes have length max wr buf copy,
  is_bytes bytes -> have <= Zlength bytes -> 0 <= copy < have -> 0 <= length -> max <= Zlength buf ->
  bytes_ok buf ->
  let '(c, b, ln, buf') := zstr_f k bytes have length max wr buf copy in
  0 <= c <= have /\ length <= ln <= Z.max length max /\ Zlength buf' = Zlength buf /\ bytes_ok buf'.
Proof.
  induction k; intros bytes have length max wr buf copy B HB C L M BO; simpl.
  - split; [lia |]. split; [lia |]. auto.
  - assert (BY: 0 <= Znth copy bytes <= Byte.max_unsigned).
    { apply (Forall_Znth bytes (fun b => 0 <= b <= Byte.max_unsigned)); auto. lia. }
    destruct (andb wr (length <? max)) eqn:WR.
    + apply andb_prop in WR. destruct WR as [_ WR]. apply Z.ltb_lt in WR.
      assert (ZL: Zlength (upd_Znth length buf (Znth copy bytes)) = Zlength buf)
        by (apply upd_Znth_Zlength; lia).
      assert (BO': bytes_ok (upd_Znth length buf (Znth copy bytes))) by (apply Forall_upd_Znth; auto).
      destruct (andb (negb (Znth copy bytes =? 0)) (copy + 1 <? have)) eqn:NX.
      * apply andb_prop in NX. destruct NX as [_ NX]. apply Z.ltb_lt in NX.
        specialize (IHk bytes have (length + 1) max wr (upd_Znth length buf (Znth copy bytes)) (copy + 1)
                    B HB ltac:(lia) ltac:(lia) ltac:(rewrite ZL; lia) BO').
        destruct (zstr_f k _ _ _ _ _ _ _) as [[[c b] ln] buf']. destruct IHk as (I1 & I2 & I3 & I4).
        split; [lia |]. split; [lia |]. split; [congruence | auto].
      * split; [lia |]. split; [lia |]. auto.
    + destruct (andb (negb (Znth copy bytes =? 0)) (copy + 1 <? have)) eqn:NX.
      * apply andb_prop in NX. destruct NX as [_ NX]. apply Z.ltb_lt in NX.
        specialize (IHk bytes have length max wr buf (copy + 1) B HB ltac:(lia) L M BO).
        destruct (zstr_f k _ _ _ _ _ _ _) as [[[c b] ln] buf']. destruct IHk as (I1 & I2 & I3 & I4).
        split; [lia |]. split; [lia |]. auto.
      * split; [lia |]. split; [lia |]. auto.
Qed.

Lemma COMMENT_ok : ok_COMMENT.
Proof.
  intros m W L M. unfold c_COMMENT. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_comm_max (m_h m)) (i_head (m_s m) && h_cp (m_h m))%bool
                  (h_cbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw_nx _ W0); lia. }
    { pose proof (mw_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_cbuf _ HW)). lia. }
    { apply (hw_cbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_comm_max _ HW). pose proof (hw_cbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x_set_leave. fin2 W HM.
    + go HCRC_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go HCRC_ok W HM.
Qed.

Lemma NAME_ok : ok_NAME.
Proof.
  intros m W L M. unfold c_NAME. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)) eqn:F.
  - destruct (m_have m =? 0) eqn:HV; [simpl; apply mwf3x_set_leave; auto |].
    apply Z.eqb_neq in HV.
    pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (zstr_f_ok (Z.to_nat (m_have m)) (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m))
                  (m_have m) (i_length (m_s m)) (h_name_max (m_h m)) (i_head (m_s m) && h_np (m_h m))%bool
                  (h_nbuf (m_h m)) 0) as ZS.
    unfold m_have in *.
    destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] buf] eqn:ZE.
    destruct ZS as (Z1 & Z2 & Z3 & Z4).
    { apply Forall_sublist. apply (mw_inp _ W0). }
    { rewrite Zlength_sublist; pose proof (mw_nx _ W0); lia. }
    { pose proof (mw_nx _ W0); lia. }
    { apply (sw_length _ SW). }
    { rewrite (proj1 (hw_nbuf _ HW)). lia. }
    { apply (hw_nbuf _ HW). }
    pose proof (sw_length _ SW). pose proof (hw_name_max _ HW). pose proof (hw_nbuf _ HW).
    unfold urange in *. clear ZE F HV.
    destruct (negb (b =? 0)).
    + simpl. apply mwf3x_set_leave. fin2 W HM.
    + go COMMENT_ok W HM.
  - destruct (i_head (m_s m)) eqn:HD; go COMMENT_ok W HM.
Qed.

Lemma put_bytes_ok: forall buf pos bytes, 0 <= pos -> pos + Zlength bytes <= Zlength buf ->
  Zlength (put_bytes buf pos bytes) = Zlength buf /\
  (bytes_ok buf -> is_bytes bytes -> bytes_ok (put_bytes buf pos bytes)).
Proof.
  intros buf pos bytes P Q. pose proof (Zlength_nonneg bytes). unfold put_bytes. split.
  - rewrite !Zlength_app, !Zlength_sublist by lia. lia.
  - intros B C. apply Forall_app; split; [apply Forall_sublist; auto |].
    apply Forall_app; split; [auto | apply Forall_sublist; auto].
Qed.

Lemma EXTRA_ok : ok_EXTRA.
Proof.
  intros m W L M. unfold c_EXTRA. cbv beta zeta.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F; [| go NAME_ok W HM].
  match goal with |- context [if negb (Z.min ?a ?b =? 0) then ?X else m] =>
    remember (if negb (Z.min a b =? 0) then X else m) as m2 eqn:E2 end.
  assert (W2: mwf3x m2 /\ m_leave m2 = 0 /\ HEAD <= m_mode m2 <= TYPEDO).
  { subst m2. pose proof (m3_w _ W) as W0. pose proof (mw_h _ W0) as HW. pose proof (mw_s _ W0) as SW.
    pose proof (mw_nx _ W0) as NX. pose proof (sw_length _ SW) as LN. pose proof (hw_extra_max _ HW) as XM.
    pose proof (hw_xbuf _ HW) as XB. pose proof (proj1 (mw_inp _ W0)) as IN. unfold m_have in *.
    unfold urange in *.
    remember (Z.min (i_length (m_s m)) (Zlength (m_inp m) - m_nx m)) as copy eqn:EC.
    assert (CP: 0 <= copy <= i_length (m_s m) /\ copy <= Zlength (m_inp m) - m_nx m) by (rewrite EC; lia).
    clear EC.
    destruct (negb (copy =? 0)); [| split; [auto | split; [auto | auto]]].
    remember (u32 (h_extra_len (m_h m) - i_length (m_s m))) as len eqn:EL.
    assert (LR: urange len) by (rewrite EL; apply u32_range). clear EL. unfold urange in LR.
    destruct (andb (andb (i_head (m_s m)) (h_xp (m_h m))) (len <? h_extra_max (m_h m))) eqn:C.
    + apply andb_prop in C; destruct C as [_ C]; apply Z.ltb_lt in C.
      remember (if h_extra_max (m_h m) <? u32 (len + copy) then h_extra_max (m_h m) - len else copy)
        as n eqn:EN.
      assert (NR: 0 <= n <= copy /\ len + n <= h_extra_max (m_h m)).
      { rewrite EN. unfold u32. rewrite (Z.mod_small (len + copy)) by rep_lia.
        destruct (Z.ltb_spec (h_extra_max (m_h m)) (len + copy)); lia. }
      clear EN.
      assert (IB: Zlength (inbytes m n) = n) by (unfold inbytes; rewrite Zlength_sublist; lia).
      destruct (put_bytes_ok (h_xbuf (m_h m)) len (inbytes m n)) as [PB1 PB2]; [lia | lia |].
      rewrite (proj1 XB) in PB1.
      specialize (PB2 (proj2 XB) (inbytes_bytes m n W0)).
      split; [fin2 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto.
    + split; [fin2 W HM |]. rewrite crc_if_eq. simpl. split; [auto |]. unfold m_mode in HM. auto. }
  destruct W2 as (W2 & L2 & HM2).
  destruct (negb (i_length (m_s m2) =? 0)); [simpl; apply mwf3x_set_leave; auto | go NAME_ok W2 HM2].
Qed.

Lemma EXLEN_ok : ok_EXLEN.
Proof.
  intros m W L M. unfold c_EXLEN.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)) eqn:F.
  - nb 16 m W L.
    assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
    go EXTRA_ok W1 HM1.
  - cbv beta zeta. go EXTRA_ok W HM.
Qed.

Lemma OS_ok : ok_OS.
Proof.
  intros m W L M. unfold c_OS. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go EXLEN_ok W1 HM1.
Qed.

Lemma TIME_ok : ok_TIME.
Proof.
  intros m W L M. unfold c_TIME. nb 32 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  go OS_ok W1 HM1.
Qed.

Lemma FLAGS_ok : ok_FLAGS.
Proof.
  intros m W L M. unfold c_FLAGS. nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  destruct (negb (Z.land (s32 (m_hold m1)) 255 =? 8)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  destruct (negb (Z.land (s32 (m_hold m1)) 57344 =? 0)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  go TIME_ok W1 HM1.
Qed.

Lemma HEAD_ok : ok_HEAD.
Proof.
  intros m W L M. unfold c_HEAD.
  assert (HM: HEAD <= m_mode m <= TYPEDO) by (rewrite M; unfold_modes; lia).
  destruct (i_wrap (m_s m) =? 0) eqn:WR; [simpl; fin2 W HM |].
  nb 16 m W L.
  assert (HM1: HEAD <= m_mode m1 <= TYPEDO) by (unfold m_mode in *; rewrite S1, M; unfold_modes; lia).
  (* s3_head: in HEAD with a wrapper, wbits = 0 only without a window *)
  assert (XW0: i_wbits (m_s m1) = 0 -> i_wsize (m_s m1) = 0).
  { intros Z0. apply (x3_head _ (m3_x _ W1)); [unfold m_mode; rewrite S1; exact M | exact Z0 |].
    rewrite S1. apply Z.eqb_neq. exact WR. }
  destruct (andb (negb (Z.land (i_wrap (m_s m1)) 2 =? 0)) (m_hold m1 =? 35615)) eqn:GZ.
  { simpl. fin2 W1 HM1. }
  destruct (i_head (m_s m1)) eqn:HD; simpl.
  all: destruct (orb _ _); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: destruct (negb (m_hold m1 mod 16 =? 8)); [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: remember (Z.shiftr (m_hold m1) 4 mod 16 + 8) as len eqn:EL.
  all: assert (LN: 8 <= len <= 23)
         by (rewrite EL; pose proof (Z.mod_pos_bound (Z.shiftr (m_hold m1) 4) 16); lia).
  all: clear EL.
  all: destruct (orb _ _) eqn:C; [simpl; apply mwf3x_set_bad; fin2 W1 HM1 |].
  all: apply orb_false_iff in C; destruct C as [C1 C2]; apply Z.ltb_ge in C1, C2.
  all: assert (P: 0 <= 2 ^ len <= 32768)
         by (split; [apply Z.pow_nonneg; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]).
  all: destruct (Z.land (Z.shiftr (m_hold m1) 4) 512 =? 0); simpl; fin2 W1 HM1.
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

(* all the cases of this file in one statement *)
Lemma header_all : ok_HCRC /\ ok_COMMENT /\ ok_NAME /\ ok_EXTRA /\ ok_EXLEN /\ ok_OS /\ ok_TIME /\
  ok_FLAGS /\ ok_HEAD /\ (ok_TYPE -> ok_DICT) /\ (ok_TYPE -> ok_DICTID).
Proof.
  split; [exact HCRC_ok|]. split; [exact COMMENT_ok|]. split; [exact NAME_ok|]. split; [exact EXTRA_ok|].
  split; [exact EXLEN_ok|]. split; [exact OS_ok|]. split; [exact TIME_ok|]. split; [exact FLAGS_ok|].
  split; [exact HEAD_ok|]. split; [exact DICT_ok | exact DICTID_ok].
Qed.

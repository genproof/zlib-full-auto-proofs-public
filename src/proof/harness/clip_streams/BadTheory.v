(* rj_bad_checksum: inflate() on a zlib or gzip stream whose trailer was changed (IFacts.bad_facts).  Until the
   trailer the decoder runs as on the true stream (the decode theory at the loop heads of a call,
   Decode7Step.decode7a_stmt); the trailer is read only in the CHECK (and, for gzip, LENGTH) modes, where the
   changed value differs from the check value the decoder computed: Z_DATA_ERROR, never Z_STREAM_END. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.IFacts Zlib.proof.harness.clip_streams.IDecode.
Require Import Zlib.proof.rfc1951.Decode7Step.
Require Import Zlib.proof.roundtrip.RTIPlain.
Require Zlib.proof.crc32.Combine.
Require Import Zlib.proof.harness.clip_streams.BadKit Zlib.proof.harness.clip_streams.BadRaw
  Zlib.proof.harness.clip_streams.BadTrl Zlib.proof.harness.clip_streams.BadLoop.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant of the call boundaries                                                           *)

(* where the decoder is between calls: in the header (the decode theory on the true stream), in the blocks
   (the decode theory on the raw stream of the blocks, BadKit.rawctx, for the state with wrap 0 and any check
   value; the zlib fields of the state: glob_ok and chk_ok of the true stream), or in the trailer
   (BadKit.pc_state) *)
Definition bad_phase (G: dctx) (src: list Z) (pos: Z) (out: list Z) (s: istate) (tout: Z) : Prop :=
  (md_hdr (i_mode s) /\ dinv G pos out s tout) \/
  (hlen G <= pos /\ (blk_mode (i_mode s) \/ i_mode s = CHECK) /\
   (exists cc, 0 <= cc < 2 ^ 64 /\
      dinv (rawctx G src) (pos - hlen G) out (set_i_check (set_i_wrap s 0) cc) tout) /\
   glob_ok G s /\ chk_ok G s out []) \/
  pc_state G src pos out s.

Definition bad_inv : inv_t := fun wbits D O src pos out z L =>
  exists G, bad_ctx G /\ dc_src G = O /\ full G = D /\ dc_iw G = iwb wbits /\ bad_src G src /\
    0 <= pos <= Zlength src /\ (exists rest, D = out ++ rest) /\ i_head (l_s L) = false /\ bytes_ok out /\
    bad_phase G src pos out (l_s L) (zf_tout z).

Lemma bad_inv_ok : inv_ok bad_inv.
Proof.
  intros wbits D O src pos out z L (G & _ & _ & _ & _ & _ & POS & PRE & HD & _). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stream deflate wrote: its trailer                                                          *)

Lemma bad_le_len v n : 0 <= n -> Zlength (le_bytes v n) = n.
Proof.
  intros N. unfold le_bytes. rewrite Zlength_map, Zlength_correct, seq_length. apply Z2Nat.id. exact N.
Qed.

Lemma bad_len wbits D O : dfinal_of wbits D O -> 8 <= wbits -> trl_of wbits <= Zlength O.
Proof.
  intros (_ & _ & bs & _ & _ & EO) W. unfold trl_of.
  unfold Zlib.proof.roundtrip.RTDIface.rwrap_of in EO.
  destruct (Z.ltb_spec wbits 0); [lia|].
  destruct (Z.gtb_spec wbits 15).
  - destruct EO as (_ & xfl & _ & ->). unfold stream_bytes. cbv zeta.
    rewrite !Zlength_app, !bad_le_len by lia.
    repeat match goal with |- context [Zlength ?a] =>
      let H := fresh in pose proof (Zlength_nonneg a) as H; revert H; generalize (Zlength a) end.
    intros. lia.
  - destruct EO as (_ & flg & _ & ->). unfold be_bytes.
    rewrite !Zlength_app, Zlength_rev, bad_le_len by lia.
    repeat match goal with |- context [Zlength ?a] =>
      let H := fresh in pose proof (Zlength_nonneg a) as H; revert H; generalize (Zlength a) end.
    intros. lia.
Qed.

(* the stream deflate wrote ends with its trailer, bytes *)
Lemma bad_split wbits D O : dfinal_of wbits D O -> 8 <= wbits ->
  exists A Tr, O = A ++ Tr /\ Zlength Tr = trl_of wbits /\ bytes_ok Tr.
Proof.
  intros (_ & _ & bs & _ & _ & EO) W. unfold trl_of.
  unfold Zlib.proof.roundtrip.RTDIface.rwrap_of in EO.
  destruct (Z.ltb_spec wbits 0); [lia|].
  destruct (Z.gtb_spec wbits 15).
  - destruct EO as (_ & xfl & _ & ->). unfold stream_bytes. cbv zeta.
    eexists _, _. rewrite app_assoc. split; [reflexivity|].
    rewrite Zlength_app, !bad_le_len by lia. split; [reflexivity|].
    unfold bytes_ok. apply Forall_app. split; apply rtip_le_ok.
  - destruct EO as (_ & flg & _ & ->). rewrite !app_assoc.
    eexists _, _. split; [reflexivity|]. unfold be_bytes. rewrite Zlength_rev, bad_le_len by lia.
    split; [reflexivity|]. apply rtip_be_ok.
Qed.

Lemma bad_init_mode sp w : i_mode (l_s (init_live sp w)) = HEAD.
Proof. unfold init_live. destruct (reset2_wb w) as [[a b]|]; reflexivity. Qed.

Lemma bad_init (DC: dctx_stmt) (DI: decode_init7a_stmt) wbits D O src z sp :
  dfinal_of wbits D O -> Zlength O <= 2 ^ 64 - 1 -> 8 <= wbits -> init_ok (iwb wbits) z sp ->
  Zlength src = Zlength O -> bytes_ok src ->
  sublist 0 (Zlength O - trl_of wbits) src = sublist 0 (Zlength O - trl_of wbits) O ->
  sublist (Zlength O - trl_of wbits) (Zlength O) src <> sublist (Zlength O - trl_of wbits) (Zlength O) O ->
  bad_inv wbits D O src 0 [] z (init_live sp (iwb wbits)).
Proof.
  intros DF L64 W8 (_ & _ & _ & _ & _ & T0 & _) LS BS EA NE.
  destruct (bad_split wbits D O DF W8) as (A & Tr & EO & LT & BT).
  assert (BO : bytes_ok O).
  { assert (EA' : A = sublist 0 (Zlength O - trl_of wbits) src).
    { pose proof (Zlength_nonneg A). rewrite EA, EO. rewrite Zlength_app, LT. rewrite sublist_app1 by lia.
      rewrite Z.add_simpl_r, sublist_same by lia. reflexivity. }
    rewrite EO. unfold bytes_ok in *. apply Forall_app. split; [|exact BT].
    rewrite EA'. apply Forall_sublist. exact BS. }
  destruct (DC wbits D O O DF ltac:(lia) (sublist_same 0 (Zlength O) O eq_refl eq_refl) BO)
    as (G & OK & SRC & SL & FU & HI & IW & ND & TL).
  assert (TL' : trl_len (dc_w G) = trl_of wbits) by (rewrite TL; destruct (Z.ltb_spec wbits 0); [lia|reflexivity]).
  assert (WR : wrapped G = true).
  { unfold wrapped. destruct (dc_w G) eqn:EW; [|reflexivity|reflexivity].
    cbn in TL'. unfold trl_of in TL'. destruct (wbits >? 15); discriminate. }
  assert (BC : bad_ctx G).
  { split; [exact OK|]. split; [exact HI|]. split; [exact WR|]. split; [exact ND|].
    destruct OK as (_ & _ & _ & _ & _ & _ & _ & E). rewrite SL, <- SRC, sublist_same in E by lia. exact E. }
  assert (TP : tpos G = Zlength O - trl_of wbits) by (unfold tpos; rewrite SL, TL'; reflexivity).
  exists G. split; [exact BC|]. split; [exact SRC|]. split; [exact FU|]. split; [exact IW|].
  split.
  { split; [lia|]. split; [exact BS|]. rewrite TP, SRC, SL. split; [exact EA|exact NE]. }
  split; [pose proof (Zlength_nonneg src); lia|]. split; [exists D; reflexivity|].
  pose proof (DI G sp (dctx_ok7_7a G OK) HI ND) as DV. rewrite IW in DV.
  split; [exact (proj1 (proj2 (proj1 (proj2 DV))))|]. split; [constructor|].
  left. split; [rewrite bad_init_mode; left; reflexivity|]. rewrite T0. exact DV.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fields of the wrapper                                                                      *)

Lemma bad_iw_nonneg G : bad_ctx G -> 0 <= dc_iw G.
Proof.
  intros ((SO & ACC & _) & _ & WR & _). destruct SO as (WB & _).
  unfold accepts, wrapped in *. destruct (dc_w G); [discriminate| |]; lia.
Qed.

(* inflateInit2's windowBits of a zlib or gzip stream: wrap 5, 6 or 7 (bit 4: check the trailer) *)
Lemma bad_reset_wrap w wrap wb : 0 <= w -> reset2_wb w = Some (wrap, wb) -> Z.land wrap 4 <> 0.
Proof.
  intros W R. unfold reset2_wb in R. destruct (Z.ltb_spec w 0); [lia|]. cbv zeta in R.
  destruct (Z.ltb_spec w 48) as [L|L].
  - destruct (_ || _); [|discriminate]. injection R as <- _.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (HH : w / 2 ^ 4 = 0 \/ w / 2 ^ 4 = 1 \/ w / 2 ^ 4 = 2).
    { assert (0 <= w / 2 ^ 4 < 3) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]). lia. }
    destruct HH as [HH|[HH|HH]]; rewrite HH; cbv; discriminate.
  - destruct (Z.eqb_spec w 0); [lia|]. destruct (Z.leb_spec 8 w); destruct (Z.leb_spec w 15); try lia;
    cbn in R; discriminate.
Qed.

Lemma bad_wrap4 G s : bad_ctx G -> glob_ok G s -> Z.land (i_wrap s) 4 <> 0.
Proof.
  intros BC ((wb0 & RW & _) & _). destruct (init_wrap_wb_bits _ _ _ RW) as (wrap & R & _ & _ & -> & _).
  exact (bad_reset_wrap _ _ _ (bad_iw_nonneg G BC) R).
Qed.

(* the data part of the output is the output (no history) *)
Lemma bad_produced G l : bad_ctx G -> produced G l = l.
Proof. intros (_ & HI & _). unfold produced. rewrite HI, Zlength_nil. apply sublist_same; lia. Qed.

(* the check value of the data continued over the output (DecCall.dc_upd_chk) *)
Lemma bad_upd_chk G s d ow : glob_ok G s -> wrapped G = true -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
  bytes_ok d -> update_check (i_flags s) (chkv G d) ow = chkv G (d ++ ow).
Proof.
  intros (_ & _ & _ & FL) WR N1 N2 B. specialize (FL WR N1 N2).
  unfold chkv, update_check, wrapped in *. destruct (dc_w G) as [| wb fl did | h]; [discriminate| |].
  - rewrite FL, Z.eqb_refl.
    assert (V1 : Zlib.proof.adler32.Model.adler_valid 1).
    { unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; discriminate. }
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref
      by (apply Zlib.proof.adler32.Model.ref_adler32_valid; exact V1).
    apply Zlib.proof.adler32.Model.ref_adler32_app. exact V1.
  - rewrite FL. destruct (Z.eqb_spec (8 + 256 * gz_flg h) 0); [lia|].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. exact B.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* From the header to the blocks within one call                                                  *)

Lemma bad_loop_first flush m m' o : loop2 flush lenfix_list distfix_list m o ->
  stepf2 flush lenfix_list distfix_list m = stepf2 flush lenfix_list distfix_list m' ->
  loop2 flush lenfix_list distfix_list m' o.
Proof.
  intros LP E. destruct LP as [m r m1 E1|m m1 E1 L1|m m1 o E1 L1 LP]; rewrite E1 in E.
  - apply loop2_ret. symmetry. exact E.
  - apply loop2_leave; [symmetry; exact E|exact L1].
  - apply loop2_next with m1; [symmetry; exact E|exact L1|exact LP].
Qed.

Lemma bad_needbits_f_mode k n m md : needbits_f k n (set_mode m md) = set_mode (needbits_f k n m) md.
Proof.
  revert m. induction k as [|k IH]; intros m; [reflexivity|]. cbn [needbits_f].
  change (m_bits (set_mode m md)) with (m_bits m). change (m_have (set_mode m md)) with (m_have m).
  destruct (m_bits m <? n); [|reflexivity]. destruct (m_have m =? 0); [destruct m; reflexivity|].
  rewrite <- IH; try (destruct m; reflexivity).
Qed.

(* TYPE (when the flush lets it go on) is TYPEDO; with input and an empty bit buffer, TYPEDO reads BFINAL and
   BTYPE and sets the mode in every branch *)
Lemma bad_typedo_same flush m :
  (m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = TYPEDO) ->
  (m_mode m = Zlib.proof.inflate.Model.TYPE -> flush <> Z_BLOCK /\ flush <> Z_TREES) ->
  0 < m_have m -> i_last (m_s m) = 0 -> m_bits m = 0 -> m_leave m = 0 ->
  stepf2 flush lenfix_list distfix_list m = stepf2 flush lenfix_list distfix_list (set_mode m TYPEDO).
Proof.
  intros M F H La B Lv.
  assert (S2 : stepf2 flush lenfix_list distfix_list (set_mode m TYPEDO) = c_TYPEDO flush (set_mode m TYPEDO))
    by reflexivity.
  assert (S1 : stepf2 flush lenfix_list distfix_list m = c_TYPEDO flush m).
  { destruct M as [M|M].
    - destruct (F M) as [F1 F2]. unfold stepf2, step2. rewrite M. cbn -[c_TYPE c_TYPEDO]. unfold c_TYPE.
      rewrite (proj2 (Z.eqb_neq _ _) F1), (proj2 (Z.eqb_neq _ _) F2). reflexivity.
    - unfold stepf2, step2. rewrite M. reflexivity. }
  rewrite S1, S2. unfold c_TYPEDO. change (i_last (m_s (set_mode m TYPEDO))) with (i_last (m_s m)). rewrite La.
  cbn [Z.eqb negb]. unfold needbits. rewrite bad_needbits_f_mode.
  assert (NB : needbits_f 4 3 m = pull m).
  { cbn [needbits_f]. rewrite B. cbn [Z.ltb Z.compare].
    destruct (Z.eqb_spec (m_have m) 0); [lia|].
    assert (E8 : m_bits (pull m) = 8) by (unfold pull; cbn; rewrite B; reflexivity).
    rewrite E8. reflexivity. }
  rewrite NB.
  assert (LP : m_leave (pull m) = 0) by exact Lv.
  change (m_leave (set_mode (pull m) TYPEDO)) with (m_leave (pull m)). rewrite LP. cbn [Z.eqb].
  generalize (pull m). intros p.
  destruct p as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
  destruct s. unfold set_mode, upd_s, dropbits, bitsn, set_leave, set_bad. cbn.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the state at the start of the blocks with an empty bit buffer and mode TYPEDO *)
Definition bad_tstate (s: istate) : istate := set_i_bits (set_i_hold (set_i_mode s TYPEDO) 0) 0.

Lemma bad_swf_t s : swf s -> swf (bad_tstate s).
Proof.
  intros []. constructor; cbn; auto; try (unfold TYPEDO, HEAD, SYNC; lia).
  unfold lrange. split; [lia|]. unfold Integers.Int64.max_unsigned. cbn. lia.
Qed.

Lemma bad_modewf_t s : modewf (bad_tstate s).
Proof.
  constructor; cbn; first [intros HM; exfalso; unfold decode_mode in HM; compute in HM; lia|
    repeat split; intros HM; exfalso; compute in HM; lia].
Qed.

Lemma bad_swf3_t s : swf3 (bad_tstate s).
Proof.
  constructor; cbn; first [intros HM; exfalso; unfold decode_mode in HM; compute in HM; lia|
    repeat split; intros HM; exfalso; compute in HM; lia].
Qed.

(* at the start of the blocks only the mode group and the last flag of the state matter *)
Lemma bad_at_type_move G2 s s' c h b o : at_mode G2 s c h b o ->
  (i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO) ->
  (i_mode s' = Zlib.proof.inflate.Model.TYPE \/ i_mode s' = TYPEDO) -> i_last s' = i_last s ->
  at_mode G2 s' c h b o.
Proof.
  intros [HO D] M M' La. split; [exact HO|].
  destruct D as [[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[Mx X]]]]]]]]]]]]]]]]];
  try (exfalso; destruct M as [M|M]; rewrite M in Mx;
       unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, HEAD, FLAGS, TIME, OS, STORED, COPY_, COPY, TABLE, LENLENS,
         CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in Mx; lia).
  right; right; left. split; [exact M'|].
  destruct X as (k & X1 & X2 & X3 & X4 & X5). exists k.
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. rewrite La. exact X5.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The rest of a call from the blocks                                                             *)

Section Call.
Variables (KI: kd_init7a_stmt) (DS: dc_step7a_stmt) (SM: stepf2_mwf3W_stmt) (DK: decode_call7a_stmt).
Variables (G: dctx) (src: list Z).
Hypotheses (BC: bad_ctx G) (BS: bad_src G src).

(* what a call gives: the input object's x, the output before the call out, aout bytes of output space *)
Definition bad_outcome (pos: Z) (x out: list Z) (aout: Z) (res: result) : Prop :=
  let m := r_m res in
  0 <= m_snx m <= Zlength x /\ m_sow m = Zlength (m_ow m) /\ m_aout m = aout /\ m_inp m = x /\
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_DATA_ERROR) /\
  (r_ret res <> Z_DATA_ERROR ->
     bad_phase G src (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\ i_head (m_s m) = false /\
     bytes_ok (out ++ m_ow m) /\ exists rest, full G = out ++ m_ow m ++ rest).

(* the input of the raw call: src's bytes from the end of the header on *)
Lemma bad_raw_inp pos d x : 0 <= pos -> hlen G <= pos + d -> pos + Zlength x <= Zlength src ->
  x = sublist pos (pos + Zlength x) src -> 0 <= d <= Zlength x ->
  let inp2 := sublist d (Zlength x) x in
  Zlength inp2 = Zlength x - d /\ 0 <= pos + d - hlen G /\
  pos + d - hlen G + Zlength inp2 <= Zlength (dc_src (rawctx G src)) /\
  inp2 = sublist (pos + d - hlen G) (pos + d - hlen G + Zlength inp2) (dc_src (rawctx G src)) /\
  bytes_ok inp2.
Proof.
  intros P0 HD PL XE D0. cbv zeta.
  destruct BS as (LS & BY & _).
  destruct (bad_raw_ok G src BC BS) as (_ & HL & _).
  assert (TS : tpos G <= slen G) by (unfold tpos; destruct (dc_w G); cbn; lia).
  assert (L2 : Zlength (sublist d (Zlength x) x) = Zlength x - d) by (rewrite Zlength_sublist; lia).
  split; [exact L2|]. split; [lia|].
  unfold rawctx; cbn [dc_src]. rewrite L2, (Zlength_sublist (hlen G) (Zlength src) src) by lia.
  split; [lia|]. split.
  - remember (Zlength x) as n eqn:En. rewrite XE.
    rewrite sublist_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
  - rewrite XE. unfold bytes_ok in *. apply Forall_sublist. apply Forall_sublist. exact BY.
Qed.


(* the zlib fields of a state from the raw view's (head, window bits) and the state at the start of the
   call (wrap, flags) *)
Lemma bad_glob_back s0 s' : glob_ok G s0 -> i_mode s0 <> HEAD -> i_mode s0 <> FLAGS ->
  i_head s' = false -> (i_mode s' <> HEAD -> dc_wb G <= i_wbits s' <= 15) ->
  i_wrap s' = i_wrap s0 -> i_flags s' = i_flags s0 -> i_mode s' <> HEAD -> i_mode s' <> FLAGS -> glob_ok G s'.
Proof.
  intros ((wb0 & RW & _) & _ & _ & FL) M1 M2 HD WB EW EF N1 N2.
  split; [exists wb0; rewrite EW; split; [exact RW|intros; contradiction]|].
  split; [exact HD|]. split; [exact WB|].
  intros WR _ _. rewrite EF. exact (FL WR M1 M2).
Qed.

(* dinv at equal arguments (keeps the kernel away from rewriting inside dinv) *)
Lemma bad_dinv_eq G2 p o s t p' o' s' t' : dinv G2 p o s t -> p' = p -> o' = o -> s' = s -> t' = t ->
  dinv G2 p' o' s' t'.
Proof. intros D -> -> -> ->. exact D. Qed.

(* the check value and total after a call that wrote ow, folded in at inf_leave or in CHECK *)
Lemma bad_chk_fold s out ow : glob_ok G s -> i_mode s <> HEAD -> i_mode s <> FLAGS -> bytes_ok out ->
  Zlength ow <= 2 ^ 32 - 1 ->
  i_check s = chkv G (produced G out) -> i_total s = Zlength (produced G out) mod 2 ^ 64 ->
  (if negb (Z.land (i_wrap s) 4 =? 0) && negb (u32 (Zlength ow) =? 0)
   then update_check (i_flags s) (i_check s) (sublist (Zlength ow - u32 (Zlength ow)) (Zlength ow) ow)
   else i_check s) = chkv G (produced G (out ++ ow)) /\
  u64 (i_total s + u32 (Zlength ow)) = Zlength (produced G (out ++ ow)) mod 2 ^ 64.
Proof.
  intros GL N1 N2 BO LW CK TT.
  destruct BC as (_ & _ & WR & _).
  rewrite !bad_produced in * by exact BC.
  assert (U : u32 (Zlength ow) = Zlength ow) by (unfold u32; apply Z.mod_small; pose proof (Zlength_nonneg ow); lia).
  rewrite U. split.
  - rewrite (proj2 (Z.eqb_neq _ _) (bad_wrap4 G s BC GL)). cbn [negb andb].
    destruct (Z.eqb_spec (Zlength ow) 0) as [Z0|Z0].
    + cbn. apply Zlength_nil_inv in Z0. subst ow. rewrite app_nil_r. exact CK.
    + cbn. rewrite Z.sub_diag, sublist_same by lia. rewrite CK. apply bad_upd_chk; auto.
  - unfold u64. rewrite TT, Zlength_app. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma bad_kd_ret G2 pos inp ob m : Kd G2 pos inp ob m -> m_mode m <> DONE -> m_ret m = Z_OK.
Proof.
  intros K N. rewrite (kd_ret _ _ _ _ _ K). destruct (Z.eqb_spec (m_mode m) DONE); [contradiction|reflexivity].
Qed.

Lemma bad_blk_nothdr md : blk_mode md \/ md = CHECK ->
  md <> HEAD /\ md <> FLAGS /\ md <> TIME /\ md <> OS /\ md <> LENGTH /\ md <> DONE.
Proof.
  intros H. unfold blk_mode, md_type, md_tab, md_dec in H.
  unfold HEAD, FLAGS, TIME, OS, LENGTH, DONE, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK in *. lia.
Qed.

(* the check value and total of the data before the call, in a block mode or CHECK *)
Lemma bad_chk_blk s out : chk_ok G s out [] -> (blk_mode (i_mode s) \/ i_mode s = CHECK) ->
  i_check s = chkv G (produced G out) /\ i_total s = Zlength (produced G out) mod 2 ^ 64.
Proof.
  intros CK Md. destruct (bad_blk_nothdr _ Md) as (MH & MF & MT & MO & ML & MD).
  destruct BC as (_ & _ & WR & _). destruct (CK WR MH MF MT MO) as (A1 & A2 & _).
  rewrite (proj2 (Z.eqb_neq _ _) ML), (proj2 (Z.eqb_neq _ _) MD) in A1, A2.
  cbn in A1, A2. split; assumption.
Qed.

(* the output space does not change *)
Lemma bad_loop_aout flush m m' o : loop2 flush lenfix_list distfix_list m o ->
  loop2 flush lenfix_list distfix_list m' o -> URunFrame.vmode (m_mode m) -> URunFrame.vmode (m_mode m') ->
  m_aout m' = m_aout m.
Proof.
  intros L L' V V'. apply URunFrame.loop2_ok in L; [|exact V]. apply URunFrame.loop2_ok in L'; [|exact V'].
  destruct o as [mF|r mF]; cbn in L, L'; destruct L as (_ & A & _); destruct L' as (_ & A' & _); congruence.
Qed.

(* the rest of a call from a CHECK head reached in the blocks *)
Lemma bad_bcont_check pos d x out cc m o res flush mC xs' hh' bb' :
  0 <= pos -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src ->
  Zlength x <= 2 ^ 32 - 1 -> 0 <= d <= Zlength x ->
  glob_ok G (m_s m) -> m_mode m <> HEAD -> m_mode m <> FLAGS ->
  i_check (m_s m) = chkv G (produced G out) -> i_total (m_s m) = Zlength (produced G out) mod 2 ^ 64 ->
  bytes_ok out -> (blk_mode (m_mode m) \/ m_mode m = CHECK) ->
  loop2 flush lenfix_list distfix_list m o ->
  match o with IRet r m1 => res = Res r m1 None | IBrk m1 => inf_leave flush m1 res end ->
  r_ret res <> Z_MEM_ERROR ->
  m_mode mC = CHECK -> m_leave mC = 0 -> loop2 flush lenfix_list distfix_list mC o ->
  Kd (rawctx G src) (pos + d - hlen G) (sublist d (Zlength x) x) out
    (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mC) ->
  mwf3W (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mC) ->
  i_wrap (m_s mC) = i_wrap (m_s m) -> i_check (m_s mC) = i_check (m_s m) ->
  i_total (m_s mC) = i_total (m_s m) -> i_flags (m_s mC) = i_flags (m_s m) ->
  m_inp mC = x -> d <= m_nx mC <= Zlength x ->
  bad_outcome pos x out (m_aout m) res.
Proof.
  intros P0 PL XE LX D0 GL M0H M0F CK1 CK2 BO Md LP RO NM MC LC LPC KC WC CW CC' CT CF ICq NC.
    pose proof (kd_at _ _ _ _ _ KC) as AT.
    assert (MC' : i_mode (m_s (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mC)) = CHECK)
      by exact MC.
    destruct (bad_raw_check G src _ _ _ _ _ BC BS AT MC') as (Ec & Eb & Eh & Eo). clear AT MC'.
    cbn in Ec, Eb, Eh, Eo.
    destruct WC as (WWC & _ & _). pose proof (mwW_ow _ WWC) as (OWL & OWB). pose proof (mwW_aout _ WWC) as AOC.
    pose proof (mwW_in _ WWC) as INC. cbn in OWL, OWB, AOC, INC. rewrite ICq in INC.
    rewrite Zlength_sublist in INC by (clear - D0; lia).
    pose proof (kd_out _ _ _ _ _ KC) as KOC. unfold after_check, wrapped in KOC. cbn [rawctx dc_w andb] in KOC.
    cbn in KOC.
    assert (MCH : m_mode mC <> HEAD /\ m_mode mC <> FLAGS /\ m_mode mC <> DONE).
    { rewrite MC. unfold CHECK, HEAD, FLAGS, DONE. repeat split; discriminate. }
    destruct MCH as (MCH & MCF & MCD).
    assert (RTC : m_ret mC = Z_OK) by exact (bad_kd_ret _ _ _ _ _ KC MCD).
    pose proof (kd_glob _ _ _ _ _ KC) as (_ & H2 & W2 & _). cbn in H2, W2.
    assert (GLC : glob_ok G (m_s mC)) by exact (bad_glob_back (m_s m) (m_s mC) GL M0H M0F H2 W2 CW CF MCH MCF).
    assert (CH : chead G src pos x out mC).
    { split; [exact ICq|]. split; [exact P0|]. split; [exact PL|]. split; [exact XE|]. split; [exact LX|].
      split; [clear - NC D0; lia|]. split; [clear - INC; lia|]. split; [exact LC|]. split; [exact RTC|].
      split; [exact GLC|]. split; [exact Eo|]. split; [clear - OWL AOC; lia|].
      split; [exact KOC|]. left. split; [exact MC|]. split; [rewrite CC'; exact CK1|].
      split; [rewrite CT; exact CK2|].
      exists 0. split; [clear; lia|]. split; [clear - Ec NC; lia|]. split; [exact Eb|].
      rewrite Z.add_0_r, sublist_nil. exact Eh. }
    destruct (bad_trl_call G src pos x out flush mC o res BC BS CH LPC RO NM) as (S1 & S2 & S3 & S4 & S5 & S6).
    assert (AOC' : m_aout mC = m_aout m).
    { apply bad_loop_aout with flush o; [exact LP|exact LPC|apply bad_vmode_blk; exact Md|].
      apply bad_vmode_blk. right. exact MC. }
    unfold bad_outcome. cbv zeta.
    split; [exact S1|]. split; [exact S2|]. split; [rewrite S3, AOC'; reflexivity|]. split; [exact S5|].
    split; [destruct S6 as [S6|(S6 & _)]; [right; right; exact S6|destruct S6 as [S6|S6]; [left|right; left]; exact S6]|].
    intros ND. destruct S6 as [S6|(_ & PC)]; [contradiction|].
    split; [right; right; exact PC|]. destruct PC as (PO & (_ & PH & _) & _).
    split; [exact PH|]. split.
    + rewrite S4. unfold bytes_ok in *. apply Forall_app. split; [exact BO|exact OWB].
    + exists []. rewrite app_nil_r. symmetry. exact PO.
Qed.

(* the rest of a call that leaves in the blocks: the raw call of the decode theory *)
Lemma bad_bcont_exit pos d x out cc z2 L2 m res flush xs hh bb mE xs' hh' bb' :
  0 <= pos -> hlen G <= pos + d -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src ->
  Zlength x <= 2 ^ 32 - 1 -> 0 <= d <= Zlength x -> 0 <= cc < 2 ^ 64 ->
  m_init z2 L2 (sublist d (Zlength x) x) = bview d xs hh bb 0 cc (i_total (m_s m)) (i_flags (m_s m)) m ->
  dinv (rawctx G src) (pos + d - hlen G) out (l_s L2) (zf_tout z2) -> live_ok L2 -> zf_ok z2 ->
  zf_ao z2 <= 2 ^ 32 - 1 ->
  glob_ok G (m_s m) -> m_mode m <> HEAD -> m_mode m <> FLAGS ->
  i_check (m_s m) = chkv G (produced G out) -> i_total (m_s m) = Zlength (produced G out) mod 2 ^ 64 ->
  bytes_ok out -> inf_leave flush mE res -> r_ret res <> Z_MEM_ERROR -> m_leave mE = 1 ->
  loop2 flush lenfix_list distfix_list (bview d xs hh bb 0 cc (i_total (m_s m)) (i_flags (m_s m)) m)
    (IBrk (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mE)) ->
  Kd (rawctx G src) (pos + d - hlen G) (sublist d (Zlength x) x) out
    (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mE) ->
  mwf3W (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mE) ->
  (blk_mode (m_mode mE) \/ m_mode mE = CHECK) ->
  i_wrap (m_s mE) = i_wrap (m_s m) -> i_check (m_s mE) = i_check (m_s m) ->
  i_total (m_s mE) = i_total (m_s m) -> i_flags (m_s mE) = i_flags (m_s m) ->
  m_inp mE = x -> d <= m_nx mE <= Zlength x ->
  bad_outcome pos x out (zf_ao z2) res.
Proof.
  intros P0 HD PL XE LX D0 CC EI DV LV ZF AO GL M0H M0F CK1 CK2 BO RO NM LE LPR KE WE MdE EW EC ET EF IEq NE.
  unfold bad_outcome. cbv zeta.
  destruct (bad_raw_ok G src BC BS) as (OK2 & HL & SL2 & FU2 & D0E & TLE).
  pose proof (dctx_ok7_7a _ OK2) as C2.
  destruct (bad_raw_inp pos d x P0 HD PL XE D0) as (LI2 & P20 & PL2 & IE2 & BI2).
  destruct RO as [_ _|]; [cbn in NM; contradiction|].
    set (R2 := leave_fin flush (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mE)).
    assert (RUN2 : run2 flush lenfix_list distfix_list (m_init z2 L2 (sublist d (Zlength x) x)) R2).
    { exists (IBrk (bview d xs' hh' bb' 0 cc (i_total (m_s m)) (i_flags (m_s m)) mE)). split.
      - rewrite EI. exact LPR.
      - apply il_ok. }
    destruct (bad_blk_nothdr _ MdE) as (MH & MF & MT & MO & ML & MD).
    assert (RT : m_ret mE = Z_OK) by exact (bad_kd_ret _ _ _ _ _ KE MD).
    pose proof (bad_leave_view flush d xs' hh' bb' cc mE ltac:(clear - NE D0; lia) ltac:(rewrite IEq; clear - NE D0; lia)) as LVw.
    rewrite ET, EF in LVw. fold R2 in LVw. cbv zeta in LVw. clearbody R2.
    destruct LVw as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & _ & V19).
    destruct (V19 RT) as [RR RR2].
    destruct (DK (rawctx G src) (pos + d - hlen G) out L2 z2 (sublist d (Zlength x) x) flush R2 C2 DV LV ZF AO
                ltac:(clear - LI2 LX D0; lia) P20 PL2 IE2 RUN2)
      as [MEM|(_ & SNX & SOW & MAO & (rest & PRE) & DVE & _)].
    { rewrite MEM in RR2. destruct RR2 as [E|E]; discriminate E. }
    set (R := leave_fin flush mE) in *. clearbody R.
    pose proof (kd_out _ _ _ _ _ KE) as KO. unfold after_check, wrapped in KO. cbn [rawctx dc_w andb] in KO.
    destruct WE as (WWE & _ & _). pose proof (mwW_ow _ WWE) as (OWL & OWB). pose proof (mwW_aout _ WWE) as AOE.
    cbn in KO, OWL, OWB, AOE.
    assert (OUTE : u32 (m_out mE - m_left mE) = Zlength (m_ow mE)).
    { unfold m_left. rewrite KO.
      replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by (clear; lia).
      unfold u32. apply Z.mod_small. pose proof (Zlength_nonneg (m_ow mE)) as Z0. clear - OWL AOE Z0. lia. }
    rewrite OUTE in V16, V17.
    pose proof (kd_glob _ _ _ _ _ KE) as (_ & GH & GW & _). cbn in GH, GW.
    assert (GLE : glob_ok G (m_s mE)) by (apply bad_glob_back with (m_s m); auto; congruence).
    destruct (bad_chk_fold (m_s mE) out (m_ow mE) GLE MH MF BO ltac:(clear - OWL AOE; lia)
                ltac:(congruence) ltac:(congruence)) as [F1 F2].
    rewrite EF in F1. rewrite ET in F2.
    assert (SN : m_snx (r_m R) = m_snx (r_m R2) + d) by exact V2.
    split; [rewrite SN; clear - SNX LI2 D0; lia|]. split; [rewrite V11, V6; reflexivity|].
    split; [rewrite <- V4; exact MAO|]. split; [rewrite V8; exact IEq|]. split; [destruct RR as [RR|RR]; [left|right; left]; exact RR|].
    intros _. split; [|split; [|split]].
    + right; left. split; [rewrite SN; clear - HD SNX; lia|]. split; [unfold m_mode in MdE; rewrite V14; exact MdE|].
      split; [exists cc; split; [exact CC|]|].
      { apply (bad_dinv_eq _ _ _ _ _ _ _ _ _ DVE); [rewrite SN; clear; lia|rewrite V5; reflexivity|exact (eq_sym V1)|exact (eq_sym V7)]. }
      assert (U : u32 (Zlength (m_ow mE)) = Zlength (m_ow mE)).
      { unfold u32. apply Z.mod_small. pose proof (Zlength_nonneg (m_ow mE)) as Z0. clear - OWL AOE Z0. lia. }
      rewrite U in F1, F2.
      split.
      * pose proof (proj1 (proj2 DVE)) as G2E. rewrite V1 in G2E. destruct G2E as (_ & H2 & W2 & _).
        cbn in H2, W2.
        apply bad_glob_back with (m_s m); auto; try congruence;
          unfold m_mode in MH, MF; rewrite V14; assumption.
      * intros _ _ _ _ _. unfold m_mode in ML, MD.
        rewrite V14, (proj2 (Z.eqb_neq _ _) ML), (proj2 (Z.eqb_neq _ _) MD). cbn [orb]. cbv zeta. rewrite ?app_nil_r, V6.
        split; [rewrite V17; exact F1|]. split; [rewrite V16; exact F2|].
        exists (out ++ m_ow mE). destruct BC as (_ & HI & _). rewrite HI. reflexivity.
    + rewrite V15. exact (proj1 (proj2 GLE)).
    + rewrite V6. unfold bytes_ok in *. apply Forall_app. split; [exact BO|exact OWB].
    + exists rest. rewrite <- FU2, PRE, V5. reflexivity.
Qed.

(* the rest of a call from a loop head in the blocks (or at CHECK): the zlib machine m, whose raw view
   (input from byte d of the call's input on) is the start of a call of the decode theory on the raw stream *)

(* the rest of a call from a loop head in the blocks (or at CHECK): the zlib machine m, whose raw view
   (input from byte d of the call's input on) is the start of a call of the decode theory on the raw stream *)
Lemma bad_bcont pos d x out cc z2 L2 m o res flush xs hh bb :
  0 <= pos -> hlen G <= pos + d -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src ->
  Zlength x <= 2 ^ 32 - 1 -> 0 <= d <= Zlength x -> 0 <= cc < 2 ^ 64 ->
  m_init z2 L2 (sublist d (Zlength x) x) = bview d xs hh bb 0 cc (i_total (m_s m)) (i_flags (m_s m)) m ->
  dinv (rawctx G src) (pos + d - hlen G) out (l_s L2) (zf_tout z2) -> live_ok L2 -> zf_ok z2 ->
  zf_ao z2 <= 2 ^ 32 - 1 ->
  m_leave m = 0 -> m_inp m = x -> (blk_mode (m_mode m) \/ m_mode m = CHECK) ->
  glob_ok G (m_s m) -> chk_ok G (m_s m) out [] -> bytes_ok out ->
  loop2 flush lenfix_list distfix_list m o ->
  match o with IRet r m1 => res = Res r m1 None | IBrk m1 => inf_leave flush m1 res end ->
  r_ret res <> Z_MEM_ERROR ->
  bad_outcome pos x out (zf_ao z2) res.
Proof.
  intros P0 HD PL XE LX D0 CC EI DV LV ZF AO L0 I Md GL CK BO LP RO NM.
  unfold bad_outcome. cbv zeta.
  destruct (bad_raw_ok G src BC BS) as (OK2 & HL & SL2 & FU2 & D0E & TLE).
  pose proof (dctx_ok7_7a _ OK2) as C2.
  destruct (bad_raw_inp pos d x P0 HD PL XE D0) as (LI2 & P20 & PL2 & IE2 & BI2).
  destruct (KI (rawctx G src) (pos + d - hlen G) out L2 z2 (sublist d (Zlength x) x) C2 DV LV ZF AO ltac:(clear - LI2 LX D0; lia) BI2)
    as [K0 W0].
  assert (AOm : m_aout m = zf_ao z2) by (apply (f_equal m_aout) in EI; exact (eq_sym EI)).
  rewrite EI in K0, W0.
  destruct (bad_chk_blk (m_s m) out CK Md) as [CK1 CK2].
  destruct (bad_blk_nothdr _ Md) as (M0H & M0F & _).
  destruct (bad_bloop DS SM (rawctx G src) (pos + d - hlen G) d x out flush cc (i_total (m_s m)) (i_flags (m_s m))
              C2 P20 D0 PL2 IE2 m o LP xs hh bb K0 W0 L0 I Md eq_refl eq_refl)
    as [(mE & xs' & hh' & bb' & EO & LE & LPR & KE & WE & MdE & EW & EC & ET & EF & IEq & NE)|
        (mC & xs' & hh' & bb' & MC & LC & LPC & KC & WC & CW & CC' & CT & CF & ICq & NC)].
  - (* the call leaves in the blocks: the raw call of the decode theory *)
    subst o.
    exact (bad_bcont_exit pos d x out cc z2 L2 m res flush xs hh bb mE xs' hh' bb' P0 HD PL XE LX D0 CC EI DV LV ZF AO
             GL M0H M0F CK1 CK2 BO RO NM LE LPR KE WE MdE EW EC ET EF IEq NE).
  - (* a loop head at CHECK: the trailer *)
    rewrite <- AOm.
    exact (bad_bcont_check pos d x out cc m o res flush mC xs' hh' bb' P0 PL XE LX D0 GL M0H M0F CK1 CK2 BO Md LP RO NM
             MC LC LPC KC WC CW CC' CT CF ICq NC).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The state invariants of the raw view                                                           *)

Lemma bad_live L s' h' : live_ok L -> swf s' -> modewf s' -> hwf h' -> swf3 s' -> i_wbits s' <> 0 ->
  i_head s' = false ->
  live_ok (Live (l_sp L) (l_winp L) s' h' (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
Proof.
  intros (A & _ & _ & _ & _ & WS & _) SW MW HW S3 WB HD. unfold live_ok. cbn [l_sp l_s l_h l_hsh].
  split; [exact A|]. split; [exact SW|]. split; [exact MW|]. split; [exact HW|]. split; [exact S3|].
  split; [exact WS|]. split; [intros E; contradiction|]. split; [intros E; congruence|].
  intros E; contradiction.
Qed.

Lemma bad_lrange c : 0 <= c < 2 ^ 64 -> lrange c.
Proof. intros H. unfold lrange. split; [lia|]. unfold Integers.Int64.max_unsigned. cbn. lia. Qed.

Lemma bad_swf_raw s cc : swf s -> lrange cc -> swf (set_i_check (set_i_wrap s 0) cc).
Proof. intros [] C. constructor; cbn; auto; lia. Qed.

Lemma bad_modewf_raw s cc : modewf s -> modewf (set_i_check (set_i_wrap s 0) cc).
Proof. intros []. constructor; cbn; assumption. Qed.

Lemma bad_swf3_raw s cc : swf3 s -> swf3 (set_i_check (set_i_wrap s 0) cc).
Proof.
  intros []. constructor; cbn; [intros _ _ HH; exfalso; apply HH; reflexivity|assumption..].
Qed.

(* the start of a call from the blocks: TYPE becomes TYPEDO *)
Lemma bad_typedo_glob s : glob_ok G s -> i_mode s = Zlib.proof.inflate.Model.TYPE -> glob_ok G (set_i_mode s TYPEDO).
Proof.
  intros GL M. pose proof GL as (_ & HD & WB & _).
  apply bad_glob_back with s; cbn; auto; rewrite ?M; try (unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, HEAD, FLAGS; lia).
  intros _. apply WB. rewrite M. unfold Zlib.proof.inflate.Model.TYPE, HEAD. lia.
Qed.

Lemma bad_chk_move s s' out : chk_ok G s out [] -> (blk_mode (i_mode s) \/ i_mode s = CHECK) ->
  (blk_mode (i_mode s') \/ i_mode s' = CHECK) -> i_check s' = i_check s -> i_total s' = i_total s ->
  chk_ok G s' out [].
Proof.
  intros CK Md Md' EC ET. destruct (bad_chk_blk s out CK Md) as [C1 C2].
  destruct (bad_blk_nothdr _ Md') as (MH & MF & MT & MO & ML & MD).
  intros _ _ _ _ _. rewrite (proj2 (Z.eqb_neq _ _) ML), (proj2 (Z.eqb_neq _ _) MD). cbn [orb]. cbv zeta.
  rewrite ?app_nil_r. split; [congruence|]. split; [congruence|]. exists out.
  destruct BC as (_ & HI & _). rewrite HI. reflexivity.
Qed.

(* the start of a call of the raw view: the state with wrap 0 and the check value cc *)
Lemma bad_minit_raw z0 L x cc :
  m_init z0 (Live (l_sp L) (l_winp L) (set_i_check (set_i_wrap (l_s L) 0) cc) (l_h L) (l_headp L) (l_hsh L)
               (l_xb L) (l_nb L) (l_cb L)) (sublist 0 (Zlength x) x) =
  bview 0 0 (i_hold (l_s L)) (i_bits (l_s L)) 0 cc (i_total (m_s (m_init z0 L x))) (i_flags (m_s (m_init z0 L x)))
    (m_init z0 L x).
Proof.
  rewrite sublist_same by lia. destruct L as [sp winp s h headp hsh xb nb cb]. cbn [l_sp l_winp l_s l_h l_headp l_hsh l_xb l_nb l_cb].
  unfold m_init, bview. cbv zeta. cbn [l_s l_h].
  destruct s; cbn; destruct (i_mode =? Zlib.proof.inflate.Model.TYPE); cbn; f_equal; try reflexivity; try lia;
    symmetry; rewrite ZtoNat_Zlength; apply firstn_all.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A call from the blocks (or CHECK with nothing of the trailer read)                             *)

Lemma bad_run_blk pos out z0 L x cc flush res :
  hlen G <= pos -> (blk_mode (i_mode (l_s L)) \/ i_mode (l_s L) = CHECK) -> 0 <= cc < 2 ^ 64 ->
  dinv (rawctx G src) (pos - hlen G) out (set_i_check (set_i_wrap (l_s L) 0) cc) (zf_tout z0) ->
  glob_ok G (l_s L) -> chk_ok G (l_s L) out [] -> bytes_ok out ->
  live_ok L -> zf_ok z0 -> zf_ao z0 <= 2 ^ 32 - 1 -> Zlength x <= 2 ^ 32 - 1 ->
  0 <= pos -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src ->
  run2 flush lenfix_list distfix_list (m_init z0 L x) res -> r_ret res <> Z_MEM_ERROR ->
  bad_outcome pos x out (zf_ao z0) res.
Proof.
  intros HP Md CC DV GL CK BO LV ZF AO LX P0 PL XE (o & LP & RO) NM.
  set (s := l_s L) in *.
  set (L2 := Live (l_sp L) (l_winp L) (set_i_check (set_i_wrap s 0) cc) (l_h L) (l_headp L) (l_hsh L) (l_xb L)
               (l_nb L) (l_cb L)).
  set (m := m_init z0 L x).
  assert (EI : m_init z0 L2 (sublist 0 (Zlength x) x) =
               bview 0 0 (i_hold s) (i_bits s) 0 cc (i_total (m_s m)) (i_flags (m_s m)) m)
    by exact (bad_minit_raw z0 L x cc).
  assert (LV2 : live_ok L2).
  { pose proof LV as (_ & SW & MW & HW & S3 & _). destruct GL as (_ & HD & WB & _).
    apply bad_live; auto.
    - apply bad_swf_raw; [exact SW|apply bad_lrange; exact CC].
    - apply bad_modewf_raw; exact MW.
    - apply bad_swf3_raw; exact S3.
    - cbn. destruct (bad_blk_nothdr _ Md) as (MH & _). specialize (WB MH).
      destruct BC as ((SO & _) & _). destruct SO as (WB0 & _). lia. }
  assert (Mm : blk_mode (m_mode m) \/ m_mode m = CHECK).
  { unfold m, m_mode, m_init. fold s. cbn.
    destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE) as [E|E]; cbn; [|exact Md].
    left. left. unfold md_type. right; left. reflexivity. }
  assert (GLm : glob_ok G (m_s m)).
  { unfold m, m_init. fold s. cbn. destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE) as [E|E];
    [apply bad_typedo_glob; auto|exact GL]. }
  assert (CKm : chk_ok G (m_s m) out []).
  { apply bad_chk_move with s; auto; unfold m, m_init; fold s; cbn;
    destruct (i_mode s =? Zlib.proof.inflate.Model.TYPE); reflexivity. }
  assert (DV2 : dinv (rawctx G src) (pos + 0 - hlen G) out (l_s L2) (zf_tout z0))
    by (rewrite Z.add_0_r; exact DV).
  exact (bad_bcont pos 0 x out cc z0 L2 m o res flush 0 (i_hold s) (i_bits s) P0 ltac:(clear - HP; lia) PL XE LX
           ltac:(clear - LX; pose proof (Zlength_nonneg x); lia) CC EI DV2 LV2 ZF AO eq_refl eq_refl Mm GLm CKm BO
           LP RO NM).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A call with part of the trailer read                                                           *)

Lemma bad_run_trl pos out z0 L x flush res :
  pc_state G src pos out (l_s L) -> bytes_ok out -> zf_ok z0 -> zf_ao z0 <= 2 ^ 32 - 1 ->
  Zlength x <= 2 ^ 32 - 1 -> 0 <= pos -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src ->
  run2 flush lenfix_list distfix_list (m_init z0 L x) res -> r_ret res <> Z_MEM_ERROR ->
  bad_outcome pos x out (zf_ao z0) res.
Proof.
  intros PC BO ZF AO LX P0 PL XE (o & LP & RO) NM.
  pose proof ZF as (_ & ZA & _).
  pose proof (bad_trl_start G src pos out z0 L x BC BS PC P0 PL XE LX ltac:(clear - ZA AO; lia)) as CH.
  destruct (bad_trl_call G src pos x out flush _ o res BC BS CH LP RO NM) as (S1 & S2 & S3 & S4 & S5 & S6).
  unfold bad_outcome. cbv zeta.
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S5|].
  split; [destruct S6 as [S6|(S6 & _)]; [right; right; exact S6|destruct S6 as [S6|S6]; [left|right; left]; exact S6]|].
  intros ND. destruct S6 as [S6|(_ & PC')]; [contradiction|].
  split; [right; right; exact PC'|]. destruct PC' as (PO & (_ & PH & _) & _).
  split; [exact PH|]. rewrite S4. cbn [m_init m_ow]. rewrite app_nil_r. split; [exact BO|].
  exists []. rewrite app_nil_r. symmetry. rewrite S4 in PO. cbn [m_init m_ow] in PO. rewrite app_nil_r in PO. exact PO.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A call from the header                                                                          *)

(* in the header nothing is written (no history) *)
Lemma bad_hdr_out s c h b o : at_mode G s c h b o -> md_hdr (i_mode s) -> o = [].
Proof.
  intros [_ D] M. destruct BC as (_ & HI & _).
  destruct D as [[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[[Mx X]|[Mx X]]]]]]]]]]]]]]]]];
  try (exfalso; unfold md_hdr in M; rewrite ?Mx in M;
       try (destruct Mx as [Mx|Mx]; rewrite Mx in M); try (destruct Mx as [Mx|[Mx|Mx]]; rewrite Mx in M);
       compute in M; lia).
  - destruct X as (X & _). rewrite X, HI. reflexivity.
  - destruct X as (hh & _ & X & _). rewrite X, HI. reflexivity.
Qed.

(* inf_leave keeps the input, the output, the output space; next_in = next *)
Lemma bad_leave_basic flush m :
  m_snx (r_m (leave_fin flush m)) = m_nx m /\ m_ow (r_m (leave_fin flush m)) = m_ow m /\
  m_aout (r_m (leave_fin flush m)) = m_aout m /\ m_inp (r_m (leave_fin flush m)) = m_inp m /\
  i_mode (m_s (r_m (leave_fin flush m))) = m_mode m /\ i_head (m_s (r_m (leave_fin flush m))) = i_head (m_s m).
Proof.
  destruct (URunFrame.leave_fin_fr flush m) as (A1 & A2 & _ & A4 & A5).
  split; [|split; [|split; [exact A2|split; [exact A1|split; [exact A5|exact A4]]]]];
  unfold leave_fin; cbv zeta; destruct (leave_ok flush m); cbn [r_m];
  match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the state right after the header as a state of the blocks (the raw view) *)
Lemma bad_hdr_to_blk p o s t : dinv G p o s t ->
  (i_mode s = Zlib.proof.inflate.Model.TYPE \/ i_mode s = TYPEDO) -> p <= hlen G ->
  hlen G <= p /\ (blk_mode (i_mode s) \/ i_mode s = CHECK) /\
  (exists cc, 0 <= cc < 2 ^ 64 /\ dinv (rawctx G src) (p - hlen G) o (set_i_check (set_i_wrap s 0) cc) t) /\
  glob_ok G s /\ chk_ok G s o [].
Proof.
  intros (A & GL & WN & CK & TT) M Lp.
  destruct (bad_type_start G src s p (i_hold s) (i_bits s) o BC BS A M Lp) as (Ep & Eb & Eh & Eo & _).
  assert (MH : i_mode s <> HEAD) by (destruct M as [M|M]; rewrite M; compute; discriminate).
  split; [lia|]. split; [left; left; unfold md_type; destruct M as [M|M]; [left|right; left]; exact M|].
  split; [|split; [exact GL|exact CK]].
  exists 0. split; [lia|].
  destruct (bad_raw_type G src s p (i_hold s) (i_bits s) o 0 BC BS A M Lp) as (_ & _ & _ & _ & A2).
  subst o. replace (p - hlen G) with 0 by lia.
  split; [cbn; rewrite Eh, Eb; exact A2|]. split; [exact (bad_raw_glob G src s 0 BC GL MH)|].
  split; [intros ML; cbn in ML |- *; specialize (WN ML); exact WN|].
  split; [intros WR; discriminate WR|].
  rewrite TT. rewrite !bad_produced by exact BC. unfold produced. reflexivity.
Qed.

(* from the header loop's TYPE head to the raw call of the blocks *)
Lemma bad_junction pos x z0 L flush o res inp' mT' :
  0 <= pos -> pos + Zlength x <= Zlength src -> x = sublist pos (pos + Zlength x) src -> Zlength x <= 2 ^ 32 - 1 ->
  live_ok L -> zf_ok z0 -> zf_ao z0 <= 2 ^ 32 - 1 -> Zlength x = Zlength inp' ->
  Kd G pos inp' [] mT' -> mwf3W mT' -> m_leave mT' = 0 ->
  (m_mode mT' = Zlib.proof.inflate.Model.TYPE \/ m_mode mT' = TYPEDO) -> pos + m_nx mT' = hlen G ->
  m_bits mT' = 0 -> m_hold mT' = 0 -> i_last (m_s mT') = 0 -> m_ow mT' = [] -> 0 < m_have mT' ->
  (m_mode mT' = Zlib.proof.inflate.Model.TYPE -> flush <> Z_BLOCK /\ flush <> Z_TREES) ->
  loop2 flush lenfix_list distfix_list (set_m_inp mT' x) o -> m_aout mT' = zf_ao z0 ->
  match o with IRet r m1 => res = Res r m1 None | IBrk m1 => inf_leave flush m1 res end ->
  r_ret res <> Z_MEM_ERROR ->
  bad_outcome pos x [] (zf_ao z0) res.
Proof.
  intros P0 PL XE LX LV ZF0 AO XL K W L0 M NX Bt Ht Lt Ot Hv Ft LPT AOT RO NM.
  set (d := m_nx mT') in *.
  pose proof (kd_inp _ _ _ _ _ K) as KI0.
  destruct W as (WW & WS3 & WH).
  pose proof (mwW_nx _ WW) as N0. pose proof (mwW_in _ WW) as IN0. pose proof (mwW_s _ WW) as SW.
  pose proof (mwW_h _ WW) as HW. pose proof (mwW_tin _ WW) as TIN. pose proof (mwW_adler _ WW) as ADL.
  pose proof (mwW_sow _ WW) as SOW0. rewrite KI0 in N0, IN0. rewrite Ot in SOW0.
  assert (MH : m_mode mT' <> HEAD /\ m_mode mT' <> FLAGS /\ m_mode mT' < CHECK /\
               (m_mode mT' =? LENGTH) || (m_mode mT' =? DONE) = false).
  { destruct M as [M|M]; rewrite M; compute; repeat split; try discriminate; reflexivity. }
  destruct MH as (MH & MF & MC & MLD).
  pose proof (kd_out _ _ _ _ _ K) as KO. unfold after_check in KO. rewrite MLD, andb_false_r in KO.
  pose proof (kd_ret _ _ _ _ _ K) as KR.
  assert (RT : m_ret mT' = Z_OK).
  { rewrite KR. destruct (Z.eqb_spec (m_mode mT') DONE) as [E|E]; [|reflexivity].
    exfalso. destruct M as [M|M]; rewrite M in E; discriminate E. }
  pose proof (kd_tout _ _ _ _ _ K) as KT. unfold after_check in KT. rewrite MLD, andb_false_r in KT.
  rewrite bad_produced in KT by exact BC. cbn in KT.
  pose proof (kd_glob _ _ _ _ _ K) as GL. pose proof (kd_chk _ _ _ _ _ K) as CK. rewrite Ot in CK.
  pose proof (kd_win _ _ _ _ _ K MC) as WN.
  pose proof GL as (_ & GHD & GWB & _).
  (* the zlib machine at the start of the blocks, mode TYPEDO *)
  set (m1 := set_mode (set_m_inp mT' x) TYPEDO).
  assert (LP1 : loop2 flush lenfix_list distfix_list m1 o).
  { apply bad_loop_first with (set_m_inp mT' x); [exact LPT|].
    apply bad_typedo_same; auto.
    unfold m_have in *. cbn [m_inp m_nx set_m_inp]. rewrite KI0 in Hv. lia. }
  (* the raw machine *)
  set (sT := bad_tstate (m_s mT')).
  set (s2 := set_i_check (set_i_wrap sT 0) 0).
  set (z2 := Zlib.proof.inflate_api.ApiModel.ZF (zf_ni z0) (Zlength x - d) (m_tin mT') (zf_no z0) (m_aout mT') (m_tout mT') (m_msg mT') 0
                (m_adler mT') (zf_res z0)).
  set (L2 := Live (l_sp L) (l_winp L) s2 (m_h mT') (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  assert (EI : m_init z2 L2 (sublist d (Zlength x) x) =
               bview d 0 0 0 0 0 (i_total (m_s m1)) (i_flags (m_s m1)) m1).
  { unfold m1, L2, z2, s2, sT, d. clear - KI0 IN0 KO RT SOW0 Ot Ht Bt XL N0 L0 KT.
    destruct mT' as [s h inp aout nx ow hold bits in_ out ret leave adler msg tin tout snx sow].
    cbn in *. subst. unfold m_init, bview, bad_tstate, vst. cbn.
    f_equal; try (destruct s; reflexivity); try lia.
    rewrite Zlength_sublist by lia. lia. }
  assert (MT : i_mode sT = TYPEDO) by reflexivity.
  assert (GLT : glob_ok G sT).
  { apply bad_glob_back with (m_s mT'); auto; cbn; try (compute; discriminate). }
  assert (DV2 : dinv (rawctx G src) (pos + d - hlen G) [] (l_s L2) (zf_tout z2)).
  { replace (pos + d - hlen G) with 0 by (clear - NX; lia). cbn [l_s L2 zf_tout z2]. rewrite KT.
    destruct (bad_raw_type G src (m_s mT') (pos + d) (m_hold mT') (m_bits mT') ([] ++ m_ow mT') 0 BC BS
                (kd_at _ _ _ _ _ K) M ltac:(clear - NX; lia)) as (_ & _ & _ & _ & A2).
    split; [|split; [|split; [|split]]].
    - apply bad_at_type_move with (set_i_check (set_i_wrap (m_s mT') 0) 0); [exact A2|exact M|right; reflexivity|].
      cbn. reflexivity.
    - exact (bad_raw_glob G src sT 0 BC GLT ltac:(rewrite MT; compute; discriminate)).
    - intros _. unfold win_ok, win_at in *. cbn. exact WN.
    - intros WR; discriminate WR.
    - reflexivity. }
  assert (LV2 : live_ok L2).
  { apply bad_live; auto.
    - apply bad_swf_raw; [apply bad_swf_t; exact SW|apply bad_lrange; lia].
    - apply bad_modewf_raw. apply bad_modewf_t.
    - apply bad_swf3_raw. apply bad_swf3_t.
    - cbn. pose proof (GWB MH) as WB. destruct BC as ((SO & _) & _). destruct SO as (WB0 & _). lia. }
  assert (ZF2 : zf_ok z2).
  { pose proof ZF0 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zf_ok. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler z2].
    rewrite AOT. unfold lrange in TIN, ADL.
    split; [change Integers.Int.max_unsigned with 4294967295; clear - N0 XL LX; lia|].
    split; [exact Z2|]. split; [exact TIN|]. split; [rewrite KT; split; [lia|unfold Integers.Int64.max_unsigned; cbn; lia]|].
    split; [change Integers.Int.min_signed with (-2147483648); change Integers.Int.max_signed with 2147483647; lia|].
    exact ADL. }
  assert (GL1 : glob_ok G (m_s m1)).
  { apply bad_glob_back with (m_s mT'); auto; cbn; try (compute; discriminate). }
  assert (CK1 : chk_ok G (m_s m1) [] []).
  { apply bad_chk_move with (m_s mT'); auto.
    - left. left. unfold md_type. destruct M as [M'|M']; [left|right; left]; exact M'.
    - left. left. unfold md_type. right; left. reflexivity. }
  pose proof (bad_bcont pos d x [] 0 z2 L2 m1 o res flush 0 0 0 P0 ltac:(clear - NX; lia) PL XE LX
                ltac:(clear - N0 XL; lia) ltac:(lia) EI DV2 LV2 ZF2 ltac:(cbn; rewrite AOT; exact AO)
                L0 eq_refl ltac:(left; left; unfold md_type; right; left; reflexivity) GL1 CK1
                ltac:(constructor) LP1 RO NM) as OUT.
  cbn [zf_ao z2] in OUT. rewrite AOT in OUT. exact OUT.
Qed.

(* the outcome of a call on another input of the same length (only m_inp differs) *)
Lemma bad_outcome_inp pos x out aout r m dt :
  0 <= m_snx m <= Zlength x -> m_sow m = Zlength (m_ow m) -> m_aout m = aout ->
  (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) ->
  (r <> Z_DATA_ERROR ->
     bad_phase G src (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\ i_head (m_s m) = false /\
     bytes_ok (out ++ m_ow m) /\ exists rest, full G = out ++ m_ow m ++ rest) ->
  bad_outcome pos x out aout (Res r (set_m_inp m x) dt).
Proof.
  intros A1 A2 A3 A4 A5. unfold bad_outcome. cbv zeta.
  change (m_snx (r_m (Res r (set_m_inp m x) dt))) with (m_snx m).
  change (m_sow (r_m (Res r (set_m_inp m x) dt))) with (m_sow m).
  change (m_ow (r_m (Res r (set_m_inp m x) dt))) with (m_ow m).
  change (m_aout (r_m (Res r (set_m_inp m x) dt))) with (m_aout m).
  change (m_inp (r_m (Res r (set_m_inp m x) dt))) with x.
  change (m_s (r_m (Res r (set_m_inp m x) dt))) with (m_s m).
  change (m_tout (r_m (Res r (set_m_inp m x) dt))) with (m_tout m).
  change (r_ret (Res r (set_m_inp m x) dt)) with r.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [reflexivity|]. split; [exact A4|exact A5].
Qed.

(* a call from the header *)
Lemma bad_run_hdr pos out z0 L x flush res :
  md_hdr (i_mode (l_s L)) -> dinv G pos out (l_s L) (zf_tout z0) -> live_ok L -> zf_ok z0 ->
  zf_ao z0 <= 2 ^ 32 - 1 -> Zlength x <= 2 ^ 32 - 1 -> 0 <= pos -> pos + Zlength x <= Zlength src ->
  x = sublist pos (pos + Zlength x) src ->
  run2 flush lenfix_list distfix_list (m_init z0 L x) res -> r_ret res <> Z_MEM_ERROR ->
  bad_outcome pos x out (zf_ao z0) res.
Proof.
  intros MH DV LV ZF0 AO LX P0 PL XE (o & LP & RO) NM.
  pose proof BC as (OK7 & HI & WR & ND & SRC).
  pose proof (dctx_ok7_7a _ OK7) as C.
  pose proof BS as (LS & BY & EA & NE).
  destruct (bad_raw_ok G src BC BS) as (_ & HL & _).
  assert (TS : tpos G <= slen G) by (unfold tpos; destruct (dc_w G); cbn; lia).
  assert (SL : Zlength (dc_src G) = slen G) by (unfold slen; rewrite SRC; reflexivity).
  set (inp' := sublist pos (pos + Zlength x) (dc_src G)).
  pose proof (Zlength_nonneg x) as X0.
  assert (XL : Zlength x = Zlength inp') by (unfold inp'; rewrite Zlength_sublist by lia; lia).
  assert (PL' : pos + Zlength inp' <= Zlength (dc_src G)) by lia.
  assert (IE : inp' = sublist pos (pos + Zlength inp') (dc_src G)) by (rewrite <- XL; reflexivity).
  assert (XB : bytes_ok x) by (rewrite XE; unfold bytes_ok in *; apply Forall_sublist; exact BY).
  assert (BI : bytes_ok inp').
  { destruct OK7 as (_ & _ & _ & _ & _ & _ & BYO & _). unfold inp', bytes_ok in *. apply Forall_sublist. exact BYO. }
  assert (XA : forall i, 0 <= i < Zlength x -> pos + i < hlen G -> Znth i x = Znth i inp').
  { intros i Hi Hh. unfold inp'. rewrite XE at 1. rewrite !Znth_sublist by lia.
    replace (i + pos) with (pos + i) by lia.
    assert (E := f_equal (Znth (pos + i)) EA). rewrite !Znth_sublist in E by lia. rewrite Z.add_0_r in E. exact E. }
  clearbody inp'.
  pose proof (bad_hdr_out _ _ _ _ _ (proj1 DV) MH) as Eo. subst out.
  destruct (KI G pos [] L z0 inp' C DV LV ZF0 AO ltac:(clear - XL LX; lia) BI) as [K0 W0].
  assert (EM : m_init z0 L x = set_m_inp (m_init z0 L inp') x) by (unfold m_init; rewrite XL; reflexivity).
  assert (MI : m_mode (m_init z0 L inp') = i_mode (l_s L)).
  { unfold m_mode, m_init. cbn. destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [E|E];
    [exfalso; rewrite E in MH; unfold md_hdr in MH; compute in MH; lia|reflexivity]. }
  destruct (bad_hloop DS SM G src pos inp' x [] flush BC BS C P0 PL' IE XL XB XA (m_init z0 L x) o LP
              (m_init z0 L inp') EM K0 W0 eq_refl ltac:(left; rewrite MI; exact MH))
    as [(mE' & LE & EO & IEq & NE' & OE & ME)|
        (mT' & K' & W' & L' & Mt & Nt & Bt & Ht & Lt & Ot & Hv & Ft & LPT)].
  - (* the call ends in the header or right at the start of the blocks *)
    subst o. destruct RO as [_ _|]; [cbn in NM; contradiction|].
    rewrite (bad_leave_inp flush mE' x ltac:(rewrite IEq; exact XL)) in NM |- *.
    set (R' := leave_fin flush mE') in *.
    assert (RUN' : run2 flush lenfix_list distfix_list (m_init z0 L inp') R')
      by (exists (IBrk mE'); split; [exact LE|apply il_ok]).
    destruct (DK G pos [] L z0 inp' flush R' C DV LV ZF0 AO ltac:(clear - XL LX; lia) P0 PL' IE RUN')
      as [MEM|(RC & SNX & SOW & MAO & (rest & PRE) & DVE & _ & SE & _)]; [contradiction|].
    destruct (bad_leave_basic flush mE') as (B1 & B2 & B3 & B4 & B5 & B6). fold R' in B1, B2, B3, B4, B5, B6.
    clearbody R'. rewrite OE in B2. cbn [m_init m_ow] in B2.
    assert (SNE : r_ret R' <> Z_STREAM_END).
    { intros E. destruct (SE E) as [_ E2]. rewrite B1 in E2. clear - E2 NE' HL TS. lia. }
    apply bad_outcome_inp; [clear - SNX XL; lia|exact SOW|exact MAO|
      destruct RC as [RC|[RC|RC]]; [left|right; left|contradiction]; exact RC|].
    intros _. rewrite B2 in *. cbn [app] in *.
    split; [|split; [exact (proj1 (proj2 (proj1 (proj2 DVE))))|split; [constructor|exists rest; exact PRE]]].
    rewrite <- B5 in ME.
    destruct ME as [ME|ME].
    + left. split; [exact ME|exact DVE].
    + right; left. apply bad_hdr_to_blk; [exact DVE|exact ME|rewrite B1; exact NE'].
  - (* the blocks begin in this call *)
    assert (AOT : m_aout mT' = zf_ao z0).
    { assert (V0 : URunFrame.vmode (m_mode (m_init z0 L x))).
      { unfold URunFrame.vmode. rewrite EM. change (m_mode (set_m_inp (m_init z0 L inp') x)) with (m_mode (m_init z0 L inp')).
        rewrite MI. unfold md_hdr in MH. unfold HEAD, BAD, FLAGS, TIME, OS in *. lia. }
      assert (V1 : URunFrame.vmode (m_mode (set_m_inp mT' x))).
      { unfold URunFrame.vmode. change (m_mode (set_m_inp mT' x)) with (m_mode mT').
        destruct Mt as [Mt|Mt]; rewrite Mt; unfold HEAD, BAD, Zlib.proof.inflate.Model.TYPE, TYPEDO; lia. }
      pose proof (bad_loop_aout flush (m_init z0 L x) (set_m_inp mT' x) o LP LPT V0 V1) as A. exact A. }
    cbn [m_init m_ow] in Ot.
    exact (bad_junction pos x z0 L flush o res inp' mT' P0 PL XE LX LV ZF0 AO XL K' W' L' Mt Nt Bt Ht Lt Ot Hv Ft
             LPT AOT RO NM).
Qed.

End Call.

(* ---------------------------------------------------------------------------------------------- *)
(* One call of the harness's loop                                                                 *)

Lemma bad_call (KI: kd_init7a_stmt) (DS: dc_step7a_stmt) (SM: stepf2_mwf3W_stmt) (DK: decode_call7a_stmt)
    wbits D O src pos out z L strmp flush ib inp o aout r z' st' ow :
  bad_inv wbits D O src pos out z L -> call_pre src pos z L strmp flush ib inp o aout ->
  pos + Zlength inp <= Zlength src ->
  inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp (Some o)
    r z' st' ow ->
  r <> Z_MEM_ERROR -> zf_ok z' ->
  exists L', call_post ib inp o aout z' st' ow L' /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\
    (r <> Z_DATA_ERROR -> bad_inv wbits D O src (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L').
Proof.
  intros (G & BC & SRC & FU & IW & BS & POS & PRE & HD & BO & PH)
         (LV & ZF & SN & FL & IB & INOK & OUTOK & LI & LA & INP) LE REL NM ZF'.
  destruct REL as [(BAD & _) | (_ & L0 & o0 & res & winp & EL & EO & RUN & _ & ER & EOW & EZ & _ & EST)].
  { exfalso. destruct BAD as [B | [B | [B _]]].
    - unfold is_live in B. match type of B with context [if ?c then _ else _] => destruct c end; congruence.
    - discriminate.
    - contradiction. }
  injection EL as <-. injection EO as <-.
  set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  assert (AO : 0 <= aout) by (destruct o; apply OUTOK).
  assert (ZF0 : zf_ok z0).
  { destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold z0, offer_z, zf_ok; cbn.
    unfold umax in *. pose proof (Zlength_nonneg inp).
    split; [lia|]. split; [lia|]. exact (conj Z3 (conj Z4 (conj Z5 Z6))). }
  assert (T0 : zf_tout z0 = zf_tout z) by reflexivity.
  assert (A0 : zf_ao z0 = aout) by reflexivity.
  unfold umax in *. subst r.
  assert (OUT : bad_outcome G src pos inp out aout res).
  { rewrite <- A0. rewrite <- T0 in PH.
    destruct PH as [(MH & DV)|[(HP & Md & (cc & CC & DV) & GL & CK)|PC]].
    - exact (bad_run_hdr KI DS SM DK G src BC BS pos out z0 L inp flush res MH DV LV ZF0 ltac:(cbn; lia) LI
               ltac:(lia) LE INP RUN NM).
    - exact (bad_run_blk KI DS SM DK G src BC BS pos out z0 L inp cc flush res HP Md CC DV GL CK BO LV ZF0
               ltac:(cbn; lia) LI ltac:(lia) LE INP RUN NM).
    - exact (bad_run_trl G src BC BS pos out z0 L inp flush res PC BO ZF0 ltac:(cbn; lia) LI
               ltac:(lia) LE INP RUN NM). }
  destruct OUT as (S1 & S2 & S3 & S4 & S5 & S6).
  set (m := r_m res) in *.
  assert (AI : zf_ai z' = Zlength inp - m_snx m) by (subst z'; unfold z_after; cbv zeta; cbn [zf_ai]; fold m; rewrite S4; reflexivity).
  assert (AOz : zf_ao z' = aout - Zlength ow) by (subst z' ow; unfold z_after; cbv zeta; cbn [zf_ao]; fold m; rewrite S3, S2; reflexivity).
  exists (Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  pose proof (Zlength_nonneg ow).
  destruct ZF' as (_ & ZA & _).
  split; [|split; [exact S5|]].
  - split; [exact EST|]. split; [lia|]. split; [lia|].
    split; [rewrite AI; subst z'; unfold z_after; cbv zeta; cbn [zf_ni]; fold m; f_equal; lia|].
    split; [rewrite AOz; subst z'; unfold z_after; cbv zeta; cbn [zf_no]; fold m; f_equal; rewrite S2; subst ow; lia|].
    lia.
  - intros ND. destruct (S6 ND) as (PH' & HD' & BO' & (rest & PRE')).
    replace (pos + (Zlength inp - zf_ai z')) with (pos + m_snx m) by lia.
    exists G. split; [exact BC|]. split; [exact SRC|]. split; [exact FU|]. split; [exact IW|]. split; [exact BS|].
    split; [lia|]. split; [exists rest; rewrite <- FU, PRE', EOW, app_assoc; reflexivity|].
    split; [exact HD'|]. split; [subst ow; exact BO'|].
    subst ow z'. unfold z_after; cbv zeta; cbn [zf_tout l_s]. exact PH'.
Qed.

Lemma bad_theory : dctx_stmt -> decode7a_stmt -> bad_stmt.
Proof.
  intros DC (DI & DK & KI & DS & SM). exists bad_inv. constructor.
  - exact bad_inv_ok.
  - exact bad_len.
  - intros wbits D O src z sp DF L64 _ W8 IO LS BS EA NE. exact (bad_init DC DI wbits D O src z sp DF L64 W8 IO LS BS EA NE).
  - intros. eapply bad_call; eauto.
Qed.

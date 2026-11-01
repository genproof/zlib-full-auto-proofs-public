(* RT-D part DEFLATE, stage 8: the parts of kf_comp_ok (RTDDgComp.v).
   - [kfull_stmt]: deflate()'s Z_FULL_FLUSH reset (CLEAR_HASH = clear_hash_eq's head of zeros, then strstart,
     block_start, insert := 0 when lookahead = 0) after a block_done (nothing tallied, everything read in
     blocks) keeps kcore3 with the same blocks;
   - [kbd_stmt]: the block_done tail of c_deflate_compress ([bd_tail]: _tr_align / the empty stored block (+ the
     full-flush reset) / nothing for Z_BLOCK, then flush_pending) appends zero or one block to the blocks BS:
     the bits are still the header's then Format's encoding of the blocks, kcore3 holds. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDDgDefs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Definition kfull_stmt : Prop :=
  forall dict D BS syms s,
    W3 s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    kcore3 dict D BS syms s ->
    kcore3 dict D BS syms (full_reset (set_d_slid (set_d_head s (repeat 0 (Z.to_nat (d_hash_size s)))) 0)).

Lemma kfull_chain0 : forall s, (forall b, Znth b (d_head s) = 0) -> chain_hok s.
Proof.
  intros s Hz b Hb. exists (fun q => q = 0). split; [apply Hz|]. intros q Hq Hq'. lia.
Qed.

Lemma kfull_ok : kfull_stmt.
Proof.
  intros dict D BS syms s HW Hsn Hla Hss HK.
  pose proof (W3_prm s HW) as HP.
  destruct HW as [[HW0 _] _].
  destruct HW0 as (_ & _ & _ & _ & _ & HM & _).
  destruct HK as [(K1 & K2 & K3 & K4 & K5 & K6 & K7) [K8 K9]].
  assert (Hsy : syms = []).
  { destruct K3 as ((_ & _ & T & _) & _). unfold d_sym_next in Hsn. rewrite Hsn in T.
    destruct syms; [reflexivity|]. rewrite Zlength_cons in T. pose proof (Zlength_nonneg syms). lia. }
  subst syms.
  assert (Hma : d_match_available s = 0).
  { destruct HM as (_ & _ & [E|E] & _ & HM1); [exact E|].
    destruct (HM1 E) as (Hf & _).
    destruct K3 as (_ & _ & _ & _ & Hb).
    assert (d_level s <> 0) by (intro L0; unfold fn_of in Hf; rewrite L0 in Hf; discriminate).
    specialize (Hb H). cbn in Hb. lia. }
  assert (Hw : 0 < d_w_size s).
  { destruct HP as (Hwb & Hws & _). rewrite Hws. apply Z.pow_pos_nonneg; lia. }
  set (n := Z.to_nat (d_hash_size s)).
  assert (Hhz : forall b, Znth b (repeat 0 n) = 0) by (intro b; apply (@Znth_repeat Z 0)).
  assert (Hsl : forall b, Znth b (map (slide_entry (d_w_size s)) (repeat 0 n)) = 0).
  { intro b. rewrite map_repeat. unfold slide_entry.
    destruct (0 >=? d_w_size s) eqn:E; [rewrite Z.geb_le in E; lia|]. apply Hhz. }
  set (s' := full_reset (set_d_slid (set_d_head s (repeat 0 n)) 0)).
  assert (E1 : d_strstart s' = 0) by reflexivity.
  assert (E2 : d_block_start s' = 0) by reflexivity.
  assert (E3 : d_lookahead s' = d_lookahead s) by reflexivity.
  assert (E4 : d_tr s' = d_tr s) by reflexivity.
  assert (E5 : d_pbm s' = d_pbm s) by reflexivity.
  assert (E6 : d_w_bits s' = d_w_bits s) by reflexivity.
  assert (E7 : d_w_size s' = d_w_size s) by reflexivity.
  assert (E8 : d_head s' = repeat 0 n) by reflexivity.
  assert (E9 : d_match_available s' = d_match_available s) by reflexivity.
  assert (E10 : d_hash_size s' = d_hash_size s) by reflexivity.
  clearbody s'.
  unfold kcore3, kdata3 in *. cbv zeta in *.
  unfold kwin, kmatch3, wtrees, tree_ok, khash, d_L, d_level, d_strategy, d_matches, d_sym_next in *.
  rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E9.
  rewrite Hla, Hma in *.
  set (H := dict ++ D) in *.
  assert (Hoff : Zlength H - (d_strstart s + 0) + d_block_start s = Zlength H) by lia.
  split; [|split].
  - split; [split; [rewrite Z.add_0_r; apply Zlength_nonneg | intros i Hi; lia]|].
    split; [intros E; discriminate|].
    split.
    + destruct K3 as (T & T2 & _ & _ & _). split; [exact T|]. split; [exact T2|].
      split; [constructor|]. split; [reflexivity|]. intros _. cbn. lia.
    + split; [exact K4|]. rewrite Z.sub_0_r, Z.add_0_r.
      split; [rewrite K5, Hoff; reflexivity|]. split; [exact K6|].
      rewrite K7. f_equal. destruct (tr_level (d_tr s) =? 0); lia.
  - destruct (tr_level (d_tr s) =? 0).
    + destruct K8 as [(E & _) | [(E & _) | E]].
      * left. split; [exact E|]. apply kfull_chain0. intro b. rewrite E8. apply Hhz.
      * right; left. split; [exact E|]. apply kfull_chain0. intro b. unfold slide_hc.
        cbn [d_head set_d_prev set_d_head]. rewrite E8, E7. apply Hsl.
      * right; right. exact E.
    + apply kfull_chain0. intro b. rewrite E8. apply Hhz.
  - intros _ Hm. unfold MIN_MATCH in Hm. lia.
Qed.

Definition kbd_stmt : Prop :=
  forall dict D O BS syms HDR s z flush s' z' o,
    W3 s -> outok s -> quiet s -> d_sym_next s = 0 -> d_lookahead s = 0 -> d_strstart s = d_block_start s ->
    flush <> Z_NO_FLUSH -> flush <> Z_FINISH -> 0 <= flush <= 5 ->
    0 <= z_avail_out z <= 1073741824 -> 0 <= z_total_out z <= 1099511627776 ->
    kcore3 dict D BS syms s ->
    allbits O s = F.bytes_bits HDR ++ enc_from 0 BS false ->
    bd_tail s z flush = Some (s', z', o) ->
    exists x BS' syms',
      zout_only z z' x /\
      d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s /\
      d_w_bits s' = d_w_bits s /\
      kcore3 dict D (BS ++ BS') syms' s' /\
      allbits (O ++ x) s' = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false.

(** ** Helpers of kbd_ok *)
Lemma kbd_enc_from_snoc : forall BS p b,
  enc_from p (BS ++ [b]) false = enc_from p BS false ++ F.enc_block (p + Zlength (enc_from p BS false)) false b.
Proof.
  induction BS as [|c r IH]; intros p b.
  - cbn [app enc_from andb]. rewrite Zlength_nil, Z.add_0_r, !app_nil_r. reflexivity.
  - cbn [app enc_from andb]. rewrite IH, Zlength_app, Z.add_assoc, app_assoc. reflexivity.
Qed.

Lemma kbd_bits_le_len : forall v n, 0 <= n -> Zlength (F.bits_le v n) = n.
Proof. intros v n Hn. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma kbd_bytes_bits_app : forall l1 l2, F.bytes_bits (l1 ++ l2) = F.bytes_bits l1 ++ F.bytes_bits l2.
Proof. intros l1 l2. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma kbd_bytes_bits_len : forall l, Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b r IH]; [reflexivity|].
  change (F.bytes_bits (b :: r)) with (F.bits_le b 8 ++ F.bytes_bits r).
  rewrite Zlength_app, IH, kbd_bits_le_len, Zlength_cons by lia. lia.
Qed.

Lemma kbd_allbits_po0 : forall O s, d_po s = 0 ->
  allbits O s = F.bytes_bits O ++ obits (tr_out (d_tr s)).
Proof.
  intros O s H. unfold allbits, pend, obits, bibits, d_bi_valid, d_pending. rewrite H, Z.add_0_l.
  rewrite kbd_bytes_bits_app, app_assoc. reflexivity.
Qed.

Lemma kbd_kcore3_snoc : forall dict D BS syms s b,
  kcore3 dict D BS syms s -> F.block_ok (2 ^ d_w_bits s) (F.expand dict BS) b ->
  F.block_data (F.expand dict BS) b = F.expand dict BS -> kcore3 dict D (BS ++ [b]) syms s.
Proof.
  intros dict D BS syms s b [(A1 & A2 & A3 & A4 & A5 & A6 & A7) A8] Hb He.
  assert (E : F.expand dict (BS ++ [b]) = F.expand dict BS).
  { unfold F.expand. rewrite fold_left_app. exact He. }
  split; [|exact A8]. unfold kdata3. rewrite E.
  refine (conj A1 (conj A2 (conj A3 (conj _ (conj A5 (conj A6 A7)))))).
  clear -A4 Hb. unfold F.expand in Hb. revert A4 Hb. generalize dict as out.
  induction BS as [|c r IH]; intros out H1 H2; cbn in *.
  - tauto.
  - destruct H1 as [Hc Hr]. split; auto.
Qed.

Lemma kbd_core_eq_lf : forall s v, core_eq s (set_d_last_flush s v).
Proof.
  intros s v. pose proof (core_eq_api_setters s (d_status s) v (d_wrap s) (d_gzhead s)) as H.
  destruct s; exact H.
Qed.

Lemma kbd_ok : kfull_stmt -> writer_fspec -> stored_block_fspec -> align_fspec -> fpend_fspec2 -> kbd_stmt.
Proof.
  intros KF _ SB AL FP dict D O BS syms HDR s z flush s' z' o HW Ho Hq Hsym Hla Hss Hf1 Hf2 Hfr Hao Hto HK HA Hbd.
  set (p := Zlength (enc_from 0 BS false)).
  assert (Hps : pend s = []).
  { destruct Hq as (Q1 & Q2 & _). unfold pend. rewrite Q1, Q2. apply sublist_nil. }
  assert (Hbo : bits_ok (tr_out (d_tr s))) by exact (proj1 (proj2 Ho)).
  assert (Hbv0 : 0 <= d_bi_valid s) by (destruct Hbo as [? _]; unfold d_bi_valid; lia).
  assert (HL : 8 * Zlength O + d_bi_valid s = 8 * Zlength HDR + p).
  { apply (f_equal (@Zlength bool)) in HA. unfold allbits in HA.
    rewrite Hps, app_nil_r, !Zlength_app, !kbd_bytes_bits_len in HA. unfold bibits in HA.
    rewrite kbd_bits_le_len in HA by exact Hbv0. exact HA. }
  assert (Hp0 : 0 <= p) by (unfold p; apply Zlength_nonneg).
  assert (Hpm : (p - o_bi_valid (tr_out (d_tr s))) mod 8 = 0).
  { change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s).
    replace (p - d_bi_valid s) with ((Zlength O - Zlength HDR) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hob : obits (tr_out (d_tr s)) = bibits s).
  { unfold obits, bibits, d_bi_valid. destruct Hq as (Q1 & _).
    change (o_pending (tr_out (d_tr s))) with (d_pending s). rewrite Q1, sublist_nil. reflexivity. }
  assert (HA0 : allbits O s = F.bytes_bits O ++ bibits s).
  { rewrite kbd_allbits_po0 by exact (proj1 (proj2 Hq)). rewrite Hob. reflexivity. }
  (* the bits after one more block b appended by the writer *)
  assert (HB : forall s1 b, d_po s1 = 0 ->
      obits (tr_out (d_tr s1)) = obits (tr_out (d_tr s)) ++ F.enc_block p false b ->
      allbits O s1 = F.bytes_bits HDR ++ enc_from 0 (BS ++ [b]) false).
  { intros s1 b P1 E1. rewrite kbd_allbits_po0 by exact P1. rewrite E1, Hob, app_assoc, <- HA0, HA.
    rewrite kbd_enc_from_snoc, <- app_assoc. reflexivity. }
  unfold bd_tail in Hbd.
  match type of Hbd with @eq _ (bind ?X _) _ =>
    assert (S1 : exists s2 BS', X = Some s2 /\ outok s2 /\ d_bi_valid s2 <= 7 /\
      d_status s2 = d_status s /\ d_wrap s2 = d_wrap s /\ d_gzhead s2 = d_gzhead s /\
      d_w_bits s2 = d_w_bits s /\ kcore3 dict D (BS ++ BS') syms s2 /\
      allbits O s2 = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false) end.
  { pose proof (W3_prm s HW) as HP.
    destruct (flush =? Z_PARTIAL_FLUSH).
    - destruct (tr_align_ok s HP Ho Hq Hsym) as (om & E & O1 & C1 & A1 & P1 & B1 & _).
      destruct om as [o1 m1].
      destruct (AL _ _ o1 m1 p Hbo E) as (_ & _ & Eo).
      rewrite E. cbn [bind]. exists (set_d_out s (o1, m1)), [F.Fixed []].
      destruct A1 as (A1 & A2 & A3 & _).
      destruct (core_eq_fields _ _ C1) as (_ & _ & Fw & _).
      split; [reflexivity|]. split; [exact O1|]. split; [exact B1|].
      do 4 (split; [assumption|]). split.
      + apply kbd_kcore3_snoc; [exact (kcore3_frame _ _ _ _ _ _ C1 HK)|exact I|reflexivity].
      + apply HB; [exact P1|exact Eo].
    - destruct (flush =? Z_BLOCK); cbn [negb].
      + exists s, []. rewrite app_nil_r. split; [reflexivity|]. split; [exact Ho|].
        split; [exact (proj2 (proj2 Hq))|]. do 4 (split; [reflexivity|]). split; [exact HK|exact HA].
      + destruct (stored_empty_ok s HP Ho Hq Hsym) as (om & E & O1 & C1 & A1 & P1 & B1 & _).
        destruct om as [o1 m1].
        destruct (SB _ _ [] 0 0 o1 m1 p Hbo ltac:(lia) ltac:(lia) (or_introl eq_refl)
                    ltac:(rewrite sublist_nil; constructor) Hp0 Hpm E) as (_ & _ & Eo).
        rewrite E. cbn [bind].
        set (s1 := set_d_out s (o1, m1)) in *.
        assert (K1 : kcore3 dict D (BS ++ [F.Stored (sublist 0 0 [])]) syms s1).
        { apply kbd_kcore3_snoc; [exact (kcore3_frame _ _ _ _ _ _ C1 HK)| |].
          - rewrite sublist_nil. cbn. split; [lia|constructor].
          - rewrite sublist_nil. cbn. apply app_nil_r. }
        assert (AB1 : allbits O s1 = F.bytes_bits HDR ++ enc_from 0 (BS ++ [F.Stored (sublist 0 0 [])]) false).
        { apply HB; [exact P1|exact Eo]. }
        destruct A1 as (A1 & A2 & A3 & _).
        destruct (core_eq_fields _ _ C1) as (_ & _ & Fw & _ & Fb & Fs & Fl & _ & Fn & _).
        destruct (flush =? Z_FULL_FLUSH).
        * assert (W1 : W3 s1) by exact (W3_frame s s1 HW C1).
          assert (Hws : wstruct s1) by (destruct W1 as [[[_ [X _]] _] _]; exact X).
          rewrite (Zlib.proof.roundtrip.RTDLTCMisc.clear_hash_eq s1 (W3_prm s1 W1) Hws). cbn [bind].
          change (d_lookahead (set_d_slid (set_d_head s1 (repeat 0 (Z.to_nat (d_hash_size s1)))) 0))
            with (d_lookahead s1).
          rewrite Fl, Hla. cbn [Z.eqb].
          exists (full_reset (set_d_slid (set_d_head s1 (repeat 0 (Z.to_nat (d_hash_size s1)))) 0)),
            [F.Stored (sublist 0 0 [])].
          split; [reflexivity|]. split; [exact O1|]. split; [change (d_bi_valid s1 <= 7); lia|].
          do 4 (split; [assumption|]). split.
          -- apply KF; [exact W1|congruence|congruence|congruence|exact K1].
          -- exact AB1.
        * exists s1, [F.Stored (sublist 0 0 [])].
          split; [reflexivity|]. split; [exact O1|]. split; [lia|].
          do 4 (split; [assumption|]). split; [exact K1|exact AB1]. }
  destruct S1 as (s2 & BS' & E1 & O2 & B2 & St2 & Wr2 & G2 & Wb2 & K2 & A2).
  rewrite E1 in Hbd. cbn [bind] in Hbd.
  destruct (flush_pending_ok s2 z O2 B2 Hao Hto) as (s3 & x & E3 & _ & _ & _ & O3 & C3 & A3 & _).
  destruct (FP s2 z _ _ O2 ltac:(unfold zout_ok; lia) ltac:(left; lia) E3) as (x' & Zx & Bx).
  rewrite E3 in Hbd. cbn [bind] in Hbd.
  destruct A3 as (A31 & A32 & A33 & _).
  destruct (core_eq_fields _ _ C3) as (_ & _ & Fw3 & _).
  assert (K3 : kcore3 dict D (BS ++ BS') syms s3) by exact (kcore3_frame _ _ _ _ _ _ C3 K2).
  assert (AB3 : allbits (O ++ x') s3 = F.bytes_bits HDR ++ enc_from 0 (BS ++ BS') false).
  { rewrite <- A2. unfold allbits. rewrite <- app_assoc, !kbd_bytes_bits_app, <- !app_assoc.
    f_equal. rewrite <- Bx, kbd_bytes_bits_app, <- app_assoc. reflexivity. }
  exists x', BS', syms.
  destruct (_ =? 0); inversion Hbd; subst; clear Hbd.
  - split; [exact Zx|]. cbn [d_status d_wrap d_gzhead d_w_bits set_d_last_flush].
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [exact (kcore3_frame _ _ _ _ _ _ (kbd_core_eq_lf s3 (-1)) K3)|exact AB3].
  - split; [exact Zx|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [exact K3|exact AB3].
Qed.

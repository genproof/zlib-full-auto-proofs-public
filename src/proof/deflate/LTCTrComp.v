(** * TREES part, sub-part COMP: see LTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCTrKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Checked bit output runs when the model's output stays inside pending_buf *)

Lemma cc_rd_in l i : 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros H. unfold rd, in_range.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma cc_put_byte o m c : 0 <= o_pending o < Zlength (o_buf o) ->
  c_put_byte (o, m) c = Some (put_byte o c, upd_Znth (o_pending o) m true).
Proof.
  intros H. rewrite c_put_byte_spec. unfold in_range.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma cc_send_bits o m v l :
  0 <= o_bi_valid o <= 16 -> 0 <= o_pending o ->
  o_pending (send_bits o v l) <= Zlength (o_buf o) ->
  exists m', c_send_bits (o, m) v l = Some (send_bits o v l, m').
Proof.
  intros Hv Hp Hl. unfold c_send_bits.
  replace (guard ((0 <=? o_bi_valid o) && (o_bi_valid o <=? Buf_size))) with (Some tt)
    by (unfold guard, Buf_size; rewrite (proj2 (Z.leb_le _ _)) by lia; rewrite (proj2 (Z.leb_le _ _)) by lia;
        reflexivity).
  cbn [bind].
  unfold send_bits in Hl |- *.
  destruct (o_bi_valid o >? Buf_size - l).
  - cbn [o_pending set_bits put_short put_byte o_buf] in Hl. unfold c_put_short.
    rewrite cc_put_byte by (cbn [o_pending set_bits o_buf]; lia). cbn [bind].
    rewrite cc_put_byte by (cbn [o_pending set_bits o_buf put_byte]; rewrite Zlength_upd_Znth_any; lia).
    cbn [bind]. eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma cc_send_code o m c codes lens :
  0 <= c < Zlength lens -> 0 <= c < Zlength codes ->
  0 <= o_bi_valid o <= 16 -> 0 <= o_pending o ->
  o_pending (send_code o c codes lens) <= Zlength (o_buf o) ->
  exists m', c_send_code (o, m) c codes lens = Some (send_code o c codes lens, m').
Proof.
  intros H1 H2 Hv Hp Hl. unfold c_send_code.
  rewrite (cc_rd_in lens c H1). cbn [bind]. rewrite (cc_rd_in codes c H2). cbn [bind].
  apply cc_send_bits; auto.
Qed.

Lemma cc_tabs : Zlength length_code_tab = 256 /\ Zlength extra_lbits = 29 /\ Zlength base_length_tab = 29 /\
  Zlength dist_code_tab = 512 /\ Zlength extra_dbits = 30 /\ Zlength base_dist_tab = 30.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma cc_d_code d : 0 <= d <= 32767 -> c_d_code d = Some (d_code d).
Proof.
  intros Hd. destruct cc_tabs as [_ [_ [_ [T _]]]]. unfold c_d_code, d_code.
  destruct (Z.ltb_spec d 256).
  - apply cc_rd_in. lia.
  - apply cc_rd_in. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 7) with 128.
    assert (0 <= d / 128) by (apply Z.div_pos; lia).
    assert (d / 128 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma cc_writes_pending o o' : writes o o' -> o_pending o <= o_pending o' /\ Zlength (o_buf o') = Zlength (o_buf o).
Proof. intros [A [B _]]. auto. Qed.

Lemma cc_send_symbol o m lcodes llens dcodes dlens dist lc :
  bits_ok o -> valid_sym dist lc -> sym_codes_ok lcodes llens dcodes dlens dist lc ->
  L_CODES <= Zlength lcodes -> L_CODES <= Zlength llens -> D_CODES <= Zlength dcodes -> D_CODES <= Zlength dlens ->
  o_pending (send_symbol o lcodes llens dcodes dlens dist lc) <= Zlength (o_buf o) ->
  exists m', c_send_symbol (o, m) lcodes llens dcodes dlens dist lc =
             Some (send_symbol o lcodes llens dcodes dlens dist lc, m').
Proof.
  intros Ho [Hlc Hd] Hc HL1 HL2 HD1 HD2 Hl.
  destruct cc_tabs as [T1 [T2 [T3 [T4 [T5 T6]]]]].
  assert (Hok := Ho). destruct Hok as [Hv [Hb Hp]].
  unfold L_CODES, D_CODES in *.
  unfold c_send_symbol, send_symbol, sym_codes_ok, LITERALS in *.
  destruct (Z.eqb_spec dist 0) as [Hd0|Hd0].
  - apply cc_send_code; auto; lia.
  - destruct Hc as [[Hl1 Hc1] [Hl2 Hc2]].
    destruct (length_code_facts lc Hlc) as [Hcode [Hx Hext]].
    destruct (dist_code_facts (dist - 1) ltac:(lia)) as [Hdcode [Hdx Hdext]].
    rewrite (cc_rd_in length_code_tab lc) by lia. cbn [bind].
    set (code := Znth lc length_code_tab) in *.
    set (dcode := d_code (dist - 1)) in *.
    replace (code + 256 + 1) with (code + 257) in * by lia.
    set (o1 := send_code o (code + 257) lcodes llens) in *.
    destruct (send_code_spec o (code + 257) lcodes llens Ho (conj Hl1 Hc1)) as [_ [_ [Ho1 [_ W1]]]].
    fold o1 in Ho1, W1.
    set (o2 := if negb (Znth code extra_lbits =? 0)
               then send_bits o1 (lc - Znth code base_length_tab) (Znth code extra_lbits) else o1) in *.
    assert (Ho2 : bits_ok o2 /\ writes o1 o2).
    { unfold o2. destruct (Z.eqb_spec (Znth code extra_lbits) 0) as [E|E]; simpl.
      - split; [exact Ho1|apply writes_refl].
      - destruct (send_bits_spec o1 (lc - Znth code base_length_tab) (Znth code extra_lbits)) as [_ [_ [B [_ W]]]];
          auto; lia. }
    destruct Ho2 as [Ho2 W2].
    set (o3 := send_code o2 dcode dcodes dlens) in *.
    destruct (send_code_spec o2 dcode dcodes dlens Ho2 (conj Hl2 Hc2)) as [_ [_ [Ho3 [_ W3]]]].
    fold o3 in Ho3, W3.
    set (o4 := if negb (Znth dcode extra_dbits =? 0)
               then send_bits o3 (dist - 1 - Znth dcode base_dist_tab) (Znth dcode extra_dbits) else o3) in *.
    assert (W4 : writes o3 o4).
    { unfold o4. destruct (negb (Znth dcode extra_dbits =? 0)); [apply send_bits_writes|apply writes_refl]. }
    apply cc_writes_pending in W1, W2, W3, W4.
    destruct Ho1 as [Hv1 [_ Hp1]]. destruct Ho2 as [Hv2 [_ Hp2]]. destruct Ho3 as [Hv3 [_ Hp3]].
    destruct (cc_send_code o m (code + 257) lcodes llens ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold o1; lia))
      as [m1 E1].
    fold o1. rewrite E1. cbn [bind].
    rewrite (cc_rd_in extra_lbits code) by lia. cbn [bind].
    assert (E2 : exists m2, (if negb (Znth code extra_lbits =? 0) then
                   let* bl := rd base_length_tab code in
                   c_send_bits (o1, m1) (lc - bl) (Znth code extra_lbits) else Some (o1, m1)) = Some (o2, m2)).
    { clearbody o3 o4. unfold o2 in *. destruct (negb (Znth code extra_lbits =? 0)).
      - rewrite (cc_rd_in base_length_tab code) by lia. cbn [bind]. apply cc_send_bits; lia.
      - eexists; reflexivity. }
    destruct E2 as [m2 E2]. fold o1.
    match goal with |- exists _, bind ?x _ = _ => replace x with (Some (o2, m2)) by (symmetry; exact E2) end. cbn [bind].
    rewrite cc_d_code by lia. cbn [bind]. fold dcode.
    destruct (cc_send_code o2 m2 dcode dcodes dlens ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold o3; lia))
      as [m3 E3].
    fold o3. rewrite E3. cbn [bind]. fold o3.
    rewrite (cc_rd_in extra_dbits dcode) by lia. cbn [bind].
    unfold o4 in Hl |- *. destruct (negb (Znth dcode extra_dbits =? 0)).
    + rewrite (cc_rd_in base_dist_tab dcode) by lia. cbn [bind]. apply cc_send_bits; lia.
    + eexists; reflexivity.
Qed.

Lemma cc_rd_pb o m i : 0 <= i < Zlength (o_buf o) -> Znth i m = true -> c_rd_pb (o, m) i = Some (Znth i (o_buf o)).
Proof.
  intros H1 H2. unfold c_rd_pb, in_range.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite H2. reflexivity.
Qed.

Lemma cc_compress_loop : forall rest fuel o m sx L sym_next lcodes llens dcodes dlens,
  rest <> [] -> (length rest <= fuel)%nat -> sym_next = sx + 3 * Zlength rest -> 0 <= sx -> 0 <= L ->
  bits_ok o -> Zlength m = Zlength (o_buf o) -> L + sym_next <= Zlength (o_buf o) ->
  L_CODES <= Zlength lcodes -> L_CODES <= Zlength llens -> D_CODES <= Zlength dcodes -> D_CODES <= Zlength dlens ->
  (forall s, In s rest -> valid_sym (fst s) (snd s) /\ sym_codes_ok lcodes llens dcodes dlens (fst s) (snd s)) ->
  (forall i, 0 <= i < 3 * Zlength rest -> Znth (L + sx + i) (o_buf o) = Znth i (sym_bytes rest)) ->
  (forall i, 0 <= i < 3 * Zlength rest -> Znth (L + sx + i) m = true) ->
  (forall k, (1 <= k <= length rest)%nat ->
     o_pending (compress_sep o lcodes llens dcodes dlens (firstn k rest)) <= L + sx + 3 * Z.of_nat k) ->
  exists m', c_compress_loop fuel L sym_next lcodes llens dcodes dlens (o, m) sx =
             Some (compress_sep o lcodes llens dcodes dlens rest, m').
Proof.
  induction rest as [|[d l] r IH];
    intros fuel o m sx L sym_next lcodes llens dcodes dlens Hne Hf Hsn Hsx HL Ho Hm Hlen HL1 HL2 HD1 HD2 Hs Hb Hmk Hp;
    [congruence|].
  destruct fuel as [|fuel]; [simpl in Hf; lia|].
  assert (Hlen' : Zlength ((d, l) :: r) = 1 + Zlength r) by (rewrite Zlength_cons; pose proof (Zlength_nonneg r); lia).
  assert (Hr0 := Zlength_nonneg r).
  destruct (Hs (d, l) (or_introl eq_refl)) as [Hv Hc]. cbn [fst snd] in Hv, Hc.
  assert (B0 := Hb 0 ltac:(lia)). assert (B1 := Hb 1 ltac:(lia)). assert (B2 := Hb 2 ltac:(lia)).
  rewrite sym_bytes_cons in B0, B1, B2. rewrite Z.add_0_r in B0.
  rewrite Znth_0_cons in B0. rewrite Znth_pos_cons, Znth_0_cons in B1 by lia.
  rewrite !Znth_pos_cons, Znth_0_cons in B2 by lia. cbn [fst snd] in B0, B1, B2.
  assert (M0 := Hmk 0 ltac:(lia)). assert (M1 := Hmk 1 ltac:(lia)). assert (M2 := Hmk 2 ltac:(lia)).
  rewrite Z.add_0_r in M0.
  cbn [c_compress_loop compress_sep].
  rewrite (cc_rd_pb o m (L + sx)) by first [lia|assumption]. cbn [bind].
  rewrite (cc_rd_pb o m (L + sx + 1)) by first [lia|assumption]. cbn [bind].
  rewrite (cc_rd_pb o m (L + sx + 2)) by first [lia|assumption]. cbn [bind].
  rewrite B0, B1, B2, read_dist by (destruct Hv; lia).
  assert (Hp1 := Hp 1%nat ltac:(simpl; lia)). simpl firstn in Hp1. cbn [compress_sep] in Hp1.
  set (o1 := send_symbol o lcodes llens dcodes dlens d l) in *.
  destruct (cc_send_symbol o m lcodes llens dcodes dlens d l Ho Hv Hc HL1 HL2 HD1 HD2 ltac:(fold o1; lia))
    as [m1 E1].
  pose proof (capp _ _ E1) as A1. cbn [o_pending] in A1. destruct A1 as [_ [A1l A1]].
  fold o1. rewrite E1. cbn [bind].
  destruct (send_symbol_spec o lcodes llens dcodes dlens d l Ho Hv Hc) as [[W1 [Ho1 _]] _]. fold o1 in W1, Ho1.
  destruct (Z.ltb_spec (sx + 3) sym_next) as [Hlt|Hge].
  - destruct r as [|s r']; [rewrite Hsn in Hlt; simpl in Hlt; lia|].
    apply IH; auto.
    + congruence.
    + simpl in Hf |- *; lia.
    + rewrite Hsn, Hlen'; lia.
    + lia.
    + destruct W1 as [_ [W1l _]]. lia.
    + destruct W1 as [_ [W1l _]]. lia.
    + intros s0 Hs0; apply Hs; right; auto.
    + intros i Hi.
      destruct W1 as [_ [_ [_ W]]].
      rewrite W by (right; lia).
      replace (L + (sx + 3) + i) with (L + sx + (i + 3)) by lia.
      rewrite Hb by lia. rewrite sym_bytes_cons, !Znth_pos_cons by lia.
      replace (i + 3 - 1 - 1 - 1) with i by lia; reflexivity.
    + intros i Hi. rewrite A1 by lia.
      destruct (_ && _); [reflexivity|].
      replace (L + (sx + 3) + i) with (L + sx + (i + 3)) by lia. apply Hmk. lia.
    + intros k Hk.
      assert (Hk' := Hp (S k) ltac:(simpl in Hk |- *; lia)). simpl firstn in Hk'. cbn [compress_sep] in Hk'.
      fold o1 in Hk'. rewrite Nat2Z.inj_succ in Hk'. lia.
  - destruct r as [|s r']; [eexists; reflexivity|].
    rewrite Hsn in Hge. rewrite !Zlength_cons in Hge. assert (Hz := Zlength_nonneg r'). lia.
Qed.

(** The END_BLOCK code after a bit position [b]: the output stays below [pending] + 2 of [8 * p + 16 > b + 15]. *)
Lemma cc_end_block o m lcodes llens P :
  bits_ok o -> code_ok lcodes llens END_BLOCK -> L_CODES <= Zlength lcodes -> L_CODES <= Zlength llens ->
  bitpos o + 15 < 8 * P -> P <= Zlength (o_buf o) ->
  exists m', c_send_code (o, m) END_BLOCK lcodes llens = Some (send_code o END_BLOCK lcodes llens, m').
Proof.
  intros Ho Hc HL1 HL2 Hb HP.
  destruct (send_code_spec o END_BLOCK lcodes llens Ho Hc) as [B [V [_ [_ _]]]].
  destruct Hc as [Hl _]. assert (Ho' := Ho). destruct Ho' as [Hv [_ Hp]].
  unfold L_CODES, END_BLOCK, bitpos in *.
  apply cc_send_code; try lia.
Qed.

Theorem comp_some : comp_statement.
Proof.
  intros L syms o m lcodes llens dcodes dlens Hv Hov Hn Hm Hmk HL1 HL2 HD1 HD2.
  destruct (overlay_compress L syms o lcodes llens dcodes dlens Hv Hov) as [Hcb Hp].
  destruct Hov as [Hok [Hlen [Hsy [Hcodes [Hend Hbits]]]]].
  rewrite Hcb.
  assert (Hn0 := Zlength_nonneg syms).
  assert (Hs : forall s, In s syms -> valid_sym (fst s) (snd s) /\ sym_codes_ok lcodes llens dcodes dlens (fst s) (snd s))
    by (intros s Hs; split; auto).
  destruct (compress_sep_spec syms o lcodes llens dcodes dlens Hok Hs) as [[W [Ho' _]] _].
  destruct W as [_ [Wl _]].
  assert (Hb := Hbits (length syms) ltac:(lia)). rewrite firstn_all in Hb.
  rewrite <- Zlength_correct in Hb.
  unfold c_compress_block.
  destruct syms as [|s0 r].
  - rewrite Zlength_nil in *. cbn [Z.mul Z.eqb negb]. cbn [bind compress_sep] in *.
    apply (cc_end_block o m lcodes llens (4 * L)); auto; lia.
  - assert (Hpos : 0 < Zlength (s0 :: r)) by (rewrite Zlength_cons; pose proof (Zlength_nonneg r); lia).
    rewrite (proj2 (Z.eqb_neq (3 * Zlength (s0 :: r)) 0)) by lia. cbn [negb].
    destruct (cc_compress_loop (s0 :: r) (Z.to_nat (3 * Zlength (s0 :: r))) o m 0 L (3 * Zlength (s0 :: r))
                lcodes llens dcodes dlens) as [m1 E1]; try lia.
    + congruence.
    + rewrite Zlength_correct in *. lia.
    + exact Hok.
    + exact Hs.
    + intros i Hi. rewrite Z.add_0_r. auto.
    + intros i Hi. rewrite Z.add_0_r. auto.
    + intros k Hk. rewrite Z.add_0_r. assert (H := Hp k Hk). lia.
    + rewrite E1. cbn [bind].
      apply (cc_end_block _ m1 lcodes llens (4 * L)); auto; lia.
Qed.

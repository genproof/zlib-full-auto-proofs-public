(* Law rj_bad_block with clip() pieces (BBWDefs.v): the facts about the stream and the first passes of inflate()
   that the theory (BBWTheory.v) needs beyond BBRun.v.
   - `bbw_bits`, `bbw_layout`: BBFacts.bb_bits_stmt and BBRun.bbt_layout for the inputs of BBWDefs.bbw_ok (any
     number of literals, any length of the stream);
   - `bbw_refused`: kinds 0, 1 and 4 are refused by a call offered any prefix of at least 5 bytes of the stream
     (the header reads at most the first 5);
   - `bbw_bad_call`: a call from BAD returns Z_DATA_ERROR or Z_MEM_ERROR (the window may fail to be allocated);
   - `bbw_trees`: from the block header with an empty bit buffer and no window, a call with flush = Z_TREES
     offered a fixed block returns Z_OK (it consumed the header's byte). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.harness.bit_writer.BBRun.
Require Import Zlib.proof.harness.bit_writer.BWBits.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the bits main writes (BWBits.bw_bb_bits, which only uses the kind, the literals being bytes and the length of
   the stream) *)
Lemma bbw_bits S0 kind which lits : bbw_ok S0 kind which lits ->
  let S := bb_bytes S0 kind which lits in
  let B := bits_le (bb_btype kind) 2 ++ concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which in
  Zlength S = Zlength S0 /\ is_bytes S /\ 1 + Zlength B <= 8 * Zlength S0 /\
  sublist 1 (1 + Zlength B) (bytes_bits S) = B.
Proof.
  intros Hok. destruct Hok as (Hk & Hw & _ & Hlb & HS0 & HS0n & _).
  destruct (put_lits_send lits (put_bits_m S0 1 (bb_btype kind) 2 0) 3 (bw_lits_range lits Hlb)) as [PL LL].
  pose proof (lits_len_bounds lits) as LB. pose proof (Zlength_nonneg lits).
  set (L := concat (map (send_sym fixed_ll) lits)) in *.
  assert (HT: Zlength (bb_tail_bits kind which) <= 12).
  { unfold bb_tail_bits. destruct (kind =? 2); [bw_len LL|]. destruct (kind =? 3); [bw_len LL|].
    destruct (kind =? 4); [bw_len LL|]. rewrite Zlength_nil. lia. }
  assert (E: bb_bytes S0 kind which lits = write_bits S0 1 (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which)).
  { unfold bb_bytes, bb_tail_bits. cbv zeta. rewrite PL. unfold put_bits_m, pb_bits. cbn [Z.eqb].
    rewrite bw_write_bits_join by bw_len LL.
    destruct (kind =? 2); [rewrite bw_write_bits_join by bw_len LL; reflexivity|].
    destruct (kind =? 3); [rewrite !bw_write_bits_join by bw_len LL; reflexivity|].
    destruct (kind =? 4); [rewrite bw_write_bits_join by bw_len LL; reflexivity|].
    rewrite !app_nil_r. reflexivity. }
  cbv zeta. rewrite E.
  assert (HB: Zlength (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which) = 2 + lits_len lits + Zlength (bb_tail_bits kind which))
    by (rewrite !Zlength_app, dkit_bits_le_len, <- LL by lia; lia).
  rewrite HB. destruct (bw_window S0 1 (bits_le (bb_btype kind) 2 ++ L ++ bb_tail_bits kind which) HS0 ltac:(lia)
    ltac:(rewrite HB; pose proof (Zlength_nonneg (bb_tail_bits kind which)); lia)) as (H1 & H2 & H3).
  rewrite HB in H3. split; [exact H1|]. split; [exact H2|]. split; [pose proof (Zlength_nonneg (bb_tail_bits kind which)); lia|].
  exact H3.
Qed.

(* the stream after main's writes: BTYPE at bits 1-2, the rest of the block from bit 3, and the first byte split
   into BFINAL x, BTYPE and the five bits c that follow (as BBRun.bbt_layout) *)
Lemma bbw_layout S0 kind which lits : bbw_ok S0 kind which lits ->
  let S := bb_bytes S0 kind which lits in
  let Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which in
  Zlength S = Zlength S0 /\ is_bytes S /\ 3 + Zlength Rest <= 8 * Zlength S /\
  sublist 1 3 (bytes_bits S) = bits_le (bb_btype kind) 2 /\
  sublist 3 (3 + Zlength Rest) (bytes_bits S) = Rest /\
  Znth 0 S = bval (sublist 0 1 (bytes_bits S)) + 2 * bval (bits_le (bb_btype kind) 2) +
             8 * bval (sublist 3 8 (bytes_bits S)) /\
  0 <= bval (sublist 0 1 (bytes_bits S)) <= 1 /\ 0 <= bval (sublist 3 8 (bytes_bits S)) < 32.
Proof.
  intros Hok S Rest.
  pose proof (bbw_bits S0 kind which lits Hok) as HB. cbv zeta in HB. fold S Rest in HB.
  set (B := bits_le (bb_btype kind) 2 ++ Rest) in HB.
  destruct HB as (HlS & HbS & Hfit & Hbits).
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & HbS0 & HS0 & Hk0).
  assert (LB : Zlength B = 2 + Zlength Rest) by (unfold B; rewrite Zlength_app, dkit_bits_le_len; lia).
  assert (Hfit' : 1 + Zlength B <= 8 * Zlength S) by lia.
  pose proof (Zlength_nonneg Rest) as LR.
  assert (Hhd : sublist 1 3 (bytes_bits S) = bits_le (bb_btype kind) 2).
  { pose proof (bbt_sub S B 0 2 Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 0) with 1 in X. change (1 + 2) with 3 in X. rewrite X. unfold B.
    rewrite sublist_app1 by (rewrite ?dkit_bits_le_len; lia).
    apply sublist_same; [lia | rewrite dkit_bits_le_len; lia]. }
  assert (Hrest : sublist 3 (3 + Zlength Rest) (bytes_bits S) = Rest).
  { pose proof (bbt_sub S B 2 (Zlength B) Hbits Hfit' ltac:(lia) ltac:(lia)) as X.
    change (1 + 2) with 3 in X. replace (1 + Zlength B) with (3 + Zlength Rest) in X by lia. rewrite X, LB. unfold B.
    rewrite sublist_app2 by (rewrite ?dkit_bits_le_len; lia). rewrite dkit_bits_le_len by lia.
    apply sublist_same; lia. }
  destruct (bbt_byte0 S HbS ltac:(lia)) as (E0 & Rx & Rc). rewrite Hhd in E0.
  repeat split; auto; lia.
Qed.

(* a prefix of k >= 5 bytes of a byte stream: bytes, with the same first five bytes *)
Lemma bbw_prefix (S: list Z) k :
  is_bytes S -> 5 <= k <= Zlength S ->
  let inp := sublist 0 k S in
  is_bytes inp /\ Zlength inp = k /\ forall i, 0 <= i < 5 -> Znth i inp = Znth i S.
Proof.
  intros Hb Hk inp. unfold inp. split; [|split].
  - unfold is_bytes in *. apply Forall_sublist. exact Hb.
  - rewrite Zlength_sublist; lia.
  - intros i Hi. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

(* kinds 0 (stored, NLEN not ~LEN), 1 (BTYPE 11) and 4 (HLIT 30/31): a call from the state after inflateInit2_
   offered the first k >= 5 bytes of the stream returns Z_DATA_ERROR *)
Lemma bbw_refused S0 kind which lits k w sp L z flush res :
  bbw_ok S0 kind which lits -> kind <> 2 -> kind <> 3 -> -15 <= w <= -8 -> l_s L = l_s (init_live sp w) ->
  5 <= k <= Zlength (bb_bytes S0 kind which lits) ->
  run2 flush lenfix_list distfix_list (m_init z L (sublist 0 k (bb_bytes S0 kind which lits))) res ->
  r_ret res = Z_DATA_ERROR.
Proof.
  intros Hok K2 K3 Hw HL Hk Hrun.
  destruct (bbw_layout S0 kind which lits Hok) as (HlS & HbS & Hfit & Hhd & Hrest & E0 & Rx & Rc).
  set (S := bb_bytes S0 kind which lits) in *.
  set (Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which) in *.
  set (x := bval (sublist 0 1 (bytes_bits S))) in *.
  set (c := bval (sublist 3 8 (bytes_bits S))) in *.
  destruct (bbw_prefix S k HbS Hk) as (Hbi & Hli & Hi). cbv zeta in Hbi, Hli, Hi.
  set (inp := sublist 0 k S) in *.
  pose proof Hok as (Hk' & Hwh & Hlits & Hbl & HbS0 & HS0 & Hk0).
  pose proof (Zlength_nonneg lits) as LL.
  pose proof Hrun as (o & Lp & Ro).
  rewrite <- (Hi 0 ltac:(lia)) in E0.
  assert (kind = 0 \/ kind = 1 \/ kind = 4) as [K|[K|K]] by lia; subst kind.
  - (* stored, NLEN not ~LEN *)
    change (bval (bits_le (bb_btype 0) 2)) with 0 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L inp sp w o x 0 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 inp STORED 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    assert (Hne := Hk0 eq_refl). cbv zeta in Hne. fold S in Hne.
    rewrite <- !(Hi 1), <- !(Hi 2), <- !(Hi 3), <- !(Hi 4) in Hne by lia.
    destruct (bbt_stored flush lenfix_list distfix_list m2 inp c M2' Rc ltac:(lia) Hbi Hne)
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
  - (* BTYPE 11 *)
    change (bval (bits_le (bb_btype 1) 2)) with 3 in E0.
    destruct (bbt_hdr flush lenfix_list distfix_list z L inp sp w o x 3 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 inp BAD 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    exact (bbt_bad _ _ _ _ _ res (mv_mode _ _ _ _ _ _ _ M2') (mv_wsize _ _ _ _ _ _ _ M2') L2' Ro).
  - (* dynamic block, HLIT 30 + which *)
    change (bval (bits_le (bb_btype 4) 2)) with 2 in E0.
    assert (Hl0 : lits = []) by (apply Hlits; discriminate).
    assert (ER : Rest = bits_le (30 + which) 5) by (unfold Rest; rewrite Hl0; reflexivity).
    assert (Hc4 : c = 30 + which).
    { assert (L8 : 3 + Zlength Rest = 8) by (rewrite ER, dkit_bits_le_len; lia).
      unfold c. rewrite <- L8, Hrest, ER. assert (which = 0 \/ which = 1) as [W|W] by lia; subst which; reflexivity. }
    destruct (bbt_hdr flush lenfix_list distfix_list z L inp sp w o x 2 c Hw HL ltac:(lia) E0 Rx ltac:(lia) Rc Lp)
      as (m2 & M2 & L2).
    assert (M2' : mv m2 inp TABLE 1 c 5 0) by exact M2.
    assert (L2' : loop2 flush lenfix_list distfix_list m2 o) by exact L2.
    destruct (bbt_table flush lenfix_list distfix_list m2 inp c M2' ltac:(lia) ltac:(lia) Hbi)
      as (m3 & H3 & Bm & Lv3 & Ws3).
    pose proof (bbt_next _ _ _ _ _ _ H3 ltac:(rewrite Lv3; discriminate) L2') as L3.
    exact (bbt_bad _ _ _ _ _ res Bm Ws3 L3 Ro).
Qed.

(* inf_leave without an allocation failure keeps a return code other than Z_OK *)
Lemma bbw_fin_ret flush m : m_ret m <> Z_OK -> r_ret (leave_fin flush m) = m_ret m.
Proof.
  intros Hr. unfold leave_fin. cbv zeta.
  cbn [r_ret]. set (Y := m_ret _).
  assert (E : Y = m_ret m)
    by (unfold Y; repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity).
  clearbody Y. subst Y.
  replace (m_ret m =? Z_OK) with false by (symmetry; apply Z.eqb_neq; exact Hr).
  rewrite andb_false_r. reflexivity.
Qed.

(* a call from BAD: c_BAD sets Z_DATA_ERROR and leaves; inf_leave keeps it, or fails to allocate the window *)
Lemma bbw_bad_call flush fx dx z L inp res :
  i_mode (l_s L) = BAD -> run2 flush fx dx (m_init z L inp) res ->
  r_ret res = Z_DATA_ERROR \/ r_ret res = Z_MEM_ERROR.
Proof.
  intros Hm (o & Lp & R).
  assert (Mm : m_mode (m_init z L inp) = BAD).
  { unfold m_init, m_mode. cbv zeta. rewrite Hm. change (BAD =? Zlib.proof.inflate.Model.TYPE) with false.
    cbv iota. cbn [m_s]. exact Hm. }
  assert (E1 : stepf2 flush fx dx (m_init z L inp) = IBrk (set_leave (set_m_ret (m_init z L inp) Z_DATA_ERROR)))
    by (unfold stepf2, step2; rewrite Mm; reflexivity).
  rewrite (bbt_last _ _ _ _ _ _ E1 eq_refl Lp) in R.
  inversion R; subst; [right; reflexivity | left].
  apply bbw_fin_ret. cbn. discriminate.
Qed.

(* the call with flush = Z_TREES from the block header (HEAD of a raw stream, or TYPEDO), with an empty bit
   buffer and no window, offered a fixed block: it pulls the header's byte, stops at LEN_ and returns Z_OK *)
Lemma bbw_trees z L inp x c res :
  ((i_mode (l_s L) = HEAD /\ i_wrap (l_s L) = 0) \/ i_mode (l_s L) = TYPEDO) ->
  i_last (l_s L) = 0 -> i_hold (l_s L) = 0 -> i_bits (l_s L) = 0 -> i_wsize (l_s L) = 0 ->
  0 < Zlength inp -> Znth 0 inp = x + 2 * 1 + 8 * c -> 0 <= x <= 1 -> 0 <= c < 32 ->
  run2 Z_TREES lenfix_list distfix_list (m_init z L inp) res -> r_ret res = Z_OK.
Proof.
  intros Hm Il Ih Ib Is Hl E Hx Hc (o & Lp & Ro).
  assert (Mt : (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) = false)
    by (destruct Hm as [[-> _]| ->]; reflexivity).
  assert (E0 : m_init z L inp = MS (l_s L) (l_h L) inp (zf_ao z) 0 [] 0 0 (Zlength inp) (zf_ao z) Z_OK 0
                                  (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. rewrite Mt. cbv iota. rewrite Ih, Ib. reflexivity. }
  rewrite E0 in Lp.
  set (m0 := MS (l_s L) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in Lp.
  assert (T : exists m1, mv m1 inp TYPEDO 0 0 0 0 /\ i_last (m_s m1) = 0 /\
                         loop2 Z_TREES lenfix_list distfix_list m1 o).
  { destruct Hm as [[Hm Hw]|Hm].
    - assert (H0 : stepf2 Z_TREES lenfix_list distfix_list m0 = IBrk (set_mode m0 TYPEDO))
        by (apply bbt_head; assumption).
      exists (set_mode m0 TYPEDO). split; [constructor; reflexivity || exact Is|]. split; [exact Il|].
      exact (bbt_next _ _ _ _ _ _ H0 ltac:(discriminate) Lp).
    - exists m0. split; [constructor; reflexivity || exact Is || exact Hm|]. split; [exact Il|exact Lp]. }
  destruct T as (m1 & M1 & Il1 & Lp1).
  destruct (bbt_typedo Z_TREES lenfix_list distfix_list m1 inp x 1 c M1 Il1 Hl E Hx ltac:(lia) Hc) as (m2 & H2 & M2).
  change (andb (1 =? 1) (Z_TREES =? Z_TREES)) with true in M2. cbv iota in M2.
  assert (M2' : mv m2 inp LEN_ 1 c 5 1) by exact M2.
  rewrite (bbt_last _ _ _ _ _ _ H2 (mv_leave _ _ _ _ _ _ _ M2') Lp1) in Ro.
  assert (Ok : leave_ok Z_TREES m2 = false).
  { unfold leave_ok, m_left. rewrite (mv_wsize _ _ _ _ _ _ _ M2'), (mv_out _ _ _ _ _ _ _ M2'), (mv_ow _ _ _ _ _ _ _ M2').
    rewrite Zlength_nil, Z.sub_0_r, !Z.eqb_refl. reflexivity. }
  inversion Ro as [Ok' _|]; [congruence|].
  destruct (bbt_lf _ _ Ok) as (-> & _ & _).
  rewrite (mv_ret _ _ _ _ _ _ _ M2').
  replace (m_in m2 - m_have m2) with 1
    by (unfold m_have; rewrite (mv_in _ _ _ _ _ _ _ M2'), (mv_inp _ _ _ _ _ _ _ M2'), (mv_nx _ _ _ _ _ _ _ M2'); lia).
  reflexivity.
Qed.

(** * TREES part, SEND: see RTDLTCTrKit.v for the statement and its purpose. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCTrKit.
Require Zlib.proof.huffman.FlushHdr Zlib.proof.huffman.FlushStream.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The guard invariant of the checked bit writer. *)
Definition sb_ok (o : outbuf) : Prop := 0 <= o_bi_valid o <= 16 /\ 0 <= o_pending o.

Lemma sb_writes_le : forall a b, writes a b -> o_pending b <= Zlength (o_buf b) -> o_pending a <= Zlength (o_buf a).
Proof. intros a b [P [L _]] H. lia. Qed.

Lemma sb_writes_len : forall a b, writes a b -> Zlength (o_buf b) = Zlength (o_buf a).
Proof. intros a b [P [L _]]. exact L. Qed.

Lemma sb_writes_pend : forall a b, writes a b -> o_pending a <= o_pending b.
Proof. intros a b [P [L _]]. exact P. Qed.

Lemma sb_bits : forall o m v l,
  sb_ok o -> 0 <= l <= 16 -> o_pending (send_bits o v l) <= Zlength (o_buf o) ->
  exists m', c_send_bits (o, m) v l = Some (send_bits o v l, m') /\ sb_ok (send_bits o v l).
Proof.
  intros o m v l [Hv Hp] Hl Hb. unfold c_send_bits, send_bits, Buf_size in *.
  assert (Eg : (0 <=? o_bi_valid o) && (o_bi_valid o <=? 16) = true)
    by (apply andb_true_iff; split; apply Z.leb_le; lia).
  rewrite Eg. cbn [guard bind].
  destruct (o_bi_valid o >? 16 - l) eqn:E.
  - apply Z.gtb_lt in E. unfold c_put_short. rewrite c_put_byte_spec.
    unfold put_short, put_byte, set_bits in Hb |- *. cbn [o_pending o_buf o_bi_buf o_bi_valid o_bi_used] in Hb |- *.
    try rewrite Zlength_upd_Znth_any in Hb.
    assert (Er : in_range (o_pending o) (Zlength (o_buf o)) = true)
      by (unfold in_range; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    rewrite Er. cbn [bind]. rewrite c_put_byte_spec. cbn [o_pending o_buf o_bi_buf o_bi_valid o_bi_used].
    rewrite Zlength_upd_Znth_any.
    assert (Er2 : in_range (o_pending o + 1) (Zlength (o_buf o)) = true)
      by (unfold in_range; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
    rewrite Er2. cbn [bind]. eexists; split; [reflexivity|].
    unfold sb_ok; cbn [o_pending o_bi_valid]; lia.
  - rewrite Z.gtb_ltb, Z.ltb_ge in E. eexists; split; [reflexivity|]. unfold sb_ok, set_bits; cbn [o_pending o_bi_valid]; lia.
Qed.

Lemma sb_rd : forall l i, 0 <= i < Zlength l -> rd l i = Some (Znth i l).
Proof.
  intros l i H. unfold rd, in_range.
  replace ((0 <=? i) && (i <? Zlength l)) with true; [reflexivity|].
  symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Lemma sb_code : forall o m c codes lens,
  sb_ok o -> 0 <= c < Zlength codes -> 0 <= c < Zlength lens -> 0 <= Znth c lens <= 16 ->
  o_pending (send_code o c codes lens) <= Zlength (o_buf o) ->
  exists m', c_send_code (o, m) c codes lens = Some (send_code o c codes lens, m') /\
             sb_ok (send_code o c codes lens).
Proof.
  intros o m c codes lens Ho H1 H2 H3 Hb. unfold c_send_code.
  rewrite (sb_rd lens c H2). cbn [bind]. rewrite (sb_rd codes c H1). cbn [bind].
  unfold send_code in *. apply sb_bits; auto.
Qed.

Lemma sb_codes : forall n o m c codes lens,
  (1 <= n)%nat -> sb_ok o -> 0 <= c < Zlength codes -> 0 <= c < Zlength lens -> 0 <= Znth c lens <= 16 ->
  o_pending (Nat.iter n (fun o => send_code o c codes lens) o) <= Zlength (o_buf o) ->
  exists m', c_send_codes n (o, m) c codes lens (Z.of_nat n) =
               Some (Nat.iter n (fun o => send_code o c codes lens) o, m') /\
             sb_ok (Nat.iter n (fun o => send_code o c codes lens) o).
Proof.
  induction n as [|n IH]; intros o m c codes lens Hn Ho H1 H2 H3 Hb; [lia|].
  rewrite Nat.iter_succ_r in Hb |- *.
  pose proof (FlushHdr.iter_send_code_writes n (send_code o c codes lens) c codes lens) as W.
  pose proof (send_code_writes o c codes lens) as W0.
  destruct (sb_code o m c codes lens Ho H1 H2 H3) as [m1 [E1 Ok1]].
  { eapply Z.le_trans; [apply (sb_writes_pend _ _ W)|exact Hb]. }
  cbn [c_send_codes]. rewrite E1. cbn [bind].
  replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
  destruct n as [|n'].
  - cbn [Z.of_nat Z.eqb negb Nat.iter]. eexists; split; [reflexivity|exact Ok1].
  - replace (negb (Z.of_nat (S n') =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
    apply IH; auto; try lia.
    rewrite (sb_writes_len _ _ W0). exact Hb.
Qed.

(** The branch of send_tree's loop that sends a run. *)
Definition m_br (o : outbuf) (curlen prevlen count min_count : Z) (blc bll : list Z) : outbuf :=
  if count <? min_count then Nat.iter (Z.to_nat count) (fun o => send_code o curlen blc bll) o
  else if negb (curlen =? 0) then
    let '(o, count) :=
      if negb (curlen =? prevlen) then (send_code o curlen blc bll, count - 1) else (o, count) in
    send_bits (send_code o REP_3_6 blc bll) (count - 3) 2
  else if count <=? 10 then send_bits (send_code o REPZ_3_10 blc bll) (count - 3) 3
  else send_bits (send_code o REPZ_11_138 blc bll) (count - 11) 7.

Definition c_br (om : cout) (curlen prevlen count min_count : Z) (blc bll : list Z) : option cout :=
  if count <? min_count then c_send_codes (Z.to_nat count) om curlen blc bll count
  else if negb (curlen =? 0) then
    let* (om, count) :=
      (if negb (curlen =? prevlen) then
         let* om := c_send_code om curlen blc bll in Some (om, count - 1)
       else Some (om, count)) in
    let* om := c_send_code om REP_3_6 blc bll in
    c_send_bits om (count - 3) 2
  else if count <=? 10 then
    let* om := c_send_code om REPZ_3_10 blc bll in c_send_bits om (count - 3) 3
  else
    let* om := c_send_code om REPZ_11_138 blc bll in c_send_bits om (count - 11) 7.

Lemma m_loop_S : forall f t max_code blc bll o n prevlen nextlen count max_count min_count,
  send_tree_loop (S f) t max_code blc bll o n prevlen nextlen count max_count min_count =
  if n <=? max_code then
    if (count + 1 <? max_count) && (nextlen =? Znth (n + 1) (dl t)) then
      send_tree_loop f t max_code blc bll o (n + 1) prevlen (Znth (n + 1) (dl t)) (count + 1) max_count min_count
    else
      let o' := m_br o nextlen prevlen (count + 1) min_count blc bll in
      let '(max_count, min_count) :=
        if Znth (n + 1) (dl t) =? 0 then (138, 3)
        else if nextlen =? Znth (n + 1) (dl t) then (6, 3)
        else (7, 4) in
      send_tree_loop f t max_code blc bll o' (n + 1) nextlen (Znth (n + 1) (dl t)) 0 max_count min_count
  else o.
Proof. reflexivity. Qed.

Lemma c_loop_S : forall f t max_code blc bll om n prevlen nextlen count max_count min_count,
  c_send_tree_loop (S f) t max_code blc bll om n prevlen nextlen count max_count min_count =
  if n <=? max_code then
    let* nl := rd (dl t) (n + 1) in
    if (count + 1 <? max_count) && (nextlen =? nl) then
      c_send_tree_loop f t max_code blc bll om (n + 1) prevlen nl (count + 1) max_count min_count
    else
      let* om := c_br om nextlen prevlen (count + 1) min_count blc bll in
      let '(max_count, min_count) :=
        if nl =? 0 then (138, 3)
        else if nextlen =? nl then (6, 3)
        else (7, 4) in
      c_send_tree_loop f t max_code blc bll om (n + 1) nextlen nl 0 max_count min_count
  else Some om.
Proof. reflexivity. Qed.

Section BL.
Context (blc bll : list Z) (Hblc : 19 <= Zlength blc) (Hbll : 19 <= Zlength bll)
  (Hbl : forall i, 0 <= i < 19 -> 0 <= Znth i bll <= 7).

Lemma sb_c : forall o m c, sb_ok o -> 0 <= c < 19 ->
  o_pending (send_code o c blc bll) <= Zlength (o_buf o) ->
  exists m', c_send_code (o, m) c blc bll = Some (send_code o c blc bll, m') /\ sb_ok (send_code o c blc bll).
Proof. intros o m c Ho Hc Hb. apply sb_code; auto; try lia. specialize (Hbl c Hc). lia. Qed.

Lemma sb_cb : forall o m c v l, sb_ok o -> 0 <= c < 19 -> 0 <= l <= 16 ->
  o_pending (send_bits (send_code o c blc bll) v l) <= Zlength (o_buf o) ->
  exists m', (let* om := c_send_code (o, m) c blc bll in c_send_bits om v l) =
               Some (send_bits (send_code o c blc bll) v l, m') /\ sb_ok (send_bits (send_code o c blc bll) v l).
Proof.
  intros o m c v l Ho Hc Hl Hb.
  pose proof (send_bits_writes (send_code o c blc bll) v l) as W.
  pose proof (send_code_writes o c blc bll) as W0.
  destruct (sb_c o m c Ho Hc) as [m1 [-> Ok1]].
  { eapply Z.le_trans; [apply (sb_writes_pend _ _ W)|exact Hb]. }
  cbn [bind]. apply sb_bits; auto. rewrite (sb_writes_len _ _ W0). exact Hb.
Qed.

Lemma sb_br : forall o m curlen prevlen count min_count,
  sb_ok o -> 1 <= count -> 0 <= curlen <= 15 ->
  o_pending (m_br o curlen prevlen count min_count blc bll) <= Zlength (o_buf o) ->
  exists m', c_br (o, m) curlen prevlen count min_count blc bll =
               Some (m_br o curlen prevlen count min_count blc bll, m') /\
             sb_ok (m_br o curlen prevlen count min_count blc bll).
Proof.
  intros o m curlen prevlen count min_count Ho Hc Hcur Hb. unfold c_br, m_br in *.
  destruct (count <? min_count).
  - pose proof (sb_codes (Z.to_nat count) o m curlen blc bll) as X. rewrite Z2Nat.id in X by lia.
    apply X; auto; try lia.
    specialize (Hbl curlen ltac:(lia)). lia.
  - destruct (negb (curlen =? 0)).
    + destruct (negb (curlen =? prevlen)).
      * pose proof (send_bits_writes (send_code (send_code o curlen blc bll) REP_3_6 blc bll) (count - 1 - 3) 2) as W.
        pose proof (send_code_writes (send_code o curlen blc bll) REP_3_6 blc bll) as W1.
        pose proof (send_code_writes o curlen blc bll) as W0.
        destruct (sb_c o m curlen Ho ltac:(lia)) as [m1 [-> Ok1]].
        { eapply Z.le_trans; [apply (sb_writes_pend _ _ W1)|].
          eapply Z.le_trans; [apply (sb_writes_pend _ _ W)|exact Hb]. }
        cbn [bind]. apply sb_cb; auto; unfold REP_3_6; try lia. rewrite (sb_writes_len _ _ W0). exact Hb.
      * cbn [bind]. apply sb_cb; auto; unfold REP_3_6; lia.
    + destruct (count <=? 10); apply sb_cb; auto; unfold REPZ_3_10, REPZ_11_138; lia.
Qed.

Lemma m_br_writes : forall o curlen prevlen count min_count,
  writes o (m_br o curlen prevlen count min_count blc bll).
Proof.
  intros. unfold m_br.
  destruct (count <? min_count); [apply FlushHdr.iter_send_code_writes|].
  destruct (negb (curlen =? 0)).
  - destruct (negb (curlen =? prevlen)); cbn beta iota.
    + eapply writes_trans; [|apply send_bits_writes]. eapply writes_trans; [|apply send_code_writes]. apply send_code_writes.
    + eapply writes_trans; [|apply send_bits_writes]. apply send_code_writes.
  - destruct (count <=? 10); (eapply writes_trans; [|apply send_bits_writes]); apply send_code_writes.
Qed.

Lemma sb_loop : forall t max_code,
  max_code + 1 < Zlength (dl t) -> (forall i, 0 <= i <= max_code -> 0 <= Znth i (dl t) <= 15) ->
  forall fuel o m n prevlen nextlen count max_count min_count,
  sb_ok o -> 0 <= n -> max_code + 1 <= n + Z.of_nat fuel -> (n <= max_code -> 0 <= nextlen <= 15) -> 0 <= count ->
  o_pending (send_tree_loop fuel t max_code blc bll o n prevlen nextlen count max_count min_count)
    <= Zlength (o_buf o) ->
  exists m', c_send_tree_loop fuel t max_code blc bll (o, m) n prevlen nextlen count max_count min_count =
               Some (send_tree_loop fuel t max_code blc bll o n prevlen nextlen count max_count min_count, m') /\
             sb_ok (send_tree_loop fuel t max_code blc bll o n prevlen nextlen count max_count min_count).
Proof.
  intros t max_code Hlt Hdl. induction fuel as [|f IH];
    intros o m n prevlen nextlen count max_count min_count Ho Hn0 Hf Hnl Hc Hb.
  - cbn [c_send_tree_loop send_tree_loop]. replace (n <=? max_code) with false by (symmetry; apply Z.leb_gt; lia).
    eexists; split; [reflexivity|exact Ho].
  - rewrite c_loop_S. rewrite m_loop_S in Hb |- *.
    destruct (Z.leb_spec n max_code) as [Hn|Hn]; [|eexists; split; [reflexivity|exact Ho]].
    rewrite (sb_rd (dl t) (n + 1)) by lia. cbn [bind].
    destruct ((count + 1 <? max_count) && (nextlen =? Znth (n + 1) (dl t))).
    + apply IH; auto; try lia. intros Hn1. apply Hdl; lia.
    + cbv zeta in Hb |- *.
      destruct (if Znth (n + 1) (dl t) =? 0 then (138, 3)
                else if nextlen =? Znth (n + 1) (dl t) then (6, 3) else (7, 4)) as [mx mn].
      pose proof (FlushHdr.send_tree_loop_writes f t max_code blc bll
                    (m_br o nextlen prevlen (count + 1) min_count blc bll)
                    (n + 1) nextlen (Znth (n + 1) (dl t)) 0 mx mn) as W.
      pose proof (m_br_writes o nextlen prevlen (count + 1) min_count) as W0.
      destruct (sb_br o m nextlen prevlen (count + 1) min_count Ho ltac:(lia) ltac:(auto)) as [m1 [-> Ok1]].
      { eapply Z.le_trans; [apply (sb_writes_pend _ _ W)|exact Hb]. }
      cbn [bind]. apply IH; auto; try lia.
      * intros Hn1. apply Hdl; lia.
      * rewrite (sb_writes_len _ _ W0). exact Hb.
Qed.

End BL.

Lemma sb_tree : forall o m t max_code bl,
  0 <= max_code < 2147483647 -> max_code + 1 < Zlength (dl t) ->
  (forall i, 0 <= i <= max_code -> 0 <= Znth i (dl t) <= 15) ->
  19 <= Zlength (fc bl) -> 19 <= Zlength (dl bl) -> (forall i, 0 <= i < 19 -> 0 <= Znth i (dl bl) <= 7) ->
  sb_ok o -> o_pending (send_tree o t max_code bl) <= Zlength (o_buf o) ->
  exists m', c_send_tree (o, m) t max_code bl = Some (send_tree o t max_code bl, m') /\
             sb_ok (send_tree o t max_code bl).
Proof.
  intros o m t max_code bl Hmc Hlt Hdl Hfc Hdlb Hbl Ho Hb. unfold c_send_tree, send_tree in *.
  replace (max_code <? 2147483647) with true by (symmetry; apply Z.ltb_lt; lia). cbn [guard bind].
  rewrite (sb_rd (dl t) 0) by lia. cbn [bind].
  destruct (if Znth 0 (dl t) =? 0 then (138, 3) else (7, 4)) as [mx mn].
  apply sb_loop; auto; try lia.
  intros _. apply Hdl; lia.
Qed.

Lemma Zlength_bl_order : Zlength bl_order = 19.
Proof. reflexivity. Qed.

Lemma sb_bl_lens : forall bl, 19 <= Zlength (dl bl) -> (forall i, 0 <= i < 19 -> 0 <= Znth i (dl bl) <= 7) ->
  forall fuel o m rank blcodes,
  blcodes <= 19 -> 0 <= rank -> blcodes <= rank + Z.of_nat fuel -> sb_ok o ->
  o_pending (send_bl_lens fuel bl o rank blcodes) <= Zlength (o_buf o) ->
  exists m', c_send_bl_lens fuel bl (o, m) rank blcodes = Some (send_bl_lens fuel bl o rank blcodes, m') /\
             sb_ok (send_bl_lens fuel bl o rank blcodes).
Proof.
  intros bl Hdlb Hbl. induction fuel as [|f IH]; intros o m rank blcodes H19 Hr Hf Ho Hb.
  - cbn [c_send_bl_lens send_bl_lens]. replace (rank <? blcodes) with false by (symmetry; apply Z.ltb_ge; lia).
    eexists; split; [reflexivity|exact Ho].
  - cbn [c_send_bl_lens send_bl_lens] in Hb |- *.
    destruct (Z.ltb_spec rank blcodes) as [Hrb|Hrb]; [|eexists; split; [reflexivity|exact Ho]].
    rewrite (sb_rd bl_order rank) by (rewrite Zlength_bl_order; lia). cbn [bind].
    pose proof (FlushStream.bl_order_range rank ltac:(lia)) as Hro.
    rewrite (sb_rd (dl bl) (Znth rank bl_order)) by lia. cbn [bind].
    set (o1 := send_bits o (Znth (Znth rank bl_order) (dl bl)) 3) in *.
    pose proof (FlushHdr.send_bl_lens_writes f bl o1 (rank + 1) blcodes) as W.
    pose proof (send_bits_writes o (Znth (Znth rank bl_order) (dl bl)) 3) as W0. fold o1 in W0.
    destruct (sb_bits o m (Znth (Znth rank bl_order) (dl bl)) 3 Ho ltac:(lia)) as [m1 [E1 Ok1]].
    { fold o1. eapply Z.le_trans; [apply (sb_writes_pend _ _ W)|exact Hb]. }
    fold o1 in E1, Ok1. rewrite E1. cbn [bind].
    apply IH; auto; try lia. rewrite (sb_writes_len _ _ W0). exact Hb.
Qed.

Theorem send_some : send_statement.
Proof.
  intros o m lt dt bl lcodes dcodes blcodes Hok Hm Hl Hd Hblc Hlt Hdt Hdll Hdld Hfc Hdlb Hbl Hb.
  assert (Ho : sb_ok o) by (destruct Hok as [A [B C]]; split; lia).
  unfold L_CODES, D_CODES, BL_CODES, LITERALS in *.
  unfold c_send_all_trees.
  replace ((-2147483648 + 257 <=? lcodes) && (-2147483648 + 1 <=? dcodes) && (-2147483648 + 4 <=? blcodes))
    with true by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
  cbn [guard bind].
  unfold send_all_trees in Hb |- *.
  set (o1 := send_bits o (lcodes - 257) 5) in *.
  set (o2 := send_bits o1 (dcodes - 1) 5) in *.
  set (o3 := send_bits o2 (blcodes - 4) 4) in *.
  set (o4 := send_bl_lens 19 bl o3 0 blcodes) in *.
  set (o5 := send_tree o4 lt (lcodes - 1) bl) in *.
  set (o6 := send_tree o5 dt (dcodes - 1) bl) in *.
  assert (W1 : writes o o1) by apply send_bits_writes.
  assert (W2 : writes o1 o2) by apply send_bits_writes.
  assert (W3 : writes o2 o3) by apply send_bits_writes.
  assert (W4 : writes o3 o4) by apply FlushHdr.send_bl_lens_writes.
  assert (W5 : writes o4 o5) by apply FlushHdr.send_tree_writes.
  assert (W6 : writes o5 o6) by apply FlushHdr.send_tree_writes.
  pose proof (sb_writes_pend _ _ W1). pose proof (sb_writes_pend _ _ W2). pose proof (sb_writes_pend _ _ W3).
  pose proof (sb_writes_pend _ _ W4). pose proof (sb_writes_pend _ _ W5). pose proof (sb_writes_pend _ _ W6).
  pose proof (sb_writes_len _ _ W1). pose proof (sb_writes_len _ _ W2). pose proof (sb_writes_len _ _ W3).
  pose proof (sb_writes_len _ _ W4). pose proof (sb_writes_len _ _ W5). pose proof (sb_writes_len _ _ W6).
  destruct (sb_bits o m (lcodes - 257) 5 Ho ltac:(lia)) as [m1 [E1 Ok1]]; [fold o1; lia|].
  fold o1 in E1, Ok1. rewrite E1. cbn [bind].
  destruct (sb_bits o1 m1 (dcodes - 1) 5 Ok1 ltac:(lia)) as [m2 [E2 Ok2]]; [fold o2; lia|].
  fold o2 in E2, Ok2. rewrite E2. cbn [bind].
  destruct (sb_bits o2 m2 (blcodes - 4) 4 Ok2 ltac:(lia)) as [m3 [E3 Ok3]]; [fold o3; lia|].
  fold o3 in E3, Ok3. rewrite E3. cbn [bind].
  destruct (sb_bl_lens bl ltac:(lia) Hbl 19 o3 m3 0 blcodes ltac:(lia) ltac:(lia) ltac:(cbn; lia) Ok3)
    as [m4 [E4 Ok4]]; [fold o4; lia|].
  fold o4 in E4, Ok4. rewrite E4. cbn [bind].
  destruct (sb_tree o4 m4 lt (lcodes - 1) bl ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply Hdll; lia)
              ltac:(lia) ltac:(lia) Hbl Ok4) as [m5 [E5 Ok5]]; [fold o5; lia|].
  fold o5 in E5, Ok5. rewrite E5. cbn [bind].
  destruct (sb_tree o5 m5 dt (dcodes - 1) bl ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply Hdld; lia)
              ltac:(lia) ltac:(lia) Hbl Ok5) as [m6 [E6 Ok6]]; [fold o6; lia|].
  fold o6 in E6. exists m6. exact E6.
Qed.

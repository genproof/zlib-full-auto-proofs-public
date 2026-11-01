(* RT-D part FLUSH: send_all_trees sends Format's dynamic header (interface: RTDFlushDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs.
Require Zlib.proof.huffman.FlushHdr.
Import ListNotations.
Local Open Scope Z_scope.

(* a step of the writer from o to o' appending the bits b, given room for the final pending *)
Definition hstep (o o' : outbuf) (b : list bool) : Prop :=
  writes o o' /\
  (bits_ok o -> o_pending o' + 2 <= Zlength (o_buf o) -> bits_ok o' /\ obits o' = obits o ++ b).

Lemma hstep_refl : forall o, hstep o o [].
Proof. intros o. split; [apply writes_refl|]. intros Ho _. rewrite app_nil_r. auto. Qed.

Lemma hstep_trans : forall o1 o2 o3 b1 b2, hstep o1 o2 b1 -> hstep o2 o3 b2 -> hstep o1 o3 (b1 ++ b2).
Proof.
  intros o1 o2 o3 b1 b2 [W1 S1] [W2 S2]. split; [eapply writes_trans; eauto|].
  intros Ho Hr. destruct W1 as [P1 [L1 _]]. destruct W2 as [P2 [L2 _]].
  destruct (S1 Ho) as [Ho2 E2]; [lia|].
  destruct (S2 Ho2) as [Ho3 E3]; [lia|].
  split; auto. rewrite E3, E2, app_assoc. reflexivity.
Qed.

Lemma hstep_bits : wsend_stmt -> forall o v n, 1 <= n <= 16 -> 0 <= v < 2 ^ n ->
  hstep o (send_bits o v n) (F.bits_le v n).
Proof.
  intros W o v n Hn Hv. split; [apply send_bits_writes|]. intros Ho Hr.
  destruct (send_bits_writes o v n) as [P _].
  apply W; auto; [apply Ho|lia].
Qed.

Lemma hstep_code : wsend_stmt -> forall o codes lens fl c, cimpl codes lens fl c ->
  hstep o (send_code o c codes lens) (F.send_sym fl c).
Proof.
  intros W o codes lens fl c [_ [Hl [Hc E]]]. unfold send_code. rewrite <- E. apply hstep_bits; auto; lia.
Qed.

Lemma flat_map_repeat_S : forall {A B} (f : A -> list B) x m,
  flat_map f (repeat x (S m)) = flat_map f (repeat x m) ++ f x.
Proof.
  intros A B f x m. change (repeat x (S m)) with (x :: repeat x m).
  rewrite repeat_cons, flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma hstep_iter : wsend_stmt -> forall m o codes lens fl c, cimpl codes lens fl c ->
  hstep o (Nat.iter m (fun o => send_code o c codes lens) o) (flat_map (F.send_tok fl) (repeat (F.CLen c) m)).
Proof.
  intros W m. induction m as [|m IH]; intros o codes lens fl c Hc; [apply hstep_refl|].
  change (Nat.iter (S m) (fun o => send_code o c codes lens) o)
    with (send_code (Nat.iter m (fun o => send_code o c codes lens) o) c codes lens).
  rewrite flat_map_repeat_S. apply (hstep_trans _ (Nat.iter m (fun o => send_code o c codes lens) o)); [apply IH; auto|]. exact (hstep_code W _ _ _ _ _ Hc).
Qed.

Lemma hstep_tree_loop : wsend_stmt -> forall fuel t mc blc bll fl o n p nl c mx mn,
  FlushHdr.st_inv p nl c mx mn ->
  (forall q, In q (Header.syms_loop fuel (dl t) mc n p nl c mx mn) -> cimpl blc bll fl (fst q)) ->
  hstep o (send_tree_loop fuel t mc blc bll o n p nl c mx mn)
    (flat_map (F.send_tok fl) (tl_loop fuel (dl t) mc n p nl c mx mn)).
Proof.
  intros W. induction fuel as [|fuel IH]; intros t mc blc bll fl o n p nl c mx mn Hi Hc;
    cbn [send_tree_loop tl_loop]; [apply hstep_refl|].
  cbn [Header.syms_loop] in Hc.
  destruct (n <=? mc); [|apply hstep_refl].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) (dl t))) eqn:Ec.
  - apply IH; auto. apply andb_true_iff in Ec. destruct Ec as [E1 E2]. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
    destruct Hi as [Hc0 [Hz Hnz]]. split; [lia|]. rewrite <- E2. split; auto.
  - assert (Hmm := FlushHdr.st_inv_next nl (Znth (n + 1) (dl t))).
    destruct (if Znth (n + 1) (dl t) =? 0 then _ else _) as [mx' mn'] eqn:Emm.
    assert (Hc1 : forall q, In q (Header.syms_loop fuel (dl t) mc (n + 1) nl (Znth (n + 1) (dl t)) 0 mx' mn') ->
                  cimpl blc bll fl (fst q)) by (intros q Hq; apply Hc, in_or_app; right; exact Hq).
    assert (Hout : forall q, In q (if c + 1 <? mn then repeat (nl, 0) (Z.to_nat (c + 1))
                       else if negb (nl =? 0) then
                         (if negb (nl =? p) then [(nl, 0)] else []) ++ [(REP_3_6, 2)]
                       else if c + 1 <=? 10 then [(REPZ_3_10, 3)] else [(REPZ_11_138, 7)]) ->
                   cimpl blc bll fl (fst q)) by (intros q Hq; apply Hc, in_or_app; left; exact Hq).
    rewrite flat_map_app. eapply hstep_trans; [|apply IH; auto].
    destruct Hi as [Hc0 [Hz Hnz]].
    destruct (Z.ltb_spec (c + 1) mn) as [Hlt|Hge].
    + apply hstep_iter; auto. apply (Hout (nl, 0)).
      destruct (Z.to_nat (c + 1)) as [|k] eqn:Ek; [lia|]. left; reflexivity.
    + destruct (Z.eqb_spec nl 0) as [E0|E0]; cbn [negb].
      * destruct (Hz E0) as [Hmx Hmn]. subst mx mn.
        cbn [flat_map F.send_tok]. rewrite app_nil_r.
        destruct (Z.leb_spec (c + 1) 10).
        -- eapply hstep_trans; [apply hstep_code; auto; apply (Hout (REPZ_3_10, 3)); left; reflexivity|].
           apply hstep_bits; auto; [lia|]. change (2 ^ 3) with 8. lia.
        -- eapply hstep_trans; [apply hstep_code; auto; apply (Hout (REPZ_11_138, 7)); left; reflexivity|].
           apply hstep_bits; auto; [lia|]. change (2 ^ 7) with 128. lia.
      * destruct (Z.eqb_spec nl p) as [Ep|Ep]; cbn [negb].
        -- destruct (Hnz E0) as [[Hmx [Hmn _]]|[_ [_ Hne]]]; [|congruence]. subst mx mn. cbn beta iota.
           cbn [flat_map F.send_tok]. rewrite app_nil_r.
           eapply hstep_trans; [apply hstep_code; auto; apply (Hout (REP_3_6, 2)); left; reflexivity|].
           apply hstep_bits; auto; [lia|]. change (2 ^ 2) with 4. lia.
        -- destruct (Hnz E0) as [[_ [_ Hpe]]|[Hmx [Hmn _]]]; [congruence|]. subst mx mn. cbn beta iota.
           cbn [flat_map F.send_tok]. rewrite app_nil_r.
           eapply hstep_trans; [apply hstep_code; auto; apply (Hout (nl, 0)); left; reflexivity|].
           eapply hstep_trans; [apply hstep_code; auto; apply (Hout (REP_3_6, 2)); right; left; reflexivity|].
           apply hstep_bits; auto; [lia|]. change (2 ^ 2) with 4. lia.
Qed.

Lemma hstep_tree : wsend_stmt -> forall o t mc bl fl, 0 <= mc -> 0 <= Znth 0 (dl t) ->
  (forall q, In q (Header.tree_syms (dl t) mc) -> cimpl (fc bl) (dl bl) fl (fst q)) ->
  hstep o (send_tree o t mc bl) (flat_map (F.send_tok fl) (tree_toks (dl t) mc)).
Proof.
  intros W o t mc bl fl Hmc H0 Hc. unfold send_tree, tree_toks. unfold Header.tree_syms in Hc.
  unfold Header.init_counts in *.
  assert (Hi := FlushHdr.st_inv_init (Znth 0 (dl t)) H0).
  destruct (Znth 0 (dl t) =? 0); apply hstep_tree_loop; auto.
Qed.

Lemma hstep_bl_lens : wsend_stmt -> forall m bl o rank blcodes, 0 <= rank ->
  (Z.to_nat (blcodes - rank) <= m)%nat ->
  (forall r, rank <= r < blcodes -> 0 <= Znth (Znth r bl_order) (dl bl) < 8) ->
  hstep o (send_bl_lens m bl o rank blcodes)
    (flat_map (fun c => F.bits_le c 3)
       (map (fun i => Znth (Znth (Z.of_nat i) bl_order) (dl bl)) (seq (Z.to_nat rank) (Z.to_nat (blcodes - rank))))).
Proof.
  intros W. induction m as [|m IH]; intros bl o rank blcodes Hr Hm Hb; cbn [send_bl_lens].
  - replace (Z.to_nat (blcodes - rank)) with O by lia. apply hstep_refl.
  - destruct (Z.ltb_spec rank blcodes) as [Hlt|Hge].
    + replace (Z.to_nat (blcodes - rank)) with (S (Z.to_nat (blcodes - (rank + 1)))) by lia.
      cbn [seq map flat_map]. rewrite Z2Nat.id by lia.
      replace (S (Z.to_nat rank)) with (Z.to_nat (rank + 1)) by lia.
      eapply hstep_trans; [apply hstep_bits; auto; [lia|change (2 ^ 3) with 8; apply Hb; lia]|].
      apply IH; [lia|lia|intros; apply Hb; lia].
    + replace (Z.to_nat (blcodes - rank)) with O by lia. apply hstep_refl.
Qed.

(* the code length code lengths *)
Lemma clpos_order : forall s, 0 <= s < 19 ->
  0 <= Znth s F.clpos < 19 /\ Znth (Znth s F.clpos) bl_order = s.
Proof.
  intros s Hs. assert (E : s = Z.of_nat (Z.to_nat s)) by lia. rewrite E.
  assert (Hn : (Z.to_nat s < 19)%nat) by lia. remember (Z.to_nat s) as k. clear -Hn.
  do 19 (destruct k as [|k]; [split; reflexivity || (cbv; split; congruence)|]). lia.
Qed.

Lemma zlength_clsent : forall bl blcodes, 0 <= blcodes -> Zlength (clsent_of bl blcodes) = blcodes.
Proof. intros. unfold clsent_of. rewrite Zlength_map, Zlength_correct, length_seq. lia. Qed.

Lemma znth_seq0 : forall i k, 0 <= i < Z.of_nat k -> Znth i (seq 0 k) = Z.to_nat i.
Proof.
  intros i k Hi. unfold Znth. destruct (Z_lt_dec i 0); [lia|].
  rewrite nth_indep with (d' := 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. reflexivity.
Qed.

Lemma znth_clsent : forall bl blcodes i, 0 <= i < blcodes ->
  Znth i (clsent_of bl blcodes) = Znth (Znth i bl_order) (dl bl).
Proof.
  intros bl blcodes i Hi. unfold clsent_of.
  rewrite Znth_map by (rewrite Zlength_correct, length_seq; lia).
  rewrite znth_seq0 by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma cl_lens_clsent : forall bl blcodes, 0 <= blcodes <= 19 -> 19 <= Zlength (dl bl) ->
  (forall r, blcodes <= r < 19 -> Znth (Znth r bl_order) (dl bl) = 0) ->
  F.cl_lens (clsent_of bl blcodes) = sublist 0 19 (dl bl).
Proof.
  intros bl blcodes Hb Hl Hz. unfold F.cl_lens.
  apply VST.zlist.list_solver.Znth_eq_ext.
  - rewrite Zlength_map, Zlength_correct, length_seq, Zlength_sublist by lia. reflexivity.
  - intros s Hs. rewrite Zlength_map, Zlength_correct, length_seq in Hs. cbn in Hs.
    rewrite Znth_map by (rewrite Zlength_correct, length_seq; cbn; lia).
    rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    rewrite znth_seq0 by (cbn; lia). rewrite Z2Nat.id by lia.
    destruct (clpos_order s Hs) as [Hp Ho].
    rewrite zlength_clsent by lia.
    destruct (Z.ltb_spec (Znth s F.clpos) blcodes).
    + rewrite znth_clsent by lia. rewrite Ho. reflexivity.
    + rewrite <- (Hz (Znth s F.clpos)) by lia. rewrite Ho. reflexivity.
Qed.

Theorem rtd_hdr_ok : wsend_stmt -> hdr_stmt.
Proof.
  intros W o lt dt bl lcodes dcodes blcodes Ho Hp Hlc Hdc Hbc Hlt Hdt Hbl Hfc Hlr Hdr Hbr Hz Hc Hroom.
  cbv zeta.
  assert (Ecl := cl_lens_clsent bl blcodes ltac:(lia) Hbl Hz).
  split; [exact Ecl|].
  unfold dyn_hdr_bits. rewrite Ecl, zlength_clsent by lia. rewrite flat_map_app.
  assert (Hst : hstep o (send_all_trees o lt dt bl lcodes dcodes blcodes)
    (F.bits_le (lcodes - 257) 5 ++ F.bits_le (dcodes - 1) 5 ++ F.bits_le (blcodes - 4) 4 ++
     flat_map (fun c => F.bits_le c 3) (clsent_of bl blcodes) ++
     flat_map (F.send_tok (sublist 0 19 (dl bl))) (tree_toks (dl lt) (lcodes - 1)) ++
     flat_map (F.send_tok (sublist 0 19 (dl bl))) (tree_toks (dl dt) (dcodes - 1)))).
  { unfold send_all_trees.
    eapply hstep_trans; [apply hstep_bits; auto; [lia|change (2 ^ 5) with 32; lia]|].
    eapply hstep_trans; [apply hstep_bits; auto; [lia|change (2 ^ 5) with 32; lia]|].
    eapply hstep_trans; [apply hstep_bits; auto; [lia|change (2 ^ 4) with 16; lia]|].
    eapply hstep_trans.
    { unfold clsent_of. replace (Z.to_nat blcodes) with (Z.to_nat (blcodes - 0)) by lia.
      change (seq 0) with (seq (Z.to_nat 0)).
      apply (hstep_bl_lens W 19 bl _ 0 blcodes); [lia|lia|].
      intros r Hr. assert (Hor : 0 <= Znth r bl_order < 19).
      { assert (E : r = Z.of_nat (Z.to_nat r)) by lia. rewrite E.
        assert (Hn : (Z.to_nat r < 19)%nat) by lia. remember (Z.to_nat r) as k. clear -Hn.
        do 19 (destruct k as [|k]; [cbv; split; congruence|]). lia. }
      specialize (Hbr _ Hor). lia. }
    eapply hstep_trans; [apply hstep_tree; auto; [lia|apply Hlr; lia|]|apply hstep_tree; auto; [lia|apply Hdr; lia|]].
    all: intros q Hq; apply Hc, in_or_app; auto. }
  destruct Hst as [_ S]. exact (S Ho Hroom).
Qed.

(** * Lemma (i): the dynamic block header (send_all_trees): writes, bits_ok, size bounds *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits.
Require Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.

Module H := Zlib.proof.huffman.Header.

(** ** Writes (no hypothesis) *)

Lemma iter_send_code_writes : forall m o c codes lens,
  writes o (Nat.iter m (fun o => send_code o c codes lens) o).
Proof.
  induction m as [|m IH]; intros; [apply writes_refl|].
  change (Nat.iter (S m) (fun o => send_code o c codes lens) o)
    with (send_code (Nat.iter m (fun o => send_code o c codes lens) o) c codes lens).
  eapply writes_trans; [apply IH|apply send_code_writes].
Qed.

Lemma send_tree_loop_writes : forall fuel t mc blc bll o n p nl c mx mn,
  writes o (send_tree_loop fuel t mc blc bll o n p nl c mx mn).
Proof.
  induction fuel as [|fuel IH]; intros; cbn [send_tree_loop]; [apply writes_refl|].
  destruct (n <=? mc); [|apply writes_refl].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) (dl t))); [apply IH|].
  destruct (if Znth (n + 1) (dl t) =? 0 then _ else _) as [mx' mn'].
  eapply writes_trans; [|apply IH].
  destruct (c + 1 <? mn); [apply iter_send_code_writes|].
  destruct (negb (nl =? 0)).
  - destruct (negb (nl =? p)); cbn beta iota.
    + eapply writes_trans; [|apply send_bits_writes]. eapply writes_trans; [|apply send_code_writes]. apply send_code_writes.
    + eapply writes_trans; [|apply send_bits_writes]. apply send_code_writes.
  - destruct (c + 1 <=? 10); (eapply writes_trans; [|apply send_bits_writes]); apply send_code_writes.
Qed.

Lemma send_tree_writes : forall o t mc bl, writes o (send_tree o t mc bl).
Proof.
  intros. unfold send_tree. destruct (Znth 0 (dl t) =? 0); apply send_tree_loop_writes.
Qed.

Lemma send_bl_lens_writes : forall m bl o rank blcodes, writes o (send_bl_lens m bl o rank blcodes).
Proof.
  induction m as [|m IH]; intros; cbn [send_bl_lens]; [apply writes_refl|].
  destruct (rank <? blcodes); [|apply writes_refl].
  eapply writes_trans; [apply send_bits_writes|apply IH].
Qed.

Lemma send_all_trees_writes : forall o lt dt bl lcodes dcodes blcodes,
  writes o (send_all_trees o lt dt bl lcodes dcodes blcodes).
Proof.
  intros. unfold send_all_trees.
  eapply writes_trans; [|apply send_tree_writes]. eapply writes_trans; [|apply send_tree_writes].
  eapply writes_trans; [|apply send_bl_lens_writes].
  eapply writes_trans; [|apply send_bits_writes]. eapply writes_trans; [|apply send_bits_writes].
  apply send_bits_writes.
Qed.

(** ** bits_ok *)

Lemma send_code_ok : forall o c codes lens, bits_ok o -> code_ok codes lens c -> bits_ok (send_code o c codes lens).
Proof. intros o c codes lens Ho Hc. destruct (send_code_spec o c codes lens Ho Hc) as [_ [_ [H _]]]. exact H. Qed.

Lemma send_bits_ok : forall o v l, bits_ok o -> 1 <= l <= 16 -> 0 <= v < 2 ^ l -> bits_ok (send_bits o v l).
Proof. intros o v l Ho Hl Hv. destruct (send_bits_spec o v l Ho Hl Hv) as [_ [_ [H _]]]. exact H. Qed.

Lemma iter_send_code_ok : forall m o c codes lens, bits_ok o -> code_ok codes lens c ->
  bits_ok (Nat.iter m (fun o => send_code o c codes lens) o).
Proof.
  induction m as [|m IH]; intros o c codes lens Ho Hc; [exact Ho|].
  change (Nat.iter (S m) (fun o => send_code o c codes lens) o)
    with (send_code (Nat.iter m (fun o => send_code o c codes lens) o) c codes lens).
  apply send_code_ok; auto.
Qed.

(** The loop state of send_tree / scan_tree: the counters match the current length. *)
Definition st_inv (p nl c mx mn : Z) : Prop :=
  0 <= c < mx /\
  (nl = 0 -> mx = 138 /\ mn = 3) /\
  (nl <> 0 -> (mx = 6 /\ mn = 3 /\ p = nl) \/ (mx = 7 /\ mn = 4 /\ p <> nl)).

Lemma st_inv_next : forall cur nxt,
  let '(mx, mn) := if nxt =? 0 then (138, 3) else if cur =? nxt then (6, 3) else (7, 4) in
  st_inv cur nxt 0 mx mn.
Proof.
  intros cur nxt. destruct (Z.eqb_spec nxt 0) as [E|E]; [|destruct (Z.eqb_spec cur nxt) as [E2|E2]]; unfold st_inv.
  - split; [lia|]. split; [intros; lia|]. intros; contradiction.
  - split; [lia|]. split; [intros; contradiction|]. intros; left; lia.
  - split; [lia|]. split; [intros; contradiction|]. intros; right; lia.
Qed.

Lemma send_tree_loop_ok : forall fuel t mc blc bll o n p nl c mx mn,
  bits_ok o -> st_inv p nl c mx mn ->
  (forall q, In q (H.syms_loop fuel (dl t) mc n p nl c mx mn) -> code_ok blc bll (fst q)) ->
  bits_ok (send_tree_loop fuel t mc blc bll o n p nl c mx mn).
Proof.
  induction fuel as [|fuel IH]; intros t mc blc bll o n p nl c mx mn Ho Hi Hc; cbn [send_tree_loop]; [exact Ho|].
  cbn [H.syms_loop] in Hc.
  destruct (n <=? mc); [|exact Ho].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) (dl t))) eqn:Ec.
  - apply IH; auto. apply andb_true_iff in Ec. destruct Ec as [E1 E2]. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
    destruct Hi as [Hc0 [Hz Hnz]]. split; [lia|]. rewrite <- E2. split; auto.
  - assert (Hmm := st_inv_next nl (Znth (n + 1) (dl t))).
    destruct (if Znth (n + 1) (dl t) =? 0 then _ else _) as [mx' mn'] eqn:Emm.
    assert (Hc1 : forall q, In q (H.syms_loop fuel (dl t) mc (n + 1) nl (Znth (n + 1) (dl t)) 0 mx' mn') ->
                  code_ok blc bll (fst q)) by (intros q Hq; apply Hc, in_or_app; right; exact Hq).
    assert (Hout : forall q, In q (if c + 1 <? mn then repeat (nl, 0) (Z.to_nat (c + 1))
                       else if negb (nl =? 0) then
                         (if negb (nl =? p) then [(nl, 0)] else []) ++ [(REP_3_6, 2)]
                       else if c + 1 <=? 10 then [(REPZ_3_10, 3)] else [(REPZ_11_138, 7)]) ->
                   code_ok blc bll (fst q)) by (intros q Hq; apply Hc, in_or_app; left; exact Hq).
    apply IH; auto.
    destruct Hi as [Hc0 [Hz Hnz]].
    destruct (Z.ltb_spec (c + 1) mn) as [Hlt|Hge].
    + apply iter_send_code_ok; auto. apply (Hout (nl, 0)).
      destruct (Z.to_nat (c + 1)) as [|k] eqn:Ek; [lia|]. left; reflexivity.
    + destruct (Z.eqb_spec nl 0) as [E0|E0]; cbn [negb].
      * destruct (Hz E0) as [Hmx Hmn]. subst mx mn.
        destruct (Z.leb_spec (c + 1) 10).
        -- apply send_bits_ok; [apply send_code_ok; auto; apply (Hout (REPZ_3_10, 3)); left; reflexivity|lia|].
           change (2 ^ 3) with 8. lia.
        -- apply send_bits_ok; [apply send_code_ok; auto; apply (Hout (REPZ_11_138, 7)); left; reflexivity|lia|].
           change (2 ^ 7) with 128. lia.
      * destruct (Z.eqb_spec nl p) as [Ep|Ep]; cbn [negb].
        -- destruct (Hnz E0) as [[Hmx [Hmn _]]|[_ [_ Hne]]]; [|congruence]. subst mx mn. cbn beta iota.
           apply send_bits_ok; [apply send_code_ok; auto; apply (Hout (REP_3_6, 2)); left; reflexivity|lia|].
           change (2 ^ 2) with 4. lia.
        -- destruct (Hnz E0) as [[_ [_ Hpe]]|[Hmx [Hmn _]]]; [congruence|]. subst mx mn. cbn beta iota.
           apply send_bits_ok; [|lia|change (2 ^ 2) with 4; lia].
           apply send_code_ok; [apply send_code_ok; auto; apply (Hout (nl, 0)); left; reflexivity|].
           apply (Hout (REP_3_6, 2)); right; left; reflexivity.
Qed.

Lemma st_inv_init : forall nl, 0 <= nl ->
  let '(mx, mn) := if nl =? 0 then (138, 3) else (7, 4) in st_inv (-1) nl 0 mx mn.
Proof.
  intros nl Hnl. destruct (Z.eqb_spec nl 0) as [E|E]; unfold st_inv.
  - split; [lia|]. split; [intros; lia|]. intros; contradiction.
  - split; [lia|]. split; [intros; contradiction|]. intros; right; lia.
Qed.

Lemma send_tree_ok : forall o t mc bl, 0 <= mc ->
  bits_ok o -> (forall i, 0 <= i <= mc -> 0 <= Znth i (dl t)) ->
  (forall q, In q (H.tree_syms (dl t) mc) -> code_ok (fc bl) (dl bl) (fst q)) ->
  bits_ok (send_tree o t mc bl).
Proof.
  intros o t mc bl Hmc Ho Hl Hc. unfold send_tree. unfold H.tree_syms, H.init_counts in Hc.
  assert (Hi := st_inv_init (Znth 0 (dl t)) ltac:(apply Hl; lia)).
  destruct (Znth 0 (dl t) =? 0); apply send_tree_loop_ok; auto.
Qed.

Lemma send_bl_lens_ok : forall m bl o rank blcodes,
  bits_ok o -> (forall r, rank <= r < blcodes -> 0 <= Znth (Znth r bl_order) (dl bl) < 8) ->
  bits_ok (send_bl_lens m bl o rank blcodes).
Proof.
  induction m as [|m IH]; intros bl o rank blcodes Ho Hb; cbn [send_bl_lens]; [exact Ho|].
  destruct (Z.ltb_spec rank blcodes); [|exact Ho].
  apply IH; [|intros; apply Hb; lia]. apply send_bits_ok; auto; [lia|]. change (2 ^ 3) with 8. apply Hb; lia.
Qed.

Theorem send_all_trees_ok : forall o lt dt bl lcodes dcodes blcodes,
  bits_ok o -> 257 <= lcodes <= 286 -> 1 <= dcodes <= 30 -> 4 <= blcodes <= 19 ->
  (forall r, 0 <= r < blcodes -> 0 <= Znth (Znth r bl_order) (dl bl) < 8) ->
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= Znth i (dl lt)) ->
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= Znth i (dl dt)) ->
  (forall q, In q (H.tree_syms (dl lt) (lcodes - 1)) -> code_ok (fc bl) (dl bl) (fst q)) ->
  (forall q, In q (H.tree_syms (dl dt) (dcodes - 1)) -> code_ok (fc bl) (dl bl) (fst q)) ->
  bits_ok (send_all_trees o lt dt bl lcodes dcodes blcodes).
Proof.
  intros o lt dt bl lcodes dcodes blcodes Ho Hl Hd Hb Hbl Hlt Hdt Hcl Hcd. unfold send_all_trees.
  apply send_tree_ok; [lia|..|auto|auto]. apply send_tree_ok; [lia|..|auto|auto]. apply send_bl_lens_ok; [|intros; apply Hbl; lia].
  apply send_bits_ok; [|lia|change (2 ^ 4) with 16; lia].
  apply send_bits_ok; [|lia|change (2 ^ 5) with 32; lia].
  apply send_bits_ok; [exact Ho|lia|change (2 ^ 5) with 32; lia].
Qed.

(** ** The stream: at most one symbol per table entry *)

Lemma syms_loop_length : forall fuel lens mc n p nl c mx mn,
  0 <= c -> 3 <= mn -> 0 <= n ->
  Z.of_nat (length (H.syms_loop fuel lens mc n p nl c mx mn)) <= c + Z.max 0 (mc + 1 - n).
Proof.
  induction fuel as [|fuel IH]; intros lens mc n p nl c mx mn Hc Hmn Hn; cbn [H.syms_loop]; [simpl; lia|].
  destruct (Z.leb_spec n mc) as [Hle|Hgt]; [|simpl; lia].
  destruct ((c + 1 <? mx) && (nl =? Znth (n + 1) lens)).
  - assert (H1 := IH lens mc (n + 1) p (Znth (n + 1) lens) (c + 1) mx mn ltac:(lia) Hmn ltac:(lia)). lia.
  - set (mm := if Znth (n + 1) lens =? 0 then (138, 3) else if nl =? Znth (n + 1) lens then (6, 3) else (7, 4)).
    assert (Hmm : mm = (fst mm, snd mm)) by (destruct mm; reflexivity).
    assert (Hmn' : 3 <= snd mm) by (unfold mm; destruct (_ =? 0); [|destruct (_ =? _)]; simpl; lia).
    rewrite Hmm. cbn beta iota. rewrite length_app, Nat2Z.inj_add.
    assert (H1 := IH lens mc (n + 1) nl (Znth (n + 1) lens) 0 (fst mm) (snd mm) ltac:(lia) Hmn' ltac:(lia)).
    assert (Hout : Z.of_nat (length (if c + 1 <? mn then repeat (nl, 0) (Z.to_nat (c + 1))
                       else if negb (nl =? 0) then
                         (if negb (nl =? p) then [(nl, 0)] else []) ++ [(REP_3_6, 2)]
                       else if c + 1 <=? 10 then [(REPZ_3_10, 3)] else [(REPZ_11_138, 7)])) <= c + 1).
    { destruct (Z.ltb_spec (c + 1) mn).
      - rewrite repeat_length. lia.
      - destruct (negb (nl =? 0)); [destruct (negb (nl =? p))|destruct (c + 1 <=? 10)]; simpl; lia. }
    lia.
Qed.

Lemma tree_syms_length : forall lens mc, 0 <= mc -> Z.of_nat (length (H.tree_syms lens mc)) <= mc + 1.
Proof.
  intros lens mc Hmc. unfold H.tree_syms, H.init_counts.
  destruct (Znth 0 lens =? 0); (eapply Z.le_trans; [apply syms_loop_length; lia|]); lia.
Qed.

(** ** The crude bound with the bit-length lengths given as a longer list *)

Lemma stream_bits_ext : forall bll1 bll2 l, (forall q, In q l -> Znth (fst q) bll1 = Znth (fst q) bll2) ->
  H.stream_bits bll1 l = H.stream_bits bll2 l.
Proof.
  intros bll1 bll2 l Hq. unfold H.stream_bits, H.cost_tau. f_equal. apply map_ext_in.
  intros q Hin. rewrite (Hq q Hin). reflexivity.
Qed.

Lemma stream_crude : forall bll lens mc, 0 <= mc -> 19 <= Zlength bll ->
  (forall s, 0 <= s < 19 -> Znth s bll <= 7) -> (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) ->
  H.stream_bits bll (H.tree_syms lens mc) <= 7 * (mc + 1).
Proof.
  intros bll lens mc Hmc HL Hb Hl.
  rewrite (stream_bits_ext bll (sublist 0 19 bll)).
  - apply H.tree_syms_crude; auto. intros s.
    destruct (Z_le_gt_dec 0 s); [destruct (Z_lt_ge_dec s 19)|].
    + rewrite Znth_sublist by lia. rewrite Z.add_0_r. apply Hb; lia.
    + rewrite Znth_overflow by (rewrite Zlength_sublist; lia). cbv [default Inhabitant_Z]; lia.
    + rewrite Znth_underflow by lia. cbv [default Inhabitant_Z]; lia.
  - intros q Hq. assert (Hok := H.tree_syms_ok lens mc Hmc Hl q Hq). destruct Hok as [Hs _].
    rewrite Znth_sublist by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(** ** charge reads only the indices below its bound *)

Lemma zrun_nat_ext : forall l1 l2 m, (forall i, 0 <= i < Z.of_nat m -> Znth i l1 = Znth i l2) ->
  H.zrun_nat l1 m = H.zrun_nat l2 m.
Proof.
  intros l1 l2 m. induction m as [|m IH]; intros E; cbn [H.zrun_nat]; [reflexivity|].
  rewrite E by lia. rewrite IH by (intros; apply E; lia). reflexivity.
Qed.

Lemma charge_ext : forall tau l1 l2 n, 0 <= n -> (forall i, 0 <= i < n -> Znth i l1 = Znth i l2) ->
  H.charge tau l1 n = H.charge tau l2 n.
Proof.
  intros tau l1 l2 n Hn E. unfold H.charge.
  assert (G : forall m, (Z.of_nat m <= n) -> H.chs_nat tau l1 m = H.chs_nat tau l2 m).
  { induction m as [|m IH]; intros Hm; cbn [H.chs_nat]; [reflexivity|].
    rewrite IH by lia. f_equal. unfold H.ch, H.zrun.
    rewrite E by lia. rewrite (zrun_nat_ext l1 l2) by (intros i Hi; apply E; lia). reflexivity. }
  apply G. lia.
Qed.

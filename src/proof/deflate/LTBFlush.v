(** * deflate_bound theory: the bits of one _tr_flush_block at level > 0, for any lit_bufsize

    The generalisation of the case analysis of huffman/BlockBoundProof.v (block_bound_proof) to every memLevel:
    either a Huffman block (static or dynamic, at most the static cost; when buf <> NULL also cheaper than a
    stored block), or a stored block (only when buf <> NULL and cheaper than the static codes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.Bits Zlib.proof.huffman.Overlay
               Zlib.proof.huffman.BlockBound Zlib.proof.huffman.DynSum.
Require Zlib.proof.huffman.BlockBoundProof Zlib.proof.huffman.BlockStored Zlib.proof.huffman.FlushDyn
        Zlib.proof.huffman.TreeDD Zlib.proof.huffman.RepairBound Zlib.proof.huffman.OverlayDyn
        Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.

(** The last block is padded to a byte. *)
Definition rnd (last x : Z) : Z := if last =? 0 then x else 8 * ((x + 7) / 8).

Lemma fbc_rnd_mono : forall last x y, x <= y -> rnd last x <= rnd last y.
Proof.
  intros last x y H. unfold rnd. destruct (last =? 0); [lia|].
  assert ((x + 7) / 8 <= (y + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma fbc_rnd_8 : forall last k, rnd last (8 * k) = 8 * k.
Proof.
  intros last k. unfold rnd. destruct (last =? 0); [lia|].
  replace (8 * k + 7) with (7 + k * 8) by lia. rewrite Z.div_add by lia. change (7 / 8) with 0. lia.
Qed.

(** The end of _tr_flush_block: init_block keeps the output, the last block is padded to a byte. *)
Lemma fbc_finish : forall s1 (p : outbuf * block_kind) last,
  0 <= o_bi_valid (fst p) <= 16 ->
  bitpos (tr_out (fst (let '(o, kind) := p in
                       let s := init_block (set_out s1 o) in
                       let s := if negb (last =? 0) then set_out s (bi_windup (tr_out s)) else s in
                       (s, kind)))) = rnd last (bitpos (fst p)).
Proof.
  intros s1 [o kind] last Hv. cbn [fst] in *. unfold rnd.
  assert (Hi : tr_out (init_block (set_out s1 o)) = o) by reflexivity.
  destruct (last =? 0); cbn [negb fst]; [rewrite Hi; reflexivity|].
  change (tr_out (set_out (init_block (set_out s1 o)) (bi_windup (tr_out (init_block (set_out s1 o))))))
    with (bi_windup (tr_out (init_block (set_out s1 o)))).
  rewrite Hi. destruct (BlockBoundProof.windup_bitpos' o Hv) as [-> _]. reflexivity.
Qed.

Lemma flush_block_cost : forall t syms buf B last,
  flush_pre t syms -> 0 <= last <= 1 -> 0 < tr_level t -> B = blk_len syms ->
  match buf with Some b => B <= 65535 /\ B <= Zlength b | None => True end ->
  let p := bitpos (tr_out t) in
  let p' := bitpos (tr_out (fst (tr_flush_block t buf B last))) in
  (p' <= rnd last (p + 3 + stat_data syms) /\ (buf <> None -> p' <= rnd last (p + 8 * B + 24))) \/
  (buf <> None /\ 8 * (B + 4) <= stat_data syms + 10 /\ p' = 8 * ((p + 10) / 8) + 32 + 8 * B).
Proof.
  intros t syms buf B last Hpre Hlast Hlev HB Hbuf. cbv zeta.
  assert (Hds : DynSum.dyn_sum_statement)
    by exact (DynSum.dyn_sum_holds FlushDyn.dyn_prep (TreeDD.tree_dd RepairBound.repair15_bound)).
  assert (Hov : overlay_statement) by exact (OverlayDyn.overlay_proof Hds).
  pose proof Hpre as [_ [Hok [Hp0 [Hv7 _]]] [Hsn [Hsl [Hval _]]] _ _ _ _].
  assert (HB0 : 0 <= B) by (rewrite HB; apply BlockBoundProof.blk_len_nonneg; exact Hval).
  rewrite tr_flush_block_prep.
  destruct (Hds t syms B Hpre Hlev) as (s' & olb & slb & mbi & ll & dl0 & dd & dd0 & Hh & E & D).
  pose proof (ds_prep _ _ _ _ _ _ _ _ _ _ _ _ _ D) as Hp.
  pose proof (ds_keep _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Ko [KL [Ks Kst]]].
  assert (Hcall := Hov t syms buf B last Hpre Hlast). unfold flush_call in Hcall. rewrite Hp in Hcall.
  rewrite Hp. cbv beta iota zeta in Hcall. cbv beta iota.
  set (os := send_bits (tr_out s') (Z.shiftl STATIC_TREES 1 + last) 3) in *.
  set (od := send_all_trees (send_bits (tr_out s') (Z.shiftl DYN_TREES 1 + last) 3) (tr_ltree s') (tr_dtree s')
               (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1)) in *.
  rewrite KL, Ks, Hsn.
  assert (Hv3 : forall u, 0 <= u <= 2 -> 0 <= Z.shiftl u 1 + last < 2 ^ 3).
  { intros u Hu. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8. lia. }
  assert (Bos : Bits.bitpos os = Bits.bitpos (tr_out t) + 3).
  { unfold os. rewrite Ko.
    destruct (send_bits_spec (tr_out t) (Z.shiftl STATIC_TREES 1 + last) 3 Hok ltac:(lia)
                (Hv3 STATIC_TREES ltac:(unfold STATIC_TREES; lia))) as [Hx _]. exact Hx. }
  assert (Bod : Bits.bitpos od = Bits.bitpos (tr_out t) + 3 + Hh).
  { unfold od. rewrite Ko.
    destruct (send_bits_spec (tr_out t) (Z.shiftl DYN_TREES 1 + last) 3 Hok ltac:(lia)
                (Hv3 DYN_TREES ltac:(unfold DYN_TREES; lia))) as [Hx [_ [Ok1 _]]].
    destruct (ds_hdr _ _ _ _ _ _ _ _ _ _ _ _ _ D _ Ok1) as [_ [Hy _]]. unfold Header.bitpos in Hy.
    unfold Bits.bitpos in *. lia. }
  assert (Sb : overlay_ok (tr_lit_bufsize t) syms (os, static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len) ->
               0 <= o_bi_valid (compress_block os (tr_lit_bufsize t) (3 * Zlength syms) static_ltree_code
                                  static_ltree_len static_dtree_code static_dtree_len) <= 16 /\
               Bits.bitpos (compress_block os (tr_lit_bufsize t) (3 * Zlength syms) static_ltree_code
                              static_ltree_len static_dtree_code static_dtree_len) =
                 Bits.bitpos (tr_out t) + 3 + stat_data syms).
  { intros Hx. destruct (BlockBoundProof.call_bits _ _ _ _ _ _ _ Hval Hx) as [V1 B1]. split; [exact V1|].
    rewrite B1, Bos. pose proof (ds_cost_stat _ _ _ _ _ _ _ _ _ _ _ _ _ D). lia. }
  assert (Db : overlay_ok (tr_lit_bufsize t) syms (od, fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')) ->
               0 <= o_bi_valid (compress_block od (tr_lit_bufsize t) (3 * Zlength syms) (fc (tr_ltree s'))
                                  (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s'))) <= 16 /\
               Bits.bitpos (compress_block od (tr_lit_bufsize t) (3 * Zlength syms) (fc (tr_ltree s'))
                              (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s'))) =
                 Bits.bitpos (tr_out t) + 3 + Hh + dyn_data syms ll dl0).
  { intros Hx. destruct (BlockBoundProof.call_bits _ _ _ _ _ _ _ Hval Hx) as [V1 B1]. split; [exact V1|].
    rewrite B1, Bod.
    pose proof (ds_cost_guard _ _ _ _ _ _ _ _ _ _ _ _ _ D (length syms)) as G. rewrite firstn_all in G. rewrite G.
    destruct (ds_guard _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [G1 _]. rewrite G1.
    destruct (ds_lmax _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hm _].
    rewrite Znth_upd_Znth_other by (unfold END_BLOCK in *; lia).
    pose proof (ds_cost_dyn _ _ _ _ _ _ _ _ _ _ _ _ _ D). lia. }
  destruct (ds_lenb _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [Hslb Holb].
  pose proof (ds_E _ _ _ _ _ _ _ _ _ _ _ _ _ D) as [HE _].
  pose proof (Z.mul_div_le (stat_data syms + 10) 8 ltac:(lia)) as Hsd.
  set (X := Hh + dyn_data syms ll dl0 + E + 10) in *.
  assert (Hdyn : slb <> olb -> X < stat_data syms + 10 /\ olb = X / 8).
  { intros Hne. destruct ((slb <=? X / 8) || (tr_strategy t =? Z_FIXED)) eqn:Ec; [lia|].
    apply orb_false_iff in Ec as [Ec _]. apply Z.leb_gt in Ec. split; [|exact Holb].
    rewrite Hslb in Ec. apply BlockBoundProof.div8_lt in Ec. lia. }
  assert (Holb' : olb <= slb).
  { destruct ((slb <=? X / 8) || (tr_strategy t =? Z_FIXED)) eqn:Ec; [lia|].
    apply orb_false_iff in Ec as [Ec _]. apply Z.leb_gt in Ec. lia. }
  destruct buf as [b|].
  - destruct Hbuf as [HB1 HB2].
    assert (Hu : u64 (B + 4) = B + 4) by (unfold u64; apply Z.mod_small; lia).
    rewrite Hu in Hcall |- *.
    destruct (Z.leb_spec (B + 4) olb) as [Hst|Hst].
    + right. split; [discriminate|]. split; [lia|].
      destruct (BlockStored.stored_block_bitpos (tr_out s') b B last ltac:(rewrite Ko; exact Hok) Hlast HB0) as [E1 V1].
      rewrite (fbc_finish s' (tr_stored_block (tr_out s') b B last, BK_stored) last ltac:(cbn [fst]; lia)).
      cbn [fst]. rewrite E1, Ko.
      replace (8 * ((Bits.bitpos (tr_out t) + 3 + 7) / 8) + 32 + 8 * B)
        with (8 * ((Bits.bitpos (tr_out t) + 10) / 8 + 4 + B)) by (replace (Bits.bitpos (tr_out t) + 3 + 7) with (Bits.bitpos (tr_out t) + 10) by lia; ring).
      rewrite fbc_rnd_8. ring.
    + left. destruct (Z.eqb_spec slb olb) as [Heq|Hne].
      * destruct (Sb (Hcall _ eq_refl)) as [V1 B1].
        rewrite (fbc_finish s' (_, BK_static) last V1). cbn [fst]. rewrite B1.
        split; [lia|]. intros _. apply fbc_rnd_mono.
        assert (Hs8 : (stat_data syms + 10) / 8 < B + 4) by lia. apply BlockBoundProof.div8_lt in Hs8. lia.
      * destruct (Db (Hcall _ eq_refl)) as [V1 B1]. destruct (Hdyn Hne) as [Hx Ho].
        rewrite (fbc_finish s' (_, BK_dynamic) last V1). cbn [fst]. rewrite B1.
        split; [apply fbc_rnd_mono; lia|]. intros _. apply fbc_rnd_mono.
        rewrite Ho in Hst. apply BlockBoundProof.div8_lt in Hst. lia.
  - left. split; [|intros []; reflexivity].
    destruct (Z.eqb_spec slb olb) as [Heq|Hne].
    + destruct (Sb (Hcall _ eq_refl)) as [V1 B1].
      rewrite (fbc_finish s' (_, BK_static) last V1). cbn [fst]. rewrite B1. lia.
    + destruct (Db (Hcall _ eq_refl)) as [V1 B1]. destruct (Hdyn Hne) as [Hx Ho].
      rewrite (fbc_finish s' (_, BK_dynamic) last V1). cbn [fst]. rewrite B1.
      apply fbc_rnd_mono. lia.
Qed.

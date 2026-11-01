(* RT-D part FBO, kit: fbo_fspec proved (fbo_proof) and flush_pending's functional spec
   under the precondition fix (fpend_fixed); fpend_fspec as stated is false (RTDFix.v: bi_flush writes at
   pending_buf[pending], not at the end of the pending bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Lists *)

Lemma fbo_sublist_clip {A} lo hi (l : list A) : sublist lo hi l = sublist lo (Z.min hi (Zlength l)) l.
Proof.
  unfold sublist. f_equal. destruct (Z.le_ge_cases hi (Zlength l)) as [L|L].
  - rewrite Z.min_l by lia. reflexivity.
  - rewrite Z.min_r by lia. rewrite Zlength_correct in L.
    rewrite !firstn_all2; [reflexivity| |]; rewrite ?Zlength_correct; lia.
Qed.

Lemma fbo_sublist_rejoin {A} lo mid hi (l : list A) :
  0 <= lo <= mid -> mid <= hi -> sublist lo mid l ++ sublist mid hi l = sublist lo hi l.
Proof.
  intros H1 H2. pose proof (Zlength_nonneg l).
  rewrite (fbo_sublist_clip lo mid), (fbo_sublist_clip mid hi), (fbo_sublist_clip lo hi).
  destruct (Z.le_ge_cases mid (Zlength l)) as [L|L].
  - rewrite (Z.min_l mid) by lia. apply sublist_rejoin; lia.
  - rewrite (Z.min_r mid), (Z.min_r hi) by lia. rewrite (sublist_nil_gen l mid) by lia. apply app_nil_r.
Qed.

Lemma fbo_Zlength_prefix {A} n (l : list A) : 0 <= n -> Zlength (sublist 0 n l) = Z.min n (Zlength l).
Proof.
  intros Hn. destruct (Z.le_ge_cases n (Zlength l)) as [L|L].
  - rewrite Zlength_sublist by lia. lia.
  - rewrite sublist_same_gen by lia. lia.
Qed.

Lemma fbo_Zlength_lz_copy n d out : Zlength (F.lz_copy n d out) = Zlength out + Z.of_nat n.
Proof.
  revert out. induction n as [|n IH]; intros out; cbn [F.lz_copy]; [lia|].
  rewrite IH, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

(** the symbols expand [out] by [blk_len] bytes, each symbol at least one *)
Lemma fbo_syms_len w out syms :
  syms_rok w out syms ->
  Zlength (F.syms_data out (map fsym syms)) = Zlength out + blk_len syms /\ Zlength syms <= blk_len syms.
Proof.
  revert out. induction syms as [|x r IH]; intros out Hr.
  - change (blk_len []) with 0. rewrite Zlength_nil. split; [cbn; lia|lia].
  - destruct Hr as [Hx Hr]. destruct (IH _ Hr) as [E1 E2].
    change (F.syms_data out (map fsym (x :: r))) with (F.syms_data (F.sym_data out (fsym x)) (map fsym r)).
    change (blk_len (x :: r)) with (sym_len x + blk_len r).
    assert (Hs : Zlength (F.sym_data out (fsym x)) = Zlength out + sym_len x /\ 1 <= sym_len x).
    { unfold fsym, sym_len. destruct (fst x =? 0).
      - cbn [F.sym_data]. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      - cbn [F.sym_data]. rewrite fbo_Zlength_lz_copy. destruct Hx as (Hx & _). rewrite Z2Nat.id by lia. lia. }
    rewrite E1, Zlength_cons. lia.
Qed.

Lemma fbo_blocks_ok_app w out bs b :
  F.blocks_ok w out bs -> F.block_ok w (F.expand out bs) b -> F.blocks_ok w out (bs ++ [b]).
Proof.
  revert out. induction bs as [|c r IH]; intros out H1 H2.
  - cbn [app F.blocks_ok]. split; [exact H2|exact I].
  - destruct H1 as [Hc Hr]. cbn [app F.blocks_ok]. split; [exact Hc|].
    apply IH; [exact Hr|exact H2].
Qed.

Lemma fbo_expand_app hist bs b : F.expand hist (bs ++ [b]) = F.block_data (F.expand hist bs) b.
Proof. unfold F.expand. rewrite fold_left_app. reflexivity. Qed.

(** ** flush_pending *)

(* flush_pending after _tr_flush_bits *)
Definition fp_tail (s : dstate) (z : strm) : option (dstate * strm) :=
  let len := if d_pending s >? z_avail_out z then z_avail_out z else u32 (d_pending s) in
  if len =? 0 then Some (s, z) else
  let* bytes := mb_read (mkMB (o_buf (tr_out (d_tr s))) (d_pbm s)) (d_po s) len in
  let* z := out_put z bytes in
  let s := set_d_po s (d_po s + len) in
  let z := set_z_total_out z (u64 (z_total_out z + len)) in
  let z := set_z_avail_out z (z_avail_out z - len) in
  let o := tr_out (d_tr s) in
  let s := set_d_out s (mkOut (o_buf o) (o_pending o - len) (o_bi_buf o) (o_bi_valid o) (o_bi_used o), d_pbm s) in
  let s := if d_pending s =? 0 then set_d_po s 0 else s in
  Some (s, z).

Lemma fp_unfold s z : c_flush_pending s z = let* o := c_tr_flush_bits (d_out s) in fp_tail (set_d_out s o) z.
Proof. reflexivity. Qed.

Lemma fp_tail_ok s z s' z' :
  0 <= d_po s -> 0 <= d_pending s -> zout_ok z -> fp_tail s z = Some (s', z') ->
  exists x, zout_only z z' x /\ x ++ pend s' = pend s /\ bibits s' = bibits s.
Proof.
  intros Hpo Hp Hz H. unfold fp_tail in H.
  set (len := if d_pending s >? z_avail_out z then z_avail_out z else u32 (d_pending s)) in H.
  assert (Hl : 0 <= len <= d_pending s /\ len <= z_avail_out z).
  { subst len. destruct Hz as (Ha & _). destruct (Z.gtb_spec (d_pending s) (z_avail_out z)); [lia|].
    unfold u32. pose proof (Z.mod_le (d_pending s) 4294967296 ltac:(lia) ltac:(lia)).
    pose proof (Z.mod_pos_bound (d_pending s) 4294967296 ltac:(lia)). lia. }
  clearbody len.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - injection H as <- <-. exists []. split; [unfold zout_only; rewrite app_nil_r, Zlength_nil; repeat split; lia|].
    split; reflexivity.
  - destruct (mb_read _ _ _) as [bytes|] eqn:Er; [|discriminate]. cbn [bind] in H.
    unfold mb_read in Er. destruct (_ && _) eqn:Ed; [|discriminate]. injection Er as <-.
    apply andb_prop in Ed. destruct Ed as [_ Ed]. unfold mb_definedb in Ed.
    apply andb_prop in Ed. destruct Ed as [Ed _]. apply andb_prop in Ed. destruct Ed as [_ Ed].
    apply Z.leb_le in Ed. cbn [mb_val] in Ed.
    assert (Hxl : Zlength (sublist (d_po s) (d_po s + len) (o_buf (tr_out (d_tr s)))) = len)
      by (rewrite Zlength_sublist by lia; lia).
    unfold out_put in H. rewrite Hxl in H.
    destruct (Z.leb_spec len (z_avail_out z)) as [_|]; [|lia]. cbn [bind] in H.
    injection H as Hs Hz'. subst z'.
    exists (sublist (d_po s) (d_po s + len) (o_buf (tr_out (d_tr s)))).
    split.
    { unfold zout_only. rewrite Hxl. cbn. rewrite u64_id by (destruct Hz as (? & ? & ?); lia).
      repeat split; reflexivity. }
    subst s'.
    match goal with |- context [d_pending ?X =? 0] =>
      assert (EX : d_pending X = d_pending s - len) by reflexivity;
      assert (PX : pend X = sublist (d_po s + len) (d_po s + len + (d_pending s - len)) (o_buf (tr_out (d_tr s))))
        by reflexivity;
      assert (P0 : pend (set_d_po X 0) = sublist 0 (0 + (d_pending s - len)) (o_buf (tr_out (d_tr s))))
        by reflexivity;
      assert (BX : bibits X = bibits s) by reflexivity;
      assert (B0 : bibits (set_d_po X 0) = bibits s) by reflexivity;
      rewrite EX; destruct (Z.eqb_spec (d_pending s - len) 0) as [E|E]; [rewrite P0, B0|rewrite PX, BX]
    end.
    + split; [|reflexivity]. rewrite E, Z.add_0_r, sublist_nil, app_nil_r. unfold pend. f_equal. lia.
    + split; [|reflexivity]. unfold pend. rewrite fbo_sublist_rejoin by lia. f_equal. lia.
Qed.

Lemma fbo_obits_pend s : d_po s = 0 -> F.bytes_bits (pend s) ++ bibits s = obits (tr_out (d_tr s)).
Proof. intros H. unfold pend, bibits, obits, d_pending, d_bi_valid. rewrite H, Z.add_0_l. reflexivity. Qed.

(* flush_pending when bi_flush writes at the end of the pending bytes (nothing to write, or pending_out at the
   start of pending_buf) *)
Lemma fbo_fpend_gen s z s' z' :
  writer_fspec -> bits_ok (tr_out (d_tr s)) -> 0 <= d_po s -> zout_ok z -> (d_bi_valid s < 8 \/ d_po s = 0) ->
  c_flush_pending s z = Some (s', z') ->
  exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.
Proof.
  intros W Hb Hpo Hz Hr H. rewrite fp_unfold in H.
  destruct (c_tr_flush_bits (d_out s)) as [[o' m']|] eqn:Ef; [|discriminate]. cbn [bind] in H.
  assert (Hmid : bits_ok o' /\
    F.bytes_bits (pend (set_d_out s (o', m'))) ++ bibits (set_d_out s (o', m')) = F.bytes_bits (pend s) ++ bibits s).
  { destruct Hr as [Hlt|H0].
    - unfold d_out, c_tr_flush_bits, c_bi_flush in Ef. unfold d_bi_valid in Hlt.
      destruct (Z.eqb_spec (o_bi_valid (tr_out (d_tr s))) 16); [lia|].
      destruct (Z.geb_spec (o_bi_valid (tr_out (d_tr s))) 8); [lia|].
      injection Ef as <- <-. split; [exact Hb|reflexivity].
    - destruct W as (_ & _ & W3 & _). destruct (W3 _ _ _ _ Hb Ef) as (Hb' & _ & Eo). split; [exact Hb'|].
      rewrite (fbo_obits_pend s H0), (fbo_obits_pend (set_d_out s (o', m')) H0). exact Eo. }
  destruct Hmid as (Hb' & Hmid).
  destruct (fp_tail_ok (set_d_out s (o', m')) z s' z' Hpo (proj2 (proj2 Hb')) Hz H) as (x & Hzo & Ex & Eb).
  exists x. split; [exact Hzo|]. rewrite <- Hmid, <- Ex, Eb. reflexivity.
Qed.

(** fpend_fspec with the precondition fix: bi_valid < 8, or pending_out at the start of pending_buf. *)
Lemma fpend_fixed : writer_fspec ->
  forall s z s' z',
    outok s -> zout_ok z -> (d_bi_valid s < 8 \/ d_po s = 0) -> c_flush_pending s z = Some (s', z') ->
    exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.
Proof.
  intros W s z s' z' (_ & Hb & Hpo & _) Hz Hr H. exact (fbo_fpend_gen s z s' z' W Hb Hpo Hz Hr H).
Qed.

(** ** FLUSH_BLOCK_ONLY *)

(* the window bytes [block_start, strstart) are the bytes of H after the blocks: the symbols expand to them *)
Lemma fbo_data (H out : list Z) syms s w :
  kwin H s -> out = sublist 0 (Zlength H - (d_strstart s + d_lookahead s) + d_block_start s) H ->
  syms_rok w out syms ->
  F.syms_data out (map fsym syms) = sublist 0 (Zlength H - (d_strstart s + d_lookahead s) + d_strstart s) H ->
  blk_len syms = d_strstart s - d_block_start s -> 0 <= d_block_start s <= d_strstart s ->
  d_strstart s <= Zlength (mb_val (d_window s)) ->
  F.syms_data out (map fsym syms) =
    out ++ sublist (d_block_start s) (d_strstart s) (mb_val (d_window s)).
Proof.
  intros (Hwl & Hw) Hout Hrok Hsd Hbl Hbs Hwn.
  set (wl := d_strstart s + d_lookahead s) in *.
  destruct (Z_le_gt_dec (d_strstart s) wl) as [Le|Gt].
  - rewrite Hsd, Hout.
    rewrite <- (sublist_rejoin 0 (Zlength H - wl + d_block_start s) (Zlength H - wl + d_strstart s)) by lia.
    f_equal. apply VST.zlist.list_solver.Znth_eq_ext.
    + rewrite !Zlength_sublist by lia. lia.
    + intros i Hi. rewrite Zlength_sublist in Hi by lia.
      rewrite !Znth_sublist by lia. rewrite Hw by lia. f_equal. lia.
  - pose proof (fbo_syms_len w out syms Hrok) as [L1 L2].
    rewrite Hsd, fbo_Zlength_prefix in L1 by lia. rewrite Hout, fbo_Zlength_prefix in L1 by lia.
    assert (E : d_strstart s = d_block_start s) by lia.
    assert (Es : syms = []) by (destruct syms; [reflexivity|rewrite Zlength_cons in L2; pose proof (Zlength_nonneg syms); lia]).
    subst syms. rewrite E, sublist_nil. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma fbo_proof : writer_fspec -> flush_block_fspec -> fbo_fspec.
Proof.
  intros W FB s z s' z' syms last dict D BS p Hpre H off wmax Hkw Hbs Hexp Hrok Hsd Hp Hpm Hrun.
  destruct Hpre as (Hprm & Hws & Hlev & Htok & HsL & Hblk & Hbs0 & Hbs24 & Hwin & Hok & Hq & Hlast & Hz).
  pose proof (flush_pre_of s syms Hprm Htok HsL Hok Hq) as Hfp.
  unfold c_flush_block_only in Hrun.
  replace (in_long (d_strstart s - d_block_start s)) with true in Hrun
    by (symmetry; unfold in_long; apply andb_true_intro; split; apply Z.leb_le; lia).
  cbn [guard bind] in Hrun. rewrite u64_id in Hrun by lia.
  match type of Hrun with bind ?e _ = _ => remember e as eb eqn:Eeb end.
  destruct eb as [buf|]; [|discriminate]. cbn [bind] in Hrun.
  assert (Hbuf : forall b, buf = Some b ->
    Zlength b = d_strstart s - d_block_start s /\ d_strstart s - d_block_start s <= 65535 /\
    F.syms_data (F.expand dict BS) (map fsym syms) = F.expand dict BS ++ b).
  { intros b ->. destruct (Z.geb_spec (d_block_start s) 0) as [Bp|Bn]; [|discriminate].
    destruct (mb_read _ _ _) as [b0|] eqn:Er; cbn [bind] in Eeb; [|discriminate]. injection Eeb as <-.
    destruct (Hwin ltac:(lia)) as (W1 & W2 & W3).
    unfold mb_read in Er. destruct (_ && _); [|discriminate]. injection Er as <-.
    replace (d_block_start s + (d_strstart s - d_block_start s)) with (d_strstart s) by lia.
    split; [rewrite Zlength_sublist by lia; lia|]. split; [lia|].
    apply (fbo_data H (F.expand dict BS) syms s wmax); [exact Hkw|exact Hexp|exact Hrok|exact Hsd|exact Hblk|lia|lia]. }
  destruct (c_tr_flush_block (d_trm s) buf (d_strstart s - d_block_start s) last) as [[[t' m'] kind]|] eqn:Ef;
    [|discriminate].
  cbn [bind] in Hrun.
  destruct (FB (d_tr s) (d_pbm s) buf (d_strstart s - d_block_start s) last t' m' kind syms (F.expand dict BS)
              wmax p Hfp Hlast Hp Hpm Hrok Hbuf Ef) as (blk & Hbok & Hbd & Hbits' & Hlast' & Hob).
  set (s1 := set_d_block_start _ _) in Hrun.
  assert (Hpo0 : d_po s = 0) by apply Hq.
  assert (Hpo1 : d_po s1 = 0) by exact Hpo0.
  destruct (fbo_fpend_gen s1 z s' z' W Hbits' ltac:(lia) Hz (or_intror Hpo1) Hrun) as (x & Hzo & Hx).
  exists x, blk. split; [exact Hzo|]. split; [apply fbo_blocks_ok_app; [exact Hbs|exact Hbok]|].
  split; [rewrite fbo_expand_app, Hbd; exact Hsd|].
  rewrite Hx, (fbo_obits_pend s1 Hpo1). change (tr_out (d_tr s1)) with (tr_out t'). rewrite Hob.
  rewrite <- (fbo_obits_pend s Hpo0). unfold pend. destruct Hq as (Hq1 & _).
  rewrite Hq1, Hpo0, sublist_nil. reflexivity.
Qed.

(** The corrected fpend_fspec (one more hypothesis: bi_flush writes at the end of the pending bytes) and the
    part's target, fpend and fbo_fspec, under it. *)
Definition fpend_fspec_fixed : Prop :=
  forall s z s' z',
    outok s -> zout_ok z -> (d_bi_valid s < 8 \/ d_po s = 0) -> c_flush_pending s z = Some (s', z') ->
    exists x, zout_only z z' x /\ F.bytes_bits (x ++ pend s') ++ bibits s' = F.bytes_bits (pend s) ++ bibits s.

Theorem rtd_fbo_ok_fixed :
  Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> flush_block_fspec ->
  fpend_fspec_fixed /\ fbo_fspec.
Proof. intros _ W FB. split; [exact (fpend_fixed W)|exact (fbo_proof W FB)]. Qed.

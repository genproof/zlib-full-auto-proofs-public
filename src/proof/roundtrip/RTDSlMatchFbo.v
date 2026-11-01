(* RT-D part SLOW, part MATCH: FLUSH_BLOCK_ONLY(s, 0) of deflate_slow's main loop, functionally:
   from the run's facts before it (kdata3 without the trees part, the symbols covering [block_start, strstart),
   no pending byte) to the functional invariant FI after it (one more block, no symbols). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSlowKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* kcore3 without wtrees and kmatch3 (no pending byte): the symbols cover the window bytes below strstart *)
Definition kpre (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s) H /\
  khash s.

Lemma smf_fp_out s z s' z' :
  c_flush_pending s z = Some (s', z') -> 0 <= z_avail_out z ->
  exists y, z_out z' = z_out z ++ y /\ Zlength y <= z_avail_out z.
Proof.
  intros H Hz. unfold c_flush_pending, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  destruct (_ =? 0).
  - injection H as _ <-. exists []. rewrite app_nil_r, Zlength_nil. split; [reflexivity|lia].
  - destruct (mb_read _ _ _) as [b|]; [|discriminate].
    unfold out_put in H. destruct (Z.leb_spec (Zlength b) (z_avail_out z)) as [Hl|]; [|discriminate].
    injection H as _ <-. exists b. split; [reflexivity|exact Hl].
Qed.

Lemma smf_fbo_out s z last s' z' :
  c_flush_block_only s z last = Some (s', z') -> 0 <= z_avail_out z ->
  exists y, z_out z' = z_out z ++ y /\ Zlength y <= z_avail_out z.
Proof.
  intros H Hz. unfold c_flush_block_only, bind in H.
  destruct (guard (in_long (d_strstart s - d_block_start s))); [|discriminate].
  destruct (if d_block_start s >=? 0 then _ else _) as [buf|]; [|discriminate].
  destruct (c_tr_flush_block (d_trm s) buf _ last) as [[t k]|]; [|discriminate].
  exact (smf_fp_out _ _ _ _ H Hz).
Qed.

Lemma fbo_FI : fbo_spec -> fbo_fspec -> forall dict D BS p s0 z0 flush s z evs syms k x0 BS' s' z',
  FG dict D p s0 -> EI s0 z0 flush s z evs -> fbo_pre s z syms 0 -> d_match_available s = 0 ->
  zstep (d_wrap s0) z0 z k x0 ->
  kpre dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS ++ BS') syms s ->
  F.bytes_bits (x0 ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' false ->
  c_flush_block_only s z 0 = Some (s', z') ->
  FI dict D BS p s0 z0 s' z'.
Proof.
  intros Hfbo Hff dict D BS p s0 z0 flush s z evs syms k x0 BS' s' z' HG HE Hpre Hma Hst Hk Hbits Hc.
  destruct HG as (Hdict & HD & Hp0 & Hal).
  destruct HE as (Hc0 & Hfn & Hos & Hsp & Hapi & Hza & Had & _ & _ & _).
  pose proof Hc0 as (_ & Ho0 & _ & _ & Hz0 & _ & Ha0).
  assert (Hv0 : 0 <= d_bi_valid s0).
  { destruct Ho0 as (_ & (Hbv & _) & _). unfold d_bi_valid. lia. }
  assert (Hz0a : zall z0) by (apply zin_ok_zall; exact Hz0).
  pose proof Hk as (Rw & Rb & Re & Rs & Rd & Rh).
  destruct (fbo_bits_step s0 s z s' z' syms 0 dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0))
              BS BS' p x0 Hff Hpre Rw Rb Re Rs Rd Hp0 Hal Hv0 Hbits Hc)
    as (x & blk & Hzo & Hbok & Hexp & Hbits').
  pose proof Hpre as (Hprm & _ & Hlev & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hzok).
  destruct (Hfbo s z syms 0 Hpre) as (s2 & z2 & x2 & buf & Hc2 & _ & _ & _ & _ & _ & Hkp & Hbs'
    & Ht' & Hcfg & _).
  rewrite Hc in Hc2. injection Hc2 as <- <-.
  assert (E_wb : d_w_bits s' = d_w_bits s) by exact (f_equal d_w_bits Hkp).
  assert (E_ws : d_w_size s' = d_w_size s) by exact (f_equal d_w_size Hkp).
  assert (E_wm : d_w_mask s' = d_w_mask s) by exact (f_equal d_w_mask Hkp).
  assert (E_hs : d_hash_size s' = d_hash_size s) by exact (f_equal d_hash_size Hkp).
  assert (E_hm : d_hash_mask s' = d_hash_mask s) by exact (f_equal d_hash_mask Hkp).
  assert (E_hsh : d_hash_shift s' = d_hash_shift s) by exact (f_equal d_hash_shift Hkp).
  assert (E_win : d_window s' = d_window s) by exact (f_equal d_window Hkp).
  assert (E_prev : d_prev s' = d_prev s) by exact (f_equal d_prev Hkp).
  assert (E_head : d_head s' = d_head s) by exact (f_equal d_head Hkp).
  assert (E_la : d_lookahead s' = d_lookahead s) by exact (f_equal d_lookahead Hkp).
  assert (E_ss : d_strstart s' = d_strstart s) by exact (f_equal d_strstart Hkp).
  assert (E_ma : d_match_available s' = d_match_available s) by exact (f_equal d_match_available Hkp).
  assert (E_ih : d_ins_h s' = d_ins_h s) by exact (f_equal d_ins_h Hkp).
  assert (E_ins : d_insert s' = d_insert s) by exact (f_equal d_insert Hkp).
  assert (E_L : d_L s' = d_L s) by exact (f_equal (fun c => fst (fst (fst c))) Hcfg).
  assert (E_lev : d_level s' = d_level s) by exact (f_equal (fun c => snd (fst c)) Hcfg).
  assert (E_sg : d_strategy s' = d_strategy s) by exact (f_equal (fun c => snd c) Hcfg).
  assert (HL2 : 128 <= d_L s).
  { destruct Hprm as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _). rewrite P8.
    assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in H. lia. }
  assert (Hao : 0 <= z_avail_out z').
  { destruct Hzok as (Hzo1 & _).
    destruct (smf_fbo_out _ _ _ _ _ Hc Hzo1) as (y & Ey & Ly).
    destruct Hzo as (_ & _ & _ & _ & _ & _ & Z7 & Z8 & _).
    rewrite Z7 in Ey. apply app_inv_head in Ey. subst y. lia. }
  assert (Hst' : zstep (d_wrap s0) z0 z' (k + 0) (x0 ++ x)).
  { apply (zstep_trans _ z0 z z'); [exact (proj1 Hz0a)|exact Ha0|exact Hst|].
    apply zout_only_zstep; [exact Hza|exact Had|exact Hzo|exact Hao]. }
  rewrite Z.add_0_r in Hst'.
  exists k, (x0 ++ x), (BS' ++ [blk]), [].
  split; [exact Hst'|].
  split; [|exact Hbits'].
  rewrite app_assoc.
  assert (Hl0 : (d_level s' =? 0) = false) by (rewrite E_lev; apply Z.eqb_neq; lia).
  split.
  - unfold kdata3. cbv zeta. rewrite Hl0, E_ss, E_la, E_wb, Hbs', E_ma, Hma, Z.sub_0_r.
    split.
    { unfold kwin in *. rewrite E_ss, E_la, E_win. exact Rw. }
    split.
    { unfold kmatch3. rewrite E_ma, Hma. intros C. discriminate C. }
    split.
    { unfold wtrees. split; [exact Ht'|]. split; [rewrite Zlength_nil, E_L; lia|].
      split; [constructor|]. split; [intros; reflexivity|].
      intros _. rewrite Hbs', E_ss, E_ma, Hma. unfold blk_len. cbn. lia. }
    split; [exact Hbok|]. split; [exact Hexp|]. split; [exact I|]. exact Hexp.
  - unfold khash in *. destruct Rh as (Rh1 & Rh2).
    assert (Hl0' : (d_level s =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hl0 . rewrite Hl0' in Rh1.
    assert (Efn : fn_of s' = fn_of s) by (unfold fn_of; rewrite E_lev, E_sg; reflexivity).
    split.
    + unfold chain_hok, lim, h3, update_hash, MAX_DIST in *.
      rewrite E_hs, E_head, E_ss, E_la, E_ws, E_win, E_wm, E_prev, E_hsh, E_hm. exact Rh1.
    + rewrite Efn, E_la, E_ins, E_ss. intros Hf Hla. destruct (Rh2 Hf Hla) as (Hi & Hpr).
      split; [exact Hi|]. unfold primed, update_hash in *. rewrite E_ih, E_win, E_hsh, E_hm. exact Hpr.
Qed.

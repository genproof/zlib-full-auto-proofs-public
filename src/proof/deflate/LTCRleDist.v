(** * deflate_rle, part: the run branch (distance 1)
    Statement: LTCRleKit.v ([rdist_stmt]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma rd_u32_id x : 0 <= x < 4294967296 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma rd_lim_mono s s' : d_w_size s' = d_w_size s -> d_strstart s <= d_strstart s' -> lim s <= lim s'.
Proof.
  intros E H. unfold lim, MAX_DIST. rewrite E.
  destruct (Z.gtb_spec (d_strstart s) (d_w_size s - MIN_LOOKAHEAD));
  destruct (Z.gtb_spec (d_strstart s') (d_w_size s - MIN_LOOKAHEAD)); lia.
Qed.

Lemma rd_chain_mono s n n' l l' G : chain_with s n l G -> n <= n' -> l <= l' -> chain_with s n' l' G.
Proof.
  intros (A & B & C) Hn Hl. split; [intros v Hv; destruct (A v Hv); [left|right]; lia|].
  split; [exact B|]. intros q Hq Hq0 Hql. apply C; auto; lia.
Qed.

Lemma rd_chain_eq s s' n l G :
  d_head s' = d_head s -> d_prev s' = d_prev s -> d_hash_size s' = d_hash_size s -> d_w_mask s' = d_w_mask s ->
  chain_with s n l G -> chain_with s' n l G.
Proof. intros E1 E2 E3 E4. unfold chain_with. rewrite E1, E2, E3, E4. auto. Qed.

(** The fields the run branch changes outside the trees state blanked. *)
Definition rd_keep (x : dstate) : dstate :=
  set_d_lookahead (set_d_match_start (hc_keep (set_d_strstart (set_d_match_length x 0) 0)) 0) 0.

Lemma rd_sym_ok s s' x :
  d_w_size s' = d_w_size s -> d_level s' = d_level s -> d_strategy s' = d_strategy s ->
  sym_ok s x -> sym_ok s' x.
Proof. unfold sym_ok, MAX_DIST. intros E1 E2 E3. rewrite E1, E2, E3. auto. Qed.

Ltac rd_fld Hk f E := assert (E := f_equal f Hk); unfold rd_keep, hc_keep in E; autorewrite with fproj in E.

(** The state after the run branch: RTS and fr. *)
Lemma rd_core s s3 syms t' m' ml :
  W s -> outok s -> quiet s -> fn_of s = 4 -> wtrees s syms ->
  tree_ok t' m' (syms ++ [(1, ml - 3)]) -> tally_frame (d_tr s) (d_pbm s) t' m' ->
  rd_keep s3 = rd_keep (set_d_pbm (set_d_tr s t') m') -> wstruct s3 ->
  d_head s3 = d_head s -> d_prev s3 = d_prev s ->
  d_strstart s3 = d_strstart s + ml -> d_lookahead s3 = d_lookahead s - ml -> d_match_length s3 = 0 ->
  3 <= ml <= d_lookahead s -> ml <= MAX_MATCH -> d_strstart s + ml < d_window_size s ->
  RTS s3 (syms ++ [(1, ml - 3)]) (3 * Zlength syms + 3 =? tr_sym_end (d_tr s)) /\ fr s s3 /\
  d_lookahead s3 < d_lookahead s.
Proof.
  intros HW Ho Hq Hfn Hwt Htr Hfr Hk Hws3 Ehead Eprev Hss3 Hla3 Hml3 Hml Hml' Hwin3.
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & _).
  assert (Hlev := fn_of_rle s Hp Hfn).
  assert (Ha := wmatch_avail0 s Hm Hfn).
  destruct Hfr as (Hcfg & Hmat & Hpnd & Hbb & Hbv & Hbu & Hgrow).
  unfold tr_cfg in Hcfg. injection Hcfg as Ec1 Ec2 Ec3 Ec4.
  rd_fld Hk d_tr Etr. rd_fld Hk d_pbm Epbm. rd_fld Hk d_status Estatus. rd_fld Hk d_po Epo.
  rd_fld Hk d_wrap Ewrap. rd_fld Hk d_gzhead Egzh. rd_fld Hk d_gzindex Egzi. rd_fld Hk d_method Emeth.
  rd_fld Hk d_last_flush Elf. rd_fld Hk d_w_size Ewsize. rd_fld Hk d_w_bits Ewbits. rd_fld Hk d_w_mask Ewmask.
  rd_fld Hk d_window Ewin. rd_fld Hk d_window_size Ewsz. rd_fld Hk d_hash_size Ehsize.
  rd_fld Hk d_hash_bits Ehbits. rd_fld Hk d_hash_mask Ehmask. rd_fld Hk d_hash_shift Ehshift.
  rd_fld Hk d_block_start Ebs. rd_fld Hk d_match_available Ema. rd_fld Hk d_prev_length Eplen.
  rd_fld Hk d_insert Eins. rd_fld Hk d_high_water Ehw. rd_fld Hk d_pending_buf_size Epbs.
  assert (Elev : d_level s3 = d_level s) by (unfold d_level; rewrite Etr; exact Ec3).
  assert (Estr : d_strategy s3 = d_strategy s) by (unfold d_strategy; rewrite Etr; exact Ec4).
  assert (EL : d_L s3 = d_L s) by (unfold d_L; rewrite Etr; exact Ec1).
  assert (Efn : fn_of s3 = 4) by (unfold fn_of; rewrite Elev, Estr; exact Hfn).
  assert (Epend : d_pending s3 = d_pending s) by (unfold d_pending; rewrite Etr; exact Hpnd).
  assert (Ebiv : d_bi_valid s3 = d_bi_valid s) by (unfold d_bi_valid; rewrite Etr; exact Hbv).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  assert (Hw9 : 512 <= d_w_size s).
  { rewrite Hwsz. change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia. }
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (Hb' : blk_len syms = d_strstart s - d_block_start s) by (rewrite Hb by lia; lia).
  assert (Htr' := Htr). destruct Htr' as (T1 & T2 & T3 & T4 & _).
  set (syms' := syms ++ [(1, ml - 3)]) in *.
  assert (Hlen' : Zlength syms' = Zlength syms + 1) by (unfold syms'; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hbl' : blk_len syms' = d_strstart s - d_block_start s + ml).
  { unfold syms'. rewrite blk_len_app, Hb'. unfold sym_len. cbn [fst snd]. cbn. lia. }
  assert (Hbb' := blk_len_bound syms' T4).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (HRTS0 : RTS0 s3 syms').
  { unfold RTS0. split.
    { unfold prm. rewrite Ewbits, Ewsize, Ewmask, Ehbits, Ehsize, Ehmask, Ehshift, EL, Epbs, Elev, Estr, Emeth.
      rewrite Etr, Epbm, T1, T2, Ec2, Ec1. fold (d_L s).
      exact (conj Hwb (conj Hwsz (conj Hwm (conj Hhb (conj Hhs (conj Hhm (conj Hhsh (conj HL (conj Hpbs
        (conj eq_refl (conj eq_refl (conj Hse (conj Hlv (conj Hstrat Hmeth)))))))))))))). }
    split; [exact Hws3|].
    split.
    { unfold wpos. unfold MAX_DIST in *. rewrite Hla3, Hss3, Ewsz, Ebs, Eins, Ehw, Ewsize. lia. }
    split.
    { unfold wwin. rewrite Ewin, Hla3, Hss3, Ehw. intros i Hi. apply Hwin. lia. }
    split.
    { unfold whash. rewrite Elev. destruct (Z.eqb_spec (d_level s) 0); [lia|].
      unfold whash in Hh. destruct (Z.eqb_spec (d_level s) 0); [lia|]. destruct Hh as [Hm0 [G HG]].
      split; [unfold d_matches in *; rewrite Etr, Hmat; exact Hm0|].
      exists G. apply (rd_chain_eq s); try assumption.
      eapply rd_chain_mono; [exact HG|lia|]. apply rd_lim_mono; [exact Ewsize|lia]. }
    split.
    { unfold wmatch. rewrite Hml3, Eplen, Ema, Ha. destruct Hm as (_ & Hm2 & _ & Hm4 & _).
      split; [unfold MAX_MATCH; lia|]. split; [exact Hm2|]. split; [left; reflexivity|].
      split; [intros _; unfold MIN_MATCH in *; split; [lia|exact (proj2 (Hm4 Ha))]|]. intros; lia. }
    split; [rewrite Etr, Epbm; exact Htr|].
    split; [rewrite EL; lia|].
    split.
    { unfold syms'. apply Forall_app. split.
      - eapply Forall_impl; [|exact Hf]. intros x. apply rd_sym_ok; assumption.
      - constructor; [|constructor]. unfold sym_ok. cbn [fst snd]. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
        rewrite Ewsize, Elev.
        split; [exact (T4 (1, ml - 3) ltac:(unfold syms'; apply in_or_app; right; left; reflexivity))|].
        split; [intros _; lia|]. intros; unfold TOO_FAR; lia. }
    split; [rewrite Hss3, Ebs; lia|].
    split.
    { apply (outok_grow s s3 Ho); [rewrite Etr, Epbm; exact Hgrow|exact Epo|exact Epend|exact Epbs|].
      destruct Ho as (_ & Hbo & _). unfold bits_ok in *. rewrite Etr, Hbv, Hbb, Hpnd. exact Hbo. }
    split.
    { unfold quiet in *. rewrite Epend, Epo, Ebiv. exact Hq. }
    split; [exact Efn|].
    rewrite Hss3, Ewsz. exact Hwin3. }
  split; [split; [exact HRTS0|]|].
  { rewrite Hse, EL, Hlen'. destruct (Z.eqb_spec (3 * Zlength syms + 3) (3 * (d_L s - 1)));
    destruct (Z.eqb_spec (Zlength syms + 1) (d_L s - 1)); lia. }
  split; [|lia].
  unfold fr. split.
  { unfold same_prm. rewrite Ewbits, Ewsize, Ehbits, EL, Epbs, Elev, Estr. repeat split; reflexivity. }
  split.
  { unfold api_eq. rewrite Estatus, Ewrap, Egzh, Egzi, Elf, Emeth. repeat split; reflexivity. }
  split.
  { unfold ub. rewrite Hss3, Hla3, Ebs. lia. }
  intros tout. unfold Gb. rewrite Epend, Ebiv. reflexivity.
Qed.

Theorem rdist_ok : tally_spec2 -> rdist_stmt.
Proof.
  intros [_ Htd] s ml HW Ho Hq Hfn Hrd Hml Hmla Hss1.
  assert (HW0 := HW).
  destruct HW as (Hp & Hws & Hpos & Hwin & Hh & Hm & _ & syms & Hwt).
  assert (Hwt0 := Hwt).
  assert (Hp0 := Hp).
  destruct Hp as (Hwb & Hwsz & Hwm & Hhb & Hhs & Hhm & Hhsh & HL & Hpbs & Hob & Hpbm & Hse & Hlv & Hstrat & Hmeth).
  destruct Hpos as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  destruct Hwt as (Ht1 & HL2 & Hf & _ & Hb).
  assert (HL15 : d_L s <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hw15 : d_w_size s <= 32768).
  { rewrite Hwsz. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hws0 := Hws). destruct Hws as (Hwl & Hwok & Hwss & Hpl & Hhl).
  assert (Hlen : 0 <= ml - 3 <= 255) by (unfold MAX_MATCH, MIN_MATCH in *; lia).
  destruct (Htd (d_tr s) (d_pbm s) syms 1 (ml - 3) Ht1 HL2 HL15 ltac:(lia) Hlen) as (t' & m' & Etl & Ht' & Hfr).
  assert (Hwin3 : d_strstart s + ml < d_window_size s).
  { unfold rready in Hrd. unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *. destruct Hrd as [R|R]; lia. }
  unfold rdist, c_dtally_dist, d_trm. autorewrite with fproj.
  rewrite (rd_u32_id (ml - MIN_MATCH)) by (unfold MIN_MATCH, MAX_MATCH in *; lia).
  change MIN_MATCH with 3. rewrite Etl.
  cbn [bind]. unfold set_d_trm. cbn [fst snd]. autorewrite with fproj.
  rewrite (rd_u32_id (d_lookahead s - ml)) by lia.
  rewrite (rd_u32_id (d_strstart s + ml)) by lia.
  eexists _, _, _. split; [reflexivity|].
  unfold MIN_MATCH in Hml.
  apply (rd_core s _ syms t' m' ml HW0 Ho Hq Hfn Hwt0 Ht' Hfr).
  all: try (autorewrite with fproj; reflexivity).
  all: try (unfold wstruct; autorewrite with fproj; exact Hws0).
  all: try (unfold MAX_MATCH in *; lia).
Qed.

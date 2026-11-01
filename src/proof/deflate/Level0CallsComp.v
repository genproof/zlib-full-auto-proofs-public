(** * Level 0 over several deflate() calls: the compression stage of deflate() and the bytes written

    [l0_ready s]: the state between two calls of the harnesses' loop once the header is written (status BUSY,
    nothing pending, nothing left in the window).  From it, deflate()'s compression stage
    - with Z_NO_FLUSH and [k] whole blocks offered returns Z_OK at once ([l0c_comp_nf]), the state ready again;
    - with Z_FINISH writes the stored blocks of the rest and goes on to the trailer ([l0c_comp_fin]).
    The bytes written (stored blocks of bytes) are bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsStored.
Require Export Zlib.proof.deflate.Level0CallsHead.
Require Import Zlib.proof.deflate.LTCStored2.
Require Import Zlib.proof.deflate.LTCStoredLoopLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The stored blocks are bytes *)

Lemma bytes_stored_block last d : 0 <= last < 256 -> Zlength d <= 65535 -> bytes d -> bytes (stored_block last d).
Proof.
  intros Hl Hd Hb. pose proof (Zlength_nonneg d). unfold stored_block, bytes. apply Forall_app. split; [|exact Hb].
  repeat (apply Forall_cons;
          [first [lia | apply Z.mod_pos_bound; lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]|]).
  apply Forall_nil.
Qed.

Lemma bytes_nblocks a i d : 0 <= a -> a + 65535 * Z.of_nat i <= Zlength d -> bytes d -> bytes (nblocks a i d).
Proof.
  induction i as [|i IH]; intros H0 H Hb; [apply Forall_nil|].
  rewrite Nat2Z.inj_succ in H.
  rewrite nblocks_S. unfold bytes. apply Forall_app. split; [apply IH; auto; lia|].
  apply bytes_stored_block; [lia| |apply bytes_sublist; auto].
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma bytes_stored_blocks d : bytes d -> bytes (stored_blocks d).
Proof.
  remember (Z.to_nat (Zlength d / 65535)) as k eqn:Ek.
  revert d Ek. induction k as [|k IH]; intros d Ek Hb.
  - rewrite stored_blocks_eq. unfold MAX_STORED_LEN.
    destruct (Z.leb_spec (Zlength d) 65535) as [H|H].
    + apply bytes_stored_block; auto; lia.
    + exfalso. assert (1 <= Zlength d / 65535) by (apply Z.div_le_lower_bound; lia). lia.
  - rewrite stored_blocks_eq. unfold MAX_STORED_LEN.
    destruct (Z.leb_spec (Zlength d) 65535) as [H|H].
    + apply bytes_stored_block; auto; lia.
    + unfold bytes. apply Forall_app. split.
      * apply bytes_stored_block; [lia| |apply bytes_sublist; auto]. rewrite Zlength_sublist by lia. lia.
      * apply IH; [|apply bytes_sublist; auto].
        rewrite Zlength_sublist by lia.
        replace (Zlength d - 65535) with ((Zlength d) + (-1) * 65535) by lia.
        rewrite Z.div_add by lia. lia.
Qed.

(** ** The ready state *)

Definition l0_ready (s : dstate) : Prop :=
  W s /\ outok s /\ d_pending s = 0 /\ d_po s = 0 /\ d_bi_valid s = 0 /\ d_level s = 0 /\
  d_strstart s = d_block_start s /\ d_status s = BUSY_STATE.

Lemma cp_api s s' : cp s' = cp s -> d_status s' = d_status s /\ d_wrap s' = d_wrap s /\ d_gzhead s' = d_gzhead s.
Proof. unfold cp. intros H. injection H. intros. repeat split; congruence. Qed.

Lemma l0c_comp_nf s z k :
  l0_ready s -> zall_w z -> adler_ok (d_wrap s) (z_adler z) ->
  z_avail_in z = 65535 * Z.of_nat k -> (1 <= k)%nat -> 65540 * Z.of_nat k + 5 <= z_avail_out z <= 4294967295 ->
  exists s' z',
    c_deflate_compress s z Z_NO_FLUSH = Some (s', z', Some Z_OK) /\
    zstep (d_wrap s) z z' (65535 * Z.of_nat k) (nblocks (z_next_in z) k (z_in z)) /\
    l0_ready s' /\ cp s' = cp s.
Proof.
  intros (HW & Ho & Hp & Hpo & Hbv & Hlv & Hss & Hst) Hz Ha Hai Hk Hao.
  destruct (l0c_stored_nf s z k HW Ho Hp Hpo Hbv Hlv Hss Hz Ha Hai Hk Hao)
    as (s' & z' & E & Hstp & HW' & Ho' & Hp' & Hpo' & Hbv' & Hss' & Ecp).
  pose proof Hz as [(_ & Hn0 & _ & Hn1 & _) _].
  unfold c_deflate_compress.
  replace (negb (z_avail_in z =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
  cbn [orb]. unfold c_compress_func. rewrite Hlv. cbn [Z.eqb]. rewrite E. cbn [bind].
  pose proof Hstp as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
  rewrite Zlength_nblocks in C9 by lia.
  replace (z_avail_out z' =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  exists s', z'. split; [reflexivity|]. split; [exact Hstp|].
  destruct (cp_fields _ _ Ecp) as (_ & _ & Elv & _). destruct (cp_api _ _ Ecp) as (Est & _).
  split; [|exact Ecp].
  refine (conj HW' (conj Ho' (conj Hp' (conj Hpo' (conj Hbv' (conj _ (conj Hss' _))))))); congruence.
Qed.

Lemma l0c_comp_fin s z :
  l0_ready s -> zall_w z -> adler_ok (d_wrap s) (z_adler z) ->
  5 * l0_blocks (z_avail_in z) + z_avail_in z <= z_avail_out z <= 4294967295 ->
  exists s' z',
    c_deflate_compress s z Z_FINISH = Some (s', z', None) /\
    zstep (d_wrap s) z z' (z_avail_in z)
      (stored_blocks (sublist (z_next_in z) (z_next_in z + z_avail_in z) (z_in z))) /\
    outok s' /\ d_pending s' = 0 /\ d_po s' = 0 /\ d_bi_valid s' = 0 /\ d_wrap s' = d_wrap s /\
    8 <= Zlength (o_buf (tr_out (d_tr s'))) /\
    d_status s' = FINISH_STATE /\ d_gzhead s' = d_gzhead s /\
    d_pending_buf_size s' = Zlength (o_buf (tr_out (d_tr s'))) /\ d_pending_buf_size s' <= 131072 /\
    d_lookahead s' = 0.
Proof.
  intros (HW & Ho & Hp & Hpo & Hbv & Hlv & Hss & Hst) Hz Ha Hao.
  destruct (l0c_stored_fin s z HW Ho Hp Hpo Hbv Hlv Hss Hz Ha Hao)
    as (s' & z' & E & Hstp & Ho' & Hp' & Hpo' & Hbv' & Ecp & Hlen & Hla').
  unfold c_deflate_compress. rewrite Hst.
  replace (andb (negb (Z_FINISH =? Z_NO_FLUSH)) (negb (BUSY_STATE =? FINISH_STATE))) with true
    by reflexivity.
  rewrite Bool.orb_true_r. cbv beta iota.
  unfold c_compress_func. rewrite Hlv. cbn [Z.eqb]. rewrite E. cbn [bind].
  exists (set_d_status s' FINISH_STATE), z'. split; [reflexivity|]. split; [exact Hstp|].
  destruct (cp_api _ _ Ecp) as (_ & Ew & Eg).
  destruct (cp_fields _ _ Ecp) as (_ & _ & _ & Epbs' & _).
  pose proof HW as (Hprm & _). destruct (prm_pbsize s Hprm) as [Epb Hpb].
  pose proof Hprm as (_ & _ & _ & Hhb & _ & _ & _ & HL & Hps & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1)) by (apply Z.pow_le_mono_r; lia).
  split; [exact Ho'|]. split; [exact Hp'|]. split; [exact Hpo'|]. split; [exact Hbv'|].
  split; [exact Ew|].
  split; [change (8 <= Zlength (o_buf (tr_out (d_tr s')))); lia|].
  split; [reflexivity|]. split; [exact Eg|].
  change (d_pending_buf_size s' = Zlength (o_buf (tr_out (d_tr s'))) /\ d_pending_buf_size s' <= 131072 /\
          d_lookahead s' = 0).
  split; [lia|]. split; [lia|exact Hla'].
Qed.

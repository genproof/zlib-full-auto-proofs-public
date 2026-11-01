(** * At every return of deflate_stored, ub <= 65535 ([LTWClipKit.stored_ub_spec]), for any input and output
    space: the first-phase loop only moves block_start forward ([dsloop_clip_stmt]); the window update either
    keeps ub or sets block_start = strstart; Z_FINISH's finish_done keeps the ub of the loop, block_done has
    ub = 0; otherwise the window refill fills at most up to window_size <= 65536 and the second-phase block
    ([blk2_ub_stmt]) leaves at most 65535 bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWClipKit.
Require Import Zlib.proof.wide.deflate.LTCStored2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem stored_ub_assembly : dsloop_clip_stmt -> dswin_stmt_w -> fill2_stmt_w -> blk2_ub_stmt -> stored_ub_spec.
Proof.
  intros HL HWn HF HB s z flush s' z' bs Hpre Hfn Hub0 E.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hz & Hwr & Ha).
  assert (H0 : d_level s = 0) by (apply level0_of; [destruct HW as (Hp & _); exact Hp|exact Hfn]).
  pose proof (zin_ok_zall_w z Hz) as Hza.
  assert (Hao : z_avail_out z <= 4294967295) by (destruct Hz as (_ & _ & _ & _ & A & _); lia).
  destruct (HL s z flush HW Ho Hq H0 Hza Ha Hfl Hao)
    as (s1 & z1 & last & k & x & Eloop & K1 & B1 & O1 & Q1 & G1 & Z1 & X1 & Zo1 & A1 & L1 & _ & _).
  rewrite c_deflate_stored_eq in E. cbv zeta in E. rewrite Eloop in E. cbn [bind] in E.
  (* the state after the first phase: block_start only moved forward *)
  pose proof (ob_keep_eq s s1 K1) as E1.
  assert (HW1 : W s1).
  { rewrite E1. destruct G1 as (G1a & G1b & _). apply W_ob; auto. }
  destruct (cp_fields s s1 (cp_ob_eq s s1 K1)) as (SP1 & AP1 & Lv1 & Pb1 & Ws1 & DL1 & St1).
  assert (Ss1 : d_strstart s1 = d_strstart s) by (rewrite E1; reflexivity).
  destruct (W_level0 s1 HW1 ltac:(congruence)) as (La1 & Bs1 & Sy1).
  destruct (W_level0 s HW H0) as (La0 & Bs0 & Sy0).
  assert (U1 : ub s1 <= ub s) by (unfold ub; lia).
  pose proof (zall_zstep_w _ _ _ _ _ Hza Z1 Zo1) as Hza1.
  pose proof (adler_ok_zstep_w _ _ _ _ _ Hza Ha Z1) as Ha1.
  pose proof Z1 as Z1'. destruct Z1' as (Zi1 & Zk1 & Zn1 & Za1 & _).
  assert (Hk : u32 (z_avail_in z - z_avail_in z1) = k).
  { rewrite Za1. replace (z_avail_in z - (z_avail_in z - k)) with k by lia. unfold u32. apply Z.mod_small.
    destruct Hz as (_ & _ & Hai & _). lia. }
  rewrite Hk in E.
  (* the window update keeps ub *)
  pose proof Hza1 as Hza1c. destruct Hza1c as [(Hb1 & Hn1 & Hai1 & Hl1 & _) _].
  destruct (HWn s1 z1 k HW1 ltac:(congruence) Hb1 ltac:(destruct Hza as [(_ & Hn & _) _]; lia) ltac:(lia)
              ltac:(destruct Hz as (_ & _ & Hai & _); lia) ltac:(intros Hk0; rewrite Ss1; auto))
    as (s2 & E2 & HW2 & WK2 & U2).
  rewrite E2 in E. cbn [bind] in E.
  set (s3 := upd_high_water s2) in E.
  pose proof (W_hw s2 HW2) as HW3. fold s3 in HW3.
  assert (CP3 : cp s3 = cp s).
  { unfold s3. rewrite cp_uhw, (cp_win_eq _ _ WK2). apply cp_ob_eq; auto. }
  assert (OP3 : op s3 = op s1). { unfold s3. rewrite op_uhw. apply op_win_eq; auto. }
  destruct (cp_fields s s3 CP3) as (SP3 & AP3 & Lv3 & Pb3 & Ws3 & DL3 & St3).
  destruct (op_fields s1 s3 OP3 ltac:(congruence)) as (Ok3 & Qk3 & Gb3 & Bv3 & Sh3 & Pd3).
  assert (U3 : ub s3 = ub s1) by (unfold s3; rewrite ub_uhw; auto).
  destruct (W_level0 s3 HW3 ltac:(congruence)) as (La3 & Bs3 & Sy3).
  destruct (negb (last =? 0)) eqn:EL.
  { (* finish_done *)
    injection E as <- <- <-. destruct (bu_fields s3) as (_ & _ & _ & _ & Ubb & _). lia. }
  destruct (negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z1 =? 0) &&
            (d_strstart s3 =? d_block_start s3)) eqn:EB.
  { (* block_done *)
    injection E as <- <- <-. rewrite !andb_true_iff, Z.eqb_eq in EB. destruct EB as (_ & Sb3).
    unfold ub. lia. }
  (* the second phase: the refill, then the block *)
  assert (Wr3 : d_wrap s3 = d_wrap s) by (destruct AP3 as (_ & Wr & _); exact Wr).
  destruct (HF s3 z1 HW3 ltac:(congruence) Hza1 ltac:(rewrite Wr3; exact Ha1))
    as (s4 & z4 & k4 & EF & HW4 & WK4 & Z4 & U4).
  rewrite EF in E.
  assert (CP4 : cp s4 = cp s) by (rewrite (cp_win_eq _ _ WK4); exact CP3).
  assert (OP4 : op s4 = op s1) by (rewrite (op_win_eq _ _ WK4); exact OP3).
  destruct (cp_fields s s4 CP4) as (SP4 & AP4 & Lv4 & Pb4 & Ws4 & DL4 & St4).
  destruct (op_fields s1 s4 OP4 ltac:(congruence)) as (Ok4 & Qk4 & Gb4 & Bv4 & Sh4 & Pd4).
  destruct (W_level0 s4 HW4 ltac:(congruence)) as (La4 & Bs4 & Sy4).
  pose proof HW4 as (_ & (_ & _ & Hws4 & _) & (P1 & P2 & P3 & P4 & P5 & _) & _).
  destruct HW as (Hp & _). destruct Hp as (Hwb & Hws & _ & Hhb & _ & _ & _ & HLs & Hps & _).
  assert (2 ^ 7 <= 2 ^ (d_hash_bits s - 1) <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  assert (2 ^ 9 <= 2 ^ d_w_bits s <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  pose proof (Ok4 O1) as (_ & (Bva & _) & _).
  destruct (Qk4 Q1) as (_ & _ & Bvb).
  destruct (HB _ s4 z4 flush _ _ E ltac:(unfold d_bi_valid in *; lia) ltac:(rewrite Pb4; lia) ltac:(lia))
    as (s5 & z5 & last2 & EK & Ss5 & La5 & Ub5).
  destruct (last2 =? 0); injection EK as <- <- <-.
  - unfold ub. lia.
  - destruct (bu_fields s5) as (_ & _ & _ & _ & Ubb & _). rewrite Ubb. unfold ub. lia.
Qed.

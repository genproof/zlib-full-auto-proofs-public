(* RT-I: copy of rfc1951/DecDecMatch.v over the generalized definitions RTIGDefs.v. *)
(* Part of DecDec.group_dec: the pass from MATCH.  Statements: DecDecDefs.v; helpers: DecDecKd.v; template:
   DecDecLit.v (pass_lit). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDecDecKd.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dm_lz_copy_add (a b: nat) dist out :
  lz_copy (a + b) dist out = lz_copy b dist (lz_copy a dist out).
Proof.
  revert out. induction a as [|a IH]; intros out; [reflexivity|].
  cbn [Nat.add lz_copy]. apply IH.
Qed.

Lemma dm_Zlength_lz_copy (n: nat) dist out : Zlength (lz_copy n dist out) = Zlength out + Z.of_nat n.
Proof.
  revert out. induction n as [|n IH]; intros out; cbn [lz_copy]; [lia|].
  rewrite IH, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma dm_lz_split (len l c: Z) dist out : 0 <= c -> c <= l -> l <= len ->
  lz_copy (Z.to_nat c) dist (lz_copy (Z.to_nat (len - l)) dist out) = lz_copy (Z.to_nat (len - (l - c))) dist out.
Proof.
  intros. rewrite <- dm_lz_copy_add. f_equal. lia.
Qed.

Lemma pass_match : lay_stmt -> copy_stmt -> pass_ok MATCH c_MATCH.
Proof.
  intros LAY CPY G pos inp ob flush m Ctx K D Hl Hmd.
  pose proof Ctx as (Gok & _).
  pose proof (kd_at _ _ _ _ _ K) as At.
  destruct (at_mode_match_e _ _ _ _ _ _ At Hmd)
    as (Hh & k & j & ll & dl & syms & p0 & len & dist & IH & Hj & Hs & Hoff & Hlen & Ho & Hq & Hb).
  destruct (LAY G (m_s m) k j ll dl syms p0 Gok IH) as (_ & _ & _ & _ & _ & _ & L1 & _).
  destruct (L1 Hj) as (SO & _ & _ & Oj & IH1). clear L1. rewrite Hs in SO, Oj, IH1.
  destruct SO as (Sl & Sd1 & Sd2 & _).
  destruct (LAY G (m_s m) k (j + 1) ll dl syms _ Gok IH1) as (_ & _ & _ & _ & _ & (rest & Fr) & _).
  cbn [sym_data] in Oj.
  assert (Hmd' : md_dec (m_mode m)) by (unfold md_dec; tauto).
  pose proof (dm_Zlength_lz_copy (Z.to_nat (len - i_length (m_s m))) dist (outj G k syms j)) as Lo.
  unfold c_MATCH at 1. destruct (m_left m =? 0) eqn:EL.
  - cbn [dstep_post]. split; [|split].
    + apply kd_tr with m; auto; try reflexivity.
      * apply same_fix_refl.
      * right; exact Hmd'.
    + exists []. rewrite app_nil_r. reflexivity.
    + intros _. right; right; left. cbn [set_leave m_ow m_left set_m_leave]. unfold m_left in EL.
      split; [apply Z.eqb_eq; exact EL|].
      rewrite Ho, Fr, Oj, Zlength_app, Lo, dm_Zlength_lz_copy.
      pose proof (Zlength_nonneg rest). lia.
  - apply Z.eqb_neq in EL.
    assert (Hw : win_ok G (m_s m) ob).
    { apply (kd_win _ _ _ _ _ K). rewrite Hmd. unfold MATCH, CHECK. lia. }
    pose proof (kd_glob _ _ _ _ _ K) as (_ & _ & Gwb & _).
    assert (Hwb : dc_wb G <= i_wbits (m_s m)).
    { apply Gwb. unfold m_mode in Hmd. rewrite Hmd. unfold MATCH, HEAD. lia. }
    assert (Hwb0 : 0 <= dc_wb G).
    { destruct (Z_lt_le_dec (dc_wb G) 0) as [N|N]; [|exact N].
      rewrite (Z.pow_neg_r 2 _ N) in Sd2. lia. }
    assert (Hd2 : dist <= 2 ^ i_wbits (m_s m)).
    { eapply Z.le_trans; [exact Sd2|]. apply Z.pow_le_mono_r; lia. }
    assert (Hout : m_out m = m_aout m).
    { pose proof (kd_out _ _ _ _ _ K) as O.
      assert (AC : after_check G (m_mode m) = false).
      { unfold after_check. rewrite Hmd. unfold MATCH, LENGTH, DONE. cbn. apply andb_false_r. }
      rewrite AC in O. exact O. }
    destruct D as (_ & _ & _ & Da & Dw).
    assert (Hd1 : 1 <= dist <= Zlength (ob ++ m_ow m)).
    { rewrite Ho, Lo. pose proof (Zlength_nonneg (outj G k syms j)). lia. }
    destruct (CPY G m ob dist Hw ltac:(lia) Dw Hout Da ltac:(unfold m_left in *; lia) Hoff Hd1 Hd2 ltac:(lia))
      as (c & ow' & Hc & Hcp & (d & Hd) & Hm).
    unfold c_MATCH in Hm. rewrite (proj2 (Z.eqb_neq _ _) EL) in Hm. rewrite Hm. clear Hm.
    assert (Hob : ob ++ ow' = lz_copy (Z.to_nat (len - (i_length (m_s m) - c))) dist (outj G k syms j)).
    { rewrite Hcp, Ho. apply dm_lz_split; lia. }
    destruct (i_length (m_s m) - c =? 0) eqn:E0.
    + apply Z.eqb_eq in E0.
      cbn [dstep_post]. split; [|split].
      * apply kd_tr with m; auto; try reflexivity.
        -- unfold set_mode, upd_s. sf_auto.
        -- right. cbn. unfold md_dec; tauto.
        -- apply at_mode_len_i.
           ++ exact Hh.
           ++ right; reflexivity.
           ++ exists k, (j + 1), ll, dl, syms, (p0 + Zlength (send_one ll dl (Ref len dist))).
              split; [|split; [|split]].
              ** apply in_huff_tr with (m_s m); [unfold set_mode, upd_s; sf_auto|exact IH1].
              ** cbn [m_ow set_mode upd_s set_m_s set_m_ow]. rewrite Hob, Oj, E0. f_equal. lia.
              ** cbn [m_nx m_bits set_mode upd_s set_m_s set_m_ow]. rewrite Hq. reflexivity.
              ** left. exact Hb.
      * exists d. exact Hd.
      * intros E. exfalso. cbn [set_mode upd_s m_leave set_m_s set_m_ow] in E. lia.
    + apply Z.eqb_neq in E0.
      cbn [dstep_post]. split; [|split].
      * apply kd_tr with m; auto; try reflexivity.
        -- unfold upd_s. sf_auto.
        -- right. cbn. unfold m_mode in Hmd. rewrite Hmd. unfold md_dec; tauto.
        -- apply at_mode_match_i.
           ++ exact Hh.
           ++ cbn. exact Hmd.
           ++ exists k, j, ll, dl, syms, p0, len, dist.
              split; [exact (in_huff_tr _ _ _ _ _ _ _ _ _ ltac:(unfold upd_s; sf_auto) IH)|].
              unfold upd_s. cbn [m_ow m_s set_m_s set_m_ow i_offset i_length set_i_length m_nx m_bits].
              split; [exact Hj|]. split; [exact Hs|].
              split; [exact Hoff|]. split; [lia|]. split; [exact Hob|]. split; [exact Hq|exact Hb].
      * exists d. exact Hd.
      * intros E. exfalso. cbn [upd_s m_leave set_m_s set_m_ow] in E. lia.
Qed.

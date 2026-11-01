(* RT-D part STORED LOOP: helpers on the pieces of ds_body (contents of the writes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredLoopBits.
Require Export Zlib.proof.roundtrip.RTDLTCStoredLoopLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma app_inv_len {A} (l1 l2 l3 l4 : list A) :
  Zlength l2 = Zlength l4 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3.
Proof.
  intros HL. rewrite !Zlength_correct in HL. revert l3. induction l1 as [|a r IH]; intros l3 E.
  - destruct l3 as [|b r3]; [reflexivity|].
    exfalso. apply (f_equal (@length A)) in E. rewrite ?app_length in E. cbn [app length] in E. rewrite ?app_length in E. lia.
  - destruct l3 as [|b r3].
    + exfalso. apply (f_equal (@length A)) in E. rewrite ?app_length in E. cbn [app length] in E. rewrite ?app_length in E. lia.
    + cbn [app] in E. inversion E; subst. f_equal. apply IH. assumption.
Qed.

(** [c_pb_wr] stores the byte and keeps the rest of the output state. *)
Lemma pb_wr_eq s i v s' :
  c_pb_wr s i v = Some s' ->
  o_buf (tr_out (d_tr s')) = upd_Znth i (o_buf (tr_out (d_tr s))) v /\
  d_pending s' = d_pending s /\ o_bi_buf (tr_out (d_tr s')) = o_bi_buf (tr_out (d_tr s)) /\
  d_bi_valid s' = d_bi_valid s /\ d_po s' = d_po s.
Proof.
  unfold c_pb_wr, mb_wr, d_pb. cbn [mb_val mb_def].
  destruct (in_range i (Zlength (o_buf (tr_out (d_tr s))))); cbn [bind]; intros E; inversion E; subst.
  unfold set_d_pb. cbn [mb_val mb_def]. auto.
Qed.

Lemma sublist_upd4 (l : list Z) h b0 b1 b2 b3 :
  4 <= h <= Zlength l ->
  sublist 0 h (upd_Znth (h - 1) (upd_Znth (h - 2) (upd_Znth (h - 3) (upd_Znth (h - 4) l b0) b1) b2) b3) =
  sublist 0 (h - 4) l ++ [b0; b1; b2; b3].
Proof.
  intros Hh.
  set (l1 := upd_Znth (h - 4) l b0).
  assert (L1 : Zlength l1 = Zlength l) by (unfold l1; rewrite upd_Znth_Zlength by lia; reflexivity).
  set (l2 := upd_Znth (h - 3) l1 b1).
  assert (L2 : Zlength l2 = Zlength l) by (unfold l2; rewrite upd_Znth_Zlength by lia; lia).
  set (l3 := upd_Znth (h - 2) l2 b2).
  assert (L3 : Zlength l3 = Zlength l) by (unfold l3; rewrite upd_Znth_Zlength by lia; lia).
  set (l4 := upd_Znth (h - 1) l3 b3).
  assert (L4 : Zlength l4 = Zlength l) by (unfold l4; rewrite upd_Znth_Zlength by lia; lia).
  apply list_solver.Znth_eq_ext.
  - rewrite Zlength_app, !Zlength_sublist by lia. cbn. lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    destruct (Z_lt_le_dec i (h - 4)) as [L|L].
    + rewrite app_Znth1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. rewrite Z.add_0_r.
      unfold l4; rewrite upd_Znth_diff by lia; unfold l3; rewrite upd_Znth_diff by lia; unfold l2; rewrite upd_Znth_diff by lia; unfold l1; rewrite upd_Znth_diff by lia. reflexivity.
    + rewrite app_Znth2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      assert (C : i = h - 4 \/ i = h - 3 \/ i = h - 2 \/ i = h - 1) by lia.
      destruct C as [ -> | [ -> | [ -> | -> ]]].
      * unfold l4; rewrite upd_Znth_diff by lia; unfold l3; rewrite upd_Znth_diff by lia; unfold l2; rewrite upd_Znth_diff by lia; unfold l1. rewrite upd_Znth_same by lia.
        replace (h - 4 - (h - 4 - 0)) with 0 by lia. reflexivity.
      * unfold l4; rewrite upd_Znth_diff by lia; unfold l3; rewrite upd_Znth_diff by lia; unfold l2. rewrite upd_Znth_same by lia.
        replace (h - 3 - (h - 4 - 0)) with 1 by lia. reflexivity.
      * unfold l4; rewrite upd_Znth_diff by lia; unfold l3. rewrite upd_Znth_same by lia.
        replace (h - 2 - (h - 4 - 0)) with 2 by lia. reflexivity.
      * unfold l4. rewrite upd_Znth_same by lia.
        replace (h - 1 - (h - 4 - 0)) with 3 by lia. reflexivity.
Qed.

(** RTDLTCStoredLoopLib.win_copy_ok with the bytes copied. *)
Lemma win_copy_ok2 w (s : dstate) (z : strm) (len left : Z) :
  0 <= left -> 0 <= len < 4294967296 -> 0 <= d_block_start s -> d_block_start s + left <= 4294967296 ->
  Z.min left len <= z_avail_out z -> z_avail_out z < 4294967296 ->
  zall z -> adler_ok w (z_adler z) -> mb_ok (d_window s) ->
  mb_defined (d_window s) (d_block_start s) (d_block_start s + Z.min left len) ->
  exists s6 z6 wb,
    (if left =? 0 then Some (s, z, len) else
     let left := if left >? len then len else left in
     let* bytes := mb_read (d_window s) (d_block_start s) left in
     let* z := out_put z bytes in
     let z := set_z_avail_out z (u32 (z_avail_out z - left)) in
     let z := set_z_total_out z (u64 (z_total_out z + left)) in
     let* _ := guard (in_long (d_block_start s + left)) in
     let s := set_d_block_start s (d_block_start s + left) in
     Some (s, z, u32 (len - left))) = Some (s6, z6, len - Z.min left len) /\
    zstep w z z6 0 wb /\ Zlength wb = Z.min left len /\ bytes wb /\
    d_block_start s6 = d_block_start s + Z.min left len /\ ob_keep s6 = ob_keep s /\
    d_tr s6 = d_tr s /\ d_pbm s6 = d_pbm s /\ d_po s6 = d_po s /\
    wb = sublist (d_block_start s) (d_block_start s + Z.min left len) (mb_val (d_window s)).
Proof.
  intros Hl Hn Hb Hbl Hao Haol Hz Ha Hmb Hdef.
  destruct (Z.eqb_spec left 0) as [->|N].
  - exists s, z, []. rewrite Z.min_l by lia. rewrite Z.sub_0_r, Z.add_0_r.
    split; [reflexivity|]. split; [apply zstep_refl; auto|]. split; [reflexivity|]. split; [constructor|].
    rewrite sublist_nil. repeat split; reflexivity.
  - rewrite min_if. cbv zeta.
    set (kw := Z.min left len) in *.
    assert (Hkw : 0 <= kw <= left /\ kw <= len) by (unfold kw; lia). clearbody kw.
    rewrite (mb_read_some (d_window s) (d_block_start s) kw ltac:(lia) Hdef). cbn [bind].
    set (wb := sublist (d_block_start s) (d_block_start s + kw) (mb_val (d_window s))).
    assert (Lw : Zlength wb = kw).
    { unfold wb. destruct Hdef as (_ & D2 & _). rewrite Zlength_sublist by lia. lia. }
    unfold out_put. rewrite Lw. replace (kw <=? z_avail_out z) with true by zb. cbn [bind].
    replace (in_long (d_block_start s + kw)) with true by (unfold in_long; zb). cbn [bind guard].
    rewrite (u32_id (len - kw)) by lia.
    do 3 eexists. split; [reflexivity|].
    split; [apply out_step; auto|].
    split; [exact Lw|]. split; [unfold wb; apply mb_bytes; auto|].
    split; [reflexivity|]. split; [reflexivity|]. auto.
Qed.

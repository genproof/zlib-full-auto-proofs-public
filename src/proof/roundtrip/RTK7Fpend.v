(* flush_pending writes the first pending bytes, for any output space (RTK7Defs.fpend_fspec7). *)
Require Import Zlib.proof.roundtrip.RTK7Defs.
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTDWriter Zlib.proof.roundtrip.RTDFboKit.
Local Open Scope Z_scope.

(** flush_pending only adds the number of bytes written to total_out and never reads it: the run from the
    stream with total_out set to 0 makes the same decisions and ends in the same stream up to total_out.
    With total_out + avail_out <= 2^64-1 the 64-bit sum does not wrap. *)
Lemma rtk7_fpend_shift s z s' z' :
  zout_ok7 z -> c_flush_pending s z = Some (s', z') ->
  exists z0', c_flush_pending s (set_z_total_out z 0) = Some (s', z0') /\
    z' = set_z_total_out z0' (z_total_out z + z_total_out z0').
Proof.
  intros Hz H. unfold c_flush_pending in *.
  destruct (c_tr_flush_bits (d_out s)) as [o|] eqn:Eo; simpl in *; [|discriminate].
  set (len := if d_pending (set_d_out s o) >? z_avail_out z then z_avail_out z
              else u32 (d_pending (set_d_out s o))) in *.
  destruct (len =? 0) eqn:E0.
  - injection H as <- <-. exists (set_z_total_out z 0). split; [reflexivity|].
    destruct z; unfold set_z_total_out; simpl. f_equal; lia.
  - destruct (mb_read _ (d_po s) len) as [b|] eqn:Eb; simpl in *; [|discriminate].
    pose proof (RTDLTCHuffKit.mb_read_len _ _ _ _ Eb) as Lb.
    unfold out_put in *. simpl in *. destruct (Zlength b <=? z_avail_out z) eqn:Eav; [|discriminate].
    simpl in *. injection H as <- <-. eexists. split; [reflexivity|].
    apply Z.leb_le in Eav. unfold mb_read in Eb.
    destruct ((0 <=? len) && _) eqn:Ed; [|discriminate]. apply andb_prop in Ed as [Ed _].
    apply Z.leb_le in Ed. unfold zout_ok7 in Hz.
    destruct z; unfold set_z_total_out, set_z_avail_out, set_z_out; simpl in *.
    rewrite !u64_id by lia. f_equal; lia.
Qed.

(** The proved fpend_fspec2 (RTDFboKit.fpend_fixed with the proved bit writer) on the shifted stream, whose
    total_out 0 and avail_out < 2^32 meet the narrow bound zout_ok, carried back to the stream. *)
Theorem rtk7_fpend_ok : fpend_fspec7.
Proof.
  intros s z s' z' Ho Hz Hb H.
  destruct (rtk7_fpend_shift s z s' z' Hz H) as (z0' & H0 & ->).
  assert (Hz0 : zout_ok (set_z_total_out z 0)).
  { unfold zout_ok7 in Hz. unfold zout_ok, set_z_total_out; simpl. lia. }
  destruct (fpend_fixed rtdw_writer s _ s' z0' Ho Hz0 Hb H0) as (x & Hzo & Ex).
  exists x. split; [|exact Ex].
  destruct Hzo as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold set_z_total_out in *; simpl in *.
  unfold zout_only; simpl; repeat split; auto; lia.
Qed.

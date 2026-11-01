(* RT-D part FLUSH: the unchecked bit writer appends Format bits (interface: RTDFlushDefs.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs.
Require Zlib.proof.roundtrip.RTDLTCTrComp.
Import ListNotations.
Local Open Scope Z_scope.

Theorem rtd_fw_ok : writer_fspec -> wsend_stmt.
Proof.
  intros [Hw _] o v n Hok Hn Hv Hp Hl.
  pose proof Hok as (Hbv & _ & _).
  destruct (RTDLTCTrComp.cc_send_bits o (repeat true (length (o_buf o))) v n) as [m' Hc].
  - lia.
  - lia.
  - unfold send_bits. destruct (o_bi_valid o >? Buf_size - n); cbn; lia.
  - exact (Hw _ _ _ _ _ _ Hok Hn Hv Hc).
Qed.

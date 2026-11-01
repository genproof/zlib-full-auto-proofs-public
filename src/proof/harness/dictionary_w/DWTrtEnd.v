(* Law rt_dictionary, main (DWKit.v): the final checks (next_in == compressed + compressed_len, next_out == out + data_len, bytes_eq(out, expected, data_len) against the data's copy) and `return 0` (RB with DWKit.F_drt -> main's postcondition). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Zlib.proof.harness.inflate_buffers.IBMainChecks.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* out + data_len: the pointer n bytes after the start of out *)
Lemma trte_add_ptr (p : val) (n : Z) : isptr p -> 0 <= n <= Ptrofs.max_unsigned ->
  force_val (sem_add_ptr_long tuchar p (Vlong (Int64.repr n))) = offset_val n p.
Proof.
  intros P N. destruct p; try contradiction. simpl.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. reflexivity.
Qed.

Lemma trt_end_ok : trt_end_stmt.
Proof.
intros Espec gv vc vd wbits n b D O dict dp op ddp cp dcp ep.
  unfold RB, F_drt.
  rewrite exp_sepcon1; apply extract_exists_pre; intro z.
  rewrite exp_sepcon1; apply extract_exists_pre; intro L.
  rewrite PROP_combine. simpl app.
  unfold trt_end, POST_drt, POST_of, Delta_drt. simplify_func_tycontext.
  Intros.
  destruct H as (DF & (Hn & HD & BD & Pdp & Pop & _) & HO & Hb & RD & RO & Pcp).
  unfold max_size in Hn. subst n.
  rewrite rtl_istreamA_unfold. Intros. unfold rtl_tup. rewrite H1, H2.
  apply seq_assoc1, semax_if_seq. forward_if.
  2: { exfalso. match goal with X: Int.repr Z_STREAM_END <> _ |- _ => apply X; reflexivity end. }
  forward.
  forward.
  (* next_in == compressed + compressed_len: the same pointer, within or one past the end of compressed *)
  { entailer!. apply (Zlib.proof.harness.inflate_buffers.IBMainChecks.ibc_test_eq_self _ b); [lia | ].
    sep_apply (data_at_data_at_ Ews (tarray tuchar b)). cancel. }
  forward_call (Int.repr 1).
  forward.
  apply semax_if_seq.
  forward_if.
  (* next_out == out + data_len: the same pointer, one past the end of out (out itself when data_len = 0) *)
  { try rewrite trte_add_ptr by (auto; rep_lia).
    apply (Zlib.proof.harness.inflate_buffers.IBMainChecks.ibc_test_eq_self _ (Zlength D)); [lia | ].
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength D)) (bytes_rep D) op). cancel. }
  2: { exfalso. match goal with X: offset_val _ _ <> _ |- _ => apply X end.
       rewrite trte_add_ptr by (auto; rep_lia). reflexivity. }
  apply seq_assoc1.
  (* bytes_eq(out, expected, data_len): out holds D, and so does expected, the copy of the data *)
  rewrite <- (rtl_bytes_a Ews (Zlength D) (bytes_rep D) op), <- (rtl_bytes_a Ews (Zlength D) (bytes_rep D) ep).
  forward_call (op, Ews, op, 0, Zlength D, bytes_rep D, D, ep, Ews, ep, 0, Zlength D, bytes_rep D, D,
                Zlength D).
  { split; apply Zlib.proof.harness.inflate_buffers.IBMainChecks.ibc_cbuf0; auto with share. }
  destruct (list_eq_dec Z.eq_dec D D) as [_ | X]; [ | congruence].
  forward.
  forward_call (Int.repr 1).
  forward. Exists (Int.repr 0).
  (* the decompressor's struct back to the local's memory, the rest to TT *)
  sep_apply (data_at_data_at_ Tsh t_zsl). entailer!.
Qed.

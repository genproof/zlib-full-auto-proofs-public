(* Law api_dict_id, main (DWKit.v): after the first inflate(): code == Z_NEED_DICT and strm->adler == adler32_z(1, dict_copy, dict_len), the Adler-32 of the dictionary's copy (A26 with DWKit.F_dai -> main's postcondition). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the dictionary's malloc token as adler32_z's (Adler32's compspecs) *)
Lemma dw_tok_a sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

Lemma tail_api_ok : tail_api_stmt.
Proof.
  intros Espec Q P gv vc vd wbits n b D O dict dp op ddp cp z L dcp DI.
  unfold A26, F_dai, tail_api, tinf_dai. rewrite PROP_combine. simpl app. abbreviate_semax.
  Intros.
  destruct H as (Hfin & (Hn & HD & HbD & Pdp & Pop & Hdl & Hbd & Pddp & Hw) & HO & Hb & HrD & HrO & Pcp).
  forward.
  (* the decompressor as main's struct; strm->adler holds the model's value (the stream is not raw) *)
  rewrite RTLoop.rtl_istreamA_unfold. Intros.
  assert (Hraw : raw_live (Some L) = false) by (simpl; apply Z.eqb_neq; auto).
  rewrite Hraw. unfold adler_v.
  apply seq_assoc1, semax_if_seq.
  (* if (code == Z_NEED_DICT): the else branch is excluded by A26 *)
  forward_if.
  2: { exfalso. match goal with X : Int.repr Z_NEED_DICT <> _ |- _ => apply X; reflexivity end. }
  (* adler32_z(1, dict_copy, dict_len), the copy's object (the dictionary's bytes) at adler32's compspecs *)
  rewrite <- (RTLoop.rtl_bytes_a Ews (Zlength dict) (bytes_rep dict) dcp).
  rewrite <- (dw_tok_a Ews (Zlength dict) dcp).
  forward_call (1, dcp, Zlength dict, false, Ews, dcp, 0, Zlength dict, bytes_rep dict, dict, true, Ews).
  { unfold dict_max in Hdl. split; [rep_lia | ].
    unfold cbuf_ok. split; [destruct dcp; try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity | ].
    split; [auto | ]. split; [lia | ]. split; [lia | ]. split; [auto | ]. split; [auto | ].
    rewrite Z.add_0_l, sublist_same; auto. unfold bytes_rep; rewrite Zlength_map; lia. }
  (* its value is the reference Adler-32 of the dictionary, which A26 says strm->adler holds *)
  assert (Hval : adler32_z_val 1 dict = zf_adler z)
    by (rewrite H1; apply Zlib.proof.adler32.Model.adler32_z_val_ref;
        unfold Zlib.proof.adler32.Model.adler_valid; vm_compute; intuition discriminate).
  unfold RTLoop.rtl_tup.
  forward.
  rewrite Hval.
  forward.
  unfold Int64.cmpu. rewrite Int64.eq_true.
  (* gp_assert(1); return 0, the decompressor given back to the stack frame *)
  forward_call (Int.one).
  sep_apply (data_at_data_at_ Tsh t_zsl).
  unfold POSTCONDITION, abbreviate, POST_dai, POST_of.
  forward.
  Exists (Int.repr 0). entailer!.
Qed.

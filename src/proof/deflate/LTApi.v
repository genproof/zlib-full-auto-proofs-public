(** * The model theory of the deflate laws, deflate_api part.

    [api_facts I Iend] (LawFacts.v) for invariants chosen here, from the core part's facts ([core_facts W]: the
    compressors, deflateInit2_, deflateTune, deflateSetDictionary, deflateParams' level change, the full-flush
    reset) and the header part's ([hdr_facts HI]).  What remains here: deflate()'s entry stage, its compression
    stage around the compression function (block_done: _tr_align, the empty stored block, Z_FULL_FLUSH), the
    trailer, deflateParams, deflateSetHeader, deflateEnd, and the tracking of the data (adler), the output
    (header ... trailer) and the counters. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface.
Require Import Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTApiParams.
Import ListNotations.
Local Open Scope Z_scope.

Theorem api_theory : forall W HI, core_facts W -> hdr_facts HI -> exists I Iend, api_facts I Iend.
Proof.
  intros W HI CF HF. exists (Iapi W HI), Iend. constructor.
  - intros. destruct (api_init W HI level method wbits mem strategy a1 a2 a3 a4 a5 z CF HF) as [A B]; auto.
    split; [exact A|]. intros os z' code E. destruct (B os z' code E) as (B1 & B2 & B3).
    split; [exact B1|]. split; [exact B2|]. intros Hc. destruct (B3 Hc) as (s & ? & ? & _ & ?). eauto.
  - intros. destruct (api_tune W HI wrap s tin tout adler good lazy nice chain z CF HF) as (s' & ? & ? & _ & ?); eauto.
  - intros wrap s tin tout adler d ain aout msg HI0 Hd Hdl Hain Haout.
    destruct (api_dict W HI wrap s tin tout adler d ain aout msg CF HF HI0 Hd Hdl Hain Haout)
      as (s' & z' & code & E1 & E2 & E3 & E4 & _ & E6).
    exists s', z', code. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|exact E6].
  - intros. eapply (api_head W HI); eauto.
  - intros. eapply (api_deflate W HI); eauto.
  - intros. eapply (api_params W HI); eauto.
  - (* af_end_finish *)
    intros s inb nin tin tout adler msg (Hst & Hw & Hp & Hl & Hlf) Hnin.
    exists (set_d_last_flush s Z_FINISH), (zcall inb nin 0 tin 1 tout adler msg).
    rewrite c_deflate_stages.
    assert (Hb : bad_state s = false).
    { unfold bad_state, c_deflateStateCheck, status_ok. rewrite Hst. reflexivity. }
    rewrite Hb. simpl orb. cbv iota.
    unfold c_deflate_entry.
    assert (E1 : d_pending (set_d_last_flush s Z_FINISH) = 0) by exact Hp.
    assert (E2 : d_status (set_d_last_flush s Z_FINISH) = FINISH_STATE) by exact Hst.
    assert (Hin : in_int (d_last_flush s * 2) = true).
    { unfold in_int. apply andb_true_intro; split; apply Z.leb_le; lia. }
    rewrite Hst, E1, Hin. cbn [then_stage bind guard andb negb Z.eqb Z.ltb z_avail_out z_avail_in zcall Z.compare Pos.compare Pos.compare_cont].
    change (Z_FINISH <? 0) with false. change (FINISH_STATE =? FINISH_STATE) with true. change (Z_FINISH =? Z_FINISH) with true.
    destruct (rank Z_FINISH <=? rank (d_last_flush s)); cbn [then_stage bind andb negb].
    all: rewrite E2; change (FINISH_STATE =? FINISH_STATE) with true; cbn [then_stage bind andb negb Z.eqb z_avail_in zcall].
    all: rewrite hdr_stages_busy by (right; exact E2).
    all: cbn [then_stage bind].
    all: unfold c_deflate_compress.
    all: assert (E3 : d_lookahead (set_d_last_flush s Z_FINISH) = 0) by exact Hl.
    all: rewrite E3, E2; cbn [then_stage bind andb orb negb Z.eqb z_avail_in zcall].
    all: change (negb (Z_FINISH =? Z_NO_FLUSH) && negb (FINISH_STATE =? FINISH_STATE)) with false; cbn [bind].
    all: unfold c_deflate_trailer; change (negb (Z_FINISH =? Z_FINISH)) with false.
    all: assert (E4 : d_wrap (set_d_last_flush s Z_FINISH) <=? 0 = true) by (apply Z.leb_le; exact Hw).
    all: rewrite E4.
    all: split; [reflexivity|]; repeat split; auto.
    all: cbn; unfold Z_FINISH; lia.
  - (* af_end_other *)
    intros s z flush (Hst & _) Hf Hne. exists (set_z_msg z (Some Z_STREAM_ERROR)).
    rewrite c_deflate_stages.
    assert (Hb : bad_state s = false).
    { unfold bad_state, c_deflateStateCheck, status_ok. rewrite Hst. reflexivity. }
    rewrite Hb, Z.gtb_ltb. replace (Z_BLOCK <? flush) with false by (symmetry; apply Z.ltb_ge; unfold Z_BLOCK; lia).
    replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). simpl.
    unfold c_deflate_entry. rewrite Hst. simpl.
    replace (flush =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; auto). reflexivity.
  - (* af_end_bad *)
    intros s z flush (Hst & _) Hf. rewrite c_deflate_stages.
    destruct Hf as [Hf|Hf].
    + replace (flush <? 0) with true by (symmetry; apply Z.ltb_lt; lia). rewrite !orb_true_r. reflexivity.
    + rewrite Z.gtb_ltb. replace (Z_BLOCK <? flush) with true by (symmetry; apply Z.ltb_lt; unfold Z_BLOCK; lia).
      rewrite orb_true_r. reflexivity.
  - (* af_end_end *)
    intros s z (Hst & _). unfold c_deflateEnd.
    assert (Hb : bad_state s = false).
    { unfold bad_state, c_deflateStateCheck, status_ok. rewrite Hst. reflexivity. }
    rewrite Hb, Hst. reflexivity.
Qed.

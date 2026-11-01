(* RT-D part FBO against interface v2 (RTDFix.v): fpend_fspec2 and fbo_fspec, from
   flush_block_fspec2.  The kit RTDFboKit.v has the flush_pending proof and the list lemmas. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix.
Require Import Zlib.proof.roundtrip.RTDFboKit Zlib.proof.roundtrip.RTDLTCFlushKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma fbo_proof2 : writer_fspec -> flush_block_fspec2 -> fbo_fspec.
Proof.
  intros W FB s z s' z' syms last dict D BS p Hpre H off wmax Hkw Hbs Hexp Hrok Hsd Hp Hpm Hrun.
  destruct Hpre as (Hprm & Hws & Hlev & Htok & HsL & Hblk & Hbs0 & Hbs24 & Hwin & Hok & Hq & Hlast & Hz).
  pose proof (flush_pre_of s syms Hprm Htok HsL Hok Hq) as Hfp.
  unfold c_flush_block_only in Hrun.
  replace (in_long (d_strstart s - d_block_start s)) with true in Hrun
    by (symmetry; unfold in_long; apply andb_true_intro; split; apply Z.leb_le; lia).
  cbn [guard bind] in Hrun. rewrite u64_id in Hrun by lia.
  match type of Hrun with bind ?e _ = _ => remember e as eb eqn:Eeb end.
  destruct eb as [buf|]; [|discriminate]. cbn [bind] in Hrun.
  assert (Hbuf : forall b, buf = Some b ->
    Zlength b = d_strstart s - d_block_start s /\ d_strstart s - d_block_start s <= 65535 /\
    Forall F.byte_ok b /\ F.syms_data (F.expand dict BS) (map fsym syms) = F.expand dict BS ++ b).
  { intros b ->. destruct (Z.geb_spec (d_block_start s) 0) as [Bp|Bn]; [|discriminate].
    destruct (mb_read _ _ _) as [b0|] eqn:Er; cbn [bind] in Eeb; [|discriminate]. injection Eeb as <-.
    destruct (Hwin ltac:(lia)) as (W1 & W2 & W3).
    unfold mb_read in Er. destruct (_ && _) eqn:Ed; [|discriminate]. injection Er as <-.
    replace (d_block_start s + (d_strstart s - d_block_start s)) with (d_strstart s) by lia.
    split; [rewrite Zlength_sublist by lia; lia|]. split; [lia|].
    split.
    { destruct Hws as (_ & Hwok & _). apply (mb_bytes (d_window s)); [exact Hwok|].
      split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia. }
    apply (fbo_data H (F.expand dict BS) syms s wmax); [exact Hkw|exact Hexp|exact Hrok|exact Hsd|exact Hblk|lia|lia]. }
  destruct (c_tr_flush_block (d_trm s) buf (d_strstart s - d_block_start s) last) as [[[t' m'] kind]|] eqn:Ef;
    [|discriminate].
  cbn [bind] in Hrun.
  destruct (FB (d_tr s) (d_pbm s) buf (d_strstart s - d_block_start s) last t' m' kind syms (F.expand dict BS)
              wmax p Hfp Hlast Hp Hpm Hrok Hbuf Ef) as (blk & Hbok & Hbd & Hbits' & Hlast' & Hob).
  set (s1 := set_d_block_start _ _) in Hrun.
  assert (Hpo0 : d_po s = 0) by apply Hq.
  assert (Hpo1 : d_po s1 = 0) by exact Hpo0.
  destruct (fbo_fpend_gen s1 z s' z' W Hbits' ltac:(lia) Hz (or_intror Hpo1) Hrun) as (x & Hzo & Hx).
  exists x, blk. split; [exact Hzo|]. split; [apply fbo_blocks_ok_app; [exact Hbs|exact Hbok]|].
  split; [rewrite fbo_expand_app, Hbd; exact Hsd|].
  rewrite Hx, (fbo_obits_pend s1 Hpo1). change (tr_out (d_tr s1)) with (tr_out t'). rewrite Hob.
  rewrite <- (fbo_obits_pend s Hpo0). unfold pend. destruct Hq as (Hq1 & _).
  rewrite Hq1, Hpo0, sublist_nil. reflexivity.
Qed.

Theorem rtd_fbo_ok2 :
  Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> flush_block_fspec2 -> fpend_fspec2 /\ fbo_fspec.
Proof. intros _ W FB. split; [exact (fpend_fixed W)|exact (fbo_proof2 W FB)]. Qed.

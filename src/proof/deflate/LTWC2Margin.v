(** * The margin of the last block, for compress2_z's loop

    When the compression function writes the last block (finish_started / finish_done) of a stream of
    n >= 2^25 bytes, the bits produced leave a bit of deflateBound (LTWBEvent.chain_acct_w, the margin [slk]);
    the bit buffer is then empty, so the bytes handed out and pending plus the trailer stay strictly below the
    bound: LTWC2Defs.mg holds from the end of the last block on. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWBComp Zlib.proof.deflate.LTWBEvent.
Require Export Zlib.proof.deflate.LTWC2Defs.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma comp_margin : block_bound_statement -> forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' bs evs,
  MidW W HI n b pos0 inb aout tin0 tout0 flush gz0 s z -> z_next_in z = 0 ->
  d_status s = BUSY_STATE -> d_pending s = 0 -> d_po s = 0 -> d_bi_valid s <= 7 ->
  c_compress_func s z flush = Some (s', z', bs) -> cpost W s z flush s' z' bs evs ->
  (bs = finish_started \/ bs = finish_done) -> 33554432 <= n ->
  z_total_out z' + d_pending s' + tleft s' < b.
Proof.
  intros BB W HI CF HF n b pos0 inb aout tin0 tout0 flush gz0 s z s' z' bs evs HM Hni Hst Hpd Hpo Hbi Ec Hcp
    Hbs Hn25.
  destruct HM as ((Hin & _ & Hav & Htin & Hao & Hol & Hto & Hby) & Hbytes & Hpos0 & Hle & Hfl & Hfin & Haout &
                  Htin0 & Htout0 & Hgz & Hbr).
  rewrite Hni in *.
  destruct Hbr as (H & w0 & HW & Ho & Hw0 & Hb & HH & Hn & Hpos & Htinb & Htout & Hgzok & Hlf & Hph).
  destruct Hph as [P0|[P1|[P2|P3]]].
  { exfalso. destruct P0 as (Hs0 & _). rewrite Hs0 in Hst.
    unfold BUSY_STATE, INIT_STATE, GZIP_STATE in Hst. destruct (w0 =? 2); lia. }
  { exfalso. destruct P1 as (_ & _ & (k & HI1 & _) & _).
    destruct (hw_status HI HF _ _ _ _ HI1) as (_ & _ & Hs1 & _).
    unfold BUSY_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in *. lia. }
  2:{ exfalso. destruct P3 as (Hs3 & _). rewrite Hs3 in Hst. unfold BUSY_STATE, FINISH_STATE in Hst. lia. }
  destruct P2 as (Hs2 & Hwr & _ & Had & E & k & HE & Hk0 & Hmk & Hg).
  pose proof (cw_prm W CF s HW) as Hprm.
  destruct (cpost_extra_w _ _ _ _ _ _ _ _ Hcp) as [Hlvl _].
  destruct Hcp as (HW' & Ho' & Hsp & Hae & (kk & x & Hzs & Hbx & Hkk) & Hch & Hevok & Hbs').
  destruct Hzs as (Zin & Hk & Zni & Zai & _).
  destruct (chain_acct_w BB s flush evs _ _ (Zlength H) E k Hprm Hfl Hevok Hlvl Hch (conj Hk0 (conj Hmk Hg))
              (Zlength_nonneg H)) as (Hsl & _ & Hlast).
  assert (C : last_ev evs /\ flush = Z_FINISH /\ z_avail_in z' = 0 /\ ub s' = 0 /\ d_bi_valid s' = 0).
  { destruct Hbs as [-> | ->].
    - destruct Hbs' as (Hle' & Hff & Hai0 & Hu0 & _ & Hb0 & _). auto.
    - destruct Hbs' as (Hle' & Hff & Hai0 & Hu0 & _ & _ & Hb0). auto. }
  destruct C as (Hle' & Hff & Hai0 & Hu0 & Hb0).
  specialize (Hlast Hle').
  assert (En : E + sum_len evs = n) by (specialize (Hfin Hff); lia).
  rewrite En in Hlast.
  assert (Hs1 : slk n = 1) by (unfold slk; destruct (Z.ltb_spec n 33554432); lia).
  rewrite Hs1 in Hlast. unfold Gb in Hlast. rewrite Hb0 in Hlast.
  destruct Hae as (_ & Ewr' & _).
  unfold tleft. rewrite Ewr', Hwr. unfold tlen in *.
  destruct (Z.ltb_spec 0 w0), (Z.eqb_spec w0 1), (Z.eqb_spec w0 2); lia.
Qed.

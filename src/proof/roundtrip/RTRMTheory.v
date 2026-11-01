(* Law deflate_roundtrip, main (kit: RTRMKit.v): the pure facts of the inflate() calls without a gzip
   header (first_facts) from RTIIface.ifacts: if_plain (no dictionary; zlib/gzip/raw), if_rawdict (raw with a
   dictionary), if_zdict (zlib with a dictionary), at wb := rwbe (rs_wbits): rf_ok's dfinal; iw_of wrap (rwbe
   wbits) = rm_iw rf (rf_ok: wrap = 0 -> rwbe wbits = wb_of wbits; iw_of ignores wb otherwise); dset = 0 ->
   rf_dict = []; hset = 0 -> d_gzhead = None; zd_nomem excludes Z_MEM_ERROR from if_zdict's first call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rm_iw_of_ne wrap wb wb' : wrap <> 0 -> iw_of wrap wb = iw_of wrap wb'.
Proof. intros H. unfold iw_of. destruct (wrap =? 0) eqn:E; [lia | reflexivity]. Qed.

Lemma rm_first_facts Iend vR rf : ifacts -> zd_nomem -> rf_ok Iend vR rf -> rf_hset rf = 0 -> first_facts rf.
Proof.
  intros IF ZN OK H0.
  destruct OK as (RS & _ & _ & _ & NF & OL & DS & HS & DF & WB & _).
  assert (HG : d_gzhead (rf_s rf) = None) by (destruct HS as [(? & _) | (_ & ?)]; [lia | assumption]).
  rewrite HG in DF.
  assert (HD : Zlength (rm_D rf) <= 1048576).
  { unfold rm_D. rewrite Zlength_sublist by lia. unfold rs_ok in RS. lia. }
  assert (HDL : Zlength (rs_dict (rf_rs rf)) <= 32768) by (unfold rs_ok in RS; lia).
  unfold COMP_MAX in OL.
  assert (HW : rf_wrap rf = 0 \/ rf_wrap rf = 1 \/ rf_wrap rf = 2).
  { unfold rf_wrap, wrap_of. destruct (_ <? 0); [lia | destruct (_ >? 15); lia]. }
  assert (IW : iw_of (rf_wrap rf) (rwbe (rs_wbits (rf_rs rf))) = rm_iw rf).
  { unfold rm_iw. destruct (Z.eq_dec (rf_wrap rf) 0) as [E | E].
    - rewrite WB by exact E. reflexivity.
    - apply rm_iw_of_ne; exact E. }
  fold (rm_D rf) in DF.
  intros sp. split.
  - intros Hn z res Hl Hz Hr. unfold res_ok. destruct (rm_zd rf) eqn:E.
    + unfold rm_zd in E. apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2.
      destruct DS as [(_ & Hd & Hne) | (Hd & _)]; [ | lia].
      assert (IW0 : rm_iw rf = 0) by (rewrite <- IW, E1; reflexivity).
      rewrite IW0 in Hl, Hr. rewrite E1 in DF. rewrite Hd in DF |- *.
      pose proof (if_zdict IF _ _ _ _ sp z res DF Hne HDL HD OL Hl Hz Hr) as [M | (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8)].
      * exfalso. exact (ZN _ _ _ _ sp z res DF Hne HDL HD OL Hl Hz Hr M).
      * do 7 (split; [assumption | ]).
        intros L1 Hs Hh. unfold zd_cont. intros alloc_ok winp z1 Hl1. rewrite Hd.
        exact (R8 L1 z1 alloc_ok winp Hs Hh Hl1).
    + assert (Hd : rf_dict rf = []).
      { destruct DS as [(D1 & Hd & Hne) | (_ & Hd)]; [exfalso | exact Hd].
        unfold rm_zd in E. rewrite D1 in E.
        destruct HW as [W | [W | W]].
        - apply Hn; split; assumption.
        - rewrite W in E. discriminate.
        - rewrite W in DF. destruct DF as (_ & _ & _ & _ & ? & _). congruence. }
      rewrite Hd in DF. rewrite <- IW in Hl, Hr.
      exact (if_plain IF _ _ _ _ sp z res DF HD OL Hl Hz Hr).
  - intros Hw Hd1 Hl alloc_ok winp z.
    destruct DS as [(_ & Hd & Hne) | (? & _)]; [ | lia].
    assert (IW0 : rm_iw rf = - rwbe (rs_wbits (rf_rs rf))) by (rewrite <- IW, Hw; reflexivity).
    rewrite IW0 in Hl |- *. rewrite Hw in DF. rewrite Hd in DF |- *.
    pose proof (if_rawdict IF _ _ _ _ sp z alloc_ok winp DF Hne HDL HD OL Hl) as [A B].
    split; [exact A | ].
    intros Hok z' res Hl' Hz' Hr'. unfold res_ok.
    assert (E : rm_zd rf = false) by (unfold rm_zd; rewrite Hw; reflexivity).
    rewrite E. exact (B Hok z' res Hl' Hz' Hr').
Qed.

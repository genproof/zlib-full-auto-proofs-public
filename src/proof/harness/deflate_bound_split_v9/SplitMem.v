(* Law deflate_bound_split, main: the memory lemmas of the kit (split_mem_ok) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma split_mem : split_mem_ok.
Proof.
  intros sp hp gv bs hd s f TE Eg.
  unfold live, sf_at.
  set (ghp := ghp_of hp bs hd).
  set (DS := dstream 2 (Some s) sp ghp gv).
  set (AF := api_fields sp (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f)).
  assert (K : DS * AF * strm_pad sp |-- data_at_ Ews t_strm sp * TT)
    by (apply dstream_data_at_; exact TE).
  assert (H : hdr_at (Some s) ghp (hx_of bs) * hmem hp bs hd |-- data_at_ Tsh t_gzh hp * TT).
  { unfold hdr_at, hmem, ghp, ghp_of. rewrite Eg.
    destruct (andb hd (hset bs)).
    - unfold hx_of. cbv zeta.
      sep_apply (gzh_at_back (hdr_of bs) hp
        (if bd_xsel (bs_d bs) =? 0 then nullval else bd_xfp (bs_d bs))
        (if bd_nsel (bs_d bs) =? 0 then nullval else bd_nfp (bs_d bs))
        (if bd_csel (bs_d bs) =? 0 then nullval else bd_cfp (bs_d bs))).
      rewrite data_at__Tsh_split. cancel.
    - Intros. cancel. }
  eapply derives_trans; [ | apply sepcon_derives; [ apply sepcon_derives; [ apply derives_refl | apply derives_refl ] | apply derives_refl ] ].
  rewrite data_at__Tsh_split.
  sep_apply K. sep_apply H. cancel.
Qed.

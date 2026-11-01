(* Law deflate_bound_split, main: bound = deflateBound(&s, n); pos = 0; finishing = 0; (statements 39..41) (SplitKit.v). *)
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
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitAf.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma part_bound {Espec : OracleKind} Bpre Brun sp hp vosn gv bs s f :
  (forall b s' f', semax Delta_m (J Bpre Brun sp hp vosn gv bs b 0 false s' f') msuf42 Rm_ret) ->
  semax Delta_m (SA Bpre Brun sp hp vosn gv bs (dset bs) true s f) msuf39 Rm_ret.
Proof.
  intros HK.
  unfold msuf39, SA.
  abbreviate_semax.
  Intros.
  unfold draw_locals.
  match goal with H : bs_ok bs |- _ => pose proof H as BS end.
  match goal with H : bound_facts Bpre Brun |- _ => pose proof H as BF end.
  assert (Hn : 0 <= bd_n (bs_d bs) <= 1048576)
    by (destruct BS as ((_ & _ & _ & _ & _ & Hn & _) & _); exact Hn).
  match goal with H : Bpre _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (bf_bound _ _ BF _ _ _ _ _ _ _ _ _ (bd_n (bs_d bs)) H Hn) as (b & Hb & Hbr & _ & HBr) end.
  unfold live. Intros.
  rewrite (sf_split sp f). Intros.
  forward_call (Some s, sp, sf_nin f, ghp_of hp bs true, hx_of bs, bd_n (bs_d bs), b, gv).
  all: try (cancel; fail). all: try (unfold u64_ok; rep_lia; fail).
  sep_apply (af_join sp (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f)).
  fold (sf_at sp f).
  forward. forward.
  eapply semax_pre; [| apply (HK b s f)].
  unfold J, J_ok, loop_locals, live. entailer!.
Qed.

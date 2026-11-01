(* The simulation of the header modes (HEAD, the gzip header FLAGS .. HCRC, DICTID, DICT): one concrete pass of the switch moves the abstract state along its steps. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrFix.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrStr.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrEnd.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrHead.
Import ListNotations.
Local Open Scope Z_scope.

Lemma hcase_or P Q : hcase_ok P -> hcase_ok Q -> hcase_ok (fun md => P md \/ Q md).
Proof. intros HP HQ flush src P0 O0 m a Rl Aw L [H|H]; [apply HP|apply HQ]; auto. Qed.

(* every header mode, the fall-throughs chained from HCRC back to FLAGS *)
Lemma sh_all : kit_stmt -> awf_stmt -> hcase_ok md_hdr.
Proof.
  intros KIT AW.
  destruct sh_str as (XT & NA & CO).
  pose proof (sh_hcrc KIT AW) as HC.
  pose proof (CO KIT AW HC) as CO'.
  pose proof (NA KIT AW CO') as NA'.
  pose proof (XT KIT AW NA') as XT'.
  pose proof (sh_exlen KIT AW (hcase_or _ _ XT' NA')) as EL.
  pose proof (sh_os KIT AW EL) as OS'.
  pose proof (sh_time KIT AW OS') as TI.
  pose proof (sh_flags KIT AW TI) as FL.
  pose proof (sh_head KIT AW) as HD.
  pose proof (sh_dictid KIT AW) as DI.
  pose proof (sh_dict KIT AW) as DC.
  intros flush src P0 O0 m a Rl Aw L Hm.
  unfold md_hdr, hdr_mode in Hm.
  destruct Hm as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]];
    [apply HD|apply FL|apply TI|apply OS'|apply EL|apply XT'|apply NA'|apply CO'|apply HC|apply DI|apply DC];
    auto.
Qed.

Lemma si_hdr : hdr_sim_stmt.
Proof.
  intros KIT AW _ flush src P0 O0 m a Rl Aw L Hm.
  assert (HR: hrel src P0 O0 m a) by (split; [exact Rl | exact (hbits_rel _ _ _ _ _ Rl)]).
  pose proof (sh_all KIT AW flush src P0 O0 m a HR Aw L Hm) as G.
  unfold hgoal in G.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'].
  - destruct G as (a' & A & [R' _] & S). exists a'. auto.
  - destruct G as (Er & a' & A & [R' _] & S). split; [exact Er|]. exists a'. auto.
Qed.

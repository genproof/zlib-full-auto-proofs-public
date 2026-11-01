(* One pass of the switch keeps the header's presence and buffer sizes (Body5Parts.v stepf2_hdr_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Body5Parts.
Require Zlib.proof.inflate_api.Body5HdrKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma stepf2_hdr : stepf2_hdr_stmt.
Proof.
  intros flush m _ _.
  pose proof (Body5HdrKit.stepf2_hrel flush lenfix_list distfix_list m) as H.
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m'];
    destruct H as (A & B & C & D & E & _); unfold hdr_same; auto.
Qed.

(* Law api_deflate_any: the loop head after an iteration (AnyCheck.any_check).  read += take - strm.avail_in,
   left = strm.avail_in, finishing = finishing || flush == Z_FINISH give the next loop head [any_next]; when
   deflate did not return Z_STREAM_END it satisfies main's loop invariant again ([any_next_ok], from dr_ok's
   [J] of deflate's run and call_okw's accounting of total_in).  Also the removal of a temp from a LOCAL list by
   rewriting, for the proofs of the checks (AnyCheckCode.v, AnyCheckBytes.v, AnyCheck.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* Floyd's simplify_remove_localdef_temp (simpl on ident_eq of the large $"..." idents of main's locals) takes
   minutes in main: the proofs of the checks remove a temp by rewriting with these instead *)
Lemma rlt_nil i : remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rlt_gvars i g l : remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_lvar i j t v l : remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rlt_same i v l : remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rlt_cons i j v l :
  i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

(* the loop head after an iteration: deflate's state, [read] advanced by what deflate consumed, [left] the input
   it left (the rest of the data to give with Z_FINISH once Z_FINISH was given), the stream fields deflate left *)
Definition any_next (data : list Z) (ls : lstate) (ci : citer) (d : dres) : lstate :=
  let z := dr_z d in
  mkLS (dr_s d)
    (if ci_flush ci =? Z_FINISH then Some (sublist (z_next_in z) (ci_take ci) (ci_inb data ls ci)) else None)
    (ls_read ls + z_next_in z) (z_avail_in z) (z_total_out z) (z_adler z) (z_msg z) (dr_msgv d).

Lemma any_next_ok J n data datap ls ci c d :
  J_ok J n data datap ls -> ci_ok n ls ci -> cs_ok J ls ci c -> dr_ok J data ls ci c d ->
  dr_code d <> Z_STREAM_END -> J_ok J n data datap (any_next data ls ci d).
Proof.
  intros HJ Hci Hcs Hdr Hend.
  pose proof HJ as (Hsetup & HJs & Hrd & Hleft & Hfin & Htout & Hm).
  pose proof Hsetup as (Hdf & Hn & Hdl & Hdb & Pdp).
  pose proof Hci as (Htk & Htkn & Hfl & Hcfin & Hroom & Hbsl & Hbs & Pp & Po & Pb).
  pose proof Hcs as (HJc & Hnin & Hcout & Hcb & Hcfin' & Hctout & Hcm).
  pose proof Hdr as (Hcall & Hok & HJd & Hcodes).
  pose proof Hok as (Hzin & Hni & Hai & Hti & Hao & Hzo & Hto & Hzb).
  specialize (HJd Hend).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  unfold J_ok, any_next; simpl.
  split; [ exact Hsetup | ].
  split; [ replace (ls_read ls + z_next_in (dr_z d)) with (z_total_in (dr_z d)) by lia; exact HJd | ].
  split; [ lia | ]. split; [ lia | ].
  split.
  { (* after Z_FINISH: the rest of the piece is the data from the new [read] on, [left] bytes of it *)
    destruct (ci_flush ci =? Z_FINISH); [ | exact I ]. split; [ lia | ].
    unfold ci_inb. rewrite sublist_sublist by lia. f_equal; lia. }
  split; [ rewrite Hto; unfold u64r, u64;
           match goal with |- context [?x mod ?m] => pose proof (Z.mod_pos_bound x m ltac:(lia)) end; lia | ].
  tauto.
Qed.

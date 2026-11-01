(* uncompress2_z with a Z_NULL source of length 0 (UWNSegs.v), statement 14: the do-while loop of inflate() calls.
   Its body is the refills (UWNSegR.v) and the call (UWNSegCall.v); the test `while (err == Z_OK)` goes back to the
   invariant or leaves the loop with the model's loop ended.  The script is UWSegLoop.v's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr.
Require Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWNSegs.
Require Import Zlib.proof.uncompr.UWNSegR.
Require Import Zlib.proof.uncompr.UWNSegCall.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the loop's body: the three parts in sequence *)
Lemma un_lbody {Espec: OracleKind} (A: unargs) (v: val) : un_facts A -> isptr v ->
  semax Delta_uw (un_inv A v) (Ssequence uw_rout (Ssequence uw_rin uw_call_st)) (normal_ret_assert (un_LC A v)).
Proof.
  intros F Pv.
  eapply semax_seq'; [apply un_rout_body; auto |].
  eapply semax_seq'; [apply un_rin_body; auto |].
  apply un_call_body; auto.
Qed.

Lemma un_loop : un_loop_stmt.
Proof.
  intros Espec A v F Pv K.
  rewrite uw_seg14_eq. abbreviate_semax.
  forward_loop (un_inv A v) continue: (un_LC A v) break: (un_brk A v).
  { apply ENTAIL_refl. }
  { eapply semax_post; [ | | | | apply (un_lbody A v F Pv) ];
      unfold POSTCONDITION, abbreviate, loop1_ret_assert; destruct (POST_un A); intros; simpl;
      normalize; intros; apply andp_left2, derives_refl. }
  { (* while (err == Z_OK) *)
    destruct A as [gv dnull dsh dp dn dc cap dlp dtok slp gsh tsh].
    unfold un_LC, un_inv, un_brk, un_lcl, un_sep, un_fr, uw_test. Intros err m out z L ao.
    forward_if.
    { forward.
      match goal with Hx: err = 0 |- _ => subst err end.
      match goal with Hx: 0 = Z_OK -> _ |- _ => destruct (Hx eq_refl) as [Hr Hv] end.
      unfold un_inv, un_lcl, un_sep, un_fr.
      Exists m out z L ao. entailer!. }
    { forward.
      assert (err <> Z_OK) by (intro; subst; unfold Z_OK in *; contradiction).
      unfold un_brk, un_lcl, un_sep, un_fr.
      Exists err m out z L ao. entailer!. } }
  (* after the loop *)
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  exact K.
Qed.

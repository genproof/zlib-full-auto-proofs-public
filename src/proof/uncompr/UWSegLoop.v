(* uncompress2_z for any sizes (UWSegs.v), statement 14: the do-while loop of inflate() calls.  Its body is
   the refill of avail_out (UWSegROut.v), the refill of avail_in (UWSegRIn.v) and the call (UWSegCall.v); the
   test `while (err == Z_OK)` goes back to the invariant or leaves the loop with the model's loop ended. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.UWSegs.
Require Import Zlib.proof.uncompr.UWSegROut.
Require Import Zlib.proof.uncompr.UWSegRIn.
Require Import Zlib.proof.uncompr.UWSegCall.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the loop's body: the three parts in sequence *)
Lemma uw_lbody {Espec: OracleKind} (A: uwargs) (v: val) : uw_facts A -> isptr v ->
  semax Delta_uw (uw_inv A v) (Ssequence uw_rout (Ssequence uw_rin uw_call_st)) (normal_ret_assert (uw_LC A v)).
Proof.
  intros F Pv.
  eapply semax_seq'; [apply uw_rout_body; auto |].
  eapply semax_seq'; [apply uw_rin_body; auto |].
  apply uw_call_body; auto.
Qed.

Lemma uw_loop : uw_loop_stmt.
Proof.
  intros Espec A v F Pv K.
  rewrite uw_seg14_eq. abbreviate_semax.
  forward_loop (uw_inv A v) continue: (uw_LC A v) break: (uw_brk A v).
  { apply ENTAIL_refl. }
  { eapply semax_post; [ | | | | apply (uw_lbody A v F Pv) ];
      unfold POSTCONDITION, abbreviate, loop1_ret_assert; destruct (POST_uw A); intros; simpl;
      normalize; intros; apply andp_left2, derives_refl. }
  { (* while (err == Z_OK) *)
    destruct A as [gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh].
    unfold uw_LC, uw_inv, uw_brk, uw_lcl, uw_sep, uw_fr, uw_test. Intros err m used out z L ai ao.
    forward_if.
    { forward.
      match goal with Hx: err = 0 |- _ => subst err end.
      match goal with Hx: 0 = Z_OK -> _ |- _ => destruct (Hx eq_refl) as [Hr Hv] end.
      unfold uw_inv, uw_lcl, uw_sep, uw_fr.
      Exists m used out z L ai ao. entailer!. }
    { forward.
      assert (err <> Z_OK) by (intro; subst; unfold Z_OK in *; contradiction).
      unfold uw_brk, uw_lcl, uw_sep, uw_fr.
      Exists err m used out z L ai ao. entailer!. } }
  (* after the loop *)
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  exact K.
Qed.

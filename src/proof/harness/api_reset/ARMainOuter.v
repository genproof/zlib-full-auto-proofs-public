(* Law api_reset, main: the for-loop's body after its test (ARMainKit.seg_obody), in phase 0 or 1: the input
   (upto, any_bytes), read = 0, the do-while (invariant ARMainKit.dinv; its body: body_stmt), and after phase 0
   the reset (rst_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_input against _input_len); each identifier comparison is decided by vm_compute instead. *)
Ltac ar_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in ar_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := ar_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma obody_of : body_stmt 0 -> body_stmt 1 -> rst_stmt -> obody_stmt.
Proof.
  intros B0 B1 RS Espec J0 J1 gv va vb w ph za La zb Lb AF WB Hw Pa Pb Hph.
  unfold seg_obody, oinv_at.
  Intros.
  abbreviate_semax.
  (* input_len = upto(PTRDIFF_MAX); input = any_bytes(input_len); a NULL input returns 0 *)
  forward_call (9223372036854775807). Intros len.
  forward_call (len, gv).
  Intros vret. destruct vret as [inp src]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength src = len |- _ => subst len end.
  assert (Hph2: ph = 0 \/ ph = 1) by lia.
  destruct (eq_dec inp nullval) as [PN|PN].
  { subst inp. forward_if.
    { forward. Exists (Int.repr 0). entailer!.
      destruct Hph2 as [-> | ->]; unfold fresh_mem; simpl Z.eqb; cbv iota.
      - sep_apply a_frame. sep_apply fresh_frame. cancel.
      - sep_apply (a_frame gv va). sep_apply (a_frame gv vb). cancel. }
    { exfalso. auto. } }
  rewrite tok_adler_cs, bytes_adler_cs. Intros.
  forward_if.
  { contradiction. }
  forward. (* read = 0 *)
  assert_PROP (isptr inp) as Pinp by entailer!.
  assert (GF: g_facts J0 J1 w inp src va vb).
  { refine (conj AF (conj WB (conj Hw (conj _ (conj H3 (conj Pinp (conj Pa Pb))))))).
    change Int64.max_signed with 9223372036854775807. lia. }
  forward_loop (dinv J0 J1 gv va vb w ph inp src)
    continue: (dinv J0 J1 gv va vb w ph inp src)
    break: (dinv J0 J1 gv va vb w ph inp src).
  - (* entry: position 0 *)
    unfold dinv, dinv_at. Exists 0 za La zb Lb.
    assert (DP: dprop J0 J1 w src ph 0 za La zb Lb).
    { unfold dprop, ostate in *.
      destruct Hph2 as [-> | ->]; simpl Z.eqb in *; cbv iota in H0 |- *.
      - destruct H0 as (HJ & Hs & Hr & Hz). refine (conj Hs (conj Hr (conj (HJ src H3) Hz))).
      - destruct H0 as (HJ & Hs & Hs' & Hr & Hr').
        refine (conj Hs (conj Hr (conj (HJ src H3) (conj Hs' Hr')))). }
    entailer!.
  - (* the do-while body: B0 / B1 *)
    unfold dinv. Intros pos za1 La1 zb1 Lb1.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    destruct Hph2 as [-> | ->].
    + apply (B0 Espec J0 J1 gv va vb w inp src pos za1 La1 zb1 Lb1 GF).
    + apply (B1 Espec J0 J1 gv va vb w inp src pos za1 La1 zb1 Lb1 GF).
  - (* the test nondet_u8() != 0 *)
    unfold dinv. Intros pos za1 La1 zb1 Lb1. unfold dinv_at.
    forward_call tt. Intros c.
    forward_if.
    + forward. unfold dinv. Exists pos za1 La1 zb1 Lb1. unfold dinv_at. entailer!.
    + forward. unfold dinv. Exists pos za1 La1 zb1 Lb1. unfold dinv_at. entailer!.
  - (* after the do-while: the reset in phase 0 *)
    unfold dinv. Intros pos za1 La1 zb1 Lb1.
    destruct Hph2 as [-> | ->].
    + unfold dinv_at. Intros. forward_if.
      * unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
        eapply semax_pre; [ | eapply semax_post; [ | | | |
          apply (RS Espec J0 J1 gv va vb w inp src pos za1 La1 zb1 Lb1 GF) ] ].
        { unfold dinv_at. entailer!. }
        { apply andp_left2; apply derives_refl. }
        { simpl RA_break. apply andp_left2. unfold POST_m. simpl RA_break. intro rho. normalize. }
        { simpl RA_continue. apply andp_left2. unfold POST_m. simpl RA_continue. intro rho; normalize. }
        { intros; apply andp_left2; apply derives_refl. }
      * exfalso. auto.
    + unfold dinv_at. Intros. forward_if.
      * exfalso. lia.
      * forward. unfold ocont, oinv_at. Exists 1 za1 La1 zb1 Lb1.
        change (1 + 1) with 2. unfold fresh_mem, ostate. simpl Z.eqb. cbv iota.
        entailer!.
Qed.

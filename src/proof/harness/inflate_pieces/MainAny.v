(* Law rj_any_input, main: harness/rj_any_input.c proved against MainLib.main_core_spec R_any (Globals.v) for
   ANY invariant P with the facts of Facts.v (pieces_facts P) and of Progress.v (pieces_progress P): windowBits
   assumed in zlib.h's ranges (laws_session.h's inflate_window_ok: exactly the windowBits inflateInit2_
   accepts, laws_session/Facts.v), the input object, new_stream() and inflateInit2_ (Z_MEM_ERROR returns, so
   the asserted code is Z_OK), the stream after Z_OK as an istreamA satisfying P (pf_init), then the do-while
   with the loop invariant MainSession.pk_inv4, whose body is MainAnyLoop.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.harness.inflate_pieces.Progress.
Require Import Zlib.proof.harness.inflate_pieces.MainSession.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.rj_any_input.code.
Require Import Zlib.proof.harness.inflate_pieces.MainAnyLoop.

#[local] Existing Instance Any.CS.
#[local] Existing Instances Any.CC_inflate Any.CC_adler32 Any.CC_crc32 Any.CC_zutil Any.CC_inffast Any.CC_inftrees Any.CC_compress.
Import AnyK AnyS.

Lemma body_any P : pieces_facts P -> pieces_progress P ->
  @semax_body (QPvarspecs Any.p) Gk_any Any.CS f_main (_main, main_core_spec R_any).
Proof.
  intros PF PG.
  start_function.
  unfold R_any, R_of. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv inflate.code._zcalloc)) (func_ptr' _ (gv inflate.code._zcfree)).
  fold (zfuncs gv).
  (* window_bits = any; gp_assume(inflate_window_ok(window_bits)): zlib.h's values, those inflateInit2_ accepts *)
  forward_call tt. Intros wb.
  assert (Ew: Int.repr wb = Int.repr (Int.signed (Int.repr wb))) by (rewrite Int.repr_signed; auto).
  rewrite Ew. clear Ew. set (w := Int.signed (Int.repr wb)).
  assert (Hw: Int.min_signed <= w <= Int.max_signed) by apply Int.signed_range. clearbody w.
  forward_call w.
  forward_call (Int.repr (if LS.inflate_window_valid w then 1 else 0)).
  { destruct (LS.inflate_window_valid w); entailer!. }
  Intros. assumed_b.
  rewrite Zlib.proof.harness.laws_session.Facts.inflate_window_valid_ok in E. rename E into Hwb.
  (* the input *)
  forward_call (9223372036854775807). Intros len.
  split_call.
  forward_call (len, gv).
  Intros vret. destruct vret as [inp src]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength src = len |- _ => subst len end.
  rewrite !bytes_a, !tok_a.
  forward.
  destruct (eq_dec inp nullval) as [PN|PN].
  { subst inp. forward_if. { forward. Exists (Int.repr 0). entailer!. } infeas. }
  Intros. aptr inp Pinp.
  forward_if. { infeas. }
  (* new_stream(&strm); code = inflateInit2(&strm, window_bits) *)
  rewrite strm_undef.
  forward_call (v_strm, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  rewrite (ns_raw_eq gv v_strm).
  assert_PROP (isptr v_strm) as Pvs by entailer!.
  rewrite hversion.
  aptr (gv ___stringlit_rj_any_input_1) Pver.
  forward_call (gv, Tsh, v_strm, ns_raw, Vundef, Vundef, nullval, w, gv ___stringlit_rj_any_input_1, Ers,
                  hv_list, 49, 112).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  { change (Zlength hv_list) with 6; repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [alloc_ok sp].
  rewrite init_ret_ok by auto. rewrite Hwb.
  (* with an accepted windowBits: Z_OK, or Z_MEM_ERROR (the run ends) *)
  destruct alloc_ok;
    unfold init_mem; rewrite if_false by (intro; subst; contradiction); simpl Z.eqb; cbv iota.
  2: { forward_if; [ | infeas]. forward. Exists (Int.repr 0). sep_apply raw_frame. entailer!. }
  forward_if. { infeas. }
  forward_call (Int.repr 1).
  forward.
  simpl fst in *; simpl snd in *. rewrite Int.signed_repr by rep_lia.
  Intros. set (L0 := init_live sp w) in *.
  assert_PROP (live_ok L0) as HL0 by (unfold istream_raw; entailer!).
  sep_apply init_istreamA.
  assert (HP0: P (z_init L0 Vundef) L0).
  { apply (pf_init P PF w); auto. apply z_init_ok. }
  set (Fr := (@data_at Zlib.units.Inflate.CS Ers (tarray tschar (Zlength hv_list)) hv_list
               (gv ___stringlit_rj_any_input_1) * version_lit gv)%logic).
  (* the do-while, with the invariant pk_inv4 *)
  forward_loop (pk_inv4 P gv v_strm v_at inp src Fr)
    continue: (pk_inv4 P gv v_strm v_at inp src Fr)
    break: (pk_inv4 P gv v_strm v_at inp src Fr).
  { unfold pk_inv4. Exists (z_init L0 Vundef) L0. entailer!.
    split; [apply z_init_ok | simpl; pose proof (Zlength_nonneg src); lia]. unfold Fr; cancel. }
  2: { unfold pk_inv4. Intros z L. forward_call tt. Intros c.
       forward_if; [forward; Exists z L; entailer! | forward; Exists z L; entailer!]. }
  2: { unfold pk_inv4. Intros z L. forward. Exists (Int.repr 0). sep_apply a_frame. entailer!. }
  unfold pk_inv4. Intros z L.
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  eapply semax_pre; [ | apply (body_any_loop P gv v_strm v_at inp src Fr z L); auto; lia ].
  entailer!.
Qed.

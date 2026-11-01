(* Law api_short_output (data of any length): main's body (harness/api_short_output.c) against MainLib.main_core_spec R
   under WMainDefs.Gmain, from RTC2W.c2w_bound_stmt, RTC2WFinal.c2w_final_stmt and UTheoryW.uw_theory_stmt. The proof
   is round 1's bounded one (Main.v) with the specifications for any sizes: compress2 (RTCSpecW.compress2_spec_w, whose
   precondition asks for the run's existence: c2w_bound_stmt) and uncompress2 (USpecW.uncompress2_spec_w); the output
   space may be Z_NULL when its capacity is 0, which the flag [dnull] of uncompress2_spec_w and
   BytesEqNull.bytes_eq_spec_n covers. The proof is cut in six segments, one per file, to keep each file's check short:
   here the inputs (original_len, decompressed_size, null_if_empty, level, compressed_bound: compressBound's formula,
   equal to compressBound_z by BoundFormula.cb_formula_i64), the data and its copy `original_copy`, the buffer
   `compressed` and the output space (Z_NULL when decompressed_size = 0 and null_if_empty = 1); WMainNull.v the test of the objects; WMainC2.v the call of compress2; WMainInput.v
   the input of uncompress2 (the stream and `suffix_len` more bytes); WMainCopy.v the copy of the stream into it;
   WMainTail.v the call of uncompress2 and the checks. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.roundtrip.RTCLFacts.
Require Import Zlib.proof.compress.BoundFormula.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WMainDefs.
Require Import Zlib.proof.harness.api_short_output.WMainTail Zlib.proof.harness.api_short_output.WMainC2.
Require Import Zlib.proof.harness.api_short_output.WMainNull.
Require Import Zlib.proof.harness.api_short_output.WMainCopy.
Require Import Zlib.proof.harness.api_short_output.WMainInput.
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

Lemma body_main_w : body_main_w_stmt.
Proof.
  intros CB CF UF.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  forward_call (9223372036854775807 - 1).
  Intros n0.
  forward.
  replace (Int64.add (Int64.repr (Int.signed (Int.repr 1))) (Int64.repr n0)) with (Int64.repr (1 + n0))
    by (rewrite add64_repr; reflexivity).
  assert (Hn: 1 <= 1 + n0 <= 9223372036854775807) by lia. forget (1 + n0) as n. clear H.
  forward_call (n - 1).
  Intros cap.
  (* null_if_empty = upto(1) *)
  forward_call 1.
  Intros ne.
  forward_call 10.
  Intros v.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.signed_repr by rep_lia. rep_lia. }
  rewrite Int64.unsigned_repr by rep_lia.
  replace (Int.add (Int.neg (Int.repr 1)) (Int.repr v)) with (Int.repr (v - 1))
    by (rewrite Int.neg_repr, add_repr; f_equal; lia).
  (* compressed_bound = compressBound's formula, compressBound_z(n) *)
  forward.
  match goal with |- context [temp _compressed_bound (Vlong ?x)] =>
    replace x with (Int64.repr (c_compressBound n))
      by (unfold c_compressBound; rewrite <- (cb_formula_i64 n) by lia; reflexivity) end.
  pose proof (asw_cb_range n ltac:(rep_lia)) as Hcb.
  set (cb := c_compressBound n) in *.
  (* original = alloc_any_bytes(original_len); if (original == NULL) return 0; *)
  forward_call (n, gv).
  Intros vret. destruct vret as [datap bs]. simpl fst in *; simpl snd in *.
  asw_law.
  destruct (eq_dec datap nullval) as [PD|PD].
  { subst datap. forward_if. { ret0. } { asw_bad. } }
  Intros.
  forward_if. { contradiction. }
  assert_PROP (isptr datap) as Pd by entailer!.
  (* original_copy = copy_of(original, original_len) *)
  rewrite <- (asw_bytes_adler Ews n _ datap).
  forward_call (datap, Ews, datap, 0, n, bytes_rep bs, n, bs, gv).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. unfold bytes_rep.
    split; [reflexivity|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|].
    rewrite Z.add_0_l, sublist_same by list_solve. reflexivity. }
  Intros expp.
  asw_law.
  (* compressed = malloc(compressed_bound) *)
  forward_call (tarray tuchar cb, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros compp.
  (* decompressed = Z_NULL; if (decompressed_size > 0 || null_if_empty == 0) decompressed = alloc_any_bytes(..) *)
  forward.
  ifpost _t'9 (Int.repr (if ((0 <? cap) || (ne =? 0))%bool then 1 else 0)).
  { forward. entailer!.
    match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    destruct (Z.ltb_spec 0 cap); [reflexivity | lia]. }
  { forward. entailer!.
    match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    destruct (Z.ltb_spec 0 cap); [lia | ]. cbn [orb]. unfold Int64.cmpu.
    destruct (Z.eqb_spec ne 0) as [E|E]; [subst ne; reflexivity | ].
    rewrite Int64.eq_false; [reflexivity | ]. intro F. apply (f_equal Int64.unsigned) in F.
    rewrite !Int64.unsigned_repr in F by rep_lia. lia. }
  (* the output space: alloc_any_bytes' result, or Z_NULL when decompressed_size = 0 and null_if_empty = 1 *)
  match goal with |- semax _ (PROPx _ (LOCALx (_ :: temp _decompressed _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (EX outp : val, EX ob : list Z,
      PROPx [Zlength ob = cap] (LOCALx (temp _decompressed outp :: Q)
        (SEPx ((if eq_dec outp nullval then emp
                else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp)
               :: R)))) end.
  { forward_call (cap, gv).
    Intros vret. destruct vret as [outp ob]. simpl fst in *; simpl snd in *.
    asw_law.
    forward. Exists outp ob. entailer!. }
  { forward.
    assert (cap = 0).
    { destruct (Z.ltb_spec 0 cap); [ | lia]. cbn [orb] in *. asw_bad. }
    subst cap. Exists nullval (@nil Z).
    destruct (eq_dec nullval nullval) as [_|NN]; [ | contradiction NN; reflexivity]. entailer!. }
  Intros outp ob.
  (* the rest: WMainNull.w_null_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  eapply semax_pre; [ | apply (w_null_ok CB CF UF gv v_compressed_len v_decompressed_len v_source_consumed_len n bs cap v datap compp
                                 outp expp ob)].
  unfold w_null_pre. subst cb. entailer!.
Qed.

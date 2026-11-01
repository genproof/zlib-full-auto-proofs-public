(* Law rt_roundtrip (data of any length): the body of main (WMainDefs.body_main_w_stmt), from
   RTC2W.c2w_bound_stmt, RTC2WFinal.c2w_final_stmt and UTheoryW.uw_theory_stmt.  The proof is round 1's bounded
   one (Main.v) with the specifications for any sizes: compress2 (RTCSpecW.compress2_spec_w, whose precondition
   asks for the run's existence: c2w_bound_stmt) and uncompress2 (USpecW.uncompress2_spec_w).  This file goes as
   far as the inputs are drawn and the data (Z_NULL when empty and null_if_empty asks for it), its copy
   original_copy and the two buffers compressed and decompressed are made; the rest is WMainNull.w_null_ok (their
   test, the copy decompressed_copy of the output space and its test), WMainMid.w_mid_ok (compress2),
   WMainInput.w_input_ok (the source of uncompress2: the stream and suffix_len bytes), WMainCopy.w_copy_ok (the
   stream copied into it) and WMainTail.w_tail_ok (uncompress2 and the checks). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.CopyOfNull.
Require Import Zlib.proof.compress.BoundFormula.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.rt_roundtrip.WCS Zlib.proof.harness.rt_roundtrip.WGlobals
        Zlib.proof.harness.rt_roundtrip.WMainDefs Zlib.proof.harness.rt_roundtrip.WMainTail
        Zlib.proof.harness.rt_roundtrip.WMainMid
        Zlib.proof.harness.rt_roundtrip.WMainNull.
Require Import Zlib.proof.harness.rt_roundtrip.WMainCopy.
Require Import Zlib.proof.harness.rt_roundtrip.WMainInput.
Require Zlib.proof.roundtrip.RTCLGlobals.
Require Import Zlib.harness.rt_roundtrip.code.
#[local] Existing Instance Zlib.proof.harness.rt_roundtrip.WCS.CS.
Local Open Scope logic.

(* `if (len > 0 || null_if_empty == 0) p = alloc_any_bytes(len);` with p Z_NULL before: after it, p is Z_NULL or
   an object of len bytes, as alloc_any_bytes returns it (Z_NULL is an empty list of bytes of length 0). *)
Ltac rtw_alloc_if p n := match goal with |- semax _ (PROPx _ (LOCALx (temp _ _ :: temp p _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (EX q: val, EX bs: list Z,
    PROPx [Zlength bs = n; is_bytes bs] (LOCALx (temp p q :: Q)
      (SEPx ((if eq_dec q nullval then emp
              else (malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (bytes_rep bs) q)) :: R))))
  end.

Lemma body_main_w : body_main_w_stmt.
Proof.
  intros CB CF UF.
  start_function.
  unfold R, Zlib.proof.roundtrip.RTCLGlobals.R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (Zlib.proof.inflate.Callees.zfuncs gv).
  (* original_len = upto(PTRDIFF_MAX); decompressed_size = original_len + upto(PTRDIFF_MAX - original_len) *)
  forward_call 9223372036854775807.
  Intros n.
  forward_call (9223372036854775807 - n).
  Intros c0.
  forward.
  replace (Int64.add (Int64.repr n) (Int64.repr c0)) with (Int64.repr (n + c0))
    by (rewrite add64_repr; reflexivity).
  assert (Hcap: n <= n + c0 <= 9223372036854775807) by lia. forget (n + c0) as cap.
  (* null_if_empty = upto(1); level = -1 + (int) upto(10) *)
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
  pose proof (rtw_cb_range n ltac:(rep_lia)) as Hcb.
  set (cb := c_compressBound n) in *.
  (* original = Z_NULL; if (original_len > 0 || null_if_empty == 0) original = alloc_any_bytes(original_len); *)
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  ifpost _t'6 (Int.repr (if ((0 <? n) || (ne =? 0))%bool then 1 else 0)).
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 n); [reflexivity | lia]. }
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 n); [lia | ]. assert (ne = 0 \/ ne = 1) as [-> | ->] by lia; reflexivity. }
  rtw_alloc_if _original n.
  { forward_call (n, gv). Intros vret. destruct vret as [q bs]. simpl fst in *; simpl snd in *. rtw_law.
    forward. Exists q bs. entailer!. }
  { rtw_tf E. apply orb_false_iff in E. destruct E as [E1 _]. apply Z.ltb_ge in E1.
    forward. Exists nullval (@nil Z). entailer!. split; [rewrite Zlength_nil; lia | apply Forall_nil]. }
  Intros datap bs. try subst n.
  (* if (original == NULL && original_len > 0) return 0; *)
  assert (Hs: exists sn: bool, if sn then datap = nullval else datap <> nullval)
    by (destruct (eq_dec datap nullval); [exists true | exists false]; auto).
  destruct Hs as [sn Hs]. rewrite (rtw_if_null sn datap) by exact Hs.
  rewrite (rtw_if_split sn). Intros.
  ifpost _t'7 (Int.repr (if (sn && (0 <? (Zlength bs)))%bool then 1 else 0)).
  { destruct sn.
    - rewrite Hs. entailer!.
    - eapply (@malloc_test_eq CS _ (Zlength bs)); [lia | ].
      sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) datap). cancel. }
  { destruct sn; [ | congruence]. forward. entailer!. rewrite rtw_gt0 by rep_lia. reflexivity. }
  { forward. destruct sn; [congruence | ]. entailer!. }
  forward_if.
  { ret0. }
  rtw_tf E. assert (Hsn: sn = true -> bs = []).
  { intros ->. simpl in E. apply Z.ltb_ge in E. apply Zlength_nil_inv. pose proof (Zlength_nonneg bs). lia. }
  clear E.
  assert_PROP (if sn then datap = nullval /\ bs = [] else isptr datap) as Fsn.
  { destruct sn; entailer!. }
  (* original_copy = copy_of(original, original_len) *)
  rewrite <- (rtw_bytes_adler Ews (Zlength bs) (bytes_rep bs) datap).
  forward_call (sn, datap, Ews, datap, 0, (Zlength bs), bytes_rep bs, (Zlength bs), bs, gv).
  { destruct sn.
    - destruct Fsn as (-> & ->). rewrite Zlength_nil in *. auto.
    - unfold cbuf_ok. rewrite isptr_offset_val_zero by exact Fsn.
      unfold bytes_rep. repeat split; auto; try rep_lia; try list_solve. }
  Intros expp.
  rtw_law.
  (* compressed = malloc(compressed_bound) *)
  forward_call (tarray tuchar cb, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros compp.
  (* decompressed = Z_NULL; if (decompressed_size > 0 || null_if_empty == 0) decompressed = alloc_any_bytes(..) *)
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  ifpost _t'11 (Int.repr (if ((0 <? cap) || (ne =? 0))%bool then 1 else 0)).
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 cap); [reflexivity | lia]. }
  { rewrite !Int64.unsigned_repr in * by rep_lia. forward. entailer!.
    destruct (Z.ltb_spec 0 cap); [lia | ]. assert (ne = 0 \/ ne = 1) as [-> | ->] by lia; reflexivity. }
  rtw_alloc_if _decompressed cap.
  { forward_call (cap, gv). Intros vret. destruct vret as [q ob]. simpl fst in *; simpl snd in *. rtw_law.
    forward. Exists q ob. entailer!. }
  { rtw_tf E. apply orb_false_iff in E. destruct E as [E1 _]. apply Z.ltb_ge in E1.
    forward. Exists nullval (@nil Z). entailer!. split; [rewrite Zlength_nil; lia | apply Forall_nil]. }
  Intros outp ob. try subst cap.
  (* the rest: WMainNull.w_null_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  apply semax_seq with FF; [ | apply semax_ff].
  eapply semax_pre; [ | apply (w_null_ok CB CF UF gv v_compressed_len v_decompressed_len v_source_consumed_len (Zlength bs) bs
                                 (Zlength ob) v sn datap compp outp expp ob)].
  unfold w_null_pre. subst cb. entailer!.
Qed.

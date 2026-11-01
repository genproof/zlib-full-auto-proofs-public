(* Law rt_dictionary, main (DWKit.v): after the first inflate(): gp_assert(code == Z_NEED_DICT), inflateSetDictionary with the dictionary's copy and its two tests (A26 -> RI at position 6 with nothing written, DWIFacts.di_set; the copies DWKit.F_drt kept). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Zlib.harness.rt_dictionary.code.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma trt_set_ok : trt_set_stmt.
Proof.
  intros Espec Q P gv vc vd wbits n b D O dict dp op ddp cp z L dcp ep IF.
  unfold A26, F_drt. rewrite PROP_combine. simpl app.
  unfold trt_set, Delta_drt, POST_drt, POST_of. simplify_func_tycontext.
  abbreviate_semax.
  Intros.
  match goal with H : dw_hf _ _ _ _ _ _ _ _ _ _ |- _ => pose proof H as HF; destruct H as (DF & CF & HO & Hb & BD & BO & Pcp) end.
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdl & IDict & Pddp & Hw).
  (* gp_assert(inflate(...) == Z_NEED_DICT) *)
  forward_call (Int.repr 1).
  (* code = inflateSetDictionary(&decompressor, dict_copy, (uInt) dict_len): the whole object of the copy *)
  assert_PROP (isptr vd) as Pvd by entailer!.
  assert_PROP (live_ok L) as LV by (unfold istreamA; entailer!).
  rewrite <- (RTLoop.rtl_bytes_i Ews (Zlength dict) (bytes_rep dict) dcp),
          <- (RTLoop.rtl_tok_i Ews (Zlength dict) dcp).
  rewrite <- (RTLoop.rtl_istreamA_opt_ptr gv Tsh vd z Vundef (Some L)) by auto.
  unfold dict_max in Hdl.
  forward_call (gv, Tsh, vd, z, Vundef, Some L, Ews, dcp, 0, Zlength dict, bytes_rep dict, dict, true).
  { entailer!. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    destruct dcp; try contradiction. simpl. rewrite ?Ptrofs.add_zero. reflexivity. }
  { unfold bytes_rep. rewrite Zlength_map. rewrite sublist_same by (rewrite ?Zlength_map; lia).
    repeat split; try rep_lia. }
  Intros vret. destruct vret as [aok winp]. simpl fst in *; simpl snd in *.
  unfold on_live. rewrite RTLoop.rtl_is_live_ptr by auto.
  destruct (di_set Q P IF wbits dict D O z L aok winp H0 LV) as [Hr Hok].
  destruct (setdict_f dict aok winp z L) as [[r z2] L2] eqn:Esd.
  unfold fst3, snd3, thd3 in Hr, Hok |- *. cbn [fst snd] in Hr, Hok |- *.
  rewrite RTLoop.rtl_istreamA_opt_ptr by auto.
  (* if (code == Z_MEM_ERROR) return 0 *)
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply RTLoop.rtl_a_frame. entailer!. }
  assert (R1: r = Z_OK) by (destruct Hr as [-> | ->]; [reflexivity | exfalso; apply H7; reflexivity]).
  destruct (Hok R1) as (-> & SW & HP).
  subst r.
  (* gp_assert(code == Z_OK) *)
  forward_call (Int.repr 1).
  (* the loop's invariant at position 6, nothing written; the copies kept *)
  destruct (di_ok Q P IF _ _ _ _ _ _ _ _ HP) as (_ & _ & H6O & _).
  unfold RI, F_drt. rewrite !exp_sepcon1. Exists 6 (@nil Z) z L2.
  rewrite PROP_combine. simpl app.
  rewrite ?RTLoop.rtl_bytes_i, ?RTLoop.rtl_tok_i.
  replace (data_at_ Ews (tarray tuchar n) op)
    with (data_at Ews (tarray tuchar n) (bytes_rep [] ++ Zrepeat Vundef (n - Zlength (@nil Z))) op)
    by (unfold data_at_; simpl; rewrite Z.sub_0_r; reflexivity).
  entailer!.
Qed.

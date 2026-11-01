(* Law api_split_invariant, main: statements 30-32, the checks: by SIFacts.sf_max the one call and the split stop
   at the same output and code, so gp_assert(code_split == code_one) when final(code_one), else
   gp_assert(!final(code_split)), and gp_assert(split.total_out == one.total_out && bytes_eq(out_one, out_split,
   one.total_out)); `return 0` (sm_brk -> return). *)
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
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

(* both streams stop the same way (SIFacts.sf_max): when the one call returned a final code, the split returned the
   same code; otherwise the split's code is not final either *)
Lemma sm_stop_same code r1: sm_stop code = sm_stop r1 ->
  (final_code r1 = true -> code = r1) /\ (final_code r1 = false -> final_code code = false).
Proof.
  unfold sm_stop. destruct (final_code code), (final_code r1); split; intros; congruence.
Qed.

(* the bytes of an output object as bytes_eq takes them: an output object's first |ow| elements are the stored
   unsigned chars of ow, the integers Int.unsigned (Int.repr b) (in 0..255 because data_at's values fit tuchar) *)
Definition sm_stored (ow: list Z) : list Z := map (fun b => Int.unsigned (Int.repr b)) ow.

Lemma sm_stored_ok ow room: Zlength ow <= room -> Forall (value_fits tuchar) (sm_out ow room) ->
  is_bytes (sm_stored ow) /\ Zlength (sm_stored ow) = Zlength ow /\
  sublist 0 (Zlength ow) (sm_out ow room) = bytes_rep (sm_stored ow).
Proof.
  intros Hr Hf. unfold sm_out in Hf. apply Forall_app in Hf. destruct Hf as [Hf _].
  unfold bytes_rep in Hf. rewrite Forall_map in Hf.
  assert (Eb: bytes_rep (sm_stored ow) = bytes_rep ow).
  { unfold bytes_rep, sm_stored. rewrite map_map. apply map_ext. intros b. rewrite Int.repr_unsigned. reflexivity. }
  split; [ | split].
  - unfold is_bytes, sm_stored. rewrite Forall_map. eapply Forall_impl; [ | exact Hf].
    intros b Hb. simpl in Hb. unfold tc_val' in Hb. specialize (Hb ltac:(discriminate)). simpl in Hb.
    pose proof (Int.unsigned_range (Int.repr b)). unfold Basics.compose. lia.
  - unfold sm_stored. apply Zlength_map.
  - pose proof (Zlength_nonneg ow).
    assert (Lb: Zlength (bytes_rep ow) = Zlength ow) by (unfold bytes_rep; apply Zlength_map).
    rewrite Eb. unfold sm_out. rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

Lemma seg_tail_ok {Espec: OracleKind} Inv Max gv vwb vone vsplit w src room flush inp ins o1 o2 r1 z1 L1 ow1:
  si_facts Inv Max -> sm_A_facts w src room flush inp ins o1 o2 -> sm_B_facts Max w src room r1 z1 ow1 ->
  semax Delta_m
    (sm_brk Max gv vwb vone vsplit w src room ins o1 o2 r1 (sm_fr gv vwb vone inp src o1 room z1 L1 ow1))
    sm_seg30 POST_B.
Proof.
  intros SF FA FB.
  unfold sm_brk, sm_seg30, Delta_m, Gmain_k, POST_B, POST_m. simplify_func_tycontext. abbreviate_semax.
  Intros O code z L.
  destruct FB as (Mx1 & R1 & T1 & L1r).
  destruct (sf_max _ _ SF _ _ _ _ _ _ _ H Mx1) as [-> Est].
  destruct (sm_stop_same _ _ Est) as [Ct Cf]. clear Est H.
  forward_call r1.
  ifsame.
  { destruct (final_code r1) eqn:F1; [ | sm_infeas].
    pose proof (Ct eq_refl); subst code. forward_call (Int.repr 1).
    { entailer!. rewrite Int.eq_true. reflexivity. }
    entailer!. }
  { destruct (final_code r1) eqn:F1; [sm_infeas | ].
    forward_call code. rewrite (Cf eq_refl).
    forward_call (Int.repr 1).
    entailer!. }
  unfold sm_fr, sm_one. rewrite !sm_istreamA_unfold. Intros. unfold sm_tup.
  forward. forward.
  rewrite H1, T1.
  destruct FA as (Fw & Fs & Fsl & Froom & Ffl & Fb & Ft & Pi & Pc & P1 & P2).
  assert_PROP (Forall (value_fits tuchar) (sm_out ow1 room)) as VF by entailer!.
  destruct (sm_stored_ok _ _ L1r VF) as (Bs & Ls & Ss).
  ifpost _t'27 Int.one.
  { forward.
    rewrite <- !(sm_bytes_a Ews room).
    forward_call (o1, Ews, o1, 0, room, sm_out ow1 room, sm_stored ow1,
                  o2, Ews, o2, 0, room, sm_out ow1 room, sm_stored ow1, Zlength ow1).
    { unfold cbuf_ok. rewrite !isptr_offset_val_zero by auto. rewrite Z.add_0_l.
      split; repeat split; auto; try lia; apply readable_Ews. }
    destruct (list_eq_dec Z.eq_dec (sm_stored ow1) (sm_stored ow1)) as [_ | NE]; [ | contradiction].
    forward. rewrite !sm_bytes_a. entailer!. }
  { sm_infeas. }
  forward_call Int.one.
  (* return 0: the two streams given back to the stack frame (entailer! on this postcondition is very slow) *)
  forward. Exists (Int.repr 0).
  apply andp_right; [apply prop_right; reflexivity | ].
  match goal with |- context [data_at Tsh t_zsl ?v vsplit] => sep_apply (data_at_data_at_ Tsh t_zsl v vsplit) end.
  match goal with |- context [data_at Tsh t_zsl ?v vone] => sep_apply (data_at_data_at_ Tsh t_zsl v vone) end.
  change (Tstruct _z_stream_s noattr) with t_zsl. cancel.
Qed.

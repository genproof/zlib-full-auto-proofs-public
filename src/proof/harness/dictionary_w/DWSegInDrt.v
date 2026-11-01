(* Law rt_dictionary, main (DWKit.v): statements 0-12, the draws of dict_len, data_len, dict and data, their NULL
   test, the copies dict_copy and expected (copy_of), out and the four ints, and the NULL test of the copies and
   out (PRE0 -> A10 * F_drt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Require Import Zlib.proof.harness.dictionary_w.DWSegIn1.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma seg_in_drt_ok : seg_in_drt_stmt.
Proof.
  intros Espec gv vc vd. unfold PRE0, seg_in_drt, POST_drt, POST_of. abbreviate_semax.
  forward_call 4294967294. Intros t1.
  forward.
  change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr.
  forward_call 9223372036854775807. Intros n.
  forward_call (1 + t1, gv). Intros vret. destruct vret as [ddp dict]. simpl fst in *; simpl snd in *.
  forward_call (n, gv). Intros vret. destruct vret as [dp D]. simpl fst in *; simpl snd in *.
  rt_law.
  replace (1 + t1) with (Zlength dict) by lia. subst n.
  fold (dwi_obj ddp dict). fold (dwi_obj dp D).
  (* if (dict == NULL || data == NULL) return 0; *)
  destruct (eq_dec ddp nullval) as [Pdi | Pdi].
  { subst ddp.
    ifpost DRT._t'5 Int.one; [forward; entailer! | dw_nob | ].
    forward_if; [ret0 | dw_nob]. }
  dwi_mkptr ddp bdi odi.
  destruct (eq_dec dp nullval) as [Pd | Pd].
  { subst dp.
    ifpost DRT._t'5 Int.one; [dwi_tceq | dw_nob | forward; entailer! | ].
    forward_if; [ret0 | dw_nob]. }
  dwi_mkptr dp bd od.
  ifpost DRT._t'5 Int.zero; [dwi_tceq | dw_nob | forward; [dwi_tceq | entailer!] | ].
  forward_if; [dw_nob | ].
  (* dict_copy = copy_of(dict, dict_len); expected = copy_of(data, data_len); *)
  unfold dwi_obj at 2. Intros.
  forward_call (Vptr bdi odi, Ews, Vptr bdi odi, 0, Zlength dict, bytes_rep dict, Zlength dict, dict, gv).
  { rewrite rt_bytes_adler. cancel. }
  { apply cbuf_ok_whole; [auto with share | auto | exact I]. }
  Intros dcp. rt_law. fold (dwi_obj dcp dict). fold (dwi_obj (Vptr bdi odi) dict).
  unfold dwi_obj at 2. Intros.
  forward_call (Vptr bd od, Ews, Vptr bd od, 0, Zlength D, bytes_rep D, Zlength D, D, gv).
  { rewrite rt_bytes_adler. cancel. }
  { apply cbuf_ok_whole; [auto with share | auto | exact I]. }
  Intros ep. rt_law. fold (dwi_obj ep D). fold (dwi_obj (Vptr bd od) D).
  (* out = malloc(data_len); the four ints *)
  forward_call (tarray tuchar (Zlength D), gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  forward_call tt. Intros u1.
  forward_call 7. Intros w.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.signed_repr by rep_lia. rep_lia. }
  rewrite Int64.unsigned_repr by rep_lia. rewrite add_repr.
  forward_call tt. Intros u2.
  forward_call tt. Intros u3.
  fold (dwi_out (Zlength D) op).
  (* if (dict_copy == NULL || expected == NULL || out == NULL) return 0; *)
  destruct (eq_dec dcp nullval) as [Pc | Pc].
  { subst dcp.
    ifpost DRT._t'13 Int.one; [forward; entailer! | dw_nob | ].
    ifpost DRT._t'14 Int.one; [forward; entailer! | dw_nob | ].
    forward_if; [ret0 | dw_nob]. }
  dwi_mkptr dcp bc oc.
  destruct (eq_dec ep nullval) as [Pe | Pe].
  { subst ep.
    ifpost DRT._t'13 Int.one; [dwi_tceq | dw_nob | forward; entailer! | ].
    ifpost DRT._t'14 Int.one; [forward; entailer! | dw_nob | ].
    forward_if; [ret0 | dw_nob]. }
  dwi_mkptr ep be oe.
  destruct (eq_dec op nullval) as [Po | Po].
  { subst op.
    ifpost DRT._t'13 Int.zero; [dwi_tceq | dw_nob | forward; [dwi_tceq | entailer!] | ].
    ifpost DRT._t'14 Int.one; [dw_nob | forward; entailer! | ].
    forward_if; [ret0 | dw_nob]. }
  dwi_mkptr op bop oop.
  ifpost DRT._t'13 Int.zero; [dwi_tceq | dw_nob | forward; [dwi_tceq | entailer!] | ].
  ifpost DRT._t'14 Int.zero; [dw_nob | forward; [dwi_tceq | entailer!] | ].
  forward_if; [dw_nob | ].
  forward.
  Exists (Zlength D) D (Vptr bd od) (Vptr bop oop) dict (Vptr bdi odi) (Int.signed (Int.repr u1)) (8 + w)
    (Int.signed (Int.repr u2)) (Int.signed (Int.repr u3)) (Vptr bc oc) (Vptr be oe).
  unfold A10, F_drt. rewrite PROP_combine. simpl app.
  unfold dw_cf, dwi_obj, dwi_out. rewrite !Int.repr_signed.
  pose proof (Int.signed_range (Int.repr u1)). pose proof (Int.signed_range (Int.repr u2)).
  pose proof (Int.signed_range (Int.repr u3)).
  entailer!.
  unfold dict_max. lia.
Qed.

(* Laws rt_dictionary and api_dict_id, main (DWKit.v): the objects of the draws and copies and their NULL tests
   (statements 4 and 12 of main; DWSegIn.v proves the draws, the copies and the tests with them). *)
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
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* the dictionary / data object (malloc'ed, holding the bytes l) and the output object (n bytes, undefined),
   kept folded through the NULL test so that the tactics do not unfold their array contents *)
Definition dwi_obj (p : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) p * data_at Ews (tarray tuchar (Zlength l)) (bytes_rep l) p.
Definition dwi_out (n : Z) (q : val) : mpred :=
  malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q.

Lemma dwi_obj_isptr p l : dwi_obj p l |-- !! isptr p.
Proof.
  unfold dwi_obj. entailer!.
Qed.

Lemma dwi_out_isptr n q : dwi_out n q |-- !! isptr q.
Proof.
  unfold dwi_out. entailer!.
Qed.

(* such an object (of any size, also 0) can be compared with NULL *)
Lemma dwi_obj_test_eq P q l : P |-- dwi_obj q l * TT -> P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q (Zlength_nonneg l)).
  eapply derives_trans; [exact HP | ]. unfold dwi_obj. sep_apply data_at_data_at_. cancel.
Qed.

Lemma dwi_out_test_eq P n q : 0 <= n -> P |-- dwi_out n q * TT -> P |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros Hn HP. apply (malloc_test_eq P n q Hn).
  eapply derives_trans; [exact HP | ]. unfold dwi_out. cancel.
Qed.

(* the typing goal of `q == NULL` (or of an expression containing it) for an object q *)
Ltac dwi_tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with
  | context [dwi_obj q ?l] => apply (dwi_obj_test_eq _ q l); cancel
  | context [dwi_out ?n q] => apply (dwi_out_test_eq _ n q); [lia | cancel]
  end end.
Ltac dwi_tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => dwi_tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; dwi_tceq_obj
  end.

(* an object's pointer is a concrete pointer *)
Ltac dwi_mkptr P b o :=
  let Ip := fresh in
  assert_PROP (isptr P) as Ip by
    (match goal with
     | |- context [dwi_obj P ?l] => sep_apply (dwi_obj_isptr P l)
     | |- context [dwi_out ?n P] => sep_apply (dwi_out_isptr n P)
     end; entailer!);
  destruct P as [ | | | | | b o]; try contradiction; clear Ip.

(* a branch excluded by the value of its test *)
Ltac dw_nob := first [ rt_bad | discriminate | exfalso; exact (Int.one_not_zero ltac:(assumption)) ].

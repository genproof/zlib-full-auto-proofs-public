(* Laws res_free_deflate and res_memory_deflate: the specifications of the functions of deflate.c that the
   allocator reaches (deflateInit2_, deflate, deflateEnd and their callees that touch the stream's allocator
   fields or tokens), for every counting allocator [counted cp za zf] (src/proof/harness/counted/Spec.v): the
   allocator-generic specifications of src/proof/za/deflate/ with the allocator chosen at each call (ZAny.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.ZAny.
#[local] Existing Instance DCS.CS.

(* the counting allocators: struct count at cp, count_alloc at za, count_free at zf *)
Definition KC : Type := (val * val * val)%type.
Definition kc (c : KC) : zallocator := counted (fst (fst c)) (snd (fst c)) (snd c).

Definition za_deflateInit2__spec_c : ident * funspec := ltac:(za_any KC kc (@za_deflateInit2__spec)).
Definition za_deflateEnd_spec_c : ident * funspec := ltac:(za_any KC kc (@za_deflateEnd_spec)).
Definition deflate_spec_c : ident * funspec := ltac:(za_any KC kc (@deflate_spec_za)).
Definition deflateStateCheck_spec_c : ident * funspec := ltac:(za_any KC kc (@deflateStateCheck_spec_za)).
Definition deflateResetKeep_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflateResetKeep_spec_v9_za) (@api_simple_spec_v9_za)).
Definition deflateReset_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflateReset_spec_v9_za) (@api_simple_spec_v9_za)).
Definition read_buf_spec_c : ident * funspec := ltac:(za_any KC kc (@read_buf_spec_za)).
Definition flush_pending_spec_c : ident * funspec := ltac:(za_any KC kc (@flush_pending_spec_za)).
Definition fill_window_spec_c : ident * funspec := ltac:(za_any KC kc (@fill_window_spec_za)).
Definition deflate_stored_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflate_stored_spec_za) (@compress_spec_za)).
Definition deflate_fast_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflate_fast_spec_za) (@compress_spec_za)).
Definition deflate_slow_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflate_slow_spec_za) (@compress_spec_za)).
Definition deflate_rle_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflate_rle_spec_za) (@compress_spec_za)).
Definition deflate_huff_spec_c : ident * funspec := ltac:(za_any_with KC kc (@deflate_huff_spec_za) (@compress_spec_za)).

(* each is a subspecification of the member of its family at [kc c] *)
Ltac sub_c X := intros c; unfold X; exact (za_sigma_sub KC kc _ _ _ _ _ c).

Lemma za_deflateInit2__sub c : funspec_sub (snd za_deflateInit2__spec_c) (snd (@za_deflateInit2__spec (kc c))).
Proof. revert c; sub_c za_deflateInit2__spec_c. Qed.
Lemma za_deflateEnd_sub c : funspec_sub (snd za_deflateEnd_spec_c) (snd (@za_deflateEnd_spec (kc c))).
Proof. revert c; sub_c za_deflateEnd_spec_c. Qed.
Lemma deflate_sub c : funspec_sub (snd deflate_spec_c) (snd (@deflate_spec_za (kc c))).
Proof. revert c; sub_c deflate_spec_c. Qed.
Lemma deflateStateCheck_sub c : funspec_sub (snd deflateStateCheck_spec_c) (snd (@deflateStateCheck_spec_za (kc c))).
Proof. revert c; sub_c deflateStateCheck_spec_c. Qed.
Lemma deflateResetKeep_sub c : funspec_sub (snd deflateResetKeep_spec_c) (snd (@deflateResetKeep_spec_v9_za (kc c))).
Proof. revert c; sub_c deflateResetKeep_spec_c. Qed.
Lemma deflateReset_sub c : funspec_sub (snd deflateReset_spec_c) (snd (@deflateReset_spec_v9_za (kc c))).
Proof. revert c; sub_c deflateReset_spec_c. Qed.
Lemma read_buf_sub c : funspec_sub (snd read_buf_spec_c) (snd (@read_buf_spec_za (kc c))).
Proof. revert c; sub_c read_buf_spec_c. Qed.
Lemma flush_pending_sub c : funspec_sub (snd flush_pending_spec_c) (snd (@flush_pending_spec_za (kc c))).
Proof. revert c; sub_c flush_pending_spec_c. Qed.
Lemma fill_window_sub c : funspec_sub (snd fill_window_spec_c) (snd (@fill_window_spec_za (kc c))).
Proof. revert c; sub_c fill_window_spec_c. Qed.
Lemma deflate_stored_sub c : funspec_sub (snd deflate_stored_spec_c) (snd (@deflate_stored_spec_za (kc c))).
Proof. revert c; sub_c deflate_stored_spec_c. Qed.
Lemma deflate_fast_sub c : funspec_sub (snd deflate_fast_spec_c) (snd (@deflate_fast_spec_za (kc c))).
Proof. revert c; sub_c deflate_fast_spec_c. Qed.
Lemma deflate_slow_sub c : funspec_sub (snd deflate_slow_spec_c) (snd (@deflate_slow_spec_za (kc c))).
Proof. revert c; sub_c deflate_slow_spec_c. Qed.
Lemma deflate_rle_sub c : funspec_sub (snd deflate_rle_spec_c) (snd (@deflate_rle_spec_za (kc c))).
Proof. revert c; sub_c deflate_rle_spec_c. Qed.
Lemma deflate_huff_sub c : funspec_sub (snd deflate_huff_spec_c) (snd (@deflate_huff_spec_za (kc c))).
Proof. revert c; sub_c deflate_huff_spec_c. Qed.

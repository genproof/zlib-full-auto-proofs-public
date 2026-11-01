(* Law rt_gzip_header on the round-2 harness: the pieces of the assembly (G2Asm.v), as in round 1's Asm.v for the
   bounded harness (superseded by this file and G2Asm.v).

   - [rtg2_trees_bodies]: the bodies of trees.c;
   - [GNc] / [gn_shape]: the specifications that DSpecN.deflate_bodyN_stmt gives to the eight functions of
     deflate.c that carry next_in;
   - [G]: the law's specification of every function main reaches, one per function;
   - [entry_cc]: QuickProof.Assembly's entry for a body whose specification is abstract (its calling convention
     is a hypothesis);
   - [entry_fast]: RTRSLaw.entry_shared' with a faster check of the context ([ctx_sub_fast]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.adler32.MainLib.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.DSpecN.
Require Zlib.proof.trees.Body_bits.
Require Zlib.proof.trees.Body_build.
Require Zlib.proof.trees.Body_scan.
Require Zlib.proof.trees.Body_send.
Require Zlib.proof.trees.Body_flush.
Require Zlib.proof.inflate.Callees.
Require Zlib.proof.inflate.Callees3.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.roundtrip.RTH8Spec Zlib.proof.roundtrip.RTH9Spec.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module D := Zlib.deflate.code.

(* The bodies of trees.c, proved in src/proof/trees/. *)
Lemma rtg2_trees_bodies : trees_bodies_ok.
Proof.
  unfold trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

(* deflate_bodyN_stmt's specifications of the eight functions of deflate.c that carry next_in and the input
   object (DSpecN.in_funs), in their order *)
Definition GNc (g1 g2 g3 g4 g5 g6 g7 g8 : funspec) : funspecs :=
  [(D._read_buf, g1); (D._flush_pending, g2); (D._fill_window, g3); (D._deflate_stored, g4); (D._deflate_fast, g5);
   (D._deflate_slow, g6); (D._deflate_rle, g7); (D._deflate_huff, g8)].

Lemma gn_shape (GN : funspecs) :
  map fst GN = Zlib.proof.deflate.DSpecN.in_funs ->
  exists g1 g2 g3 g4 g5 g6 g7 g8, GN = GNc g1 g2 g3 g4 g5 g6 g7 g8.
Proof.
  intros H.
  destruct GN as [|[i1 g1] [|[i2 g2] [|[i3 g3] [|[i4 g4] [|[i5 g5] [|[i6 g6] [|[i7 g7] [|[i8 g8] GN]]]]]]]];
    simpl in H; inversion H; subst.
  destruct GN; [ | discriminate ].
  exists g1, g2, g3, g4, g5, g6, g7, g8. reflexivity.
Qed.

(* One specification per function of the program: main's, then THE specification of every function main
   reaches.  trees.c: DSpec; deflate.c: DSpecN's [GN] (from deflate_bodyN_stmt) for the eight functions that
   carry next_in, DSpecN.deflate_specN for deflate (main offers no input object), DSpec / DSpec9 for the rest;
   inflate.c: Spec5, with inflate's v9 specification (RTH9Spec) and inflateGetHeader's v8 one (RTH8Spec), the
   ones main uses; inffast.c: the specification [fast] proved of inflate_fast's body
   (RTH9Spec.inflate_body9_stmt), the one inflate's body is proved with; inftrees.c, adler32.c, crc32.c;
   zutil.c's allocator and libc's memcpy / memset at the law's compspecs; the harness's own helpers and
   laws_common.h's; the environment. *)
Definition G (fast g1 g2 g3 g4 g5 g6 g7 g8 : funspec) : funspecs :=
  [(_main, QPmain_spec_ext' p tt main_post_TT);
   (* trees.c *)
   bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec;
   (* deflate.c *)
   (D._read_buf, g1); putShortMSB_spec; (D._flush_pending, g2); slide_hash_spec; longest_match_spec; lm_init_spec;
   (D._fill_window, g3); (D._deflate_stored, g4); (D._deflate_fast, g5); (D._deflate_slow, g6); (D._deflate_rle, g7);
   (D._deflate_huff, g8); deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9;
   deflateSetHeader_spec; deflateBound_z_spec; deflateBound_spec; deflateEnd_spec; deflateInit2__spec_v9;
   Zlib.proof.deflate.DSpecN.deflate_specN;
   (* inflate.c, inffast.c, inftrees.c *)
   S5.inflateInit2__spec; Zlib.proof.roundtrip.RTH9Spec.inflate_spec9;
   Zlib.proof.roundtrip.RTH8Spec.inflateGetHeader_spec8;
   S5.inflateReset_spec; S5.inflateReset2_spec; S5.inflateResetKeep_spec;
   Zlib.proof.inflate.Callees.inflateStateCheck_spec; Zlib.proof.inflate.Callees3.updatewindow_spec3;
   (Zlib.inffast.code._inflate_fast, fast); Zlib.proof.inflate.Callees.inflate_fixed_spec;
   Zlib.proof.inftrees.spec.inflate_table_spec;
   (* adler32.c, crc32.c, zutil.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS;
   (* the harness *)
   any_string_spec; same_field_spec; upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec;
   offer_spec; new_stream_spec;
   (* the environment *)
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_size_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Ltac entry_shared' B := Zlib.proof.roundtrip.RTRSLaw.entry_shared' B.

(* entry_shared' for a body whose specification is abstract: its calling convention is the hypothesis CC *)
Ltac entry_cc B CC :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity
      | unfold internal_static_ok; simpl callingconvention_of_funspec; rewrite CC; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | Zlib.proof.roundtrip.RTRSLaw.ctx_sub_tac' ]
    | ]
  end.

(* RTRSLaw.ctx_sub_tac' tries funspec_sub_refl first, which takes about 20 s to fail on zcalloc / zcfree at a
   unit's compspecs (deflateInit2_'s, deflateEnd's, inflateInit2_'s contexts); [ctx_sub_fast] sends those two
   straight to their transport lemmas, recognised by the identifier before [inv] substitutes it away. *)
Ltac ctx_sub_fast :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E;
    [ lazymatch goal with
      | H : i = Zlib.zutil.code._zcalloc |- _ =>
        inv E; eexists; split;
        [ reflexivity
        | apply Zlib.proof.zutil.Spec.zcalloc_spec_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity) ]
      | H : i = Zlib.zutil.code._zcfree |- _ =>
        inv E; eexists; split;
        [ reflexivity
        | apply Zlib.proof.zutil.Spec.zcfree_spec_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity) ]
      | _ => inv E; eexists; split; [ reflexivity | Zlib.proof.roundtrip.RTRSLaw.env_spec_sub' ]
      end
    | ]);
  try discriminate.

(* entry_shared' with [ctx_sub_fast] *)
Ltac entry_fast B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | ctx_sub_fast ]
    | ]
  end.

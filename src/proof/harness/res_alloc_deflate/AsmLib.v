(* Laws res_free_deflate and res_memory_deflate: the assembly of a law from main's body and the shared bodies,
   apart from main and the program's globals: the specifications [G_lib_free] / [G_lib_mem] of every function
   main reaches, QuickProof.Assembly.entry_shared for every body (laws_common.h's helpers, the counting
   allocator, deflate.c's allocator-generic functions through AsmKit.entry_za, the functions of deflate.c the
   allocator does not reach (putShortMSB, slide_hash, longest_match, lm_init), trees.c, adler32.c, crc32.c,
   libc's memcpy / memset) and entry_external for the environment.  A law: G := main's entry :: G_lib_free
   (G_lib_mem), then [harness_safe_by_specs CSa G main_post_TT] and [asm_entries_free M HL HC HB HA]
   ([asm_entries_mem]; M: main's entry body). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.veric.Clight_initial_world.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.Obligations Zlib.proof.deflate.MainCoreCfg Zlib.proof.deflate.GlobalsFixed.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.ZAny Zlib.proof.harness.res_alloc_deflate.ACS
               Zlib.proof.harness.res_alloc_deflate.Specs Zlib.proof.harness.res_alloc_deflate.Gmain
               Zlib.proof.harness.res_alloc_deflate.AsmKit.
Require Zlib.proof.compress.CSpec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.adler32.Spec Zlib.proof.adler32.Body_adler32 Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Spec Zlib.proof.crc32.Body_crc32 Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.trees.Body_bits Zlib.proof.trees.Body_build Zlib.proof.trees.Body_scan
        Zlib.proof.trees.Body_send Zlib.proof.trees.Body_flush.
Require Zlib.proof.deflate.Body_leaf Zlib.proof.deflate.Body_window.

(* The specifications of a law, but main's: every function main reaches, after the harness's own [H]. *)
Definition G_lib_with (H : funspecs) : funspecs :=
  H ++
  [(* the harness *)
   any_bytes_spec; offer_spec; counted_stream_spec; count_alloc_spec; count_free_spec;
   (* deflate.c, for every counting allocator *)
   za_deflateInit2__spec_c; deflate_spec_c; za_deflateEnd_spec_c; deflateStateCheck_spec_c;
   deflateResetKeep_spec_c; deflateReset_spec_c; read_buf_spec_c; flush_pending_spec_c; fill_window_spec_c;
   deflate_stored_spec_c; deflate_fast_spec_c; deflate_slow_spec_c; deflate_rle_spec_c; deflate_huff_spec_c;
   (* deflate.c, not reached by the allocator *)
   putShortMSB_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   (* trees.c *)
   tr_init_spec; tr_static_init_spec; init_block_spec; tr_flush_bits_spec; bi_flush_spec; tr_align_spec;
   tr_stored_block_spec; bi_windup_spec; tr_flush_block_spec; detect_data_type_spec; build_tree_spec;
   pqdownheap_spec; gen_bitlen_spec; gen_codes_spec; bi_reverse_spec; build_bl_tree_spec; scan_tree_spec;
   compress_block_spec; send_all_trees_spec; send_tree_spec;
   (* adler32.c, crc32.c, libc.c *)
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Libc.memcpy_spec DCS.CS; @Zlib.proof.zutil.Libc.memset_spec DCS.CS;
   (* the environment *)
   (_quickproof_malloc, @malloc_spec' CSa); (_quickproof_free, @free_spec' CSa);
   nondet_u32_spec; @nondet_bytes_spec CSa; gp_assert_spec].

(* res_free_deflate's program has no other helper of laws_common.h; res_memory_deflate's has upto (with its
   nondet_size) and clip, and main calls nondet_u8, laws_session.h's deflate_params_ok and gp_assume *)
Definition G_lib_free : funspecs := Eval cbv [G_lib_with app] in G_lib_with [].
Definition G_lib_mem : funspecs := Eval cbv [G_lib_with app] in
  G_lib_with [upto_spec; clip_spec; nondet_u8_spec; nondet_size_spec;
              Zlib.proof.harness.laws_session.Spec.deflate_params_ok_spec; gp_assume_spec].

(* The variables of a body's context are the program's, by ONE computation. *)
Lemma find_ids_b (V W : varspecs) :
  forallb (fun x => match initial_world.find_id (fst x) W with Some t => eqb_type t (snd x) | None => false end) V = true ->
  Forall (fun x => initial_world.find_id (fst x) W = Some (snd x)) V.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x IN. specialize (H x IN).
  destruct (initial_world.find_id (fst x) W) as [t|]; [ | discriminate]. apply eqb_type_spec in H. subst; reflexivity.
Qed.

(* the context entries: the same specification, an instance of an allocator-generic one, or an environment
   specification at other compspecs *)
Ltac spec_sub :=
  first [ apply funspec_sub_refl
        | exact (za_deflateInit2__sub _) | exact (za_deflateEnd_sub _) | exact (deflate_sub _)
        | exact (deflateStateCheck_sub _) | exact (deflateResetKeep_sub _) | exact (deflateReset_sub _)
        | exact (read_buf_sub _) | exact (flush_pending_sub _) | exact (fill_window_sub _)
        | exact (deflate_stored_sub _) | exact (deflate_fast_sub _) | exact (deflate_slow_sub _)
        | exact (deflate_rle_sub _) | exact (deflate_huff_sub _)
        | apply nondet_bytes_spec_cs
        | apply malloc_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity)
        | apply free_spec'_sub;
          try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
          try (apply preserved_by_computation; vm_compute; reflexivity) ].

Ltac ctx_sub_za :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E; [ inv E; eexists; split; [ reflexivity | spec_sub ] | ]);
  try discriminate.

Ltac entry_shared_a B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply find_ids_b; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | ctx_sub_za ]
    | ]
  end.

(* an allocator-generic entry X_c from the family's bodies [B ZA] in the contexts [G1 ZA] *)
Ltac entry_za_a X G1 B :=
  apply Forall_cons;
  [ unfold X;
    eapply (entry_za _ _ DCS.CS _ _ DSpec.Vprog G1 _ _ KC kc _ _ _ _ _ (nullval, nullval, nullval));
    [ intros j; exact (B (kc j))
    | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply find_ids_b; vm_compute; reflexivity | intros j; vm_compute; reflexivity | vm_compute; reflexivity
    | intros j; ctx_sub_za ]
  | ].

Lemma trees_bodies : trees_bodies_ok.
Proof.
  unfold trees_bodies_ok.
  destruct Zlib.proof.trees.Body_bits.trees_bits as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_build.trees_build as (? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_scan.trees_scan as (? & ? & ? & ? & ? & ?).
  destruct Zlib.proof.trees.Body_send.trees_send as (? & ? & ? & ? & ?).
  pose proof Zlib.proof.trees.Body_flush.trees_flush.
  repeat (split; [assumption | ]); assumption.
Qed.

(* After harness_safe_by_specs: main's entry from [M], the harness's own entries (res_memory_deflate: upto, clip,
   nondet_u8, nondet_size, deflate_params_ok from laws_session_ok [HS], gp_assume), then every entry of G_lib_with from the hypotheses laws_common_ok [HL], counted_ok [HC],
   za_deflate_bodies_stmt [HB], za_deflate_api_stmt [HA]. *)
Ltac asm_entries_lib HL HC HB HA :=
  destruct HL as (_ & _ & L_any_bytes & _ & _ & L_offer & _);
  destruct HC as (C_alloc & C_free & C_stream);
  destruct trees_bodies as (T_bi_reverse & T_bi_flush & T_bi_windup & T_tr_flush_bits & T_tr_align & T_tr_stored_block & T_gen_codes & T_pqdownheap & T_gen_bitlen & T_build_tree & T_scan_tree & T_build_bl_tree & T_detect_data_type & T_init_block & T_send_tree & T_send_all_trees & T_compress_block & T_tr_static_init & T_tr_init & T_tr_flush_block);
  destruct Zlib.proof.deflate.Body_leaf.deflate_leaf as (_ & D_putShortMSB & _ & D_slide_hash & D_lm_init & _);
  destruct Zlib.proof.deflate.Body_window.deflate_window as (_ & D_longest_match);
  unfold ob_bi_reverse, ob_bi_flush, ob_bi_windup, ob_tr_flush_bits, ob_tr_align, ob_tr_stored_block, ob_gen_codes, ob_pqdownheap, ob_gen_bitlen, ob_build_tree, ob_scan_tree, ob_build_bl_tree, ob_detect_data_type, ob_init_block, ob_send_tree, ob_send_all_trees, ob_compress_block, ob_tr_static_init, ob_tr_init, ob_tr_flush_block, ob_putShortMSB, ob_slide_hash, ob_longest_match, ob_lm_init in *;
  entry_shared_a L_any_bytes;
  entry_shared_a L_offer;
  entry_shared_a C_stream;
  entry_shared_a C_alloc;
  entry_shared_a C_free;
  entry_za_a za_deflateInit2__spec_c (@Gprog_za_deflateInit2_) (fun ZA => proj1 (HA ZA));
  entry_za_a deflate_spec_c (@Gprog_deflate_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA)))))))))))));
  entry_za_a za_deflateEnd_spec_c (@Gprog_za_deflateEnd) (fun ZA => proj2 (HA ZA));
  entry_za_a deflateStateCheck_spec_c (fun _ : zallocator => Gprog_deflateStateCheck) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA))))))))));
  entry_za_a deflateResetKeep_spec_c (@Gprog_deflateResetKeep_v9_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA)))))))))));
  entry_za_a deflateReset_spec_c (@Gprog_deflateReset_v9_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA))))))))))));
  entry_za_a read_buf_spec_c (fun _ : zallocator => Gprog_read_buf) (fun ZA => proj1 (HB ZA));
  entry_za_a flush_pending_spec_c (fun _ : zallocator => Gprog_flush_pending) (fun ZA => proj1 (proj2 (HB ZA)));
  entry_za_a fill_window_spec_c (@Gprog_fill_window_za) (fun ZA => proj1 (proj2 (proj2 (HB ZA))));
  entry_za_a deflate_stored_spec_c (@Gprog_compress_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (HB ZA)))));
  entry_za_a deflate_fast_spec_c (@Gprog_compress_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (HB ZA))))));
  entry_za_a deflate_slow_spec_c (@Gprog_compress_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA)))))));
  entry_za_a deflate_rle_spec_c (@Gprog_compress_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA))))))));
  entry_za_a deflate_huff_spec_c (@Gprog_compress_za) (fun ZA => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HB ZA)))))))));
  entry_shared_a D_putShortMSB;
  entry_shared_a D_slide_hash;
  entry_shared_a D_longest_match;
  entry_shared_a D_lm_init;
  entry_shared_a T_tr_init;
  entry_shared_a T_tr_static_init;
  entry_shared_a T_init_block;
  entry_shared_a T_tr_flush_bits;
  entry_shared_a T_bi_flush;
  entry_shared_a T_tr_align;
  entry_shared_a T_tr_stored_block;
  entry_shared_a T_bi_windup;
  entry_shared_a T_tr_flush_block;
  entry_shared_a T_detect_data_type;
  entry_shared_a T_build_tree;
  entry_shared_a T_pqdownheap;
  entry_shared_a T_gen_bitlen;
  entry_shared_a T_gen_codes;
  entry_shared_a T_bi_reverse;
  entry_shared_a T_build_bl_tree;
  entry_shared_a T_scan_tree;
  entry_shared_a T_compress_block;
  entry_shared_a T_send_all_trees;
  entry_shared_a T_send_tree;
  entry_shared_a Zlib.proof.adler32.Body_adler32.body_adler32;
  entry_shared_a Zlib.proof.adler32.Body_adler32_z.body_adler32_z;
  entry_shared_a Zlib.proof.crc32.Body_crc32.body_crc32;
  entry_shared_a Zlib.proof.crc32.Body_crc32_z.body_crc32_z;
  entry_shared_a (@Zlib.proof.zutil.Libc.body_memcpy DCS.CS);
  entry_shared_a (@Zlib.proof.zutil.Libc.body_memset DCS.CS);
  entry_external (@external_ok_malloc CSa);
  entry_external (@external_ok_free CSa);
  entry_external (@external_ok_u32 CSa);
  entry_external (@external_ok_bytes CSa);
  entry_external (@external_ok_assert CSa);
  apply Forall_nil.

Ltac asm_entries_free M HL HC HB HA :=
  entry_shared_a M;
  asm_entries_lib HL HC HB HA.

Ltac asm_entries_mem M HL HS HC HB HA :=
  let L_upto := fresh "L_upto" in let L_clip := fresh "L_clip" in let S_params := fresh "S_params" in
  pose proof HL as (L_upto & L_clip & _);
  pose proof HS as (S_params & _);
  entry_shared_a M;
  entry_shared_a L_upto;
  entry_shared_a L_clip;
  entry_external (@external_ok_u8 CSa);
  entry_external (@external_ok_size CSa);
  entry_shared_a S_params;
  entry_external (@external_ok_assume CSa);
  asm_entries_lib HL HC HB HA.

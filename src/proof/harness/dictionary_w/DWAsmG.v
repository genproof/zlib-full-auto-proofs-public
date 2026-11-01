(* The laws rt_dictionary and api_dict_id: the specification contexts of the two programs' assemblies.
   G_drt / G_dai: main, the laws_common.h helpers each harness uses, clip_streams' library context G_lib (with,
   for rt_dictionary, inflateSetDictionary at the port's specification for zlib's default allocator) and
   clip_streams' environment G_env.  G_lib is cut into consecutive pieces ([G_lib_split]) so that the entries
   of each piece are proved in a file of their own (each assembly in one file takes about two minutes). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Asm.
Require Zlib.harness.rt_dictionary.code.
Require Zlib.harness.api_dict_id.code.
#[local] Existing Instance Zlib.proof.harness.clip_streams.CS.CS.

(* trees.c *)
Definition G_trees : funspecs :=
  [bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec].

(* deflate.c, in three pieces *)
Definition G_defl1 : funspecs :=
  [read_buf_spec; putShortMSB_spec; flush_pending_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   fill_window_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec].

Definition G_defl2 : funspecs :=
  [deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9; deflateSetHeader_spec;
   deflateTune_spec; deflatePrime_spec].

Definition G_defl3 : funspecs :=
  [deflateBound_z_spec; deflateBound_spec; deflateSetDictionary_spec;
   deflateEnd_spec; deflateInit2__spec_v9; deflate_spec; deflateParams_spec].

(* inflate.c, inffast.c, inftrees.c, adler32.c, crc32.c, zutil.c, libc.c *)
Definition G_infl : funspecs :=
  [S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec; S5.inflateResetKeep_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; @ZU.inflate_uspec globals SWL.zc_alloc;
   @ZU.inflate_fast_uspec globals SWL.zc_alloc; @ZU.updatewindow_uspec globals SWL.zc_alloc;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS].

Lemma G_lib_split : G_lib = G_trees ++ G_defl1 ++ G_defl2 ++ G_defl3 ++ G_infl.
Proof. reflexivity. Qed.

(* main and the laws_common.h helpers of each harness *)
Definition G_drt_main : funspecs :=
  [(Zlib.harness.rt_dictionary.code._main, QPmain_spec_ext' p_drt tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec].

Definition G_dai_main : funspecs :=
  [(Zlib.harness.api_dict_id.code._main, QPmain_spec_ext' p_dai tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; offer_spec; new_stream_spec].

(* inflateSetDictionary, which only rt_dictionary calls *)
Definition G_setdict : funspecs := [@ZU.inflateSetDictionary_uspec globals SWL.zc_alloc].

Definition G_drt : funspecs := G_drt_main ++ G_lib ++ G_setdict ++ G_env.
Definition G_dai : funspecs := G_dai_main ++ G_lib ++ G_env.

(* the whole contexts (with the vacuous specifications of the functions the laws do not reach) *)
Definition GA_drt : funspecs := G_drt ++ vacuous_internals p_drt G_drt.
Definition GA_dai : funspecs := G_dai ++ vacuous_internals p_dai G_dai.

(* the entries of a piece of a program's context *)
Definition entries_drt (L : funspecs) : Prop := Forall (entry_of_prog (@HonestEspec CS) CS p_drt GA_drt) L.
Definition entries_dai (L : funspecs) : Prop := Forall (entry_of_prog (@HonestEspec CS) CS p_dai GA_dai) L.

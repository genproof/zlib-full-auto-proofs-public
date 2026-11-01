(** * The proof obligations of the deflate area, as named propositions

    One proposition per function body: [ob_X] says that X's body satisfies X's shared specification (TSpec.v,
    DSpec.v, compress/CSpec.v) in the context of its callees.  [trees_bodies_ok] and [deflate_bodies_ok] are
    their conjunctions; the laws are proved from them ([Laws.v]), and the bodies separately (Body_*.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.trees.code Zlib.deflate.code Zlib.compress.code.

(** ** trees.c *)
Definition ob_bi_reverse : Prop :=
  @semax_body TSpec.Vprog Gprog_bi_reverse DCS.CS Zlib.trees.code.f_bi_reverse bi_reverse_spec.
Definition ob_bi_flush : Prop :=
  @semax_body TSpec.Vprog Gprog_bi_flush DCS.CS Zlib.trees.code.f_bi_flush bi_flush_spec.
Definition ob_bi_windup : Prop :=
  @semax_body TSpec.Vprog Gprog_bi_windup DCS.CS Zlib.trees.code.f_bi_windup bi_windup_spec.
Definition ob_tr_flush_bits : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_flush_bits DCS.CS Zlib.trees.code.f__tr_flush_bits tr_flush_bits_spec.
Definition ob_tr_align : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_align DCS.CS Zlib.trees.code.f__tr_align tr_align_spec.
Definition ob_tr_stored_block : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_stored_block DCS.CS Zlib.trees.code.f__tr_stored_block tr_stored_block_spec.
Definition ob_gen_codes : Prop :=
  @semax_body TSpec.Vprog Gprog_gen_codes DCS.CS Zlib.trees.code.f_gen_codes gen_codes_spec.
Definition ob_pqdownheap : Prop :=
  @semax_body TSpec.Vprog Gprog_pqdownheap DCS.CS Zlib.trees.code.f_pqdownheap pqdownheap_spec.
Definition ob_gen_bitlen : Prop :=
  @semax_body TSpec.Vprog Gprog_gen_bitlen DCS.CS Zlib.trees.code.f_gen_bitlen gen_bitlen_spec.
Definition ob_build_tree : Prop :=
  @semax_body TSpec.Vprog Gprog_build_tree DCS.CS Zlib.trees.code.f_build_tree build_tree_spec.
Definition ob_scan_tree : Prop :=
  @semax_body TSpec.Vprog Gprog_scan_tree DCS.CS Zlib.trees.code.f_scan_tree scan_tree_spec.
Definition ob_build_bl_tree : Prop :=
  @semax_body TSpec.Vprog Gprog_build_bl_tree DCS.CS Zlib.trees.code.f_build_bl_tree build_bl_tree_spec.
Definition ob_detect_data_type : Prop :=
  @semax_body TSpec.Vprog Gprog_detect_data_type DCS.CS Zlib.trees.code.f_detect_data_type detect_data_type_spec.
Definition ob_init_block : Prop :=
  @semax_body TSpec.Vprog Gprog_init_block DCS.CS Zlib.trees.code.f_init_block init_block_spec.
Definition ob_send_tree : Prop :=
  @semax_body TSpec.Vprog Gprog_send_tree DCS.CS Zlib.trees.code.f_send_tree send_tree_spec.
Definition ob_send_all_trees : Prop :=
  @semax_body TSpec.Vprog Gprog_send_all_trees DCS.CS Zlib.trees.code.f_send_all_trees send_all_trees_spec.
Definition ob_compress_block : Prop :=
  @semax_body TSpec.Vprog Gprog_compress_block DCS.CS Zlib.trees.code.f_compress_block compress_block_spec.
Definition ob_tr_static_init : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_static_init DCS.CS Zlib.trees.code.f_tr_static_init tr_static_init_spec.
Definition ob_tr_init : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_init DCS.CS Zlib.trees.code.f__tr_init tr_init_spec.
Definition ob_tr_flush_block : Prop :=
  @semax_body TSpec.Vprog Gprog_tr_flush_block DCS.CS Zlib.trees.code.f__tr_flush_block tr_flush_block_spec.

(** ** deflate.c *)
Definition ob_read_buf : Prop :=
  @semax_body DSpec.Vprog Gprog_read_buf DCS.CS Zlib.deflate.code.f_read_buf read_buf_spec.
Definition ob_putShortMSB : Prop :=
  @semax_body DSpec.Vprog Gprog_putShortMSB DCS.CS Zlib.deflate.code.f_putShortMSB putShortMSB_spec.
Definition ob_flush_pending : Prop :=
  @semax_body DSpec.Vprog Gprog_flush_pending DCS.CS Zlib.deflate.code.f_flush_pending flush_pending_spec.
Definition ob_slide_hash : Prop :=
  @semax_body DSpec.Vprog Gprog_slide_hash DCS.CS Zlib.deflate.code.f_slide_hash slide_hash_spec.
Definition ob_longest_match : Prop :=
  @semax_body DSpec.Vprog Gprog_longest_match DCS.CS Zlib.deflate.code.f_longest_match longest_match_spec.
Definition ob_lm_init : Prop :=
  @semax_body DSpec.Vprog Gprog_lm_init DCS.CS Zlib.deflate.code.f_lm_init lm_init_spec.
Definition ob_fill_window : Prop :=
  @semax_body DSpec.Vprog Gprog_fill_window DCS.CS Zlib.deflate.code.f_fill_window fill_window_spec.
Definition ob_deflate_stored : Prop :=
  @semax_body DSpec.Vprog Gprog_compress DCS.CS Zlib.deflate.code.f_deflate_stored deflate_stored_spec.
Definition ob_deflate_fast : Prop :=
  @semax_body DSpec.Vprog Gprog_compress DCS.CS Zlib.deflate.code.f_deflate_fast deflate_fast_spec.
Definition ob_deflate_slow : Prop :=
  @semax_body DSpec.Vprog Gprog_compress DCS.CS Zlib.deflate.code.f_deflate_slow deflate_slow_spec.
Definition ob_deflate_rle : Prop :=
  @semax_body DSpec.Vprog Gprog_compress DCS.CS Zlib.deflate.code.f_deflate_rle deflate_rle_spec.
Definition ob_deflate_huff : Prop :=
  @semax_body DSpec.Vprog Gprog_compress DCS.CS Zlib.deflate.code.f_deflate_huff deflate_huff_spec.
Definition ob_deflateStateCheck : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateStateCheck DCS.CS Zlib.deflate.code.f_deflateStateCheck deflateStateCheck_spec.
Definition ob_deflateResetKeep : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateResetKeep DCS.CS Zlib.deflate.code.f_deflateResetKeep deflateResetKeep_spec.
Definition ob_deflateReset : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateReset DCS.CS Zlib.deflate.code.f_deflateReset deflateReset_spec.
Definition ob_deflateSetHeader : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateSetHeader DCS.CS Zlib.deflate.code.f_deflateSetHeader deflateSetHeader_spec.
Definition ob_deflateTune : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateTune DCS.CS Zlib.deflate.code.f_deflateTune deflateTune_spec.
Definition ob_deflatePrime : Prop :=
  @semax_body DSpec.Vprog Gprog_deflatePrime DCS.CS Zlib.deflate.code.f_deflatePrime deflatePrime_spec.
Definition ob_deflateBound_z : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateBound_z DCS.CS Zlib.deflate.code.f_deflateBound_z deflateBound_z_spec.
Definition ob_deflateBound : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateBound DCS.CS Zlib.deflate.code.f_deflateBound deflateBound_spec.
Definition ob_deflateSetDictionary : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateSetDictionary DCS.CS Zlib.deflate.code.f_deflateSetDictionary deflateSetDictionary_spec.
Definition ob_deflateEnd : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateEnd DCS.CS Zlib.deflate.code.f_deflateEnd deflateEnd_spec.
Definition ob_deflateInit2_ : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateInit2_ DCS.CS Zlib.deflate.code.f_deflateInit2_ deflateInit2__spec.
Definition ob_deflate : Prop :=
  @semax_body DSpec.Vprog Gprog_deflate DCS.CS Zlib.deflate.code.f_deflate deflate_spec.
Definition ob_deflateParams : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateParams DCS.CS Zlib.deflate.code.f_deflateParams deflateParams_spec.

(** ** compress.c *)
Definition ob_compressBound_z : Prop :=
  @semax_body CSpec.Vprog CSpec.Gprog_compressBound_z Zlib.units.Compress.CS Zlib.compress.code.f_compressBound_z
    CSpec.compressBound_z_spec.
Definition ob_compressBound : Prop :=
  @semax_body CSpec.Vprog CSpec.Gprog_compressBound Zlib.units.Compress.CS Zlib.compress.code.f_compressBound
    CSpec.compressBound_spec.

(** ** A conversion the laws need (v2): a live or ended stream gives what deflateEnd needs. *)
Definition ob_dstream_to_end : Prop :=
  forall (os : option dstate) (strmp ghp : val) (gv : globals),
    dstream 2 os strmp ghp gv |-- dstream_end os strmp gv.

Definition trees_bodies_ok : Prop :=
  ob_bi_reverse /\
  ob_bi_flush /\
  ob_bi_windup /\
  ob_tr_flush_bits /\
  ob_tr_align /\
  ob_tr_stored_block /\
  ob_gen_codes /\
  ob_pqdownheap /\
  ob_gen_bitlen /\
  ob_build_tree /\
  ob_scan_tree /\
  ob_build_bl_tree /\
  ob_detect_data_type /\
  ob_init_block /\
  ob_send_tree /\
  ob_send_all_trees /\
  ob_compress_block /\
  ob_tr_static_init /\
  ob_tr_init /\
  ob_tr_flush_block.

Definition deflate_bodies_ok : Prop :=
  ob_read_buf /\
  ob_putShortMSB /\
  ob_flush_pending /\
  ob_slide_hash /\
  ob_longest_match /\
  ob_lm_init /\
  ob_fill_window /\
  ob_deflate_stored /\
  ob_deflate_fast /\
  ob_deflate_slow /\
  ob_deflate_rle /\
  ob_deflate_huff /\
  ob_deflateStateCheck /\
  ob_deflateResetKeep /\
  ob_deflateReset /\
  ob_deflateSetHeader /\
  ob_deflateTune /\
  ob_deflatePrime /\
  ob_deflateBound_z /\
  ob_deflateBound /\
  ob_deflateSetDictionary /\
  ob_deflateEnd /\
  ob_deflateInit2_ /\
  ob_deflate /\
  ob_deflateParams /\
  ob_compressBound_z /\ ob_compressBound /\ ob_dstream_to_end.

(* Law inflate_decode: main of harness/inflate_decode.c, against MainLib.main_core_spec R (IDGlobals.v), from the
   decode theory (Decode.v: decode_init_stmt, decode_call_stmt) and the specifications of its callees: inflate.c's
   API (inflate_api/Spec5.v), the harness helpers (HarnessLib.v, adler32/crc32 HarnessRef.v, HarnessBytes.v) and
   deflate_ref.h's encoder (DRefSpec.v).  Main encodes a stream from the drawn blocks (its blocks bs: the
   wrapper's stream_bytes W [] bs, Format.v; data = data [] bs; isb = the block boundaries), then inflates it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit Zlib.proof.harness.inflate_decode.IDMainPro
               Zlib.proof.harness.inflate_decode.IDMainBlk Zlib.proof.harness.inflate_decode.IDMainTrl
               Zlib.proof.harness.inflate_decode.IDMainInit Zlib.proof.harness.inflate_decode.IDMainDec
               Zlib.proof.harness.inflate_decode.IDMainTail.

Definition Gmain : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; Zlib.proof.crc32.HarnessRef.ref_crc32_spec; bytes_copy_spec; bytes_same_spec;
   exact_copy_spec; exact_space_spec; stream_defaults_spec;
   bw_byte_spec; bw_bits_spec; bw_code_spec; bw_align_spec; bw_fixed_spec;
   len_code_spec id_tabs; dist_code_spec id_tabs; bw_fixed_match_spec id_tabs; dyn_header_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Lemma id_body_main : decode_init_stmt -> decode_call_stmt ->
  semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros DI DC. change Gmain with Gmain_k.
  start_function.
  unfold R. Intros.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
  apply semax_seq with FF; [ | apply semax_ff ].
  eapply semax_pre; [ | apply (id_pro_ok gv v_w v_ll v_lcodes v_dcodes v_s v_osnap (id_msg_lits gv)); [reflexivity | ] ].
  { unfold pro_pre, dres. entailer!. }
  intros wrap wb flevel isel datap srcp isbp Hpar Pd Ps Pi.
  set (Fr := (data_at Ers (tarray tuchar 10) (zvals gz_vals) (gv _gz) * id_msg_lits gv)%logic).
  (* the block loop *)
  rewrite S_blk_eq.
  forward_loop (enc_inv gv v_w v_ll v_lcodes v_dcodes v_s v_osnap wrap wb flevel isel datap srcp isbp Fr)
    break: (enc_post gv v_w v_ll v_lcodes v_dcodes v_s v_osnap wrap wb flevel isel datap srcp isbp Fr).
  { apply andp_left2, derives_refl. }
  { unfold enc_inv at 1. Intros bs ls dcont isbz llc lcc dcc.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (proj1 (semax_seq_skip _ _ _ _)). apply id_blk_ok; auto. }
  (* the trailer and inflateInit2 *)
  apply (id_trl_ok gv v_w v_ll v_lcodes v_dcodes v_s v_osnap wrap wb flevel isel datap srcp isbp Fr _ Hpar Pd Ps Pi).
  intros al ls dcont isbz srcl scont TF.
  apply (id_init_ok gv v_w v_ll v_lcodes v_dcodes v_s v_osnap wrap wb flevel isel datap srcp isbp Fr
           al ls dcont isbz srcl scont (overridePost FF POST_id) DI eq_refl TF).
  intros G DF.
  set (Fr' := (dref_tabs gv Ers id_tabs * data_at Ers (tarray tuchar 19) (zvals clorder) (gv _cl_order) *
               version_lit gv * id_hversion_lit gv * Fr)%logic).
  (* the decode loop *)
  rewrite S_dec_eq.
  forward_loop (dec_inv gv v_w v_ll v_lcodes v_dcodes v_s v_osnap G datap srcp isbp dcont scont isbz ls Fr')
    break: (dec_post gv v_w v_ll v_lcodes v_dcodes v_s v_osnap G datap srcp isbp dcont scont isbz ls Fr').
  { apply andp_left2, derives_refl. }
  { unfold dec_inv at 1. Intros pos lim opos z L.
    unfold abbreviate in POSTCONDITION, MORE_COMMANDS. subst POSTCONDITION MORE_COMMANDS.
    apply (proj1 (semax_seq_skip _ _ _ _)). apply id_decb_ok; auto. }
  apply id_tail_ok with (G := G); [reflexivity | auto].
Qed.

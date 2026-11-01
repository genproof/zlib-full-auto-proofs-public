(* Law rt_session: the specification context of the assembly (SAsm.v) and its entry tactic.

   [G]: one specification per function main reaches: main's, the laws_common.h helpers, the harness's any_string
   and same_field, laws_session.h's helpers ([G_main]); trees.c ([G_trees]); deflate.c ([G_defl]: DSpec / DSpec9,
   deflate against DSpecV.deflate_specV); inflate.c, inffast.c, inftrees.c, adler32.c, crc32.c, zutil.c and libc.c
   ([G_infl]: Spec5's inflateInit2_ and reset functions, the port's inflateStateCheck and inflateSetDictionary at
   zlib's allocator, inflate at SMainStmt.inflate_fs_ses, inflate_fast and updatewindow at SAsmI's intersections,
   RTH8Spec's inflateGetHeader); the environment ([G_env]).  The entries of each piece are proved in their own
   file (SAsmE1.v, SAsmE2.v, SAsm.v).

   [ses_entry B]: the entry of G for the shared body B (QuickProof.Assembly.entry_moved); the inclusion of B's
   context in the law's is decided callee by callee on the identifier ([ses_spec_sub_at]): zcalloc / zcfree by
   zutil's transport lemmas (a failing funspec_sub_refl on them is slow), updatewindow by SAsmI.upd_ses_sub (the
   port's callers),
   inflateStateCheck and inflateSetDictionary by SpecWBridge (the port's specifications are stronger than Callees'
   and SpecW's), the others by RTRSLaw.env_spec_sub' (equal specifications, the environment, libc). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.adler32.Spec Zlib.proof.crc32.Spec Zlib.proof.zutil.Spec Zlib.proof.zutil.Libc.
Require Zlib.proof.inftrees.spec.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.DSpecV.
Require Zlib.proof.inflate.Callees.
Require Zlib.proof.inflate_api.Spec5.
Require Zlib.proof.inflate_api.SpecWLib Zlib.proof.inflate_api.SpecWBridge.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SAsmI.
Require Zlib.harness.rt_session.code.
#[local] Existing Instance Zlib.proof.harness.rt_session.SCS.CS.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module SWL := Zlib.proof.inflate_api.SpecWLib.
Module ZU := Zlib.proof.za.inflate_api.USpec.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* main, the helpers of laws_common.h and of the harness, laws_session.h's helpers *)
Definition G_main : funspecs :=
  [(Zlib.harness.rt_session.code._main, QPmain_spec_ext' p tt main_post_TT);
   upto_spec; clip_spec; any_bytes_spec; copy_of_spec; bytes_eq_spec; offer_spec; new_stream_spec;
   Zlib.proof.harness.rt_gzip_header.G2MainDefs.any_string_spec;
   Zlib.proof.harness.rt_gzip_header.G2MainDefs.same_field_spec;
   LS.deflate_params_ok_spec; LS.position_of_spec; LS.unmoved_spec; LS.accounted_spec].

(* trees.c *)
Definition G_trees : funspecs :=
  [bi_reverse_spec; bi_flush_spec; bi_windup_spec; tr_flush_bits_spec; tr_align_spec; tr_stored_block_spec;
   gen_codes_spec; pqdownheap_spec; gen_bitlen_spec; build_tree_spec; scan_tree_spec; build_bl_tree_spec;
   detect_data_type_spec; init_block_spec; send_tree_spec; send_all_trees_spec; compress_block_spec;
   tr_static_init_spec; tr_init_spec; tr_flush_block_spec].

(* deflate.c *)
Definition G_defl : funspecs :=
  [read_buf_spec; putShortMSB_spec; flush_pending_spec; slide_hash_spec; longest_match_spec; lm_init_spec;
   fill_window_spec; deflate_stored_spec; deflate_fast_spec; deflate_slow_spec; deflate_rle_spec;
   deflate_huff_spec; deflateStateCheck_spec; deflateResetKeep_spec_v9; deflateReset_spec_v9;
   deflateSetHeader_spec; deflateSetDictionary_spec; deflateEnd_spec; deflateInit2__spec_v9;
   Zlib.proof.deflate.DSpecV.deflate_specV].

(* inflate.c, inffast.c, inftrees.c, adler32.c, crc32.c, zutil.c, libc.c *)
Definition G_infl : funspecs :=
  [S5.inflateInit2__spec; S5.inflateReset2_spec; S5.inflateReset_spec; S5.inflateResetKeep_spec;
   @ZU.inflateStateCheck_uspec globals SWL.zc_alloc; inflate_spec_ses; fast_spec_ses; upd_spec_ses;
   @ZU.inflateSetDictionary_uspec globals SWL.zc_alloc; Zlib.proof.roundtrip.RTH8Spec.inflateGetHeader_spec8;
   Zlib.proof.inflate.Callees.inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.adler32.Spec.adler32_z_spec;
   Zlib.proof.crc32.Spec.crc32_spec; Zlib.proof.crc32.Spec.crc32_z_spec;
   @Zlib.proof.zutil.Spec.zcalloc_spec CS; @Zlib.proof.zutil.Spec.zcfree_spec CS;
   @Zlib.proof.zutil.Libc.memcpy_spec CS; @Zlib.proof.zutil.Libc.memset_spec CS].

(* the environment *)
Definition G_env : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CS); (_quickproof_free, @free_spec' CS);
   nondet_size_spec; @nondet_bytes_spec CS; nondet_u8_spec; nondet_u32_spec; gp_assert_spec; gp_assume_spec].

Definition G : funspecs := G_main ++ G_trees ++ G_defl ++ G_infl ++ G_env.

(* the whole context, with the vacuous specifications of the functions main does not reach *)
Definition GA : funspecs := G ++ vacuous_internals p G.

(* the entries of a piece of G *)
Definition entries (L : funspecs) : Prop := Forall (entry_of_prog (@HonestEspec CS) CS p GA) L.

(* zcalloc / zcfree at the compspecs of deflate.c (DCS.CS) and of inflate.c are subspecifications of theirs at
   the law's: proved once here *)
Lemma dcs_pres : preserved_b Zlib.proof.deflate.DCS.CS CS = true.
Proof. vm_compute; reflexivity. Qed.
Lemma ics_pres : preserved_b Zlib.units.Inflate.CS CS = true.
Proof. vm_compute; reflexivity. Qed.

Lemma zcalloc_dcs : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcalloc_spec CS))
                                (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.proof.deflate.DCS.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcalloc_spec_sub Zlib.proof.deflate.DCS.CS CS);
    first [ exact dcs_sub | exact (preserved_by_computation _ _ dcs_pres) ].
Qed.
Lemma zcfree_dcs : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcfree_spec CS))
                               (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.proof.deflate.DCS.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcfree_spec_sub Zlib.proof.deflate.DCS.CS CS);
    first [ exact dcs_sub | exact (preserved_by_computation _ _ dcs_pres) ].
Qed.
Lemma zcalloc_ics : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcalloc_spec CS))
                                (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcalloc_spec_sub Zlib.units.Inflate.CS CS);
    first [ exact ics_sub | exact (preserved_by_computation _ _ ics_pres) ].
Qed.
Lemma zcfree_ics : funspec_sub (snd (@Zlib.proof.zutil.Spec.zcfree_spec CS))
                               (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)).
Proof.
  apply (Zlib.proof.zutil.Spec.zcfree_spec_sub Zlib.units.Inflate.CS CS);
    first [ exact ics_sub | exact (preserved_by_computation _ _ ics_pres) ].
Qed.

(* the callee X of a body at compspecs cs1 *)
Ltac ses_spec_sub_at cs1 X :=
  let x := eval compute in X in
  let zc := eval compute in Zlib.inflate.code._zcalloc in
  let zf := eval compute in Zlib.inflate.code._zcfree in
  let uw := eval compute in Zlib.inflate.code._updatewindow in
  let sc := eval compute in Zlib.inflate.code._inflateStateCheck in
  let sd := eval compute in Zlib.inflate.code._inflateSetDictionary in
  tryif constr_eq x zc then
    (tryif constr_eq cs1 Zlib.proof.deflate.DCS.CS then exact zcalloc_dcs else exact zcalloc_ics)
  else tryif constr_eq x zf then
    (tryif constr_eq cs1 Zlib.proof.deflate.DCS.CS then exact zcfree_dcs else exact zcfree_ics)
  else tryif constr_eq x uw then
    lazymatch goal with
    | |- funspec_sub _ upd_fs_ses => apply funspec_sub_refl
    | _ => apply (proj1 upd_ses_sub)
    end
  else tryif constr_eq x sc then
    first [ apply (proj2 (proj2 Zlib.proof.inflate_api.SpecWBridge.specw_bridge)) | apply funspec_sub_refl ]
  else tryif constr_eq x sd then
    first [ apply (proj1 (proj2 Zlib.proof.inflate_api.SpecWBridge.specw_bridge)) | apply funspec_sub_refl ]
  else Zlib.proof.roundtrip.RTRSLaw.env_spec_sub'.

Ltac ses_ctx_sub cs1 :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (lazymatch type of E with
          | (if Memory.EqDec_ident _ ?X then _ else _) = _ =>
            if_tac in E; [ inv E; eexists; split; [ reflexivity | ses_spec_sub_at cs1 X ] | ]
          end);
  try discriminate.

(* Goal entries (spec :: L): the entry of spec from the shared body B; leaves entries L *)
Ltac ses_entry B :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | ses_ctx_sub cs1 ]
    | ]
  end.

(* inflate_table's context lists inftrees' inflate_fixed_spec (precondition False): the entry by
   NDsubsume_subsume *)
Ltac ses_entry_table B :=
  apply Forall_cons;
  [ eapply (entry_moved _ _ Zlib.units.Inftrees.CS _ _ _ _ _ _ _ B);
    [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | ]
  | ];
  [ intros i phi E; simpl in E;
    if_tac in E; [ inv E; eexists; split; [ reflexivity | apply funspec_sub_refl ] | ];
    if_tac in E; [ | discriminate ];
    inv E; eexists; split; [ reflexivity | ];
    apply NDsubsume_subsume; [ split; reflexivity | split; [ split; reflexivity | ] ];
      intros x [ge args]; simpl; unfold PROPx; simpl; normalize
  | ].

(* The laws rt_dictionary and api_dict_id: an entry tactic for the assemblies of their programs.

   [dw_entry B BR] is clip_streams/Asm.v's clip_entry with a faster proof of the context inclusion: a callee
   zcalloc / zcfree (at its unit's compspecs; deflateInit2_, deflateEnd, inflateInit2_ and main call them) is
   moved to the program's compspecs by zutil's transport lemmas at once.  clip_entry tries funspec_sub_refl
   first, whose failure on these two specifications costs about 20 s each and would put the files of the
   assembly over the compile-time budget. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Assembly.
Require Zlib.zutil.code.
Require Zlib.proof.zutil.Spec.
Require Zlib.proof.roundtrip.RTRSLaw.
Require Zlib.proof.inflate_api.Body5_init.
Require Zlib.proof.inflate_api.Body5_reset.
Require Zlib.proof.inflate.BodySmall.
Require Zlib.proof.adler32.Body_adler32.
Require Zlib.proof.adler32.Body_adler32_z.
Require Zlib.proof.crc32.Body_crc32.
Require Zlib.proof.crc32.Body_crc32_z.
Require Zlib.proof.zutil.Libc.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Asm.

Ltac dw_zsub_tail :=
  try (apply cspecs_sub_by_computation; vm_compute; reflexivity);
  try (apply preserved_by_computation; vm_compute; reflexivity).

Ltac dw_ctx_sub BR :=
  let i := fresh "i" in let phi := fresh "phi" in let E := fresh "E" in
  intros i phi E; simpl in E;
  repeat (if_tac in E;
    [ lazymatch goal with
      | H : i = ?x |- _ =>
          first [ unify x Zlib.zutil.code._zcalloc;
                  inv E; eexists; split; [ reflexivity | apply Zlib.proof.zutil.Spec.zcalloc_spec_sub; dw_zsub_tail ]
                | unify x Zlib.zutil.code._zcfree;
                  inv E; eexists; split; [ reflexivity | apply Zlib.proof.zutil.Spec.zcfree_spec_sub; dw_zsub_tail ]
                | inv E; eexists; split; [ reflexivity | clip_spec_sub BR ] ]
      end
    | ]);
  try discriminate.

Ltac dw_entry B BR :=
  lazymatch type of B with
  | @semax_body _ _ ?cs1 ?f ?spec =>
    apply Forall_cons;
    [ eapply (entry_moved _ _ cs1 _ _ _ _ (fst spec) (snd spec) f B);
      [ reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | apply Zlib.proof.roundtrip.RTRSLaw.find_ids_b; vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | dw_ctx_sub BR ]
    | ]
  end.

(* clip_streams/Asm.v's clip_inflate_entries with dw_entry (inflateInit2_, inflateReset and inflateReset2 call
   zcalloc / zcfree at the inflate unit's compspecs): the entries of inflate.c, inffast.c, inftrees.c,
   adler32.c, crc32.c and zutil.c / libc.c, in the order of clip_streams' G_lib.  The bodies of inflateInit2_,
   the reset functions and inflate_fixed are taken one by one (not through LibProof5.inflate_lib5_proof, which
   also carries inflate.c functions the laws do not call). *)
Ltac dw_inflate_entries BR ZL :=
  let B_init2 := fresh "B_init2" in let B_resetkeep := fresh "B_resetkeep" in let B_reset := fresh "B_reset" in
  let B_reset2 := fresh "B_reset2" in let B_fixed := fresh "B_fixed" in let B_table := fresh "B_table" in
  let U_inflate := fresh "U_inflate" in let U_fast := fresh "U_fast" in let U_upd := fresh "U_upd" in
  let U_check := fresh "U_check" in
  pose proof (@Zlib.proof.inflate_api.Body5_init.body_inflateInit2_ NullExtension.Espec) as B_init2;
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateResetKeep NullExtension.Espec) as B_resetkeep;
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateReset NullExtension.Espec) as B_reset;
  pose proof (@Zlib.proof.inflate_api.Body5_reset.body_inflateReset2 NullExtension.Espec) as B_reset2;
  pose proof (@Zlib.proof.inflate.BodySmall.body_inflate_fixed NullExtension.Espec) as B_fixed;
  destruct (ZL NullExtension.Espec) as (U_inflate & U_fast & U_upd & U_check & _);
  pose proof (Zlib.proof.roundtrip.RTRSLaw.body_inflate_table NullExtension.Espec) as B_table;
  dw_entry B_init2 BR; dw_entry B_reset2 BR; dw_entry B_reset BR; dw_entry B_resetkeep BR;
  dw_entry U_check BR; dw_entry U_inflate BR; dw_entry U_fast BR; dw_entry U_upd BR;
  dw_entry B_fixed BR;
  clip_entry_table B_table;
  dw_entry Zlib.proof.adler32.Body_adler32.body_adler32 BR;
  dw_entry Zlib.proof.adler32.Body_adler32_z.body_adler32_z BR;
  dw_entry Zlib.proof.crc32.Body_crc32.body_crc32 BR;
  dw_entry Zlib.proof.crc32.Body_crc32_z.body_crc32_z BR;
  dw_entry (@Zlib.proof.zutil.Spec.body_zcalloc CS) BR;
  dw_entry (@Zlib.proof.zutil.Spec.body_zcfree CS) BR;
  dw_entry (@Zlib.proof.zutil.Libc.body_memcpy CS) BR;
  dw_entry (@Zlib.proof.zutil.Libc.body_memset CS) BR.

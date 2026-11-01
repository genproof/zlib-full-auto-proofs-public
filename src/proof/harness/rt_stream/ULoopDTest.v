(* Law rt_stream (data of any length), main's deflate loop (UMainKit.loopD): the out-of-room test at the end of its body, from DK to the loop's test or main's
   return (ULoopDKit.testD_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDKit.
Require Import Zlib.proof.harness.rt_stream.ULoopDLib.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

Lemma test_d : testD_stmt.
Proof.
  intros Espec J gv vc vd va u off flush code l.
  unfold testD, Delta_m; simplify_func_tycontext.
  unfold DK. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  subst off flush.
  match goal with H: if code =? Z_STREAM_END then _ else _ |- _ => rename H into HK end.
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst no.
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite ld_next_out_cs.
  unfold su_locals, lv_locals. simpl app.
  apply semax_if_seq.
  forward_if.
  { forward. forward.
    { entailer!. rewrite ld_add_ptr_long_tuchar by (auto; unfold max_size in *; rep_lia). unfold cobj.
      eapply derives_trans;
        [ | apply (ld_test_eq TT (su_cp u) (Zlength O) (su_cap u) (su_cap u) (cbytes (su_cap u) O))];
        [cancel | pose proof (Zlength_nonneg O); lia | lia | auto]. }
    destruct (ld_cmp_bool (su_cp u) (Zlength O) (su_cap u) Pcp) as [b Eb]. rewrite Eb.
    rewrite <- ld_next_out_cs. sep_apply (ld_cstream_fold gv vc s ni ain tin (offset_val (Zlength O) (su_cp u))
                                           aout tout msgv adler); auto.
    forward_if.
    - (* out of room: return 0 *)
      forward. Exists (Int.repr 0). sep_apply ld_cstream_frame. entailer!.
    - ld_cont code (mkDL D O fin off flush msg
                       (mkCS s ni ain tin (offset_val (Zlength O) (su_cp u)) aout tout msgv adler)). }
  { forward. forward_if; [ exfalso; lia | ].
    rewrite <- ld_next_out_cs. sep_apply (ld_cstream_fold gv vc s ni ain tin (offset_val (Zlength O) (su_cp u))
                                           aout tout msgv adler); auto.
    ld_cont code (mkDL D O fin off flush msg
                    (mkCS s ni ain tin (offset_val (Zlength O) (su_cp u)) aout tout msgv adler)). }
Qed.

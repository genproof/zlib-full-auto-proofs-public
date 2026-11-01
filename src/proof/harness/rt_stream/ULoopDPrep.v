(* Law rt_stream (data of any length), main's deflate loop (UMainKit.loopD): the third and fourth statements of its body, avail_in = clip(offered - read) and
   avail_out = clip(any room left in compressed), from DR to DC, the state before the deflate() call
   (ULoopDKit.prepD_stmt). *)
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

Lemma prep_d : prepD_stmt.
Proof.
  intros Espec J gv vc vd va u l HC.
  unfold prepD, Delta_m; simplify_func_tycontext.
  unfold DR. Intros.
  match goal with H: su_ok u |- _ => rename H into SU end.
  match goal with H: dl_ok J u l |- _ => rename H into DL end.
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  pose proof DL as (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno).
  destruct l as [D O fin off flush msg c]. cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c] in *.
  destruct c as [s ni ain tin no aout tout msgv adler].
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  subst ni no.
  unfold max_size in *.
  assert (HD0 := Zlength_nonneg D). assert (HO0 := Zlength_nonneg O).
  unfold cstream, api_fields. Intros. cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler] in *.
  rewrite ld_avail_in_cs, ld_next_out_cs, ld_avail_out_cs.
  unfold su_locals, lv_locals. simpl app.
  forward_call (off - Zlength D).
  forward.
  forward.
  forward_call (su_cap u - Zlength O).
  all: try solve [ entailer!; first [ apply prop_right, ld_sameblock_off; auto | apply ld_sameblock_off; auto
                     | unfold vl; rewrite ld_ptr_sub by (auto; rep_lia); reflexivity ] ].
  Intros ao.
  forward_call ao.
  forward.
  (* the state before the deflate() call *)
  set (l2 := mkDL D O fin off flush msg
               (mkCS s (offset_val (Zlength D) (su_dp u)) (Z.min (off - Zlength D) Int.max_unsigned) tin
                  (offset_val (Zlength O) (su_cp u)) (Z.min ao Int.max_unsigned) tout msgv adler)).
  pose proof (HC l2) as HC1.
  assert (DL2 : dl_ok J u l2) by exact DL.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | exact HC1 ].
  unfold DC, cstream, api_fields, su_locals, lv_locals. simpl app.
  cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv
       cs_adler l2].
  rewrite ld_avail_in_cs, ld_next_out_cs, ld_avail_out_cs.
  entailer!. unfold u32_ok; repeat split; rep_lia.
Qed.

(* Law rt_session (harness/rt_session.c): main's statements 63-72 with a header: inflateInit2_, inflateGetHeader and the inflate loop's start (SMKit.v, [segC_9_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMC9Kit.
Require Import Zlib.proof.harness.rt_session.SMC9Tail.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Lemma sm_segC_9 : segC_9_stmt.
Proof.
  intros Espec P PN gv vh vg vc va vd u O c src ip PF WH.
  unfold DB, segC, POST_s.
  Intros.
  match goal with H : su_ok u |- _ => rename H into Hu end.
  pose proof Hu as (Hd & _).
  destruct (c9_wb u Hd WH) as [Hwb Hiw].
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  rewrite WH, (c9_nodict u WH).
  unfold Delta_s. simplify_func_tycontext. abbreviate_semax.
  rewrite (c9_undef vd).
  forward_call (vd, Tsh, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef).
  rewrite (c9_ns_raw gv vd).
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx Pr (LOCALx Q (SEPx R))) end.
  { exfalso. lia. }
  { forward. entailer!. }
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold Rm at 1. Intros. rewrite c9_version.
  assert_PROP (isptr (gv ___stringlit_rt_session_1)) as Pv by entailer!.
  assert_PROP (isptr vd) as Pvd by entailer!.
  assert (Nd : vd <> nullval) by (intro; subst; contradiction).
  forward_call (gv, Tsh, vd, c9_r0, Vundef, Vundef, nullval, su_wbits u, gv ___stringlit_rt_session_1, Ers,
                c9_hv, 49, 112).
  { rewrite if_false by auto. cancel. }
  { change (Zlength c9_hv) with 6. repeat split; auto; rep_lia. }
  Intros vret. destruct vret as [aok sp]. cbn [fst snd] in *.
  destruct (c9_init_facts sp (su_wbits u) Hwb) as (Wok & Wrap & Wmode).
  replace (init_ret vd 49 112 (su_wbits u) aok) with (if aok then Z_OK else Z_MEM_ERROR)
    by (unfold init_ret; simpl; rewrite if_false by auto; rewrite Wok; destruct aok; reflexivity).
  destruct aok; cbv iota.
  2: { (* Z_MEM_ERROR: return 0, the locals given back *)
    forward_if; [ | exfalso; match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end].
    sep_apply (c9_init_fail gv vd c9_r0 Z_MEM_ERROR sp (su_wbits u) Pvd ltac:(cbv; congruence)).
    sep_apply (c9_comp_back gv vc (ghp vh u) c).
    sep_apply (c9_hobj_back vh u). sep_apply (c9_graw_back vg u).
    forward. Exists (Int.repr 0). entailer!. }
  (* Z_OK: a gzip-only stream in mode HEAD *)
  replace (init_mem gv Tsh vd c9_r0 Vundef Vundef nullval Z_OK sp (su_wbits u))
    with (istream_raw gv Tsh vd (raw_after_init c9_r0 (l_s (init_live sp (su_wbits u)))) (init_live sp (su_wbits u)))
    by (unfold init_mem; rewrite if_false by auto; reflexivity).
  sep_apply (c9_istream gv vd sp (su_wbits u) Nd Wrap).
  forward_if; [exfalso; match goal with H : Int.repr _ = _ |- _ =>
                  apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end | ].
  forward_call (Int.repr 1).
  (* with_head: inflateGetHeader attaches got *)
  apply semax_if_seq. forward_if.
  2: { exfalso. match goal with H : Int.repr _ = Int.zero |- _ =>
         apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end. }
  sep_apply (c9_graw u vg Hu).
  forward_call (gv, Tsh, vd, c9_z0, Some (init_live sp (su_wbits u)), vg, Tsh, su_gxp u, su_gnp u, su_gcp u, h0 u).
  { cancel. }
  { pose proof Hu as (_ & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc).
    split; [apply c9_hwf; auto |].
    split; [unfold Zlib.proof.roundtrip.RTHSpec.hattach_ok, is_live; rewrite if_false by auto;
            intros _; left; exact Wmode |].
    cbn [IR.h_xp IR.h_np IR.h_cp h0].
    split; [intros _ E; rewrite E in Px; exact Px |].
    split; [intros _ E; rewrite E in Pn; exact Pn |].
    intros _ E; rewrite E in Pc; exact Pc. }
  unfold is_live. rewrite if_false by auto. cbv iota. rewrite Wrap.
  change (Z.land 6 2 =? 0) with false. cbv iota.
  fold (Zlib.proof.roundtrip.RTIIface.head_live (init_live sp (su_wbits u)) (h0 u) vg Tsh (su_gxp u) (su_gnp u)
          (su_gcp u)).
  forward_call (Int.repr 1).
  Intros.
  (* statements 69-72: SMC9Tail.v *)
  assert (HT : tycontext_sub Delta_s Delta) by (unfold Delta, abbreviate; apply tycontext_sub_refl).
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS. change (Ssequence _ _) with c9_tail.
  unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
  eapply (semax_Delta_subsumption Delta_s _ _ _ _ HT).
  exact (c9_tail_ok P PN gv vh vg vc va vd u O c src ip sp PF WH Hu H0 H1 H2 H4 Pip Nd Wmode).
Qed.

(* Law deflate_roundtrip, gzip header: the body of main of harness/deflate_roundtrip.c against
   MainLib.main_core_spec Rm in main's context of the law (RTRSKit.GmI: inflate and inflateGetHeader with the
   intersections of their Spec5 and v6 specifications).  RTRMain.v with the run's end
   (rms_after_run, RTRSSeg1.rms_seg1) split: no gzip header by RTRMain.rm_rest_nohdr (Spec5, Delta_m), the gzip
   header by RTRSHdr.rms_hset1 (v6, Delta_m6), both moved to Delta_mI by tycontext_sub. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.roundtrip.RTRMain.
Require Import Zlib.proof.roundtrip.RTRSSeg1 Zlib.proof.roundtrip.RTRSHdr.
Require Zlib.proof.uncompr.URunFrame.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma rms_after_run {Espec : OracleKind} I Iend rf vR vs vt vih gv :
  api_facts I Iend -> ifacts6 -> Zlib.proof.deflate.Obligations.ob_dstream_to_end -> rf_ok Iend vR rf ->
  semax (Delta_mI I Iend) (A1 Iend rf vR vs vt vih gv) seg1 POST_b.
Proof.
  intros AF IF DE OK.
  apply rms_seg1; auto. intros z sp.
  pose proof OK as (_ & _ & _ & _ & _ & _ & _ & HH & _).
  assert (Hh : rf_hset rf = 0 \/ rf_hset rf = 1) by (destruct HH as [(A & _) | (A & _)]; auto).
  destruct Hh as [H0 | H1].
  - eapply semax_Delta_subsumption; [apply Delta_m_subI | ].
    apply Zlib.proof.roundtrip.RTRMain.rm_rest_nohdr; auto. apply (if6_base IF).
  - eapply semax_Delta_subsumption; [apply Delta_m6_subI | ].
    apply rms_hset1; auto.
Qed.

(* main's body (RTRMainSpec.rt_main_stmt with GmI and ifacts6) *)
Lemma rt_main6 (I : api_inv) (Iend : dstate -> Prop) :
  api_facts I Iend -> rt_extra I -> ifacts6 -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  semax_body (QPvarspecs p) (GmI I Iend) f_main (_main, main_core_spec Rm).
Proof.
  intros AF RX IF DE.
  start_function.
  make_func_ptr Zlib.inflate.code._zcalloc. make_func_ptr Zlib.inflate.code._zcfree.
  gather_SEP (func_ptr' _ (gv Zlib.inflate.code._zcalloc)) (func_ptr' _ (gv Zlib.inflate.code._zcfree)).
  fold (zfuncs gv).
  unfold Rm. Intros.
  assert (JS: sepalg.join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  assert (SPL: forall t q, data_at_ Tsh t q = data_at_ Ews t q * data_at_ (Share.comp Ews) t q)
    by (intros; unfold data_at_; symmetry; apply data_at_share_join; exact JS).
  rewrite (SPL (Tstruct _drun noattr) v_R), (SPL (Tstruct _z_stream_s noattr) v_s).
  Intros.
  forward_call (v_R, v_s, 0, gv).
  { unfold LawFacts.s32; rep_lia. }
  Intros ret. destruct H as [E|E]; subst ret.
  - (* deflate_run returned 0 *)
    unfold run_post. simpl. Intros.
    forward_if (PROP () LOCAL (temp _t'2 (Vint Int.one); lvar _ih t_gzhL v_ih; lvar _t t_strmL v_t;
                lvar _s t_strmL v_s; lvar _R t_drun v_R; gvars gv)
                SEP (TT; data_at_ Ews t_drun v_R * data_at_ Ews t_strmL v_s * TT;
                     data_at_ Tsh t_gzhL v_ih; data_at_ Tsh t_strmL v_t;
                     data_at_ (Share.comp Ews) t_strmL v_s; data_at_ (Share.comp Ews) t_drun v_R)).
    { forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    { forward. Exists (Int.repr 0). entailer!. rewrite !SPL. unfold t_drun, t_strmL, t_gzhL. cancel. }
    { exfalso. apply Int.one_not_zero. auto. }
  - unfold run_post. simpl. Intros init.
    destruct (Z.eqb_spec init 0) as [E0|E0].
    + (* the run succeeded *)
      subst init. Intros rf. Intros.
      forward_if (PROP () LOCAL (temp _t'2 (Vint Int.zero); lvar _ih t_gzhL v_ih; lvar _t t_strmL v_t;
                  lvar _s t_strmL v_s; lvar _R t_drun v_R; gvars gv)
                  SEP (mem_mgr gv; deflate_globals gv; run_ok_at rf v_R v_s gv;
                       zfuncs gv; data_at_ Tsh t_gzhL v_ih; data_at_ Tsh t_strmL v_t;
                       data_at_ (Share.comp Ews) t_strmL v_s; data_at_ (Share.comp Ews) t_drun v_R;
                       tables_rep Ers gv; version_lit gv; version_at gv vlit)).
      { exfalso. discriminate. }
      { unfold run_ok_at, drun_rest. Intros. forward. forward. entailer!. unfold run_ok_at, drun_rest. cancel. }
      forward_if.
      { contradiction. }
      eapply semax_seq with (Q := FF); [ | apply semax_ff ].
      unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
      unfold abbreviate in Delta. subst Delta.
      eapply semax_pre; [ | apply (rms_after_run I Iend rf v_R v_s v_t v_ih gv AF IF DE); auto ].
      unfold A1, Rm. entailer!.
    + (* deflateInit2 failed *)
      Intros rs. Intros.
      forward_if (PROP () LOCAL (temp _t'2 (Vint Int.one); lvar _ih t_gzhL v_ih; lvar _t t_strmL v_t;
                  lvar _s t_strmL v_s; lvar _R t_drun v_R; gvars gv)
                  SEP (TT; drun_rest rs (vi init) Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 v_R *
                       field_at_ Ews t_drun (DOT _h) v_R * data_at_ Ews t_strmL v_s * TT;
                       data_at_ Tsh t_gzhL v_ih; data_at_ Tsh t_strmL v_t;
                       data_at_ (Share.comp Ews) t_strmL v_s; data_at_ (Share.comp Ews) t_drun v_R)).
      { exfalso. discriminate. }
      { unfold drun_rest. Intros. forward. forward. entailer!.
        { rewrite Int.eq_false; [reflexivity | ]. intro X. apply repr_inj_signed in X; unfold LawFacts.s32 in *; rep_lia. }
        unfold drun_rest. cancel. }
      forward_if.
      { forward. Exists (Int.repr 0). entailer!.
        pose proof (proj2 (proj2 RTRRunMem.run_mem) rs (vi init) Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 v_R) as RM3.
        sep_apply RM3. rewrite !SPL. unfold t_drun, t_strmL, t_gzhL. cancel. }
      { exfalso. apply Int.one_not_zero. auto. }
Qed.

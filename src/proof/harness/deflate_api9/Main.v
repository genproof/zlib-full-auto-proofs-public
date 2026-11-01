(* Law deflate_api: the body of main of harness/deflate_api.c against MainLib.main_core_spec Rm, for ANY invariants
   with the facts of LawFacts.v: the call of deflate_run (main's locals R and s split into the Ews half given to it
   and the rest) and its test, then the parts MainChecks.v, MainTail.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit
               Zlib.proof.harness.deflate_api9.MainKit
               Zlib.proof.harness.deflate_api9.MainChecks Zlib.proof.harness.deflate_api9.MainTail.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

Lemma body_main I Iend :
  api_facts I Iend -> run_mem_ok -> Zlib.proof.deflate.Obligations.ob_dstream_to_end ->
  semax_body (QPvarspecs p) (Gmain I Iend) f_main (_main, main_core_spec Rm).
Proof.
  intros AF RM DE.
  start_function.
  unfold Rm. Intros.
  assert (JS: sepalg.join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  assert (SPL: forall t q, data_at_ Tsh t q = data_at_ Ews t q * data_at_ (Share.comp Ews) t q)
    by (intros; unfold data_at_; symmetry; apply data_at_share_join; exact JS).
  rewrite (SPL (Tstruct _drun noattr) v_R), (SPL (Tstruct _z_stream_s noattr) v_s).
  Intros.
  forward_call (v_R, v_s, 1, gv).
  { unfold s32; rep_lia. }
  Intros ret. destruct H as [E|E]; subst ret.
  - (* deflate_run returned 0 *)
    unfold run_post. simpl. Intros.
    forward_if (PROP () LOCAL (temp _t'2 (Vint Int.one); lvar _b (tarray tuchar 1) v_b;
                lvar _s (Tstruct _z_stream_s noattr) v_s; lvar _R (Tstruct _drun noattr) v_R; gvars gv)
                SEP (mem_mgr gv; deflate_globals gv; data_at_ Ews t_drun v_R * data_at_ Ews t_strmL v_s * TT;
                     data_at_ Tsh (tarray tuchar 1) v_b;
                     data_at_ (Share.comp Ews) (Tstruct _z_stream_s noattr) v_s;
                     data_at_ (Share.comp Ews) (Tstruct _drun noattr) v_R)).
    { forward. entailer!. }
    { exfalso. auto. }
    forward_if.
    { forward. Exists (Int.repr 0). entailer!. rewrite !SPL. unfold t_drun, t_strmL. cancel. }
    { exfalso. apply Int.one_not_zero. auto. }
  - unfold run_post. simpl. Intros init.
    destruct (Z.eqb_spec init 0) as [E0|E0].
    + (* the run succeeded *)
      subst init. Intros rf. Intros.
      forward_if (PROP () LOCAL (temp _t'2 (Vint Int.zero); lvar _b (tarray tuchar 1) v_b;
                  lvar _s (Tstruct _z_stream_s noattr) v_s; lvar _R (Tstruct _drun noattr) v_R; gvars gv)
                  SEP (mem_mgr gv; deflate_globals gv; run_ok_at rf v_R v_s gv;
                       data_at_ Tsh (tarray tuchar 1) v_b;
                       data_at_ (Share.comp Ews) (Tstruct _z_stream_s noattr) v_s;
                       data_at_ (Share.comp Ews) (Tstruct _drun noattr) v_R)).
      { exfalso. discriminate. }
      { unfold run_ok_at, drun_rest. Intros. forward. forward. entailer!. unfold run_ok_at, drun_rest. cancel. }
      forward_if.
      { contradiction. }
      (* the rest: the parts; main's body ends with return, so its normal postcondition is FF *)
      eapply semax_seq with (Q := FF); [ | apply semax_ff ].
      eapply semax_post with (R' := POST_m); [ | | | | ].
      all: try (intros; unfold POST_m; simpl; normalize; fail).
      { intros. subst POSTCONDITION. unfold abbreviate, POST_m. simpl. intro x. apply andp_left2.
        apply derives_refl. }
      eapply semax_pre; [ | apply (main_checks_ok I Iend rf v_R v_s v_b gv); apply main_tail_ok; auto ].
      unfold MA. entailer!.
    + (* deflateInit2 failed *)
      Intros rs. Intros.
      forward_if (PROP () LOCAL (temp _t'2 (Vint Int.one); lvar _b (tarray tuchar 1) v_b;
                  lvar _s (Tstruct _z_stream_s noattr) v_s; lvar _R (Tstruct _drun noattr) v_R; gvars gv)
                  SEP (mem_mgr gv; deflate_globals gv;
                       drun_rest rs (vi init) Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 v_R *
                       field_at_ Ews t_drun (DOT _h) v_R * data_at_ Ews t_strmL v_s * TT;
                       data_at_ Tsh (tarray tuchar 1) v_b;
                       data_at_ (Share.comp Ews) (Tstruct _z_stream_s noattr) v_s;
                       data_at_ (Share.comp Ews) (Tstruct _drun noattr) v_R)).
      { exfalso. discriminate. }
      { unfold drun_rest. Intros. forward. forward. entailer!.
        { rewrite Int.eq_false; [reflexivity | ]. intro X. apply repr_inj_signed in X; unfold s32 in *; rep_lia. }
        unfold drun_rest. cancel. }
      forward_if.
      { forward. Exists (Int.repr 0). entailer!.
        pose proof (proj2 (proj2 RM) rs (vi init) Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 v_R) as RM3.
        sep_apply RM3. rewrite !SPL. unfold t_drun, t_strmL. cancel. }
      { exfalso. apply Int.one_not_zero. auto. }
Qed.

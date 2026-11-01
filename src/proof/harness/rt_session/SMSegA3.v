(* Law rt_session (harness/rt_session.c): main's statements 47-56, deflateInit2_, deflateSetDictionary or deflateSetHeader and the deflate loop's start (SMKit.v, [segA3_stmt]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.

(* Statements 47-50 here: new_stream and deflateInit2_ on the compressor, the return when deflateInit2_ runs out
   of memory and gp_assert(code == Z_OK): with parameters in zlib.h's ranges (main's gp_assume) deflateInit2_
   returns Z_OK or Z_MEM_ERROR (SDFacts.sd_init_code), and on Z_OK the deflate invariant holds without a
   dictionary and without a header (sd_init).  The rest is SMA3Dict.a3_dict (51), SMA3Head.a3_head (52) and
   SMA3Stores.a3_stores (53-56), on the state SMA3Kit.AS.  The proof is rt_stream's (its deflateInit2_
   segment) on this main. *)
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMA3Kit.
Require Import Zlib.proof.harness.rt_session.SMA3Dict.
Require Zlib.proof.harness.rt_stream.USegAStrm.
Require Zlib.proof.harness.deflate_bound.MainInit.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac a3_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in a3_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := a3_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma sm_segA3 : segA3_stmt.
Proof.
  intros Espec J gv vh vg vc va vd u JF.
  unfold A47, segA3, POST_s.
  unfold Delta_s; simplify_func_tycontext. abbreviate_semax.
  Intros.
  match goal with Hs : su_ok u |- _ => rename Hs into OK end.
  pose proof OK as ((Hlev & Hwb & Hmem & Hstr & Hpar & _) & _).
  unfold c_locals, d_locals, lvs, lv_locals. cbn [app].
  rewrite (BoundKit.data_at__Tsh_split t_z vc).
  sep_apply (a3_strm_undef vc).
  forward_call (vc, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (USegAStrm.sa_new_stream_split vc).
  unfold Rm. rewrite a3_version.
  pose proof (fun a1 a2 a3 a4 a5 =>
    sd_init _ JF (su_level u) (su_wbits u) (su_mem u) (su_strategy u) a1 a2 a3 a4 a5 zrst0 Hlev Hwb Hmem Hstr)
    as FIN.
  forward_call (vc, su_level u, 8, su_wbits u, su_mem u, su_strategy u, gv ___stringlit_rt_session_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { cancel. }
  { unfold rs32 in *.
    split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI; change (112 =? 112) with true in HI.
  Intros msgv'.
  pose proof (sd_init_code _ JF _ _ _ _ _ _ _ _ _ _ _ _ _ Hpar HI) as Hcode.
  destruct Hcode as [Hc | Hc]; subst code.
  2:{ (* deflateInit2_ ran out of memory (no state): the locals back, return 0 *)
    destruct (Zlib.proof.harness.deflate_bound.MainInit.pi_init_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI)
      as [Hc | [Hos _]]; [discriminate Hc | subst os].
    forward_if.
    2:{ exfalso. match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end. }
    Intros st za zf op dt.
    sep_apply (USegAStrm.sa_fields_back vc nullval (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_total_in z') Vundef)
                 (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_total_out z') Vundef) msgv'
                 (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_adler z') Vundef) (vi 0) nullval (vi 0) st za zf op dt).
    sep_apply (a3_rejoin vc).
    forward. Exists (Int.repr 0). entailer!.
    unfold hobj, graw.
    sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh).
    sep_apply (data_at_data_at_ Tsh t_g (gval u) vg).
    cancel. }
  destruct (proj2 (FIN _ _ _ _ _) _ _ _ HI eq_refl) as (_ & s & -> & HJ).
  forward_if.
  { exfalso. match goal with H : Int.repr _ = _ |- _ => inversion H end. }
  forward. forward_call (Int.one).
  destruct (sd_range _ JF _ _ _ _ _ _ _ _ _ _ HJ) as (Rtin & Rtout & Radl & _).
  eapply semax_pre;
    [ | exact (a3_dict Espec J gv vh vg vc va vd u
                 (mkCS s nullval 0 (z_total_in z') nullval 0 (z_total_out z') msgv' (z_adler z')) (z_msg z') JF) ].
  unfold AS, cstream, srest, api_fields, Rm, c_locals, d_locals, lvs, lv_locals.
  cbn [cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
  change (Z_OK =? Z_OK) with true in *. change (Z_OK =? Z_VERSION_ERROR) with false in *. cbn [rfv] in *.
  unfold reset_fields. rewrite <- a3_version.
  entailer!.
  unfold u32_ok, u64_ok. rep_lia.
Qed.

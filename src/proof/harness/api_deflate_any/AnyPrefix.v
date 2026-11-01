(* Law api_deflate_any: main's body up to the loop (AnyKit.any_prefix_stmt): the four parameters and their check
   (deflate_params_ok, gp_assume), the data, new_stream, deflateInit2 and the tests of its code,
   read = left = finishing = 0, and the loop invariant J_at.  main's two locals go back to the law's compspecs at
   each return (AnyAt.any_strm_cs, AnyAt.any_at_cs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.harness.api_deflate_any.AnyCodes.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.proof.harness.api_deflate_any.AnyAt.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which can take minutes on main's
   LOCAL list (it holds the temporaries _out and _out_size); the same list built syntactically, comparing the
   identifiers by vm_compute *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* new_stream's postcondition back to the local's Ews half (main returns before deflateInit2) *)
Lemma any_new_back (p : val) :
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p
  |-- data_at_ Ews t_strm p.
Proof. rewrite DetMem2.det_strm_cs. apply data_at_data_at_. Qed.

(* the two halves of the local back together *)
Lemma any_join (p : val) :
  data_at_ Ews t_strm p * data_at_ BoundKit.Ecomp t_strm p |-- data_at_ Tsh t_strm p.
Proof. rewrite (BoundKit.data_at__Tsh_split t_strm p). apply derives_refl. Qed.

Lemma any_prefix : any_prefix_stmt.
Proof.
  intros Espec v gv ap [J AF] K.
  unfold PRE0, main_body, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros n1.
  forward_call tt. Intros n2.
  forward_call tt. Intros n3.
  forward_call tt. Intros n4.
  (* the four (int) casts: each parameter is the signed value of the drawn u32 *)
  rewrite <- (Int.repr_signed (Int.repr n1)), <- (Int.repr_signed (Int.repr n2)),
    <- (Int.repr_signed (Int.repr n3)), <- (Int.repr_signed (Int.repr n4)).
  pose proof (Int.signed_range (Int.repr n1)). pose proof (Int.signed_range (Int.repr n2)).
  pose proof (Int.signed_range (Int.repr n3)). pose proof (Int.signed_range (Int.repr n4)).
  forget (Int.signed (Int.repr n1)) as level. forget (Int.signed (Int.repr n2)) as wbits.
  forget (Int.signed (Int.repr n3)) as mem. forget (Int.signed (Int.repr n4)) as strategy.
  clear n1 n2 n3 n4 H H0 H1 H2.
  (* gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy)): the parameters are in zlib.h's ranges,
     the ones for which deflateInit2_ returns Z_OK or Z_MEM_ERROR (DetFacts2.df2_init) *)
  forward_call (level, wbits, mem, strategy).
  forward_call (if LS.deflate_params_valid level wbits mem strategy then Int.one else Int.zero).
  { destruct (LS.deflate_params_valid level wbits mem strategy); entailer!. }
  Intros.
  assert (Hv : Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy = true).
  { rewrite <- Zlib.proof.harness.laws_session.Facts.deflate_params_valid_ok.
    destruct (LS.deflate_params_valid level wbits mem strategy); [reflexivity | contradiction]. }
  forward_call 9223372036854775807.
  Intros n.
  forward_call (n, gv).
  Intros vret. destruct vret as [datap bs]. cbn [fst snd] in *.
  rewrite DetMem2.det_token_cs, DetMem2.det_bytes_cs.
  destruct (eq_dec datap nullval) as [Pd | Pd].
  { (* no data: return 0 *)
    subst datap. forward_if.
    { rewrite any_strm_cs, any_at_cs. forward. Exists (Int.repr 0). entailer!. }
    { contradiction. } }
  forward_if.
  { subst datap. contradiction. }
  assert_PROP (isptr datap) as Pdp by entailer!.
  (* new_stream(&strm) on the Ews half of the local *)
  rewrite (BoundKit.data_at__Tsh_split t_strm v).
  sep_apply (DetMem2.det_strm_undef v).
  forward.
  forward_call (v, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  (* deflateInit2_(&strm, level, 8, window_bits, mem_level, strategy, "1.3.2", sizeof(z_stream)) on the stream
     made by new_stream; the call is defined for the parameters drawn (DetFacts2.df2_init) *)
  sep_apply (DK.det_new_stream_split v).
  unfold version_at.
  assert (S : s32 level /\ s32 wbits /\ s32 mem /\ s32 strategy) by (unfold s32; rep_lia).
  destruct S as (S1 & S3 & S4 & S5).
  pose proof (fun a1 a2 a3 a4 a5 => df2_init _ (ay_det _ AF) level wbits mem strategy a1 a2 a3 a4 a5 zrst0
                S1 S3 S4 S5) as FIN.
  forward_call (v, level, 8, wbits, mem, strategy, gv vlit, Ers, [49; 46; 51; 46; 50; 0], 112,
                nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|].
    split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI. change (112 =? 112) with true in HI.
  Intros msgv.
  destruct (proj2 (FIN a1 a2 a3 a4 a5) _ _ _ HI) as (Hc & Hse & Hok).
  clear FIN.
  (* if (code == Z_MEM_ERROR) return 0 *)
  forward_if.
  { (* the stream back to the local, both locals at the law's compspecs *)
    sep_apply (DK.det_init_back os code v gv). sep_apply (any_join v).
    rewrite any_strm_cs, any_at_cs.
    forward. Exists (Int.repr 0). entailer!. }
  (* the parameters are valid (gp_assume): no Z_STREAM_ERROR, so Z_OK *)
  assert (Hcode : code = Z_OK).
  { assert (code <> Z_STREAM_ERROR) by (intro X; apply Hse in X; congruence).
    assert (code <> Z_MEM_ERROR).
    { intro X. subst code. match goal with H : Int.repr _ <> Int.neg _ |- _ => apply H; reflexivity end. }
    destruct Hc as [?|[?|?]]; [assumption | contradiction | contradiction]. }
  subst code.
  (* gp_assert(code == Z_OK) *)
  forward. forward_call (Int.one).
  destruct (Hok eq_refl) as [(s & -> & Htin & Htout & HJ) _]. clear Hok Hse Hc.
  pose proof (df2_adler _ (ay_det _ AF) _ _ _ _ HJ) as Had.
  change (Z_OK =? Z_VERSION_ERROR) with false in *. change (Z_OK =? Z_OK) with true. unfold rfv.
  rewrite Htin, Htout in *.
  rewrite !dstream_sp_eq. Intros sp.
  (* read = left = finishing = 0, then the loop *)
  forward. forward. forward.
  eapply semax_pre; [| apply (K J n bs datap sp (mkLS s None 0 0 0 (z_adler z') (z_msg z') msgv))].
  unfold J_at, J_ok, setup_ok, J_loc, J_sep, fin_flag, DK.shead, DK.strm_at, api_fields;
    cbn [ls_s ls_fin ls_read ls_left ls_tout ls_adler ls_msg ls_msgv].
  Exists nullval 0 nullval 0.
  change (bytes_rep bs) with (map vi bs).
  entailer!.
  - unfold bytes, is_bytes, u64r, u32_ok, u64_ok in *. split; [split; [| rep_lia] |].
    + eapply Forall_impl; [| exact H2]. intros b Hb. simpl in Hb. rep_lia.
    + rep_lia.
  - unfold reset_fields. cancel.
Qed.

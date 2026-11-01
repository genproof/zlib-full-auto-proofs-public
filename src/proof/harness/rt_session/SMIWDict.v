(* Law rt_session, main's inflate loop without a header (SMLoopIW.v): the Z_NEED_DICT branch at the end of the
   body, from ICd_w to the loop's test IC_w:
   if (code == Z_NEED_DICT) { gp_assert(with_dict && window_bits > 0 && !asked); asked = 1;
     code = inflateSetDictionary(&decompressor, dict_copy, (uInt) dict_len);
     if (code == Z_MEM_ERROR) return 0; gp_assert(code == Z_OK); }
   With Z_NEED_DICT the session is a zlib one with a dictionary and asked is false (SMIWKit.cfacts, from
   SIFacts.si_call; SMIWKit.zdict_flags gives with_dict and window_bits > 0); inflateSetDictionary
   (SpecW.inflateSetDictionary_specW on dict_copy) returns Z_OK with the invariant P and asked = true, or
   Z_MEM_ERROR (SIFacts.si_setdict). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMIWKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* a branch that cannot be taken *)
Ltac infeas := exfalso; first [ match goal with H : ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H : _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H : Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Lemma dict_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip r l :
  ses_ifacts (fun _ => True) P PN ->
  semax Delta_W (ICd_w gv vh vg vc va vd P PN u O c src ip r l) dictI_w
    (RI_w gv vh vg vc va vd P PN u O c src ip).
Proof.
  intros SF.
  unfold Delta_W; simplify_func_tycontext.
  unfold dictI_w, ICd_w, RI_w, iw_props, iw_rest, iw_locals, c_locals, d_locals, lvs, lv_locals. simpl app.
  Intros. unfold POST_s.
  apply semax_seq_skip. forward_if (IC_w gv vh vg vc va vd P PN u O c src ip).
  2: { (* another code: the loop's test with the same state *)
       forward. unfold IC_w, ICe_w. Exists r l.
       unfold iw_props, iw_rest, iw_locals, c_locals, d_locals, lvs, lv_locals. simpl app. entailer!.
       destruct H5 as [-> | [-> | [-> | ->]]]; auto. infeas. }
  assert (E : r = Z_NEED_DICT) by (destruct H5 as [-> | [-> | [-> | ->]]]; try reflexivity; infeas).
  subst r.
  pose proof H6 as (Hgeo & _ & HN & _). destruct (HN eq_refl) as (HPN & Hask & Hzd).
  destruct (zdict_flags u H Hzd) as (Hwd & Hwb).
  rewrite Hwd, Hask. simpl Z.b2z.
  forward_if (temp _t'82 (vi 1)).
  { forward. entailer!. pose proof H as ((_ & Hw & _) & _). unfold rs32 in Hw. unfold rts_iw in *. unfold Int.lt.
    rewrite !Int.signed_repr by (destruct (su_wbits u =? 8); rep_lia). destruct zlt; [reflexivity | lia]. }
  { infeas. }
  forward_if (temp _t'83 (vi 1)).
  { forward. entailer!. }
  { infeas. }
  forward_call (Int.one).
  forward.
  assert (Hih : i_head (l_s (il_L l)) = false) by (eapply (si_nshape _ _ _ SF); eauto).
  unfold head_mem. rewrite Hih.
  assert_PROP (live_ok (il_L l)) as Lo by (rewrite istreamA_unfold; entailer!).
  assert_PROP (isptr vd) as Pvd by entailer!.
  pose proof H as (DK & Pdcp & _).
  pose proof DK as (_ & _ & _ & _ & _ & _ & Hdl & Hdb & _).
  unfold dcopy, bobj. rewrite <- bytes_i, <- tok_i.
  rewrite <- (istreamA_opt_ptr gv Tsh vd) by auto.
  forward_call (gv, Tsh, vd, il_z l, Vundef, Some (il_L l), Ews, su_dcp u, 0, Zlength (su_dict u),
                map vi (su_dict u), su_dict u, true).
  { entailer!. simpl. unfold vl. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity. }
  { cancel. }
  { rewrite Zlength_map. split; [reflexivity | ]. unfold byte_vals. rewrite sublist_same by (rewrite ?Zlength_map; lia).
    split; [reflexivity | ]. unfold bytes_ok. eapply Forall_impl; [ | exact Hdb]. simpl. intros; rep_lia. }
  Intros vret. destruct vret as [aok winp]. simpl fst in *; simpl snd in *.
  unfold on_live in *. rewrite is_live_ptr in * by auto.
  assert (Edict : sc_dict (scase_of u) = su_dict u) by (unfold scase_of, sdict; simpl; rewrite Hwd; reflexivity).
  pose proof (si_setdict _ _ _ SF (scase_of u) (su_data u) O src (il_pos l) (il_out l) (il_L l) (zf_tout (il_z l))
                (il_z l) aok winp I H1 H4 HPN Lo eq_refl) as SD.
  rewrite Edict in SD. cbv zeta in SD.
  destruct (setdict_f (su_dict u) aok winp (il_z l) (il_L l)) as [[r' z'] L'] eqn:Esd.
  unfold fst3, snd3, thd3 in *. cbn [fst snd] in *.
  destruct SD as (Hr' & Hok).
  forward_if.
  { (* Z_MEM_ERROR: return 0, the locals back to the stack frame *)
    forward. Exists (Int.repr 0).
    sep_apply (a_frame_opt gv Tsh vd z' Vundef (Some L')); auto. sep_apply (cstream_frame gv vc (ghp vh u) c).
    sep_apply (hobj_frame vh u). sep_apply (graw_frame vg u). entailer!. }
  assert (r' = Z_OK) by (destruct Hr' as [-> | ->]; [reflexivity | infeas]).
  subst r'. destruct (Hok eq_refl) as (Ez & Hsw & HP). subst z'.
  forward_call (Int.one).
  assert (Hih' : i_head (l_s L') = false)
    by (rewrite (si_shape _ _ _ SF _ _ _ _ _ _ _ _ _ I HP), sgh_none by auto; reflexivity).
  unfold IC_w, ICe_w. Exists Z_OK (mkIL (il_pos l) (il_out l) true L' (il_z l)).
  cbn [il_pos il_out il_asked il_L il_z].
  rewrite head_opt_emp by auto.
  unfold iw_props, iw_rest, iw_locals, c_locals, d_locals, lvs, lv_locals. simpl app.
  rewrite istreamA_opt_ptr by auto.
  unfold dcopy, bobj. rewrite <- bytes_i, <- tok_i.
  entailer!.
  split; [ | rewrite Hwd; reflexivity].
  unfold cfacts. cbn [il_pos il_out il_asked il_L il_z].
  split; [exact Hgeo | ]. split; [intros _; split; assumption | ].
  split; intros E; discriminate E.
Qed.

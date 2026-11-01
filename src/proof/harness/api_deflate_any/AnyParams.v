(* Law api_deflate_any: maybe deflateParams (AnyKit.any_params_stmt), only before Z_FINISH, and the check of its
   code: Z_STREAM_ERROR exactly for an invalid level or strategy (AnyCodes.params_bad, params_codes), else Z_OK or
   Z_BUF_ERROR; the stream as C_at after the call (DetFacts2.df2_params). *)
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
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Zlib.proof.harness.api_deterministic.DetParams2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Module DK := Zlib.proof.harness.api_deterministic.DetKit2.
Module DP := Zlib.proof.harness.api_deterministic.DetParams2.

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

(* the output space after deflateParams wrote [O] at its start: its other bytes are still those it was made with *)
Lemma any_ovals_after (bs O : list Z) :
  map vi O ++ sublist (Zlength O) (Zlength (map vi bs)) (map vi bs) = map vi (ovals bs O).
Proof. unfold ovals. rewrite map_app, Zlength_map, sublist_map. reflexivity. Qed.

(* the comparisons of main's test [valid] after [forward]: decide each one *)
Ltac cmp_tac :=
  repeat match goal with H : context [Int.signed (Int.repr ?k)] |- _ =>
    rewrite (Int.signed_repr k) in H by rep_lia end;
  repeat match goal with H : typed_true _ _ |- _ => revert H | H : typed_false _ _ |- _ => revert H end;
  repeat match goal with
         | |- context [zlt ?a ?b] => destruct (zlt a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
         end;
  simpl; intros; try discriminate; try reflexivity; lia.

(* the end of the call's branch: C_at for the configuration [c] after the call *)
Ltac params_end :=
  match goal with c := mkCS _ _ _ _ _ _ _ |- _ =>
    Exists c; unfold C_sep, DK.out_at, DK.strm_at, BoundKit.obj, c;
    cbn [cs_s cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv] end;
  match goal with Hgz : d_gzhead ?s = None |- _ => rewrite (DP.dp_hdr_none s) by exact Hgz end;
  match goal with |- context [DP.dp_tok_rest ?r ?q] => rewrite (DP.dp_tok_split r q) end;
  rewrite any_ovals_after.

Lemma any_params : any_params_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls ci HK.
  (* the call (or none) ends in C_at for some configuration; the rest is the continuation *)
  unfold lsuf9.
  eapply semax_seq' with (P' := EX c : cstate, C_at J n data datap v sp gv ap ls ci c).
  2: { apply extract_exists_pre; intro c. apply HK. }
  clear HK.
  unfold C_at, B_loc.
  Intros.
  abbreviate_semax.
  apply semax_if_seq.
  forward_if.
  2: { forward. forward_if. { contradiction. } forward. Exists (c0 ls). entailer!. }
  forward_call tt. Intros b.
  forward.
  forward_if.
  2: { forward. Exists (c0 ls). entailer!. }
  rewrite <- !seq_assoc. forward_call tt. Intros lv. forward.
  rewrite <- !seq_assoc. forward_call tt. Intros st. forward.
  rewrite <- !seq_assoc.
  pose proof H as [[AF [Hn [Hlen [Hbytes Hdp]]]] [HJ [Hrd [Hlft [_ [Htout Hm]]]]]].
  pose proof H0 as (Htk & Hrt & Hfl & Hfin & Hroom & Hbsl & Hbsb & Pp & Po & Pb).
  (* finishing = 0: no Z_FINISH yet *)
  assert (Hf : ls_fin ls = None).
  { destruct (ls_fin ls) eqn:E; auto. unfold fin_flag in H2.
    exfalso. exact (Int.one_not_zero H2). }
  rewrite Hf in HJ.
  pose proof (df2_adler J (ay_det J AF) _ _ _ _ HJ) as Had.
  destruct (ay_live J AF _ _ _ _ HJ) as (Hbad & Hgz & Hst).
  set (level := Int.signed (Int.repr lv)).
  set (strategy := Int.signed (Int.repr st)).
  assert (Hlv : Vint (Int.repr lv) = vi level) by (unfold level, vi; rewrite Int.repr_signed; reflexivity).
  assert (Hsv : Vint (Int.repr st) = vi strategy) by (unfold strategy, vi; rewrite Int.repr_signed; reflexivity).
  assert (Hinb : Zlength (ci_inb data ls ci) = ci_take ci)
    by (unfold ci_inb; rewrite Zlength_sublist; lia).
  assert (Hinbb : bytes (ci_inb data ls ci)) by (apply Forall_sublist; auto).
  destruct (df2_params J (ay_det J AF) None (ls_s ls) (ls_read ls) (ls_adler ls) (ci_inb data ls ci) 0 (ci_room ci)
              (ls_tout ls) level strategy (ls_msg ls))
    as (s' & z' & code & Hrun & Hcall & HJ');
    try solve [auto | unfold level, strategy, s32; rep_lia | rewrite Hinb; lia | lia | intros; discriminate].
  rewrite Hinb, Z.sub_0_r in Hrun.
  unfold C_sep, c0, DK.out_at, DK.strm_at, BoundKit.obj.
  cbn [cs_s cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv].
  rewrite Zlength_nil, !Z.sub_0_r, !Z.add_0_r.
  rewrite (isptr_offset_val_zero (ci_out ci) Po).
  rewrite (DP.dp_tok_split (ci_room ci) (ci_out ci)).
  replace (ovals (ci_bs ci) []) with (ci_bs ci) by (unfold ovals; rewrite Zlength_nil, app_nil_l, sublist_same by lia; reflexivity).
  flatten_sepcon_in_SEP.
  rewrite Hlv, Hsv.
  forward_call (Some (ls_s ls), v, nullval, sp, (Ews, nullval, nullval, nullval), ci_piece ci, Ews,
                ci_inb data ls ci, 0, ci_take ci, ls_read ls,
                ci_out ci, map vi (ci_bs ci),
                DP.dp_wtok (ci_room ci), ls_tout ls, ls_msgv ls, ls_msg ls, ls_adler ls, level, strategy,
                (Some s', z', code), gv).
  { rewrite (DP.dp_hdr_none (ls_s ls)) by auto. rewrite Hinb, Zlength_map, Hbsl. cancel. }
  { rewrite Zlength_map, Hbsl.
    split; [| split; [| split; [| split]]].
    - intros; apply DP.dp_wtok_ok; lia.
    - unfold s32_ok, level; rep_lia.
    - unfold s32_ok, strategy; rep_lia.
    - unfold strm_ranges, zmk; simpl. rewrite Zlength_nil, Hinb. unfold bytes in Hinbb.
      unfold u32_ok, u64_ok, u64r in *. repeat split; auto; try rep_lia.
    - exists (fun f => f); split; [apply ef_ok_id |]. unfold on_state, c_on_state.
      rewrite DModel5.c_deflateParams_g_id. change (zmk ?a ?b ?c ?d ?e ?f ?g ?h) with (zcall a b c d e f g h).
      rewrite Hrun. reflexivity. }
  cbn [fst snd]. Intros msgv'.
  (* the configuration after the call: its stream fields and output *)
  pose proof Hcall as (Hzin & Hnx & Hav & Htin & Haout & Hzout & Htot & Hzb).
  rewrite Hinb in Hnx, Hav.
  set (c := mkCS s' (z_next_in z') (z_out z') (z_total_out z') (z_adler z') (z_msg z') msgv').
  assert (Hcs : cs_ok J ls ci c).
  { unfold cs_ok, c. cbn [cs_s cs_nin cs_out cs_tout cs_adler cs_msg cs_msgv]. rewrite Hf.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - rewrite Htin in HJ'. replace (ls_read ls + (z_next_in z' - 0)) with (ls_read ls + z_next_in z') in HJ'
        by lia. exact HJ'.
    - lia.
    - lia.
    - exact Hzb.
    - congruence.
    - rewrite Htot. unfold u64r, u64. pose proof (Z.mod_pos_bound (ls_tout ls + (ci_room ci - z_avail_out z'))
        18446744073709551616 ltac:(lia)). lia.
    - auto. }
  (* the code: Z_OK or Z_BUF_ERROR for valid parameters on the live stream, else Z_STREAM_ERROR *)
  assert (Hcode : (-1 <= level <= 9 /\ 0 <= strategy <= 4 -> code = Z_OK \/ code = Z_BUF_ERROR) /\
                  (~ (-1 <= level <= 9 /\ 0 <= strategy <= 4) -> code = Z_STREAM_ERROR)).
  { split; intros Hv.
    - destruct Hv as [Hv1 Hv2]. exact (AnyCodes.params_codes _ _ level strategy _ _ _ Hbad (Hst eq_refl) ltac:(lia) ltac:(lia) Hrun).
    - rewrite AnyCodes.params_bad in Hrun by exact Hv. congruence. }
  forward.
  rewrite <- !seq_assoc.
  forward_if (temp _t'24 (Val.of_bool ((-1 <=? level) && (level <=? 9)))).
  { forward. entailer!. cmp_tac. }
  { forward. entailer!. cmp_tac. }
  forward_if (temp _t'25 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (0 <=? strategy)))).
  { forward. entailer!. cmp_tac. }
  { forward. entailer!. cmp_tac. }
  forward_if (temp _t'26 (Val.of_bool ((-1 <=? level) && (level <=? 9) && (0 <=? strategy) && (strategy <=? 4)))).
  { forward. entailer!. cmp_tac. }
  { forward. entailer!. cmp_tac. }
  forward.
  (* the test [valid] decides the code *)
  destruct (((-1 <=? level) && (level <=? 9) && (0 <=? strategy) && (strategy <=? 4))%bool) eqn:Ev.
  - assert (Hok : code = Z_OK \/ code = Z_BUF_ERROR)
      by (apply Hcode; rewrite !andb_true_iff, !Z.leb_le in Ev; lia).
    forward_if (temp _t'27 (vi 1)).
    { forward_if; repeat forward; entailer!; destruct Hok as [-> | ->]; try reflexivity.
      match goal with H : Int.repr _ <> Int.repr _ |- _ => exfalso; apply H; reflexivity end. }
    { match goal with H : Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end. }
    forward_call (Int.one).
    params_end. rewrite Zlength_map, Hbsl, Hinb.
    replace (ci_take ci - z_next_in z') with (z_avail_in z') by lia.
    replace (ls_read ls + z_next_in z') with (z_total_in z') by lia.
    replace (ci_room ci - Zlength (z_out z')) with (z_avail_out z') by lia.
    entailer!.
  - assert (Hok : code = Z_STREAM_ERROR)
      by (apply Hcode; rewrite !andb_false_iff, !Z.leb_gt in Ev; lia).
    forward_if (temp _t'27 (vi 1)).
    { match goal with H : Int.zero <> Int.zero |- _ => exfalso; apply H; reflexivity end. }
    { forward. entailer!; rewrite Hok; reflexivity. }
    forward_call (Int.one).
    params_end. rewrite Zlength_map, Hbsl, Hinb.
    replace (ci_take ci - z_next_in z') with (z_avail_in z') by lia.
    replace (ls_read ls + z_next_in z') with (z_total_in z') by lia.
    replace (ci_room ci - Zlength (z_out z')) with (z_avail_out z') by lia.
    entailer!.
Qed.

(* Part sl_here of the main loop of inflate_table (seg_loop_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.seg_loop_defs.

#[local] Existing Instance Inftrees.CS.

Lemma sl_here_work (l: list Z) n i : 0 <= i < Zlength l ->
  Znth i (zs_rep l ++ Zrepeat Vundef n) = Vint (Int.repr (Znth i l)).
Proof.
intros. rewrite app_Znth1 by (unfold zs_rep; list_solve). unfold zs_rep. rewrite Znth_map by lia. reflexivity.
Qed.

Lemma sl_here_ze8 x : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_here_ze16 x : 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_here_zs (l: list Z) i : 0 <= i < Zlength l -> Znth i (zs_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold zs_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sl_here_bound l b i : forallb (fun x => andb (0 <=? x) (x <? b)) l = true ->
  0 <= i < Zlength l -> 0 <= Znth i l < b.
Proof.
intros F I. rewrite forallb_forall in F. specialize (F (Znth i l) (Znth_In _ _ I)).
apply andb_prop in F as [F1 F2]. rewrite Z.leb_le in F1. rewrite Z.ltb_lt in F2. lia.
Qed.

Ltac sl_here_post E :=
  destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; cbn [RA_normal];
  entailer!;
  rewrite E; unfold entry_rep; cbn [e_op e_bits e_val];
  rewrite ?Int.sub_signed, ?sl_here_ze8, ?sl_here_ze16 by rep_lia;
  unfold itables; cancel.

Lemma sl_here_ok : loop_facts -> sl_here_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (SSO & ROO & RKO & _).
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs] in WF.
destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold A_loop, SL_here, sl_props, sl_locs, sl_K, sl_sep, it_sep, params_locs, count_at, work_sorted,
  sl_here_e, base_v, extra_v, it_mx, it_root;
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold sl_here.
abbreviate_semax.
Intros.
assert (AO: acc_ok type lens req (Zlength old)) by (unfold acc_ok; auto).
destruct IN as (TY & NC & LR & RQ).
destruct (RKO _ _ _ _ _ _ AO H2) as (IT & SK).
destruct (SSO lens LR) as (SL & SF).
destruct IT as (IS & IL & ID & _).
assert (SY: 0 <= Znth (s_sym s) (sorted_syms lens) < Zlength lens).
{ eapply Forall_forall in SF; [apply SF | apply Znth_In; lia]. }
assert (MC: max_codes type <= 288) by (unfold max_codes; repeat (destruct (_ =? _)); lia).
set (sy := Znth (s_sym s) (sorted_syms lens)) in *.
forward.
forward.
{ entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
rewrite sl_here_work by lia. fold sy.
assert (type = CODES \/ type = LENS \/ type = DISTS) as [-> | [-> | ->]] by (unfold CODES, LENS, DISTS; lia);
cbn [Z.eqb Pos.eqb LENS DISTS CODES match_of max_codes] in NC |- *.
- forward_if.
  + forward. forward.
    { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_here_work by lia. fold sy.
    forward.
    assert (E: sym_entry CODES sy (s_len s - s_drop s) = mkE 0 (s_len s - s_drop s) sy).
    { unfold sym_entry; cbn [match_of CODES Z.eqb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    sl_here_post E.
  + forward.
    { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_here_work by lia. fold sy.
    forward_if.
    { lia. }
    forward. forward.
    assert (E: sym_entry CODES sy (s_len s - s_drop s) = mkE 96 (s_len s - s_drop s) 0).
    { unfold sym_entry; cbn [match_of CODES Z.eqb].
      rewrite (proj2 (Z.ltb_ge _ _)), (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
    sl_here_post E.
- unfold itables. Intros.
  forward_if.
  + forward. forward.
    { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_here_work by lia. fold sy.
    forward.
    assert (E: sym_entry LENS sy (s_len s - s_drop s) = mkE 0 (s_len s - s_drop s) sy).
    { unfold sym_entry; cbn [match_of LENS CODES Z.eqb Pos.eqb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    sl_here_post E.
  + forward.
    { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_here_work by lia. fold sy.
    forward_if.
    * forward.
      { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_work by lia. fold sy.
      assert (EB: 0 <= Znth (sy - 257) lext < 256) by (apply sl_here_bound; [reflexivity | cbn; lia]).
      assert (BB: 0 <= Znth (sy - 257) lbase < 65536) by (apply sl_here_bound; [reflexivity | cbn; lia]).
      forward.
      { rewrite sl_here_zs by (cbn; lia). entailer!. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_zs by (cbn; lia).
      forward.
      forward.
      { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_work by lia. fold sy.
      forward.
      { rewrite sl_here_zs by (cbn; lia). entailer!. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_zs by (cbn; lia).
      forward.
      assert (E: sym_entry LENS sy (s_len s - s_drop s) =
                 mkE (Znth (sy - 257) lext) (s_len s - s_drop s) (Znth (sy - 257) lbase)).
      { unfold sym_entry; cbn [match_of extra_of base_of LENS DISTS CODES Z.eqb Pos.eqb].
        rewrite (proj2 (Z.ltb_ge _ _)), (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
      sl_here_post E.
    * forward. forward.
      assert (E: sym_entry LENS sy (s_len s - s_drop s) = mkE 96 (s_len s - s_drop s) 0).
      { unfold sym_entry; cbn [match_of LENS CODES Z.eqb Pos.eqb].
        rewrite (proj2 (Z.ltb_ge _ _)), (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
      sl_here_post E.
- unfold itables. Intros.
  forward_if.
  { lia. }
  forward.
  { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite sl_here_work by lia. fold sy.
  forward_if.
  2: { lia. }
  forward.
  { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rewrite sl_here_work by lia. fold sy.
  assert (EB: 0 <= Znth (sy - 0) dext < 256) by (apply sl_here_bound; [reflexivity | cbn; lia]).
  assert (BB: 0 <= Znth (sy - 0) dbase < 65536) by (apply sl_here_bound; [reflexivity | cbn; lia]).
  pose proof EB as EB'. pose proof BB as BB'. rewrite Z.sub_0_r in EB', BB'.
      forward.
      { rewrite sl_here_zs by (cbn; lia). entailer!. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_zs by (cbn; lia).
      forward.
      forward.
      { entailer!. rewrite sl_here_work by lia. simpl. fold sy. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_work by lia. fold sy.
      forward.
      { rewrite sl_here_zs by (cbn; lia). entailer!. rewrite ?Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite sl_here_zs by (cbn; lia).
      forward.
      assert (E: sym_entry DISTS sy (s_len s - s_drop s) =
                 mkE (Znth sy dext) (s_len s - s_drop s) (Znth sy dbase)).
      { unfold sym_entry; cbn [match_of extra_of base_of LENS DISTS CODES Z.eqb Pos.eqb].
        rewrite (proj2 (Z.ltb_ge _ _)), (proj2 (Z.leb_le _ _)) by lia. rewrite Z.sub_0_r. reflexivity. }
      sl_here_post E.
Qed.

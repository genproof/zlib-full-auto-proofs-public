(* Part sl_cnt of the main loop of inflate_table (seg_loop_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.seg_loop_defs.

#[local] Existing Instance Inftrees.CS.
#[local] Arguments counts : simpl never.

Lemma sl_cnt_zs (l: list Z) i : 0 <= i < Zlength l -> Znth i (zs_rep l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold zs_rep. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sl_cnt_work (l: list Z) n i : 0 <= i < Zlength l ->
  Znth i (zs_rep l ++ Zrepeat Vundef n) = Vint (Int.repr (Znth i l)).
Proof.
intros. rewrite app_Znth1 by (unfold zs_rep; list_solve). apply sl_cnt_zs; auto.
Qed.

Lemma sl_cnt_dec c : 1 <= c <= 288 ->
  Int.zero_ext 16 (Int.sub (Int.repr c) (Int.repr 1)) = Int.repr (c - 1).
Proof.
intros. rewrite Int.sub_signed, !Int.signed_repr by rep_lia.
apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma sl_cnt_ze16 x : 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma sl_cnt_upd (l: list Z) i x : 0 <= i < Zlength l ->
  upd_Znth i (zs_rep l) (Vint (Int.repr x)) = zs_rep (upd_Znth i l x).
Proof. intros. unfold zs_rep. rewrite <- (upd_Znth_map (fun x => Vint (Int.repr x))). reflexivity. Qed.

Lemma sl_cnt_step_brk (X: itctx) (s: state) root mx :
  st_c s = 0 -> s_len s = mx ->
  step (c_type X) (c_lens X) (sorted_syms (c_lens X)) root mx s = Break (sl_brk X s).
Proof.
intros C0 LM. subst mx.
unfold step, sl_brk, sl_t1, sl_here_e, st_huff', st_cnt', st_c in *.
rewrite C0, !Z.eqb_refl. reflexivity.
Qed.

Lemma sl_cnt_ok : loop_facts -> sl_cnt_stmt.
Proof.
intros LF Espec X s WF.
destruct LF as (SSO & ROO & RKO & RRO & _ & _ & _ & RFO).
destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb vh vc vo].
unfold it_wf in WF; cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs] in WF.
destruct WF as (SHg & SHl & SH & IN & OLD & CAP).
unfold SL_huff, SL_cnt, sl_props, sl_locs, sl_K, sl_sep, params_locs, count_at, work_sorted,
  base_v, extra_v, it_mx, it_root;
cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs].
unfold Delta_it. simplify_func_tycontext.
unfold sl_cnt.
abbreviate_semax.
Intros.
assert (AO: acc_ok type lens req (Zlength old)) by (unfold acc_ok; auto).
destruct (RKO _ _ _ _ _ _ AO H2) as (IT & SK).
set (X := {| c_type := type; c_lens := lens; c_req := req; c_old := old; c_gv := gv; c_shg := shg;
             c_shl := shl; c_sh := sh; c_pl := pl; c_pw := pw; c_ptab := ptab; c_pt := pt; c_pb := pb;
             c_here := vh; c_count := vc; c_offs := vo |}) in *.
destruct IT as (IS & IL & _ & _ & _ & _ & _ & _ & _ & _ & ZC & FC & C1 & ZT).
assert (CB: 1 <= Znth (s_len s) (s_cnt s) <= 288).
{ split; [lia|]. eapply Forall_forall in FC; [apply FC | apply Znth_In; lia]. }
forward.
{ entailer!. rewrite sl_cnt_zs by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
rewrite sl_cnt_zs by lia.
forward. forward.
rewrite !(sl_cnt_dec _ CB). rewrite sl_cnt_ze16 by lia.
rewrite sl_cnt_upd by lia.
change (upd_Znth (s_len s) (s_cnt s) (Znth (s_len s) (s_cnt s) - 1)) with (st_cnt' s).
destruct (ROO type lens req (Zlength old) AO) as (RT1 & RT2 & _).
forward_if.
- assert (C0: st_c s = 0) by (unfold st_c; lia).
  forward_if.
  + assert (STB: step type lens (sorted_syms lens) (root_of req lens) (maxlen lens) s = Break (sl_brk X s))
      by (apply (sl_cnt_step_brk X); auto).
    pose proof (RFO _ _ _ _ _ _ AO H2 _ STB I) as RUN.
    forward.
    unfold sl_R. simpl RA_break.
    change (fun a : environ => (EX x : state, A_brk X x a)%logic) with (EX x : state, A_brk X x).
    Exists (sl_brk X s).
    unfold A_brk, it_sep, params_locs, count_at, work_sorted, here_, it_mx, it_root.
    unfold sl_brk at 1 2 3 4 5 6 7.
    subst X. cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count
                  c_offs s_huff s_len s_drop s_used s_next s_cnt s_tab].
    entailer!.
  + assert (LM: s_len s <> maxlen lens) by (intro E; apply H4; rewrite E; reflexivity).
    pose proof (RRO _ _ _ _ _ _ AO H2 C0 LM) as RS.
    destruct IN as (TY & NC & LR & RQ).
    destruct (SSO lens LR) as (SL & SF).
    assert (SY: 0 <= Znth (s_sym s + 1) (sorted_syms lens) < Zlength lens /\
                1 <= Znth (Znth (s_sym s + 1) (sorted_syms lens)) lens <= 15).
    { eapply Forall_forall in SF; [apply SF | apply Znth_In; lia]. }
    assert (MC: max_codes type <= 288) by (unfold max_codes; repeat (destruct (_ =? _)); lia).
    assert (S1: 0 <= s_sym s + 1 < Zlength lens) by lia.
    forward.
    { entailer!. rewrite sl_cnt_work by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_cnt_work by lia.
    forward.
    { entailer!. rewrite sl_cnt_zs by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite sl_cnt_zs by lia.
    assert (LE: st_len' lens s = Znth (Znth (s_sym s + 1) (sorted_syms lens)) lens)
      by (unfold st_len'; rewrite C0; reflexivity).
    destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; cbn [RA_normal].
    rewrite LE. entailer!.
- assert (CN: st_c s <> 0) by (unfold st_c; lia).
  assert (LE: st_len' lens s = s_len s)
    by (unfold st_len'; rewrite (proj2 (Z.eqb_neq _ _) CN); reflexivity).
  forward.
  destruct (sl_R _) as [rn rb rc rr]; cbv iota beta; cbn [RA_normal].
  rewrite LE. entailer!.
Qed.

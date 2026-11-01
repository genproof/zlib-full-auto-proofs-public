(* case LENLENS, the first loop: while (state->have < state->ncode) { NEEDBITS(3); lens[order[have++]] = BITS(3);
   DROPBITS(3); } (LLDefs5.ll_loop1; model Model.v lenlens_loop, TLFacts.v lenlens_loop_S / tl_ll_step_ok) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedKit5 Zlib.proof.inflate.NeedBits Zlib.proof.inflate.NeedBits3_5.
Require Import Zlib.proof.inflate.Model2 Zlib.proof.inflate.Steps2 Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.inflate.TLFacts Zlib.proof.inflate.TLKit5 Zlib.proof.inflate.LLDefs5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma ll_zext: forall h, 0 <= h ->
  Int.zero_ext 16 (Int.zero_ext 16 (Int.repr (h mod 2 ^ 3))) = Int.repr (h mod 2 ^ 3).
Proof.
  intros h Hh. assert (R: 0 <= h mod 2 ^ 3 < 8) by (apply Z.mod_pos_bound; reflexivity).
  rewrite !zero_ext_16 by lia. reflexivity.
Qed.

(* tables_rep with order[] apart; the other tables stay behind a definition (their gv identifiers g_lenfix,
   g_distfix, _lbase, ... are not all global variables of inflate's Delta, which Floyd's go_lower rejects) *)
Definition ll_tabs (gsh: share) (gv: globals) : mpred :=
  data_at gsh (tarray t_code 512) (map ent lenfix_list) (gv g_lenfix) *
  data_at gsh (tarray t_code 32) (map ent distfix_list) (gv g_distfix) *
  Zlib.proof.inftrees.spec.itables gsh gv.

Lemma ll_tables_eq: forall gsh gv, tables_rep gsh gv =
  data_at gsh (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order) (gv _order) * ll_tabs gsh gv.
Proof. intros. unfold tables_rep, ll_tabs. apply pred_ext; cancel. Qed.

Lemma ll_loop1_ok {Espec: OracleKind} (F: frame) (m: mst) :
  frame_ok5 F -> mwf m -> m_mode m = LENLENS -> m_leave m = 0 ->
  semax Delta_cases5 (loop_state F m) ll_loop1
    (normal_ret_assert (EX m1: mst,
       !! ll_exit m m1 && loop_state F m1)).
Proof.
  intros HF W HM HL.
  unfold ll_loop1. ll_stmt.
  forward_loop (EX m1: mst, EX k: nat,
      !! (lenlens_loop k m1 = lenlens_loop 19 m /\ i_ncode (m_s m1) - i_have (m_s m1) <= Z.of_nat k /\ tl_llok m1) &&
      loop_state F m1)
    break: (EX m1: mst, !! ll_exit m m1 && loop_state F m1).
  { apply andp_left2. Exists m 19%nat. apply andp_right; [ | apply derives_refl]. apply prop_right.
    pose proof (md_lenlens _ (mw_md _ W) HM) as Hmd. split; [reflexivity | ]. split; [simpl; lia | ].
    split; [exact W | split; [exact HM | exact HL]]. }
  { apply extract_exists_pre; intro m1. apply extract_exists_pre; intro k.
    apply semax_extract_prop; intros (Ek & Hk & Hok).
    destruct Hok as (W1 & M1 & L1).
    pose proof (md_lenlens _ (mw_md _ W1) M1) as Hmd.
    rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep. abbreviate_semax.
    unfold tl_locals. freeze [0;1;2;5;6;7;8;9;10;11;12;13;14;15] FR.
    forward. forward.
    forward_if.
    2:{ forward. Exists m1. thaw FR. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep, tl_locals.
        entailer!. split; [ | split; [exact W1 | split; [exact M1 | right; split; [exact L1 | lia]]]].
        rewrite <- Ek. apply lenlens_loop_done. lia. }
    destruct k as [|k']; [simpl in Hk; lia | ].
    rewrite lenlens_loop_S in Ek. rewrite (proj2 (Z.ltb_lt _ _) H1) in Ek. cbv zeta in Ek.
    thaw FR.
    apply semax_pre with (loop_state F m1).
    { rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep, tl_locals. entailer!. }
    pose proof (mwf_needbits 3 m1 W1 ltac:(lia)) as W2.
    apply seq_assoc.
    apply semax_seq with (Q := !! (m_leave (needbits 3 m1) = 0) && loop_state F (needbits 3 m1)).
    { eapply semax_seq'; [apply semax_needbits_LENLENS5; [exact W1 | exact L1 | lia] | ].
      pose proof (mw_leave _ W2) as HL2.
      unfold loop_state. abbreviate_semax.
      forward_if.
      - forward.
        assert (E: m_leave (needbits 3 m1) = 1) by (apply leave_from_if; auto).
        Exists (needbits 3 m1). rewrite E, Z.eqb_refl in Ek.
        apply andp_right; [apply prop_right | unfold loop_state; entailer!].
        split; [symmetry; exact Ek | split; [exact W2 | split; [ | left; exact E]]].
        unfold m_mode. rewrite tl_needbits_s. exact M1.
      - forward.
        assert (E: m_leave (needbits 3 m1) = 0) by (apply leave_from_if0; auto).
        apply andp_right; [apply prop_right; exact E | unfold loop_state; entailer!]. }
    apply semax_extract_prop; intros L2.
    destruct (tl_ll_step_ok m1 (conj W1 (conj M1 L1)) H1 ltac:(lia)) as (OK3 & Hh3 & Hn3 & B3).
    pose proof (tl_needbits_s 3 m1) as Es2.
    remember (needbits 3 m1) as m2 eqn:Em2.
    pose proof (mw_bits _ W2) as WB. pose proof (mw_hold _ W2) as WH. unfold lrange in WH.
    destruct HF as [(Hshs & Hhsh & Hgsh & Htsh) Hfl].
    pose proof (tl_order_range (i_have (m_s m1)) ltac:(lia)) as OR.
    rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep. abbreviate_semax.
    unfold tl_locals. rewrite Es2.
    freeze [0;1;2;3;6;7;8;9;10;11;12;14;15] FR.
    forward. forward. rewrite ll_tables_eq. flatten_sepcon_in_SEP.
    assert (Ho: 0 <= i_have (m_s m1) < Zlength order) by (rewrite tl_order_len; lia).
    freeze [4] FT.
    forward.
    1:{ go_lowerx. apply prop_right. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    assert (Hl: Zlength (i_lens (m_s m1)) = 320) by (destruct (sw_lens _ (mw_s _ W1)); auto).
    forward.
    replace (Int64.Z_mod_modulus (m_hold m2)) with (m_hold m2) by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
    mask_simpl. rewrite int_and_ones by lia. rewrite ll_zext by lia.
    change (Vint (Int.repr (m_hold m2 mod 2 ^ 3))) with ((fun z => Vint (Int.repr z)) (m_hold m2 mod 2 ^ 3)).
    rewrite upd_Znth_map.
    match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?S))) _ _ =>
      apply semax_dowhile0 with (Q := PROPx [] (LOCALx (tl_locals F (dropbits 3 m2)) (SEPx S))) end.
    { unfold tl_locals. forward. forward. unfold dropbits, m_have, m_left. mnorm_goal.
      change (Int.unsigned (Int.repr 3)) with 3. rewrite long_shru_eq by lia. rewrite u32_repr.
      entailer!. }
    unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS. abbreviate_semax.
    forward.
    Exists (tl_ll_step m2) k'.
    apply andp_right.
    { apply prop_right. rewrite L2 in Ek. change (0 =? 1) with false in Ek.
      split; [exact Ek | ]. split; [rewrite Hh3, Hn3; lia | exact OK3]. }
    assert (MR: mem_rest_tl F (tl_ll_step m2) = mem_rest_tl F m2) by reflexivity.
    assert (SR: tl_strm F (tl_ll_step m2) = tl_strm F m2) by reflexivity.
    assert (LE: tl_locals F (tl_ll_step m2) = tl_locals F (dropbits 3 m2)) by reflexivity.
    thaw FT. thaw FR. rewrite loop_state_tl_eq. unfold loop_state_tl, tl_sep.
    rewrite MR, SR, LE. rewrite ll_tables_eq. unfold tl_locals, tl_ll_step. mnorm_goal. rewrite Es2.
    unfold bitsn. rewrite add_repr.
    entailer!. }
Qed.

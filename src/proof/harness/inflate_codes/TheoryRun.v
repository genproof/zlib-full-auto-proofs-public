(* Law inflate_codes, theory: one inflate() call.  The pass lemma from the parts (by the mode), the loop
   (Model2.loop2) from Spec5.m_init, the exit (inf_leave). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Definition rn_hdr_b (md: Z) : bool :=
  (md =? FLAGS) || (md =? TIME) || (md =? OS) || (md =? EXLEN) || (md =? EXTRA) || (md =? NAME) ||
  (md =? COMMENT) || (md =? HCRC).
Definition rn_dict_b (md: Z) : bool :=
  (md =? DICTID) || (md =? DICT) || (md =? Zlib.proof.inflate.Model.TYPE) || (md =? TYPEDO).
Definition rn_block_b (md: Z) : bool :=
  (md =? STORED) || (md =? COPY_) || (md =? COPY) || (md =? CHECK) || (md =? LENGTH) || (md =? DONE) ||
  (md =? BAD) || (md =? MEM).
Definition rn_dec_b (md: Z) : bool :=
  (md =? LEN_) || (md =? LEN) || (md =? LENEXT) || (md =? DIST) || (md =? DISTEXT) || (md =? MATCH) ||
  (md =? LIT).
Definition rn_tab_b (md: Z) : bool := (md =? TABLE) || (md =? LENLENS) || (md =? CODELENS).
Definition rn_all_b (md: Z) : bool :=
  (md =? HEAD) || rn_hdr_b md || rn_dict_b md || rn_block_b md || rn_dec_b md || rn_tab_b md || (md =? SYNC).

Lemma rn_all_true (n: nat) : (n < 32)%nat -> rn_all_b (16180 + Z.of_nat n) = true.
Proof.
  intros H. do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Ltac rn_b H := unfold rn_hdr_b, rn_dict_b, rn_block_b, rn_dec_b, rn_tab_b in H;
  repeat rewrite orb_true_iff in H; rewrite ?Z.eqb_eq in H.

Lemma rn_mode_groups (md: Z) : HEAD <= md <= SYNC ->
  md_head md \/ md_hdr md \/ md_dict md \/ md_block md \/ decode_mode md \/ md_tab md \/ md = SYNC.
Proof.
  intros H.
  assert (E: exists n, (n < 32)%nat /\ md = 16180 + Z.of_nat n).
  { exists (Z.to_nat (md - 16180)). unfold HEAD, SYNC in H. lia. }
  destruct E as [n [Hn E]].
  pose proof (rn_all_true n Hn) as A. rewrite <- E in A. clear E Hn H.
  unfold rn_all_b in A. rewrite !orb_true_iff in A.
  unfold md_head, md_hdr, md_dict, md_block, decode_mode, md_tab.
  destruct A as [[[[[[A|A]|A]|A]|A]|A]|A].
  - left. apply Z.eqb_eq; exact A.
  - right; left. rn_b A. tauto.
  - right; right; left. rn_b A. tauto.
  - right; right; right; left. rn_b A. tauto.
  - right; right; right; right; left. rn_b A. tauto.
  - right; right; right; right; right; left. rn_b A. tauto.
  - right; right; right; right; right; right. apply Z.eqb_eq; exact A.
Qed.

Lemma rn_step : stepf2_mwf3_stmt -> head_stmt -> hdr_stmt -> dict_stmt -> block_stmt -> fast_kc_stmt ->
  dec_stmt -> tab_stmt -> group_ok (fun _ => True).
Proof.
  intros SM HE HD DI BL FA DE TA.
  assert (DE': group_ok decode_mode) by exact (DE FA).
  assert (TA': group_ok md_tab) by exact (TA SM DE').
  intros wrap src pos inp aout flush m C K W L _.
  pose proof (sw_mode _ (mw_s _ (mwf3_mwf _ W))) as R.
  destruct (rn_mode_groups (m_mode m) R) as [G|[G|[G|[G|[G|[G|G]]]]]].
  - apply HE; auto.
  - apply HD; auto.
  - apply DI; auto.
  - apply BL; auto.
  - apply DE'; auto.
  - apply TA'; auto.
  - exfalso. exact (kc_sync _ _ _ _ _ _ K G).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Z_NEED_DICT comes from c_DICT, after RESTORE                                                  *)

Lemma rn_typedo_brk (flush: Z) (m: mst) : exists m', c_TYPEDO flush m = IBrk m'.
Proof.
  unfold c_TYPEDO. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; eexists; reflexivity.
Qed.

Lemma rn_type_brk (flush: Z) (m: mst) : exists m', c_TYPE flush m = IBrk m'.
Proof.
  unfold c_TYPE. destruct (_ || _)%bool; [eexists; reflexivity | apply rn_typedo_brk].
Qed.

Lemma rn_dict_ret (flush: Z) (m: mst) (r: Z) (m': mst) :
  c_DICT flush m = IRet r m' -> i_bits (m_s m') = m_bits m'.
Proof.
  unfold c_DICT. destruct (i_havedict (m_s m) =? 0).
  - intros E; inversion E; subst. reflexivity.
  - destruct (rn_type_brk flush (set_mode (set_m_adler (upd_s m (fun s => set_i_check s 1)) 1) Zlib.proof.inflate.Model.TYPE))
      as [m2 E2]. rewrite E2. discriminate.
Qed.

Lemma rn_nd_bits (flush: Z) (m: mst) (r: Z) (m': mst) :
  (m_mode m = DICTID \/ m_mode m = DICT) -> stepf2 flush lenfix_list distfix_list m = IRet r m' ->
  i_bits (m_s m') = m_bits m'.
Proof.
  intros [E|E]; unfold stepf2, step2; rewrite E; cbn -[c_DICTID c_DICT].
  - unfold c_DICTID. destruct (m_leave _ =? 1); [discriminate|]. apply rn_dict_ret.
  - apply rn_dict_ret.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Definition rn_ret (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (r: Z) (m': mst) : Prop :=
  mwf3 m' /\ Kc wrap src pos inp aout m' /\
  ((r = Z_MEM_ERROR /\ m_mode m' = MEM) \/
   (r = Z_NEED_DICT /\ m_mode m' = DICT /\ m_snx m' = m_nx m' /\ m_sow m' = Zlength (m_ow m') /\
    i_bits (m_s m') = m_bits m' /\ (m_ow m' = [] \/ pos <= 5))).

Lemma rn_loop : stepf2_mwf3_stmt -> group_ok (fun _ => True) -> nodict_stmt ->
  forall wrap src pos inp aout flush m o,
  ctx_ok src pos inp -> loop2 flush lenfix_list distfix_list m o ->
  Kc wrap src pos inp aout m -> mwf3 m -> m_leave m = 0 -> (m_mode m = DICT -> m_ow m = []) ->
  match o with
  | IBrk m' => Kc wrap src pos inp aout m' /\ mwf3 m' /\ m_leave m' = 1 /\ m_mode m' <> DICT
  | IRet r m' => rn_ret wrap src pos inp aout r m'
  end.
Proof.
  intros SM ST ND wrap src pos inp aout flush m o C LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K W L0 D.
  - pose proof (SM flush m W L0) as W'. rewrite E in W'.
    pose proof (ST wrap src pos inp aout flush m C K W L0 I) as P. rewrite E in P. cbn in P.
    split; [exact W'|].
    destruct P as [(-> & -> & M) | (-> & MD & M' & S1 & S2 & O & L' & K')].
    + split; [exact K|]. left; auto.
    + split; [exact K'|]. right. do 4 (split; [auto|]). split; [exact (rn_nd_bits _ _ _ _ MD E)|].
      destruct MD as [MD|MD].
      * right. destruct (kc_did _ _ _ _ _ _ K MD) as (_ & _ & HP & _).
        pose proof (mw_nx _ (mwf3_mwf _ W)). lia.
      * left. rewrite O. auto.
  - pose proof (SM flush m W L0) as W'. rewrite E in W'.
    pose proof (ST wrap src pos inp aout flush m C K W L0 I) as P. rewrite E in P. cbn in P.
    destruct P as [K' _]. split; [exact K'|]. split; [exact W'|]. split; [exact L1|]. exact (ND _ _ _ E).
  - pose proof (SM flush m W L0) as W'. rewrite E in W'.
    pose proof (ST wrap src pos inp aout flush m C K W L0 I) as P. rewrite E in P. cbn in P.
    destruct P as [K' NDm].
    assert (L': m_leave m' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ W')); lia).
    apply IH; auto. intros MD. exfalso. exact (NDm L' MD).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave                                                                                      *)

Lemma rn_uw (s: istate) (d: list Z) :
  i_mode (updatewindow s d) = i_mode s /\ i_bits (updatewindow s d) = i_bits s /\
  i_hold (updatewindow s d) = i_hold s /\ i_wrap (updatewindow s d) = i_wrap s /\
  i_head (updatewindow s d) = i_head s /\ i_check (updatewindow s d) = i_check s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
Qed.

Definition rn_bufret (flush: Z) (m: mst) : Z :=
  let inn := u32 (m_in m - m_have m) in
  let out := u32 (m_out m - m_left m) in
  if andb (orb (andb (inn =? 0) (out =? 0)) (flush =? Z_FINISH)) (m_ret m =? Z_OK) then Z_BUF_ERROR else m_ret m.

Lemma rn_leave_fin (flush: Z) (m: mst) :
  let res := leave_fin flush m in
  r_ret res = rn_bufret flush m /\
  m_snx (r_m res) = m_nx m /\ m_sow (r_m res) = Zlength (m_ow m) /\ m_inp (r_m res) = m_inp m /\
  m_aout (r_m res) = m_aout m /\ m_msg (r_m res) = m_msg m /\ m_ow (r_m res) = m_ow m /\
  i_mode (m_s (r_m res)) = m_mode m /\ i_bits (m_s (r_m res)) = m_bits m /\
  i_hold (m_s (r_m res)) = m_hold m /\ i_wrap (m_s (r_m res)) = i_wrap (m_s m) /\
  i_head (m_s (r_m res)) = i_head (m_s m).
Proof.
  cbv zeta. unfold leave_fin. cbv zeta.
  set (upd := leave_ok flush m).
  set (m1 := restore m).
  set (m2 := if upd then _ else m1).
  assert (E2: m_snx m2 = m_nx m /\ m_sow m2 = Zlength (m_ow m) /\ m_inp m2 = m_inp m /\ m_aout m2 = m_aout m /\
              m_msg m2 = m_msg m /\ m_ow m2 = m_ow m /\ m_in m2 = m_in m /\ m_nx m2 = m_nx m /\
              m_out m2 = m_out m /\ m_ret m2 = m_ret m /\
              i_mode (m_s m2) = m_mode m /\ i_bits (m_s m2) = m_bits m /\ i_hold (m_s m2) = m_hold m /\
              i_wrap (m_s m2) = i_wrap (m_s m) /\ i_head (m_s m2) = i_head (m_s m)).
  { unfold m2, m1. destruct upd; cbn.
    - destruct (rn_uw (set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m))
        (sublist (Zlength (m_ow m) - u32 (m_out m - (m_aout m - Zlength (m_ow m)))) (Zlength (m_ow m)) (m_ow m)))
        as (A & B & C & D & E & _).
      unfold m_left; cbn. rewrite A, B, C, D, E. cbn. unfold m_mode. repeat split.
    - unfold m_mode. repeat split. }
  clearbody m2.
  destruct E2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15).
  unfold rn_bufret, m_have, m_left.
  destruct (andb (negb (Z.land (i_wrap (m_s _)) 4 =? 0)) _); cbn;
    rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?A13, ?A14, ?A15; repeat split.
Qed.


(* Law rt_gzip_header on the round-2 harness, inflate side: the rest of an inflate(Z_FINISH) call after the gzip
   header, from a loop head where the decode invariant holds on the machine with the small header (G2IDefs.g2_mc):
   the run of the real machine is the same up to the header model, which it keeps (RTH8SimKit), and the decode
   theory (RTIGW) gives what the harness's loop needs: nothing written (there is no data), the decode invariant
   at the next call, total_out still 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Import Zlib.proof.roundtrip.RTIGW.
Require Zlib.proof.roundtrip.RTH8SimKit.
Import ListNotations.
Local Open Scope Z_scope.

Module SK := Zlib.proof.roundtrip.RTH8SimKit.

Lemma g2d_tail : rtigw_loop_stmt -> forall gh xfl wb bs O pos inp m o res,
  rtigw_ok (g2_G gh xfl wb bs O) -> full (g2_G gh xfl wb bs O) = [] -> ctx2 O pos inp ->
  Kd (g2_G gh xfl wb bs O) pos inp [] (g2_mc m) -> mwf3W (g2_mc m) -> m_leave m = 0 -> SK.hk m ->
  loop2 Z_FINISH lenfix_list distfix_list m o ->
  match o with IRet r m' => res = Res r m' None | IBrk m' => inf_leave Z_FINISH m' res end ->
  r_ret res <> Z_MEM_ERROR ->
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
  0 <= m_snx (r_m res) <= Zlength inp /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
  m_aout (r_m res) = m_aout m /\ m_h (r_m res) = m_h m /\ m_tout (r_m res) = 0 /\
  dinv (g2_G gh xfl wb bs O) (pos + m_snx (r_m res)) [] (m_s (r_m res)) 0.
Proof.
  intros LOOP gh xfl wb bs O pos inp m o res OK FU (P0 & PL & IE) K W L0 HK LP RO NM.
  set (G := g2_G gh xfl wb bs O) in *.
  destruct (SK.hs_loop Z_FINISH lenfix_list distfix_list m g2_hc o HK LP) as [LP' HO].
  assert (RO': match SK.out_hk o g2_hc with
               | IRet r m' => SK.rh g2_hc res = Res r m' None
               | IBrk m' => inf_leave Z_FINISH m' (SK.rh g2_hc res) end /\ m_h (r_m res) = m_h m).
  { destruct o as [m1|r m1]; cbn [SK.out_hk].
    - destruct HO as [H1 H2]. destruct (SK.hs_leave Z_FINISH m1 g2_hc res H2 RO) as (A & B & _).
      split; [exact A | congruence].
    - subst res. destruct HO as [H1 _]. split; [reflexivity | exact H1]. }
  destruct RO' as [RO' HH].
  assert (SRC: dc_src G = O) by reflexivity.
  assert (HI: dc_hist G = []) by reflexivity.
  destruct (LOOP G pos inp [] Z_FINISH (g2_mc m) (SK.out_hk o g2_hc) (SK.rh g2_hc res) OK P0
              ltac:(rewrite SRC; exact PL) ltac:(rewrite SRC; exact IE) K W L0
              ltac:(exists []; rewrite HI; reflexivity) ltac:(constructor) LP' RO')
    as [MEM | (RC & SNX & SOW & AO & (rest & FR) & DV & _ & _)].
  { exfalso. apply NM. exact MEM. }
  cbn [SK.rh r_ret r_m] in *.
  unfold SK.mh, g2_mc in *.
  cbn [m_snx m_sow m_ow m_aout m_s m_tout set_m_h] in *.
  rewrite FU in FR. cbn [app] in FR.
  assert (OW: m_ow (r_m res) = []) by (symmetry in FR; apply app_eq_nil in FR; tauto).
  rewrite OW in *. cbn [app] in DV. rewrite Zlength_nil in SOW.
  assert (TO: m_tout (r_m res) = 0).
  { destruct DV as (_ & _ & _ & _ & T). rewrite T. reflexivity. }
  rewrite TO in DV.
  exact (conj RC (conj SNX (conj eq_refl (conj SOW (conj AO (conj HH (conj TO DV))))))).
Qed.

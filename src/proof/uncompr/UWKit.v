(* The model side of uncompress2_z's loop for any sizes (UModelW.uncw_loop), and the facts of the stream after
   inflateInit_ that the wide inflate specification (SpecWSelf.inflate_specW_s) needs: used by the body
   proofs of UBodiesW.v (a pointer destination and a Z_NULL destination). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.inflate_api.SpecWSelf.
Require Import Zlib.proof.uncompr.UBodies5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* the loop from (m, used, out, ai, ao) on is a continuation of the loop from the start *)
Definition reach_w (src: list Z) (cap: Z) (m: mst) (used: Z) (out: list Z) (ai ao: Z) : Prop :=
  forall err u o, uncw_loop src cap m used out ai ao err u o -> uncw_loop src cap m_first 0 [] 0 0 err u o.

Lemma reach_w_first: forall src cap, reach_w src cap m_first 0 [] 0 0.
Proof. unfold reach_w. auto. Qed.

Lemma reach_w_next: forall src cap m used out ai ao res,
  reach_w src cap m used out ai ao ->
  run2 0 lenfix_list distfix_list (uw_call src cap m used out ai ao) res ->
  r_ret res = Z_OK ->
  reach_w src cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
    (uw_ain src used ai - m_snx (r_m res)) (uw_aout cap out ao - Zlength (m_ow (r_m res))).
Proof. unfold reach_w. intros. apply H. eapply uwl_next; eauto. Qed.

Lemma reach_w_stop: forall src cap m used out ai ao res,
  reach_w src cap m used out ai ao ->
  run2 0 lenfix_list distfix_list (uw_call src cap m used out ai ao) res ->
  r_ret res <> Z_OK ->
  uncw_loop src cap m_first 0 [] 0 0 (r_ret res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res)).
Proof. unfold reach_w. intros. apply H. eapply uwl_stop; eauto. Qed.

(* the next call's offers: what the last call left, or the next piece *)
Lemma uw_ain_bounds: forall src used ai,
  0 <= used -> 0 <= ai <= uw_max -> used + ai <= Zlength src ->
  0 <= uw_ain src used ai <= uw_max /\ used + uw_ain src used ai <= Zlength src.
Proof.
  intros. unfold uw_ain, uw_max in *. destruct (ai =? 0) eqn:E; [apply Z.eqb_eq in E | ]; lia.
Qed.

Lemma uw_aout_bounds: forall cap out ao,
  0 <= ao <= uw_max -> Zlength out + ao <= cap ->
  0 <= uw_aout cap out ao <= uw_max /\ Zlength out + uw_aout cap out ao <= cap.
Proof.
  intros. unfold uw_aout, uw_max in *. destruct (ao =? 0) eqn:E; [apply Z.eqb_eq in E | ]; lia.
Qed.

Lemma uw_ain_nz: forall src used ai, ai <> 0 -> uw_ain src used ai = ai.
Proof. intros. unfold uw_ain. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma uw_ain_z: forall src used, uw_ain src used 0 = Z.min (Zlength src - used) uw_max.
Proof. reflexivity. Qed.
Lemma uw_aout_nz: forall cap out ao, ao <> 0 -> uw_aout cap out ao = ao.
Proof. intros. unfold uw_aout. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.
Lemma uw_aout_z: forall cap out, uw_aout cap out 0 = Z.min (cap - Zlength out) uw_max.
Proof. reflexivity. Qed.

(* the piece the code computes, `x > (z_size_t)max ? max : (uInt)x`, is min(x, max) *)
Lemma uw_piece_big: forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr uw_max) (Int64.repr x) = true -> Z.min x uw_max = uw_max.
Proof.
  intros x Hx H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by (unfold uw_max; rep_lia).
  destruct (zlt _ _) in H; [lia | discriminate].
Qed.
Lemma uw_piece_small: forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr uw_max) (Int64.repr x) = false -> Z.min x uw_max = x.
Proof.
  intros x Hx H. unfold Int64.ltu in H. rewrite !Int64.unsigned_repr in H by (unfold uw_max; rep_lia).
  destruct (zlt _ _) in H; [discriminate | lia].
Qed.

(* the call's machine is m_next of the loop's stream, offered the next pieces *)
Lemma m_init_call: forall z L m src cap used out ai ao,
  l_s L = m_s m -> l_h L = m_h m -> zf_ao z = uw_aout cap out ao -> zf_adler z = m_adler m ->
  zf_msg z = m_msg m -> zf_tin z = m_tin m -> zf_tout z = m_tout m ->
  m_init z L (sublist used (used + uw_ain src used ai) src) = uw_call src cap m used out ai ao.
Proof. intros. unfold uw_call. apply m_init_next; auto. Qed.

(* the stream after inflateInit_ (windowBits 15): a zlib stream (wrap 5, not raw), in mode HEAD *)
Lemma init_s_swfW: swfW (init_s 5 15).
Proof. unfold swfW. vm_compute. split; intros H; discriminate H. Qed.

Lemma init_live_raw: forall stp, raw_live (Some (init_live stp 15)) = false.
Proof. intros. vm_compute. reflexivity. Qed.

(* on a zlib stream the wide stream predicate is Spec5's *)
Lemma istreamA_opt_ptr: forall gv shs v z av L,
  isptr v -> raw_live (Some L) = false -> istreamA_opt gv shs v z av (Some L) = istream gv shs v z (Some L).
Proof.
  intros. unfold istreamA_opt. rewrite if_false by (intro; subst; contradiction).
  apply istreamA_istream; auto.
Qed.

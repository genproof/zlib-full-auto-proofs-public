(* LEN's fast path: inflate_fast moves the abstract state along the steps of the symbols it decodes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Require Import Zlib.proof.harness.api_split_invariant.SIKitLook.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastWalk.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastCopy.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastIter.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract MATCH steps of a match                                                            *)

Lemma sf_astep_match src a : a_mode a = MATCH -> astep lenfix_list distfix_list src a = a_MATCH a.
Proof. intros H. unfold astep. cbv zeta. rewrite H. reflexivity. Qed.

Lemma sf_match : fmatch_stmt.
Proof.
  intros src I R a. remember (Z.to_nat (i_length (a_s a))) as n eqn:En. revert a En.
  induction n as [|n IH]; intros a En Hm Hl Ho Hq HR; [lia|].
  pose proof (sf_astep_match src a Hm) as S. unfold a_MATCH in S.
  replace (Zlength (a_O a) <? i_offset (a_s a)) with false in S by (symmetry; apply Z.ltb_ge; lia).
  cbn [lz_copy].
  destruct (Z.eqb_spec (i_length (a_s a) - 1) 0) as [E|E].
  - assert (n = O) by lia. subst n. cbn [lz_copy].
    eapply areach_trans; [eapply areach_one; [exact S|lia|intros _; lia]|].
    replace (i_length (a_s a) - 1) with 0 by lia. apply ar_refl.
  - eapply areach_trans; [eapply areach_one; [exact S|lia|intros _; lia]|].
    set (a1 := AS _ _ _).
    specialize (IH a1 ltac:(cbn; lia)).
    apply IH; cbn; try lia; [exact Hm| |]; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.
(* ---------------------------------------------------------------------------------------------- *)
(* Small facts                                                                                    *)

(* awf along a trace *)
Lemma sf_awf_reach (AW: awf_stmt) src I R a b : awf src a -> areach src I R a b -> awf src b.
Proof.
  intros H R1. induction R1; auto. apply IHR1. destruct AW as (_ & P & _). eapply P; eauto.
Qed.

(* H says that a mode is one of a list of modes it is not *)
Ltac sf_nomode H := solve [
  exfalso; unfold hdr_mode, data_mode, post_mode, decode_mode, win_mode, len_live, off_live, ext_live in H;
  repeat (destruct H as [H|H]; [try discriminate H; try (destruct H as [H _]; discriminate H)|]);
  try discriminate H; try (destruct H as [H _]; discriminate H)].

(* seq does not look at hold, bits and back of the concrete state; in LEN and TYPE neither machine uses
   length, offset, extra *)
Lemma sf_seq_end s A md h b bk l o e : seq s A -> md = LEN \/ md = Zlib.proof.inflate.Model.TYPE ->
  seq (set_i_back (set_i_bits (set_i_hold (set_i_mode s md) h) b) bk) (fsx A md l o e).
Proof.
  intros [] Hmd; constructor; cbn; auto; intros H; destruct Hmd; subst md; sf_nomode H.
Qed.

Lemma sf_seq_len s A h b l o e : seq s A -> seq (set_i_bits (set_i_hold s h) b) (fsx A LEN l o e).
Proof. intros [] ; constructor; cbn; auto; intros H; sf_nomode H. Qed.

Lemma sf_fsx_self s : i_mode s = LEN -> fsx s LEN (i_length s) (i_offset s) (i_extra s) = s.
Proof. destruct s; cbn; intros ->; reflexivity. Qed.

Lemma sf_fset_fset m0 m nx ow h b nx' ow' h' b' :
  m = fset m0 nx ow h b -> fset m nx' ow' h' b' = fset m0 nx' ow' h' b'.
Proof. intros ->. reflexivity. Qed.

Lemma sf_fset_self m : m = fset m (m_nx m) (m_ow m) (m_hold m) (m_bits m).
Proof. destruct m; reflexivity. Qed.

Lemma sf_fset_fields m0 mt : mt = fset m0 (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt) ->
  m_s mt = m_s m0 /\ m_inp mt = m_inp m0 /\ m_aout mt = m_aout m0 /\ m_in mt = m_in m0 /\
  m_out mt = m_out m0 /\ m_ret mt = m_ret m0 /\ m_tout mt = m_tout m0 /\ m_leave mt = m_leave m0.
Proof. intros E. rewrite E. repeat split. Qed.

Lemma sf_bitbuf_restore src P0 m : bitbuf src P0 m -> bitbuf src P0 (restore m).
Proof. intros []. constructor; auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The end of inflate_fast: the unused bytes back                                                 *)

Definition ftail (m: mst) : mst :=
  let len := Z.shiftr (m_bits m) 3 in
  let m := set_m_nx m (m_nx m - len) in
  let bits := m_bits m - len * 8 in
  set_m_bits (set_m_hold m (m_hold m mod 2 ^ bits)) bits.

Lemma sf_fast_eq m : fast lenfix_list distfix_list m =
  restore (ftail (fast_loop lenfix_list distfix_list (Z.to_nat (m_aout m) + 1) m)).
Proof. reflexivity. Qed.

(* the bits pulled are those of bytes read since the start (nx0, with b0 < 8 bits then): giving the whole
   bytes of the buffer back keeps the bit position *)
Lemma sf_tail src P0 m nx0 b0 : bitbuf src P0 m -> 0 <= nx0 -> 0 <= b0 < 8 ->
  m_bits m - 8 * m_nx m <= b0 - 8 * nx0 ->
  bitbuf src P0 (ftail m) /\ mq P0 (ftail m) = mq P0 m.
Proof.
  intros Hb H0 Hb0 Hd. pose proof (sik_mq_nonneg _ _ _ Hb) as Q.
  destruct Hb as [Bs Bp Bi Bn Bb Bh].
  unfold ftail. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (K: 0 <= m_bits m / 8 <= m_nx m - nx0).
  { split; [apply Z.div_pos; lia|].
    assert (m_bits m / 8 < m_nx m - nx0 + 1) by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (Z.mod_pos_bound (m_bits m) 8 ltac:(lia)) as M. pose proof (Z.div_mod (m_bits m) 8 ltac:(lia)) as D.
  assert (E: mq P0 (set_m_bits (set_m_hold (set_m_nx m (m_nx m - m_bits m / 8))
             (m_hold m mod 2 ^ (m_bits m - m_bits m / 8 * 8))) (m_bits m - m_bits m / 8 * 8)) = mq P0 m)
    by (unfold mq; cbn [m_nx m_bits m_hold m_inp set_m_bits set_m_hold set_m_nx]; lia).
  split; [|exact E]. constructor; cbn [m_nx m_bits m_hold m_inp set_m_bits set_m_hold set_m_nx]; auto; try lia.
  rewrite E, Bh. apply sik_sbits_mod; auto; lia.
Qed.
(* ---------------------------------------------------------------------------------------------- *)
(* The relation at the end                                                                        *)

(* a machine mf after inflate_fast from m (related to a in LEN): the state changed only in its mode md
   (LEN, TYPE or BAD), hold, bits and back, the counters unchanged; the abstract state a' in md, in LEN and
   TYPE at the same bit position and with a's state up to length, offset, extra *)
Lemma sf_rel_end src P0 O0 m a mf a' md h b bk :
  rel src P0 O0 m a -> m_mode m = LEN ->
  m_s mf = set_i_back (set_i_bits (set_i_hold (set_i_mode (m_s m) md) h) b) bk ->
  m_inp mf = m_inp m -> m_aout mf = m_aout m -> m_in mf = m_in m -> m_out mf = m_out m ->
  m_ret mf = m_ret m -> m_tout mf = m_tout m ->
  bitbuf src P0 mf -> Zlength (m_ow mf) <= m_aout m -> a_O a' = O0 ++ m_ow mf -> a_mode a' = md ->
  ((md = LEN \/ md = Zlib.proof.inflate.Model.TYPE) /\ a_q a' = mq P0 mf /\
   exists l o e, a_s a' = fsx (a_s a) md l o e) \/ md = BAD ->
  rel src P0 O0 mf a'.
Proof.
  intros Hr HM Es Ei Ea Ein Eo Er Et Hb Hw HO Hmd C.
  assert (Mf: m_mode mf = md) by (unfold m_mode; rewrite Es; reflexivity).
  assert (D: data_mode (m_mode m)) by (rewrite HM; right; right; right; right; right; right; right; right; left;
                                        right; left; reflexivity).
  assert (Md: md = LEN \/ md = Zlib.proof.inflate.Model.TYPE \/ md = BAD) by (destruct C as [[[->| ->] _]| ->]; auto).
  assert (NB: md <> BAD -> (md = LEN \/ md = Zlib.proof.inflate.Model.TYPE) /\ a_q a' = mq P0 mf /\
                           exists l o e, a_s a' = fsx (a_s a) md l o e)
    by (intros N; destruct C as [C| ->]; [exact C|congruence]).
  destruct Hr as [Bb RM Rq Rbits RO [Ra1 Ra2] Rin [Ro1 [Ro2 Ro3]] Rret Rs [Rc1 Rc2] [Rt1 Rt2] Rtout Rwin Rhead].
  assert (Out: m_out m = m_aout m) by (apply Ro3; right; left; exact D).
  constructor.
  - exact Hb.
  - rewrite Mf, Hmd. reflexivity.
  - rewrite Mf. intros N. apply NB. exact N.
  - unfold bits_ok. rewrite Es. cbn. repeat split; try intros H'; destruct Md as [->|[->| ->]];
      first [sf_nomode H|sf_nomode H'].
  - exact HO.
  - rewrite Ea. lia.
  - rewrite Ein, Ei. exact Rin.
  - unfold m_left. rewrite Eo, Ea, Out. pose proof (Zlength_nonneg (m_ow mf)) as Lw. split; [lia|split].
    + intros H. rewrite Mf in H. destruct Md as [->|[->| ->]]; sf_nomode H.
    + intros _. reflexivity.
  - rewrite Mf. intros N1 N2. rewrite Er. apply Rret; rewrite HM; discriminate.
  - rewrite Mf. intros N. destruct (NB N) as (Hl & _ & l & o & e & E). rewrite Es, E.
    apply sf_seq_end; [apply Rs; rewrite HM; discriminate|exact Hl].
  - rewrite Mf. split.
    + intros H. destruct Md as [->|[->| ->]]; sf_nomode H.
    + intros H W. assert (N: md <> BAD) by (intros ->; sf_nomode H).
      destruct (NB N) as (_ & _ & l & o & e & E). rewrite Es, E. cbn.
      rewrite Es in W. apply Rc2; [exact D|exact W].
  - rewrite Mf. split.
    + intros _. rewrite Es. cbn. apply Rt1. right; left. exact D.
    + intros H. destruct Md as [->|[->| ->]]; sf_nomode H.
  - rewrite Et, Rtout. unfold m_left. rewrite Eo, Ea, Out. f_equal. lia.
  - intros _. rewrite Es. apply Rwin. right. split; [exact D|rewrite HM; discriminate].
  - rewrite Es. exact Rhead.
Qed.
(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Section Loop.
Variables (src: list Z) (P0: Z) (O0: list Z) (m0: mst) (a0: ast).
Context (AW : awf_stmt) (IT : fiter_stmt) (Hs : forall l o e, seq (m_s m0) (fsx (a_s a0) LEN l o e))
        (Hw : swin_ok (m_s m0) O0) (Hm : m_mode m0 = LEN).

Let I := P0 + Zlength (m_inp m0).
Let R := Zlength O0 + m_aout m0.

(* the machine at a symbol boundary of the loop: m0 with its locals changed, the bits pulled from the
   bytes read *)
Record finv (m: mst) (a: ast) : Prop := {
  fv_m : m = fset m0 (m_nx m) (m_ow m) (m_hold m) (m_bits m);
  fv_bb : bitbuf src P0 m;
  fv_bits : m_bits m <= 30;
  fv_nx : m_bits m - 8 * m_nx m <= m_bits m0 - 8 * m_nx m0;
  fv_O : a_O a = O0 ++ m_ow m;
  fv_ow : Zlength (m_ow m) <= m_aout m0 }.

(* where the loop ends: at a symbol boundary (LEN), after the end-of-block code (TYPE), or in BAD *)
Definition ffin (mf: mst) (a: ast) : Prop :=
  exists mt, finv mt a /\ areach src I R a0 a /\
   ((mf = mt /\ a_q a = mq P0 mt /\ exists l o e, a_s a = fsx (a_s a0) LEN l o e) \/
    (mf = set_mode mt Zlib.proof.inflate.Model.TYPE /\ a_q a = mq P0 mt /\
     exists l o e, a_s a = fsx (a_s a0) Zlib.proof.inflate.Model.TYPE l o e) \/
    (a_mode a = BAD /\ exists e, mf = set_bad mt e)).

Lemma sf_loop : forall k m a, finv m a -> areach src I R a0 a -> awf src a -> a_q a = mq P0 m ->
  (exists l o e, a_s a = fsx (a_s a0) LEN l o e) ->
  m_nx m + 6 <= Zlength (m_inp m0) -> Zlength (m_ow m) + 258 <= m_aout m0 ->
  exists a', ffin (fast_loop lenfix_list distfix_list k m) a'.
Proof.
  induction k as [|k IH]; intros m a F Ra Wa Qa Sa Hn Ho.
  { exists a, m. split; [exact F|]. split; [exact Ra|]. left. auto. }
  destruct Sa as (l & o & e & Sa).
  destruct (sf_fset_fields m0 m (fv_m _ _ F)) as (Es & Ei & Ea & _).
  cbn [fast_loop].
  generalize (IT src P0 O0 m a (fv_bb _ _ F) ltac:(unfold m_mode; rewrite Es; exact Hm)
                 ltac:(unfold a_mode; rewrite Sa; reflexivity) Qa (fv_O _ _ F)
                 ltac:(rewrite Es, Sa; apply Hs) ltac:(rewrite Es; exact Hw) Wa (fv_bits _ _ F)
                 ltac:(rewrite Ei; exact Hn) ltac:(rewrite Ea; exact Ho)).
  destruct (fast_iter lenfix_list distfix_list m) as [go m'].
  intros (a' & mt & R1 & Emt & Bt & Bits & Nx & Ot & Owt & Cs).
  rewrite Ei, Ea in R1.
  assert (Emt0: mt = fset m0 (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt))
    by (transitivity (fset m (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt)); [exact Emt|eapply sf_fset_fset; exact (fv_m _ _ F)]).
  pose proof (fv_nx _ _ F). pose proof (fv_ow _ _ F).
  assert (Ft: finv mt a') by (constructor; auto; lia).
  assert (Ra': areach src I R a0 a') by (eapply areach_trans; eauto).
  destruct Cs as [(-> & -> & Gw & Qt & l' & o' & e' & St)|[(-> & -> & Qt & l' & o' & e' & St)|(-> & Bd & ex & ->)]].
  - destruct (sf_fset_fields m0 mt Emt0) as (_ & Eti & Eta & _).
    assert (St0: a_s a' = fsx (a_s a0) LEN l' o' e') by (rewrite St, Sa; reflexivity).
    rewrite Eti, Eta. cbn [andb].
    destruct (Z.ltb_spec (m_nx mt) (Zlength (m_inp m0) - 5)); cbn [andb];
      [destruct (Z.ltb_spec (Zlength (m_ow mt)) (m_aout m0 - 257))|].
    + apply (IH mt a'); auto; [eapply sf_awf_reach; eauto|eauto|lia|lia].
    + exists a', mt. split; [exact Ft|]. split; [exact Ra'|]. left.
      split; [reflexivity|]. split; [exact Qt|]. exists l', o', e'; exact St0.
    + exists a', mt. split; [exact Ft|]. split; [exact Ra'|]. left.
      split; [reflexivity|]. split; [exact Qt|]. exists l', o', e'; exact St0.
  - cbn [andb]. exists a', mt. split; [exact Ft|]. split; [exact Ra'|]. right; left.
    split; [reflexivity|]. split; [exact Qt|]. exists l', o', e'. rewrite St, Sa. reflexivity.
  - cbn [andb]. exists a', mt. split; [exact Ft|]. split; [exact Ra'|]. right; right. eauto.
Qed.

End Loop.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast                                                                                   *)

Lemma sf_state_eq s h0 b0 h b : set_i_bits (set_i_hold (set_i_bits (set_i_hold s h0) b0) h) b =
  set_i_back (set_i_bits (set_i_hold (set_i_mode s (i_mode s)) h) b) (i_back s).
Proof. destruct s; reflexivity. Qed.

Lemma sf_state_eq2 s h0 b0 h b md : set_i_bits (set_i_hold (set_i_mode (set_i_bits (set_i_hold s h0) b0) md) h) b =
  set_i_back (set_i_bits (set_i_hold (set_i_mode s md) h) b) (i_back s).
Proof. destruct s; reflexivity. Qed.

Lemma si_fast : fast_part_stmt.
Proof.
  intros K AW src P0 O0 m a Hr Ha Hl HM Hh Hlf Hb. cbv zeta. rewrite sf_fast_eq.
  pose proof (sf_iter sf_walk sf_copy sf_match) as IT.
  assert (NB: m_mode m <> BAD) by (rewrite HM; discriminate).
  assert (Hm0: m_mode (restore m) = LEN) by exact HM.
  assert (Hs: forall l o e, seq (m_s (restore m)) (fsx (a_s a) LEN l o e))
    by (intros; apply sf_seq_len, (rl_s _ _ _ _ _ Hr NB)).
  assert (Hw: swin_ok (m_s (restore m)) O0).
  { apply (rl_win _ _ _ _ _ Hr). rewrite HM. right. split; [|discriminate].
    right; right; right; right; right; right; right; right; left; right; left; reflexivity. }
  assert (Hma: a_mode a = LEN) by (rewrite <- (rl_mode _ _ _ _ _ Hr); exact HM).
  pose proof (rl_bb _ _ _ _ _ Hr) as Bb.
  assert (F0: finv src P0 O0 (restore m) (restore m) a).
  { constructor.
    - apply sf_fset_self.
    - apply sf_bitbuf_restore, Bb.
    - cbn. lia.
    - lia.
    - exact (rl_O _ _ _ _ _ Hr).
    - exact (proj1 (rl_aout _ _ _ _ _ Hr)). }
  destruct (sf_loop src P0 O0 (restore m) a AW IT Hs Hw Hm0 (Z.to_nat (m_aout (restore m)) + 1) (restore m) a F0
              (ar_refl _ _ _ _) Ha (rl_q _ _ _ _ _ Hr NB)
              ltac:(exists (i_length (a_s a)), (i_offset (a_s a)), (i_extra (a_s a));
                    symmetry; apply sf_fsx_self, Hma)
              ltac:(unfold m_have in Hh; cbn; lia) ltac:(unfold m_left in Hlf; cbn; lia))
    as (a' & mt & Ft & Ra & Cs).
  destruct Ft as [Fm Fb Fbits Fnx FO Fow].
  destruct (sf_tail src P0 mt (m_nx m) (m_bits m) Fb ltac:(apply (bb_nx _ _ _ Bb)) ltac:(pose proof (bb_bits _ _ _ Bb); lia)
              Fnx) as [Tb Tq].
  destruct (sf_fset_fields _ _ Fm) as (Es & Ei & Ea & Ein & Eo & Er & Et & El).
  destruct Cs as [(-> & Qt & l & o & e & St)|[(-> & Qt & l & o & e & St)|(Bd & ex & ->)]].
  - replace (m_mode (restore (ftail mt)) =? Zlib.proof.inflate.Model.TYPE) with false
      by (symmetry; apply Z.eqb_neq; change (m_mode (restore (ftail mt))) with (i_mode (m_s mt)); rewrite Es;
          change (i_mode (m_s (restore m))) with (m_mode m); rewrite HM; discriminate).
    exists a'. split; [exact Ra|]. split; [|exact (eq_trans El Hl)].
    apply (sf_rel_end src P0 O0 m a _ a' LEN (m_hold (ftail mt)) (m_bits (ftail mt)) (i_back (m_s m)) Hr HM).
    + change (m_s (restore (ftail mt))) with (set_i_bits (set_i_hold (m_s mt) (m_hold (ftail mt))) (m_bits (ftail mt))).
      rewrite Es. change (m_s (restore m)) with (set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m)).
      rewrite sf_state_eq. rewrite <- HM. reflexivity.
    + exact Ei.
    + exact Ea.
    + exact Ein.
    + exact Eo.
    + exact Er.
    + exact Et.
    + apply sf_bitbuf_restore, Tb.
    + exact Fow.
    + exact FO.
    + unfold a_mode. rewrite St. reflexivity.
    + left. split; [left; reflexivity|]. split; [rewrite Qt; symmetry; exact Tq|]. exists l, o, e. exact St.
  - replace (m_mode (restore (ftail (set_mode mt Zlib.proof.inflate.Model.TYPE))) =? Zlib.proof.inflate.Model.TYPE)
      with true by reflexivity.
    exists a'. split; [exact Ra|]. split; [|exact (eq_trans El Hl)].
    apply (sf_rel_end src P0 O0 m a _ a' Zlib.proof.inflate.Model.TYPE (m_hold (ftail mt)) (m_bits (ftail mt)) (-1)
             Hr HM).
    + change (m_s (upd_s (restore (ftail (set_mode mt Zlib.proof.inflate.Model.TYPE))) (fun s => set_i_back s (-1))))
        with (set_i_back (set_i_bits (set_i_hold (set_i_mode (m_s mt) Zlib.proof.inflate.Model.TYPE)
                (m_hold (ftail mt))) (m_bits (ftail mt))) (-1)).
      rewrite Es. reflexivity.
    + exact Ei.
    + exact Ea.
    + exact Ein.
    + exact Eo.
    + exact Er.
    + exact Et.
    + destruct Tb. constructor; auto.
    + exact Fow.
    + exact FO.
    + unfold a_mode. rewrite St. reflexivity.
    + left. split; [right; reflexivity|]. split; [rewrite Qt; symmetry; exact Tq|]. exists l, o, e. exact St.
  - replace (m_mode (restore (ftail (set_bad mt ex))) =? Zlib.proof.inflate.Model.TYPE) with false by reflexivity.
    exists a'. split; [exact Ra|]. split; [|exact (eq_trans El Hl)].
    apply (sf_rel_end src P0 O0 m a _ a' BAD (m_hold (ftail mt)) (m_bits (ftail mt)) (i_back (m_s m)) Hr HM).
    + change (m_s (restore (ftail (set_bad mt ex))))
        with (set_i_bits (set_i_hold (set_i_mode (m_s mt) BAD) (m_hold (ftail mt))) (m_bits (ftail mt))).
      rewrite Es. reflexivity.
    + exact Ei.
    + exact Ea.
    + exact Ein.
    + exact Eo.
    + exact Er.
    + exact Et.
    + destruct Tb. constructor; auto.
    + exact Fow.
    + exact FO.
    + exact Bd.
    + right. reflexivity.
Qed.

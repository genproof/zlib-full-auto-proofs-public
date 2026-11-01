(* Law rj_bad_block with clip() pieces (BBWDefs.v), kinds 2 and 3 (fixed-Huffman literals, then the code 286/287,
   or the length code 257 then the distance code 30/31): one call of main's loop, from the fixed-block run theory
   (FRDefs.fr_inv, FRCall.fr_call_ok).

   The invariant between calls is the run theory's `fr_inv` and, while nothing has been consumed, "nothing written
   and no window, or BAD" (`bbw_fr_J`).  A call that does not reach the error and was not clipped can only have
   stopped for Z_TREES at the end of the block header (FRFacts.fr_stop: the output space holds every literal left,
   the input reaches the end of the tail); it started at the header with an empty bit buffer, so it consumed the
   header's byte and returned Z_OK (BBWThyRun.bbw_trees).  The next call, offered everything that is left,
   starts after byte 0, so no stop reason applies, and it cannot fail to allocate the window (none was needed:
   nothing written, wsize 0): it returns Z_DATA_ERROR. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.harness.bit_writer.FRLayout.
Require Import Zlib.proof.harness.bit_writer.FRBits.
Require Import Zlib.proof.harness.bit_writer.FRHead.
Require Import Zlib.proof.harness.bit_writer.FRLen.
Require Import Zlib.proof.harness.bit_writer.FRTail.
Require Import Zlib.proof.harness.bit_writer.FRFast.
Require Import Zlib.proof.harness.bit_writer.FRLeave.
Require Import Zlib.proof.harness.bit_writer.FRCall.
Require Import Zlib.proof.harness.bit_writer.FRTheory.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.harness.bit_writer.BBRun.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BBWThyRun.
Import ListNotations.
Local Open Scope Z_scope.

(* after inflateInit2_(strm, w), w raw: HEAD, nothing read, nothing written, no window (computed for each of the
   eight window sizes) *)
Lemma bbw_fr_inv_init C sp w : -15 <= w <= -8 -> fr_inv C 0 [] (l_s (init_live sp w)).
Proof.
  intros Hw.
  destruct (bbt_init sp w Hw) as (Hm & Hwr & Hl & Hh & Hb & _).
  assert (Wh: i_whave (l_s (init_live sp w)) = 0).
  { assert (w = -15 \/ w = -14 \/ w = -13 \/ w = -12 \/ w = -11 \/ w = -10 \/ w = -9 \/ w = -8) as E by lia.
    repeat destruct E as [E|E]; subst w; reflexivity. }
  unfold fr_inv, fr_at. rewrite Hh, Hb, Wh.
  split; [|rewrite Zlength_nil; lia].
  right. split.
  - unfold hold_ok. split; [lia|]. split; [apply Zlength_nonneg|]. rewrite sublist_nil. reflexivity.
  - left. repeat split; auto.
Qed.

(* the run theory's facts for its own invariant fr_inv (FRTheory.fr_theory states them for some invariant) *)
Lemma bbw_fr_facts : fr_facts fr_inv.
Proof.
  pose proof fr_layout as LA. pose proof fr_bits as BI.
  pose proof (fr_tail_ok LA BI) as TA.
  assert (PS: fr_passes).
  { split; [exact (fr_head LA BI)|]. split; [|exact TA].
    exact (fr_len LA BI (fr_fast LA BI) (proj1 TA)). }
  constructor.
  - intros C sp w _ Hw. exact (bbw_fr_inv_init C sp w Hw).
  - exact fr_inv_out.
  - intros. apply (fr_call_ok PS fr_leave); auto.
Qed.

(* the reasons fr_stop gives for a call to return early do not apply when everything up to fr_end is offered, the
   output space holds all the literals left, the tail is not a far distance and (for Z_TREES) the call does not
   start at the block header (as BBTheory.bbt_nostop) *)
Lemma bbw_nostop C pos used ninp nob now aout flush :
  (flush = Z_TREES -> pos <> 0) -> Zlength (fr_lits C) <= nob + aout -> ~ is_far (fr_tail C) ->
  fr_end C <= 8 * (pos + ninp) -> ~ fr_stop C pos used ninp nob now aout flush.
Proof.
  intros Ht Ha Hf He. unfold fr_stop.
  intros [(F & P & _) | [(N & [Lt | (Fa & _)]) | X]]; [apply Ht in F; contradiction | lia | contradiction | lia].
Qed.

(* the invariant between calls of kinds 2 and 3 *)
Definition bbw_fr_J (C: frc) (pos: Z) (ob: list Z) (s: istate) : Prop :=
  fr_inv C pos ob s /\ (pos = 0 -> (ob = [] /\ i_wsize s = 0) \/ i_mode s = BAD).

Lemma bbw_lpos3 C j : 3 <= fr_lpos C j.
Proof.
  unfold fr_lpos. pose proof (Zlength_nonneg (concat (map (send_sym fixed_ll) (firstn (Z.to_nat j) (fr_lits C))))).
  lia.
Qed.

Lemma bbw_fll257 : Znth 257 fixed_ll = 7.
Proof. vm_compute. reflexivity. Qed.

(* where the decoder can be with nothing consumed: BAD, or before the block header with an empty bit buffer and
   nothing written (every other position is after bit 3) *)
Lemma bbw_at0 C s hold bits out : ~ is_far (fr_tail C) -> fr_at C s 0 hold bits out ->
  i_mode s = BAD \/
  (out = [] /\ hold = 0 /\ bits = 0 /\ i_last s = 0 /\ ((i_mode s = HEAD /\ i_wrap s = 0) \/ i_mode s = TYPEDO)).
Proof.
  intros Hf A. unfold fr_at in A. cbv zeta in A.
  destruct A as [(B & _)|(Hh & A)]; [left; exact B|right].
  destruct Hh as (Hb & _ & Hho).
  assert (B0 : bits = 0) by lia. subst bits.
  assert (H0 : hold = 0) by (rewrite Hho; reflexivity). subst hold.
  pose proof (bbw_lpos3 C) as LP. unfold fr_tpos in *.
  destruct A as [(Hm & _ & _ & -> & Hl & Hw)|[(Hm & _ & _ & -> & Hl)|(_ & A)]].
  - repeat split; auto.
  - repeat split; auto.
  - exfalso.
    destruct A as [(_ & _ & j & _ & Hq & _)|[(_ & _ & j & _ & Hq & _)|[(_ & _ & _ & T)|[(_ & _ & _ & T)|
                  [(_ & _ & _ & lc & lx & dc & dx & Ht & _)|(_ & _ & lc & lx & dc & dx & Ht & _)]]]]].
    + specialize (LP j). lia.
    + specialize (LP (j + 1)). lia.
    + destruct T as [(w & _ & Hq & _)|(lc & lx & dc & dx & Ht & _)].
      * rewrite bbw_fll257 in Hq. specialize (LP (fr_n C)). lia.
      * apply Hf. rewrite Ht. exact I.
    + destruct T as [(w & _ & Hq)|(lc & lx & dc & dx & Ht & _)].
      * rewrite bbw_fll257 in Hq. specialize (LP (fr_n C)). lia.
      * apply Hf. rewrite Ht. exact I.
    + apply Hf. rewrite Ht. exact I.
    + apply Hf. rewrite Ht. exact I.
Qed.

(* one call of main's loop on the fixed block C (its input is main's stream S, its literals main's): the outcome
   bbw_post for any invariant J implied by bbw_fr_J *)
Lemma bbw_fr_call (J: bbw_J) S0 kind which lits C room pos ob L z inp flush res :
  fr_ok C -> fr_src C = bb_bytes S0 kind which lits -> fr_lits C = lits -> ~ is_far (fr_tail C) ->
  (exists x c, Znth 0 (bb_bytes S0 kind which lits) = x + 2 * 1 + 8 * c /\ 0 <= x <= 1 /\ 0 <= c < 32) ->
  (forall p o s, bbw_fr_J C p o s -> J S0 kind which lits p o s) ->
  bbw_fr_J C pos ob (l_s L) -> live_ok L -> zf_ok z ->
  0 <= pos <= Zlength (bb_bytes S0 kind which lits) -> Zlength lits <= room -> Zlength ob <= room ->
  inp = sublist pos (pos + Z.min (Zlength (bb_bytes S0 kind which lits) - pos) Int.max_unsigned)
          (bb_bytes S0 kind which lits) ->
  zf_ao z = Z.min (room - Zlength ob) Int.max_unsigned ->
  Int.min_signed <= flush <= Int.max_signed ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  bbw_post J S0 kind which lits room pos ob z inp flush res.
Proof.
  intros Hok HS Hl Hnf Hb0 HJ [I0 P0] Hlive Hz Hpos Hroom Hob Hinp Hao Hfl Hrun.
  unfold bbw_post. cbv zeta.
  set (S := bb_bytes S0 kind which lits) in *.
  pose proof Hok as (_ & _ & _ & _ & Hend & _). rewrite HS in Hend.
  assert (E3 : 3 <= fr_end C) by (unfold fr_end; pose proof (Zlength_nonneg (fr_body C)); lia).
  pose proof (Zlength_nonneg ob).
  assert (Li : Zlength inp = Z.min (Zlength S - pos) Int.max_unsigned)
    by (rewrite Hinp, Zlength_sublist; rep_lia).
  assert (Hcall := fr_call fr_inv bbw_fr_facts C pos ob L z inp flush res Hok I0 Hlive Hz ltac:(lia)
                     ltac:(rewrite HS, Li; lia) ltac:(rewrite Li, HS; exact Hinp) ltac:(rewrite Li; lia) Hfl Hrun).
  destruct Hcall as (Hsnx & Hsow & Hlow & Hws & Hcase).
  destruct Hcase as [(R & _) | [(R & _) | (R & St & I1)]]; [left; exact R | right; left; exact R |].
  right; right.
  (* a call from BAD fails: the state at byte 0 was before the header *)
  assert (NB : pos = 0 -> ob = [] /\ i_wsize (l_s L) = 0).
  { intros E. destruct (P0 E) as [X|Bd]; [exact X|].
    exfalso. destruct (bbw_bad_call _ _ _ _ _ _ _ Bd Hrun) as [R'|R']; rewrite R' in R;
      destruct R as [R|R]; discriminate R. }
  split; [exact R|]. split; [exact Hsnx|]. split; [exact Hsow|]. split; [exact Hlow|]. split.
  - apply HJ. split; [exact I1|]. intros E.
    assert (E0 : pos = 0) by lia. destruct (NB E0) as (-> & W0).
    destruct I1 as [A1 _]. rewrite E in A1.
    destruct (bbw_at0 _ _ _ _ _ Hnf A1) as [Bd|(Ho & _)]; [right; exact Bd|left].
    rewrite app_nil_l in Ho |- *. split; [exact Ho|]. apply Hws; [exact Ho | exact W0].
  - intros Us Uo.
    (* only the Z_TREES stop applies *)
    assert (Tr : flush = Z_TREES /\ pos = 0 /\ 0 < m_snx (r_m res) /\ Zlength (m_ow (r_m res)) = 0).
    { unfold fr_stop in St. rewrite Hl in St.
      destruct St as [X | [(N & [Lt | (Fa & _)]) | X]]; [exact X | lia | contradiction | lia]. }
    destruct Tr as (Ft & E0 & Su & Ow).
    assert (Ow' : m_ow (r_m res) = []) by (apply Zlength_nil_inv; exact Ow).
    destruct (NB E0) as (Ob & W0). subst pos ob flush.
    destruct I0 as [A0 _].
    destruct (bbw_at0 _ _ _ _ _ Hnf A0) as [Bd|(_ & Hh0 & Hbt0 & Hl0 & Hm0)].
    { exfalso. destruct (bbw_bad_call _ _ _ _ _ _ _ Bd Hrun) as [R'|R']; rewrite R' in R;
        destruct R as [R|R]; discriminate R. }
    destruct Hb0 as (x & c & E & Hx & Hc).
    assert (Rok : r_ret res = Z_OK).
    { apply (bbw_trees z L inp x c res Hm0 Hl0 Hh0 Hbt0 W0); [lia | | exact Hx | exact Hc | exact Hrun].
      rewrite Hinp, Znth_sublist by lia. exact E. }
    split; [exact Rok|]. split; [reflexivity|]. split; [exact Ow'|].
    unfold bbw_extra. cbv zeta. fold S. rewrite Ow', app_nil_l, Z.add_0_l.
    rewrite Ow', app_nil_l, Z.add_0_l in I1.
    intros L' z' res' HL' Hlive' Hz' Hao' Hrun'.
    rewrite Zlength_nil in Hao'.
    set (p := m_snx (r_m res)) in *.
    set (inp' := sublist p (Zlength S) S) in *.
    assert (Li' : Zlength inp' = Zlength S - p) by (unfold inp'; rewrite Zlength_sublist; lia).
    assert (I1' : fr_inv C p [] (l_s L')) by (rewrite HL'; exact I1).
    assert (Hcall := fr_call fr_inv bbw_fr_facts C p [] L' z' inp' Z_TREES res' Hok I1' Hlive' Hz' ltac:(lia)
                       ltac:(rewrite HS, Li'; lia)
                       ltac:(rewrite HS, Li'; replace (p + (Zlength S - p)) with (Zlength S) by lia; reflexivity)
                       ltac:(lia) Hfl Hrun').
    destruct Hcall as (_ & _ & _ & _ & Hcase').
    rewrite Zlength_nil in Hcase'.
    destruct Hcase' as [(R' & _) | [(R' & [St' | Wn]) | (_ & St' & _)]];
      [exact R' | | rewrite HL' in Wn; exfalso; apply Wn; apply Hws; [exact Ow' | exact W0] |];
      exfalso; revert St'; apply bbw_nostop; auto; try lia; rewrite Hl; lia.
Qed.

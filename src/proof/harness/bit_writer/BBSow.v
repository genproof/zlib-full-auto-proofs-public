(* Law rj_bad_block: when the first call stops at the end of the block header (Z_OK with Z_TREES), it has
   written nothing and says so in strm->next_out / avail_out (m_sow = 0): main needs it to offer the second call
   the same output space.  A complement of BBFacts.bb_theory_stmt, from the same theory. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRFacts.
Require Import Zlib.proof.harness.bit_writer.BBFacts.
Require Import Zlib.proof.harness.bit_writer.BBRun.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

Definition bb_sow_stmt : Prop :=
  forall S0 kind which lits w sp L z flush res,
    bb_ok S0 kind which lits -> -15 <= w <= -8 ->
    l_s L = l_s (init_live sp w) -> live_ok L -> zf_ok z ->
    Zlength lits <= zf_ao z -> Int.min_signed <= flush <= Int.max_signed ->
    run2 flush lenfix_list distfix_list (m_init z L (bb_bytes S0 kind which lits)) res ->
    r_ret res = Z_OK -> flush = Z_TREES -> m_sow (r_m res) = 0.

(* kinds 2 and 3: a call offered the whole fixed block, with room for every literal, that returns Z_OK has
   stopped at the end of the block header (the output-full and input-short reasons do not apply), so it wrote
   nothing, and fr_post says that next_out / avail_out report what it wrote *)
Lemma bbs_fr I (FI: fr_facts I) C S sp w L z flush res :
  fr_ok C -> fr_src C = S -> ~ is_far (fr_tail C) -> -15 <= w <= -8 -> l_s L = l_s (init_live sp w) ->
  live_ok L -> zf_ok z -> Zlength (fr_lits C) <= zf_ao z -> Int.min_signed <= flush <= Int.max_signed ->
  Zlength S <= Int.max_unsigned ->
  run2 flush lenfix_list distfix_list (m_init z L S) res -> r_ret res = Z_OK -> m_sow (r_m res) = 0.
Proof.
  intros Hok HS Hnf Hw HL Hlive Hz Hao Hfl HSl Hrun Hret.
  pose proof Hok as (_ & _ & _ & _ & Hend & _).
  rewrite HS in Hend.
  assert (I0 : I C 0 [] (l_s L)) by (rewrite HL; apply (fr_init I FI); auto).
  assert (Hcall := fr_call I FI C 0 [] L z S flush res Hok I0 Hlive Hz ltac:(lia)
                     ltac:(rewrite HS; lia) ltac:(rewrite HS, Z.add_0_l, sublist_same; reflexivity || lia)
                     HSl Hfl Hrun).
  destruct Hcall as (_ & Hsow & _ & _ & Hcase).
  rewrite Zlength_nil in Hcase. rewrite Hsow.
  destruct Hcase as [(R & _) | [(R & _) | (_ & St & _)]]; [rewrite Hret in R; discriminate R | rewrite Hret in R; discriminate R |].
  unfold fr_stop in St. destruct St as [(_ & _ & _ & N) | [(N & [Lt | (Fa & _)]) | X]]; [exact N | lia | contradiction | lia].
Qed.

Lemma bb_sow : fr_theory_stmt -> bb_bits_stmt -> bb_sow_stmt.
Proof.
  intros [I FI] BB S0 kind which lits w sp L z flush res Hok Hw HL Hlive Hz Hao Hfl Hrun Hret Ht.
  pose proof Hok as (Hk & Hwh & Hlits & Hbl & Hll & HbS0 & HS0 & Hk0).
  destruct (Z.eq_dec kind 2) as [K2|K2]; [|destruct (Z.eq_dec kind 3) as [K3|K3]].
  3: { (* kinds 0, 1 and 4 end in Z_DATA_ERROR *)
    rewrite (bbt_refused S0 kind which lits w sp L z flush res BB Hok K2 K3 Hw HL Hrun) in Hret. discriminate Hret. }
  all: destruct (bbt_layout S0 kind which lits BB Hok) as (HlS & HbS & Hfit & Hhd & Hrest & _).
  all: set (S := bb_bytes S0 kind which lits) in *.
  all: set (Rest := concat (map (send_sym fixed_ll) lits) ++ bb_tail_bits kind which) in *.
  all: subst kind.
  - (* literals, then the literal/length code 286 + which *)
    set (C := FRC S lits (TLL which)).
    assert (Hfr : fr_ok C).
    { unfold fr_ok, fr_end, fr_body, C. cbn [fr_src fr_lits fr_tail].
      rewrite (proj1 (bbt_tail which Hwh)). fold Rest.
      split; [exact HbS|]. split.
      { eapply Forall_impl; [|exact Hbl]. intros l Hl'. cbv beta in Hl' |- *. change Byte.max_unsigned with 255 in Hl'. lia. }
      split; [rep_lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite Hhd; reflexivity|]. exact Hrest. }
    exact (bbs_fr I FI C S sp w L z flush res Hfr eq_refl (fun f => f) Hw HL Hlive Hz Hao Hfl ltac:(lia) Hrun Hret).
  - (* literals, then the length code 257 and the distance code 30 + which *)
    set (C := FRC S lits (TDCode which)).
    assert (Hfr : fr_ok C).
    { unfold fr_ok, fr_end, fr_body, C. cbn [fr_src fr_lits fr_tail].
      rewrite (proj2 (bbt_tail which Hwh)). fold Rest.
      split; [exact HbS|]. split.
      { eapply Forall_impl; [|exact Hbl]. intros l Hl'. cbv beta in Hl' |- *. change Byte.max_unsigned with 255 in Hl'. lia. }
      split; [rep_lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite Hhd; reflexivity|]. exact Hrest. }
    exact (bbs_fr I FI C S sp w L z flush res Hfr eq_refl (fun f => f) Hw HL Hlive Hz Hao Hfl ltac:(lia) Hrun Hret).
Qed.

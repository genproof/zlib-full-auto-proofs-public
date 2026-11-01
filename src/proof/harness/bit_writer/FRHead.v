(* The fixed-block run theory (FRDefs.v): the passes of HEAD (raw stream: to TYPEDO) and TYPEDO (BFINAL, BTYPE 01:
   the fixed tables, LEN_; Z_TREES stops at the end of the header). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Require Import Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* at HEAD nothing is read and the stream is raw *)
Lemma fr_at_head C s c h b out : i_mode s = HEAD -> fr_at C s c h b out ->
  hold_ok (fr_g C) c h b /\ c = 0 /\ b = 0 /\ out = [] /\ i_last s = 0 /\ i_wrap s = 0.
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[_ A]]]]]; try lia.
  all: first [tauto | destruct A as [A _]; lia |
              destruct A as [[A _]|[[A _]|[[A _]|[[A _]|[[A _]|[A _]]]]]]; lia].
Qed.

(* at TYPEDO nothing is read and the block header is still to come *)
Lemma fr_at_typedo C s c h b out : i_mode s = TYPEDO -> fr_at C s c h b out ->
  hold_ok (fr_g C) c h b /\ c = 0 /\ b = 0 /\ out = [] /\ i_last s = 0.
Proof.
  intros Hm A. unfold fr_at in A. rewrite Hm in A.
  unfold HEAD, BAD, TYPEDO, LEN_, LEN, LIT, LENEXT, DIST, DISTEXT, MATCH in A.
  destruct A as [[A _]|[Hh [A|[A|[_ A]]]]]; try lia.
  all: first [tauto | destruct A as [A _]; lia |
              destruct A as [[A _]|[[A _]|[[A _]|[[A _]|[[A _]|[A _]]]]]]; lia].
Qed.

(* the first three bits of the input: BFINAL, then BTYPE 01 *)
Lemma fr_first3 C : fr_ok C ->
  exists v, (v = 2 \/ v = 3) /\ sublist 0 3 (bytes_bits (fr_src C)) = bits_le v 3.
Proof.
  intros (Hb & _ & _ & _ & He & H13 & _).
  assert (Hl : 3 <= Zlength (bytes_bits (fr_src C))).
  { rewrite dkit_bytes_bits_len. unfold fr_end in He. pose proof (Zlength_nonneg (fr_body C)). lia. }
  set (sb := bytes_bits (fr_src C)) in *.
  rewrite (sublist_split 0 1 3) by lia. rewrite H13.
  rewrite sublist_one by lia.
  exists (Z.b2z (Znth 0 sb) + 2). destruct (Znth 0 sb); split; auto.
Qed.

(* reduce the projections of the machine's and the state's setters (the records stay folded) *)
Ltac fr_simpl := cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg
  m_tin m_tout m_snx m_sow set_m_leave set_m_bits set_m_hold set_m_nx set_m_s m_mode upd_s set_mode
  dropbits set_leave i_mode i_last i_wrap i_wsize i_whave i_wnext i_win i_wdata i_wbits i_sane i_lencode
  i_lenbits i_distcode i_distbits set_i_mode set_i_last set_i_lencode set_i_lenbits set_i_distcode
  set_i_distbits] in *.

(* HEAD of a raw stream: straight to TYPEDO *)
Lemma fr_head_head : fr_pass (fun md => md = HEAD) (fun _ m => c_HEAD2 m).
Proof.
  intros C pos inp ob L z flush m Hctx [[Hinp Hin Haout Hout Hnx How Hwin Hwh Hat] Hlv Hret] Hmd.
  destruct (fr_at_head _ _ _ _ _ _ Hmd Hat) as (Hh & Hc & Hb & Ho & Hl & Hw).
  unfold c_HEAD2. rewrite Hw. cbn [Z.eqb]. left. split; [split|..]; fr_simpl; auto.
  all: try (unfold fr_wsame in *; fr_simpl; exact Hwin).
  unfold fr_at. right. split; [exact Hh|]. right. left. fr_simpl. auto.
Qed.

(* TYPEDO: BFINAL, BTYPE 01, the fixed tables; LEN_ at literal 0, or the input ends before the header *)
Lemma fr_head_typedo : fr_bits_stmt ->
  fr_pass (fun md => md = TYPEDO) (fun flush m => c_TYPEDO flush m).
Proof.
  intros FB C pos inp ob L z flush m Hctx [[Hinp Hin Haout Hout Hnx How Hwin Hwh Hat] Hlv Hret] Hmd.
  destruct (fr_at_typedo _ _ _ _ _ _ Hmd Hat) as (Hh & Hc & Hb & Ho & Hl).
  pose proof Hctx as (Hok & Hp & Hpl & Hinpeq & Hmax & _).
  assert (Hp0 : pos = 0) by lia. assert (Hn0 : m_nx m = 0) by lia.
  assert (He3 : 3 <= fr_end C) by (unfold fr_end; pose proof (Zlength_nonneg (fr_body C)); lia).
  assert (Hes : fr_end C <= 8 * Zlength (fr_src C)) by (destruct Hok as (_&_&_&_&X&_); exact X).
  destruct (fr_first3 C Hok) as (v & Hv & Hs).
  assert (Hin' : fr_in C pos inp) by (unfold fr_in; destruct Hok; auto).
  assert (Hbuf : fr_buf C pos inp m) by (unfold fr_buf; auto).
  pose proof (fb_need FB C pos inp m 3 v Hin' Hbuf Hlv) as N; cbv zeta in N.
  destruct N as (nx & h & b & Heq & Hnx' & Hh' & Hq & Hcase).
  { lia. }
  { destruct Hv; subst v; cbn; lia. }
  { lia. }
  { rewrite Hc, Hb. lia. }
  { rewrite Hc, Hb. exact Hs. }
  unfold c_TYPEDO. rewrite Hl. cbn [negb Z.eqb]. cbv zeta.
  rewrite Hp0, Hc, Hb in *. clear Hat.
  pose proof Hh' as [Hb0 _].
  destruct Hcase as [(Hlv1 & Hnxi & Hb3)|(Hlv0 & Hb3 & Hv')];
    [rewrite Hlv1|rewrite Hlv0]; cbn [Z.eqb Pos.eqb]; rewrite Heq; clear Heq;
    [rewrite Hlv1|rewrite Hlv0].
  - (* the input ends before the header: nothing was offered *)
    assert (nx = 0 /\ b = 0) as [-> ->] by lia.
    unfold m_mode in Hmd.
    right. split; [split|..]; unfold m_mode; fr_simpl; try assumption; try lia; try reflexivity.
    + unfold fr_at. right. split; [exact Hh'|]. right. left.
      split; [exact Hmd|]. repeat split; try lia; assumption.
    + right. split; [rewrite Hmd; unfold TYPEDO, BAD; lia|]. split; [exact Hret|].
      right. right. lia.
  - (* BFINAL, BTYPE 01: the fixed tables, LEN_ before literal 0 *)
    set (M1 := dropbits 1 _).
    assert (Hbt : bitsn M1 2 = 1).
    { subst M1. unfold bitsn, dropbits, upd_s. fr_simpl.
      rewrite Z.shiftr_div_pow2 by lia.
      pose proof (Z.rem_mul_r h 2 4 ltac:(lia) ltac:(lia)) as R.
      pose proof (Z.mod_pos_bound h 2 ltac:(lia)).
      change (2 ^ 3) with (2 * 4) in Hv'. change (2 ^ 2) with 4. change (2 ^ 1) with 2.
      destruct Hv; lia. }
    rewrite Hbt. cbn [Z.eqb Pos.eqb]. subst M1.
    assert (Hbits : u32 (u32 (b - 1) - 2) = b - 3).
    { unfold u32. rewrite (Z.mod_small (b - 1)) by lia. rewrite Z.mod_small by lia. lia. }
    assert (Hhold : hold_ok (fr_g C) (0 + nx) (Z.shiftr (Z.shiftr h 1) 2) (b - 3)).
    { replace (b - 3) with (b - 1 - 2) by lia.
      apply (dk_drop dkit); [apply (dk_drop dkit); [exact Hh'|lia]|lia]. }
    assert (Hat' : forall s, i_mode s = LEN_ -> fr_fixed s ->
                     fr_at C s (0 + nx) (Z.shiftr (Z.shiftr h 1) 2) (b - 3) (ob ++ m_ow m)).
    { intros s Hm Hfx. unfold fr_at. right. split; [exact Hhold|]. right. right.
      split; [exact Hfx|]. left. split; [left; exact Hm|]. split; [lia|].
      exists 0. split; [unfold fr_n; pose proof (Zlength_nonneg (fr_lits C)); lia|].
      split; [|rewrite Ho; reflexivity].
      unfold fr_lpos. change (Z.to_nat 0) with O. cbn [firstn map concat]. rewrite Zlength_nil. lia. }
    unfold m_mode in Hmd.
    destruct (flush =? Z_TREES) eqn:Hf; [right|left];
      split; try split; unfold m_mode, dropbits, set_mode, upd_s, set_leave, bitsn;
      fr_simpl; rewrite ?Hbits; try assumption; try lia; try reflexivity.
    all: try (apply Hat'; [reflexivity | unfold fr_fixed; repeat split; reflexivity]).
    (* Z_TREES: the call stops at the end of the header, nothing written *)
    right. split; [unfold LEN_, BAD; lia|]. split; [exact Hret|].
    left. split; [apply Z.eqb_eq; exact Hf|]. split; [reflexivity|]. split; [lia|].
    destruct (app_eq_nil _ _ Ho) as [_ ->]. reflexivity.
Qed.

Lemma fr_head : fr_layout_stmt -> fr_bits_stmt -> fr_head_stmt.
Proof.
  intros _ FB. split; [exact fr_head_head | exact (fr_head_typedo FB)].
Qed.

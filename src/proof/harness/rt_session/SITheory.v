(* Law rt_session: the inflate side's facts for main ([SIFacts.ses_itheory_stmt]) from those of the four kinds of
   session.  Under [sc_ok] every session is of one kind: a header (gzip wrapper), else no dictionary (plain), else a
   dictionary with the raw wrapper or with the zlib wrapper.  The joined invariants are the disjunction of the
   kinds' invariants, each with its kind. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* the kind of a session *)
Lemma sk_cases (c : scase) (D O : list Z) :
  sc_ok c D O -> sk_gz c \/ sk_plain c \/ sk_raw c \/ sk_zdict c.
Proof.
  intros (_ & _ & Hd & Hg & _).
  unfold sk_gz, sk_plain, sk_raw, sk_zdict.
  destruct (sc_gh c) as [h|] eqn:G; [left; discriminate|right].
  destruct (sc_dict c) as [|b l] eqn:E; [left; auto|right].
  assert (N : b :: l <> []) by discriminate.
  destruct (Hd N) as [W _].
  assert (W01 : sc_wrap c = 0 \/ sc_wrap c = 1).
  { unfold sc_wrap, rwrap_of in *. destruct (sc_wbits c <? 0); [auto|].
    destruct (sc_wbits c >? 15); [contradiction|auto]. }
  destruct W01; [left|right]; auto.
Qed.

Section Join.
Variables (P1 P2 P3 P4 : ses_iinv) (N1 N2 N3 N4 : ses_ninv).
Hypotheses (F1 : ses_ifacts sk_plain P1 N1) (F2 : ses_ifacts sk_raw P2 N2)
           (F3 : ses_ifacts sk_zdict P3 N3) (F4 : ses_ifacts sk_gz P4 N4).

Definition jP : ses_iinv := fun c D O src pos out asked L tout =>
  (sk_plain c /\ P1 c D O src pos out asked L tout) \/ (sk_raw c /\ P2 c D O src pos out asked L tout) \/
  (sk_zdict c /\ P3 c D O src pos out asked L tout) \/ (sk_gz c /\ P4 c D O src pos out asked L tout).
Definition jN : ses_ninv := fun c D O src pos out L tout =>
  (sk_plain c /\ N1 c D O src pos out L tout) \/ (sk_raw c /\ N2 c D O src pos out L tout) \/
  (sk_zdict c /\ N3 c D O src pos out L tout) \/ (sk_gz c /\ N4 c D O src pos out L tout).

Lemma join_facts : ses_ifacts (fun _ => True) jP jN.
Proof.
  constructor.
  - intros c D O src sp _ OK S.
    destruct (sk_cases c D O OK) as [K|[K|[K|K]]].
    + destruct (si_init _ _ _ F4 c D O src sp K OK S) as (W & Sw & _).
      split; [exact W|]. split; [exact Sw|]. intros G. unfold sk_gz in K. contradiction.
    + destruct (si_init _ _ _ F1 c D O src sp K OK S) as (W & Sw & I).
      split; [exact W|]. split; [exact Sw|]. intros G R. left. split; [exact K|exact (I G R)].
    + destruct (si_init _ _ _ F2 c D O src sp K OK S) as (W & Sw & _).
      split; [exact W|]. split; [exact Sw|]. intros G R. contradiction.
    + destruct (si_init _ _ _ F3 c D O src sp K OK S) as (W & Sw & I).
      split; [exact W|]. split; [exact Sw|]. intros G R. right; right; left. split; [exact K|exact (I G R)].
  - intros c D O src sp gh headp hsh xb nb cb _ OK S G L LV.
    assert (K : sk_gz c) by (unfold sk_gz; rewrite G; discriminate).
    destruct (si_head _ _ _ F4 c D O src sp gh headp hsh xb nb cb K OK S G LV) as (W & Sw & I).
    split; [exact W|]. split; [exact Sw|]. right; right; right. split; [exact K|exact I].
  - intros c D O src sp z alloc_ok winp _ OK S K T L LV.
    destruct (si_rawdict _ _ _ F2 c D O src sp z alloc_ok winp K OK S K T LV) as (C & I).
    split; [exact C|]. intros E. destruct (I E) as (Z & Sw & Q).
    split; [exact Z|]. split; [exact Sw|]. right; left. split; [exact K|exact Q].
  - intros c D O src pos out asked L tout _ [(K & H)|[(K & H)|[(K & H)|(K & H)]]].
    + exact (si_shape _ _ _ F1 c D O src pos out asked L tout K H).
    + exact (si_shape _ _ _ F2 c D O src pos out asked L tout K H).
    + exact (si_shape _ _ _ F3 c D O src pos out asked L tout K H).
    + exact (si_shape _ _ _ F4 c D O src pos out asked L tout K H).
  - intros c D O src pos out asked L z inp flush res winp _ OK S
      [(K & H)|[(K & H)|[(K & H)|(K & H)]]] LV Sw Zo Ao Li P0 PL E RUN.
    + destruct (si_call _ _ _ F1 c D O src pos out asked L z inp flush res winp K OK S H LV Sw Zo Ao Li P0 PL E RUN)
        as [M|(R & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)]; [left; exact M|right].
      do 5 (split; [assumption|]).
      split; [intros X; left; split; [exact K|exact (A5 X)]|].
      split; [intros X; destruct (A6 X) as (Q1 & Q2 & Q3); split; [exact Q1|]; split; [exact Q2|];
              left; split; [exact K|exact Q3]|].
      split; [exact A7|exact A8].
    + destruct (si_call _ _ _ F2 c D O src pos out asked L z inp flush res winp K OK S H LV Sw Zo Ao Li P0 PL E RUN)
        as [M|(R & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)]; [left; exact M|right].
      do 5 (split; [assumption|]).
      split; [intros X; right; left; split; [exact K|exact (A5 X)]|].
      split; [intros X; destruct (A6 X) as (Q1 & Q2 & Q3); split; [exact Q1|]; split; [exact Q2|];
              right; left; split; [exact K|exact Q3]|].
      split; [exact A7|exact A8].
    + destruct (si_call _ _ _ F3 c D O src pos out asked L z inp flush res winp K OK S H LV Sw Zo Ao Li P0 PL E RUN)
        as [M|(R & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)]; [left; exact M|right].
      do 5 (split; [assumption|]).
      split; [intros X; right; right; left; split; [exact K|exact (A5 X)]|].
      split; [intros X; destruct (A6 X) as (Q1 & Q2 & Q3); split; [exact Q1|]; split; [exact Q2|];
              right; right; left; split; [exact K|exact Q3]|].
      split; [exact A7|exact A8].
    + destruct (si_call _ _ _ F4 c D O src pos out asked L z inp flush res winp K OK S H LV Sw Zo Ao Li P0 PL E RUN)
        as [M|(R & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8)]; [left; exact M|right].
      do 5 (split; [assumption|]).
      split; [intros X; right; right; right; split; [exact K|exact (A5 X)]|].
      split; [intros X; destruct (A6 X) as (Q1 & Q2 & Q3); split; [exact Q1|]; split; [exact Q2|];
              right; right; right; split; [exact K|exact Q3]|].
      split; [exact A7|exact A8].
  - intros c D O src pos out L tout _ [(K & H)|[(K & H)|[(K & H)|(K & H)]]].
    + exact (si_nshape _ _ _ F1 c D O src pos out L tout K H).
    + exact (si_nshape _ _ _ F2 c D O src pos out L tout K H).
    + exact (si_nshape _ _ _ F3 c D O src pos out L tout K H).
    + exact (si_nshape _ _ _ F4 c D O src pos out L tout K H).
  - intros c D O src pos out L tout z alloc_ok winp _ OK S [(K & H)|[(K & H)|[(K & H)|(K & H)]]] LV T.
    + destruct (si_setdict _ _ _ F1 c D O src pos out L tout z alloc_ok winp K OK S H LV T) as (C & I).
      split; [exact C|]. intros X. destruct (I X) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
      left; split; [exact K|exact Q3].
    + destruct (si_setdict _ _ _ F2 c D O src pos out L tout z alloc_ok winp K OK S H LV T) as (C & I).
      split; [exact C|]. intros X. destruct (I X) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
      right; left; split; [exact K|exact Q3].
    + destruct (si_setdict _ _ _ F3 c D O src pos out L tout z alloc_ok winp K OK S H LV T) as (C & I).
      split; [exact C|]. intros X. destruct (I X) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
      right; right; left; split; [exact K|exact Q3].
    + destruct (si_setdict _ _ _ F4 c D O src pos out L tout z alloc_ok winp K OK S H LV T) as (C & I).
      split; [exact C|]. intros X. destruct (I X) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
      right; right; right; split; [exact K|exact Q3].
Qed.
End Join.

Theorem ses_itheory_join :
  ses_itheory_plain_stmt -> ses_itheory_raw_stmt -> ses_itheory_zdict_stmt -> ses_itheory_gz_stmt ->
  ses_itheory_stmt.
Proof.
  intros (P1 & N1 & F1) (P2 & N2 & F2) (P3 & N3 & F3) (P4 & N4 & F4).
  exists (jP P1 P2 P3 P4), (jN N1 N2 N3 N4). exact (join_facts _ _ _ _ _ _ _ _ F1 F2 F3 F4).
Qed.

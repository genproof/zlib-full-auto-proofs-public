(** * deflate_huff part: the main loop and the assembly of [huff_specX] from the part statements. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCHuffGlue.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** A loop terminates when a measure >= 0 decreases on every continuing iteration and starts below 2^d *)
Section HLoopMeasure.
Context {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) (m : A -> Z).
Hypothesis Hstep : forall a, P a -> 0 <= m a /\
  ((exists r, body a = Some (inr r) /\ Q r) \/ (exists a', body a = Some (inl a') /\ P a' /\ m a' < m a)).

Lemma hloop2_measure : forall d a, P a ->
  (exists r, loop2 d body a = Some (inr r) /\ Q r) \/
  (exists a', loop2 d body a = Some (inl a') /\ P a' /\ m a' + 2 ^ Z.of_nat d <= m a).
Proof.
  induction d as [|d IH]; intros a Ha; cbn [loop2].
  - destruct (Hstep a Ha) as [_ [[r [E HQ]]|[a' [E [HP Hm]]]]]; rewrite E.
    + left; eauto.
    + right; exists a'; split; [reflexivity|]; split; [exact HP|]. simpl. lia.
  - destruct (IH a Ha) as [[r [E HQ]]|[a' [E [HP Hm]]]]; rewrite E.
    + left; eauto.
    + destruct (IH a' HP) as [[r [E' HQ]]|[a'' [E' [HP' Hm']]]]; rewrite E'.
      * left; eauto.
      * right. exists a''. split; [reflexivity|]. split; [exact HP'|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma hloop_measure : forall d a, P a -> m a < 2 ^ Z.of_nat d -> exists r, loop d body a = Some r /\ Q r.
Proof.
  intros d a Ha Hm. unfold loop.
  destruct (hloop2_measure d a Ha) as [[r [E HQ]]|[a' [E [HP Hm']]]]; rewrite E.
  - eauto.
  - destruct (Hstep a' HP) as [H0 _]. lia.
Qed.
End HLoopMeasure.

Lemma W_la_bound s : W s -> 0 <= d_lookahead s <= 65536.
Proof.
  intros (Hp & Hs & Hpos & _).
  destruct Hp as (Hwb & Hws & _). destruct Hs as (_ & _ & Hwsz & _). destruct Hpos as (P1 & P2 & P3 & _).
  assert (2 ^ d_w_bits s <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Section HuffLoop.
Hypothesis Hlit : hlit_stmt.
Hypothesis Href : hrefill_stmt.
Hypothesis Hbfl : hbflush_stmt.
Hypothesis Htail : htail_stmt.

Variables (s0 : dstate) (z0 : strm) (flush : Z).
Hypothesis Hfl : 0 <= flush <= 5.
Hypothesis Hfn0 : fn_of s0 = 3.

Definition HP (a : dstate * strm) : Prop := exists evs, HFI s0 z0 flush (fst a) (snd a) evs.
Definition HQ (r : dexit) : Prop :=
  let '(s', z', o) := r in
  match o with
  | Some bs => exists evs, hcrel s0 z0 flush s' z' evs /\ hbpost s0 z0 flush s' z' bs evs
  | None => exists evs, HFI s0 z0 flush s' z' evs /\ d_lookahead s' = 0 /\ z_avail_in z' = 0 /\ flush <> Z_NO_FLUSH
  end.
Definition hm (a : dstate * strm) : Z := z_avail_in (snd a) + d_lookahead (fst a).

Lemma HFI_parts s z evs : HFI s0 z0 flush s z evs ->
  W s /\ huff_extra s /\ outok s /\ quiet s /\ fn_of s = 3 /\ zall z /\ 0 <= d_lookahead s <= 65536.
Proof.
  intros (_ & _ & Hc & Hq & Hz & _).
  assert (Hfn := fn_of_hcrel _ _ _ _ _ _ Hc). rewrite Hfn0 in Hfn.
  destruct Hc as (HW & He & Ho & _).
  split; [exact HW|]. split; [exact He|]. split; [exact Ho|]. split; [exact Hq|]. split; [exact Hfn|].
  split; [exact Hz|]. exact (W_la_bound s HW).
Qed.

Lemma lit_step s z evs : HFI s0 z0 flush s z evs -> 1 <= d_lookahead s ->
  exists r, (let* (s, bf) := hlit s in c_bflush s z bf) = Some r /\
  match r with
  | inl a' => HP a' /\ hm a' < hm (s, z)
  | inr e => HQ e
  end.
Proof.
  intros HI Hla.
  destruct (HFI_parts s z evs HI) as (HW & He & Ho & Hq & Hfn & Hz & Hlb).
  destruct (Hlit s HW He Ho Hq Hfn Hla) as (s3 & bf & syms3 & E & HS & Hbf & Hfr & Hla3).
  rewrite E. cbn [bind].
  destruct (Hbfl s0 z0 flush s z evs s3 syms3 bf HI Hfl Hfn0 HS Hbf Hfr) as (r & Er & Hr).
  exists r. split; [exact Er|].
  destruct r as [[s' z']|[[s' z'] o]].
  - destruct Hr as (Hev & Hla' & Hai'). split; [exact Hev|]. unfold hm; cbn [fst snd]. lia.
  - destruct Hr as (-> & evs' & Hc & Hb). cbn [HQ]. exists evs'. split; assumption.
Qed.

Lemma huff_step a : HP a -> 0 <= hm a /\
  ((exists r, huff_body flush a = Some (inr r) /\ HQ r) \/
   (exists a', huff_body flush a = Some (inl a') /\ HP a' /\ hm a' < hm a)).
Proof.
  destruct a as [s z]. intros [evs HI]. cbn [fst snd] in HI.
  destruct (HFI_parts s z evs HI) as (HW & He & Ho & Hq & Hfn & Hz & Hlb).
  assert (Hai : 0 <= z_avail_in z) by (destruct Hz as ((_ & _ & A & _) & _); lia).
  split; [unfold hm; cbn [fst snd]; lia|].
  rewrite huff_body_eq. unfold hrefill.
  destruct (Z.eqb_spec (d_lookahead s) 0) as [Hl0|Hl0].
  - destruct (Href s0 z0 flush s z evs HI Hfn0 Hl0) as (s2 & z2 & E & HI2 & Hsum & Hz2).
    rewrite E. cbn [bind].
    destruct (Z.eqb_spec (d_lookahead s2) 0) as [Hl2|Hl2].
    + destruct (Z.eqb_spec flush Z_NO_FLUSH) as [Hnf|Hnf]; cbn [bind]; left; eexists; split; [reflexivity| |reflexivity|].
      * cbn [HQ]. exists evs. destruct HI2 as (_ & _ & Hc2 & Hq2 & _ & _ & Hl).
        split; [exact Hc2|]. cbn [hbpost]. split; [exact Hl|]. split; [exact (proj2 (proj2 Hq2))|]. left; exact Hnf.
      * cbn [HQ]. exists evs. split; [exact HI2|]. split; [exact Hl2|]. split; [exact (Hz2 Hl2)|exact Hnf].
    + cbn [bind].
      destruct (HFI_parts s2 z2 evs HI2) as (_ & _ & _ & _ & _ & _ & Hlb2).
      destruct (lit_step s2 z2 evs HI2 ltac:(lia)) as (r & Er & Hr). rewrite Er.
      destruct r as [a'|e].
      * right. exists a'. split; [reflexivity|]. destruct Hr as [HP' Hm']. split; [exact HP'|].
        unfold hm in *; cbn [fst snd] in *. lia.
      * left. exists e. split; [reflexivity|exact Hr].
  - cbn [bind].
    destruct (lit_step s z evs HI ltac:(lia)) as (r & Er & Hr). rewrite Er.
    destruct r as [a'|e].
    + right. exists a'. split; [reflexivity|]. exact Hr.
    + left. exists e. split; [reflexivity|exact Hr].
Qed.

End HuffLoop.

Lemma cpost_of_h s z flush s' z' bs evs :
  hcrel s z flush s' z' evs -> hbpost s z flush s' z' bs evs -> cpost W s z flush s' z' bs evs /\ huff_extra s'.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) B. split; [|exact A2]. unfold cpost.
  split; [exact A1|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. destruct bs; exact B.
Qed.

Theorem huff_assembly : hlit_stmt -> hrefill_stmt -> hbflush_stmt -> htail_stmt -> huff_specX.
Proof.
  intros Hlit Href Hbfl Htail s z flush Hpre He Hfn.
  destruct Hpre as (HW & Ho & Hq & Hfl & Hzi & Hwr & Had).
  assert (Hz := zin_ok_zall z Hzi).
  assert (HI : HFI s z flush s z []).
  { unfold HFI. split; [exact Hz|]. split; [exact Had|]. split; [exact (hcrel_refl s z flush HW He Ho Hz Had)|].
    split; [exact Hq|]. split; [exact Hz|]. split; [exact Had|constructor]. }
  assert (Hm0 : hm (s, z) < 2 ^ Z.of_nat FUEL).
  { unfold hm; cbn [fst snd]. destruct Hzi as (_ & _ & Hai & _).
    pose proof (W_la_bound s HW). change (2 ^ Z.of_nat FUEL) with (2 ^ 40). lia. }
  destruct (hloop_measure (huff_body flush) (HP s z flush) (HQ s z flush) hm
              (huff_step Hlit Href Hbfl s z flush Hfl Hfn) FUEL (s, z) (ex_intro _ [] HI) Hm0)
    as (r & Er & Hr).
  unfold c_deflate_huff. rewrite Er. cbn [bind].
  destruct r as [[s' z'] [bs|]].
  - destruct Hr as (evs & Hc & Hb). destruct (cpost_of_h _ _ _ _ _ _ _ Hc Hb) as [Hp He'].
    exists s', z', bs, evs. split; [reflexivity|]. split; [exact Hp|exact He'].
  - destruct Hr as (evs & HI' & Hla & Hai & Hnf).
    destruct (Htail s z flush s' z' evs HI' Hfl Hfn Hnf Hla Hai) as (s2 & z2 & bs & evs' & E & Hc & Hb).
    destruct (cpost_of_h _ _ _ _ _ _ _ Hc Hb) as [Hp He'].
    exists s2, z2, bs, evs'. split; [exact E|]. split; [exact Hp|exact He'].
Qed.

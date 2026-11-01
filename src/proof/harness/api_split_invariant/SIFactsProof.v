(* The facts of SIFacts.v from the call: the invariant between calls, the stopping point of the abstract trace and its uniqueness. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Traces under limits                                                                            *)

Lemma sf_areach_trans: forall src I R a b c,
  areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof. intros src I R a b c H; induction H; intros; auto. econstructor; eauto. Qed.

(* a trace within limits is within larger limits *)
Lemma sf_areach_mono: forall src I R I' R' a b,
  I <= I' -> R <= R' -> areach src I R a b -> areach src I' R' a b.
Proof.
  intros src I R I' R' a b HI HR H. induction H as [a|a n w a1 a' Hs Hnb Hr IH].
  - constructor.
  - econstructor; eauto. unfold blocked in *. intros [Hq|[Hw HO]]; apply Hnb; [left; lia | right; split; auto; lia].
Qed.

Lemma sf_areach_inv: forall src I R a b, areach src I R a b ->
  a = b \/ exists n w a1, astep lenfix_list distfix_list src a = AGo n w a1 /\
                          ~ blocked I R a (AGo n w a1) /\ areach src I R a1 b.
Proof. intros src I R a b H. destruct H; [left; auto | right; eauto 6]. Qed.

(* astep is a function: two traces from the same state are prefixes of each other *)
Lemma sf_areach_total: forall src I R x a, areach src I R x a ->
  forall b, areach src I R x b -> areach src I R a b \/ areach src I R b a.
Proof.
  intros src I R x a H; induction H as [x|x n w x1 a Hs Hnb Hr IH]; intros b Hb.
  - left; exact Hb.
  - apply sf_areach_inv in Hb. destruct Hb as [<-|[n' [w' [x1' [Hs' [_ Hr']]]]]].
    + right. econstructor; eauto.
    + rewrite Hs in Hs'. injection Hs' as <- <- <-. apply IH; auto.
Qed.

Lemma sf_astep_TYPE: forall src a, a_mode a = Zlib.proof.inflate.Model.TYPE ->
  astep lenfix_list distfix_list src a = AGo (a_q a) false (AS (set_i_mode (a_s a) TYPEDO) (a_q a) (a_O a)).
Proof. intros src a H. unfold astep. cbv zeta. rewrite H. reflexivity. Qed.

Lemma sf_astop_fun: forall src I R a t t', astop src I R a t -> astop src I R a t' -> t = t'.
Proof.
  unfold astop. intros src I R a t t'.
  destruct (astep lenfix_list distfix_list src a); intuition congruence.
Qed.

(* past a stopping point the trace goes on at most by the free step TYPE -> TYPEDO, which writes nothing
   and stops the same way *)
Lemma sf_astop_after: forall src I R a t b, astop src I R a t -> areach src I R a b ->
  a_O b = a_O a /\ astop src I R b t.
Proof.
  intros src I R a t b Hst Hr. apply sf_areach_inv in Hr.
  destruct Hr as [<-|[n [w [a1 [Hs [Hnb Hr]]]]]]; [split; auto|].
  unfold astop in Hst. rewrite Hs in Hst. destruct Hst as [[Hb|[Hmd Hb1]] ->]; [contradiction|].
  rewrite sf_astep_TYPE in Hs by exact Hmd. injection Hs as <- <- <-.
  apply sf_areach_inv in Hr. destruct Hr as [<-|[n' [w' [a2 [Hs' [Hnb' _]]]]]].
  - split; [reflexivity|]. unfold astop.
    destruct (astep lenfix_list distfix_list src _) eqn:E; [|contradiction].
    split; [left; exact Hb1|reflexivity].
  - rewrite Hs' in Hb1. contradiction.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant and the stopping point                                                           *)

(* after P bytes of src read and O written (in at most room bytes): the stream's state is related to a
   state of the abstract trace from the start, reached within the whole input and the room *)
Definition sf_Inv (w: Z) (src: list Z) (room P: Z) (O: list Z) (L: live) : Prop :=
  bytes_ok src /\ Zlength src <= Int.max_unsigned /\ 0 <= room <= Int.max_unsigned /\ Zlength O <= room /\
  exists a, areach src (Zlength src) room (a0 w) a /\ awf src a /\ brel src P O (l_s L) a.

(* O and t are where the abstract trace from the start stops within the whole input and the room *)
Definition sf_Max (w: Z) (src: list Z) (room: Z) (O: list Z) (t: option Z) : Prop :=
  exists a, areach src (Zlength src) room (a0 w) a /\ a_O a = O /\ astop src (Zlength src) room a t.

Lemma sf_seq_refl: forall s, seq s s.
Proof. intros s; constructor; auto. Qed.

(* the state after inflateInit2: mode HEAD, an empty bit buffer, nothing written, no window *)
Lemma sf_init_fields: forall w, si_window w ->
  let s := a_s (a0 w) in
  i_mode s = HEAD /\ i_bits s = 0 /\ i_hold s = 0 /\ i_total s = 0 /\ i_wsize s = 0 /\ i_whave s = 0 /\
  i_head s = false.
Proof.
  intros w Hw. destruct Hw as [ -> | [ -> | [ -> | -> ]]]; repeat split; reflexivity.
Qed.

Lemma sf_init_brel: forall w sp src, si_window w -> bytes_ok src ->
  brel src 0 [] (l_s (init_live sp w)) (a0 w).
Proof.
  intros w sp src Hw Hsrc.
  assert (Hs: l_s (init_live sp w) = a_s (a0 w)) by reflexivity.
  rewrite Hs.
  destruct (sf_init_fields w Hw) as [Hmd [Hb [Hh [Ht [Hws [Hwh Hhd]]]]]].
  assert (Hq: a_q (a0 w) = 0) by reflexivity.
  assert (HO: a_O (a0 w) = []) by reflexivity.
  assert (Hnd: ~ data_mode HEAD).
  { unfold data_mode, decode_mode. intro H. repeat destruct H as [H|H]; discriminate. }
  constructor.
  - pose proof (Zlength_nonneg src); lia.
  - rewrite Hb; lia.
  - reflexivity.
  - intros _. rewrite Hq, Hb. reflexivity.
  - unfold bits_ok. rewrite Hmd, Hb. split; [|split]; intros; [split; [reflexivity|split]|..].
    + cbv. reflexivity.
    + reflexivity.
    + destruct H as [H|H]; discriminate.
    + reflexivity.
  - rewrite Hh, Hb. reflexivity.
  - exact HO.
  - intros _. apply sf_seq_refl.
  - split; [reflexivity|]. rewrite Hmd. intro H; contradiction.
  - intros _. rewrite Ht. reflexivity.
  - intros _. left. rewrite Hws, Hwh. auto.
  - exact Hhd.
Qed.



Lemma sf_u64_small: forall x, 0 <= x <= Int.max_unsigned -> u64 x = x.
Proof. intros x Hx. unfold u64. apply Z.mod_small. rep_lia. Qed.

(* where the trace stops is unique: the law *)
Lemma sf_max_unique: forall w src room O t O' t',
  sf_Max w src room O t -> sf_Max w src room O' t' -> O = O' /\ t = t'.
Proof.
  intros w src room O t O' t' [a [Hr [HO Hst]]] [a' [Hr' [HO' Hst']]]. subst O O'.
  destruct (sf_areach_total _ _ _ _ _ Hr _ Hr') as [H|H].
  - destruct (sf_astop_after _ _ _ _ _ _ Hst H) as [HO Hst2].
    split; [auto | eapply sf_astop_fun; eauto].
  - destruct (sf_astop_after _ _ _ _ _ _ Hst' H) as [HO Hst2].
    split; [auto | eapply sf_astop_fun; eauto].
Qed.

Lemma si_facts_proof : facts_part_stmt.
Proof.
  intros Haw Hcall. exists sf_Inv, sf_Max. constructor.
  - (* the initial state *)
    intros w src room sp Hw Hsrc Hlen Hroom.
    split; [auto|split; [auto|split; [auto|]]]. split; [rewrite Zlength_nil; lia|].
    exists (a0 w). split; [constructor|]. split.
    + apply (proj1 Haw); auto.
    + apply sf_init_brel; auto.
  - (* one call *)
    intros w src room P O L flush strmp z ib inp o r z' st' ow
      [Hsrc [Hlen [Hroom [HOr [a [Har [Hawf Hbr]]]]]]] HL Hz Htout Hstrm Hib Hai Hinp HPin Hao Hrel Hmem.
    destruct Hrel as [[Hbad _]|[_ [L0 [o0 [res [winp [HL0 [Ho0 [Hrun [Hsnx [Hr [How [Hz' [_ Hst']]]]]]]]]]]]]].
    { exfalso. unfold inflate_bad, is_live in Hbad.
      destruct (eq_dec strmp nullval); [contradiction|]. destruct Hbad as [H|[H|[H _]]]; congruence. }
    injection HL0 as <-. injection Ho0 as <-.
    assert (HP: 0 <= P <= Zlength src) by exact (br_P _ _ _ _ _ Hbr).
    assert (Hinl: Zlength inp <= Int.max_unsigned) by (destruct Hz; lia).
    assert (HOn: 0 <= Zlength O) by apply Zlength_nonneg.
    assert (Haon: 0 <= zf_ao z) by (destruct Hz; lia).
    assert (Htout': zf_tout z = u64 (Zlength O)) by (rewrite sf_u64_small by lia; exact Htout).
    pose proof (Hcall src flush P O z L inp res a Hawf Hbr HL Hz Htout' (proj1 HP) HPin Hinp Hinl Hrun) as Hc.
    cbv zeta in Hc.
    destruct Hc as [Hc|[Hminp [Haout [Hsnx' [Hsow [Howl [Hmt [a' [Har' [Hawf' [Hbr' [Hfin Hnf]]]]]]]]]]]].
    { subst r. contradiction. }
    subst r ow z'.
    set (m := r_m res) in *.
    exists (Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
    change (zf_ai (z_after z ib o res)) with (Zlength (m_inp m) - m_snx m).
    change (zf_ni (z_after z ib o res)) with (in_ptr ib (m_snx m)).
    change (zf_no (z_after z ib o res)) with (out_ptr o (m_sow m)).
    change (zf_ao (z_after z ib o res)) with (m_aout m - m_sow m).
    change (zf_tout (z_after z ib o res)) with (m_tout m).
    rewrite Hminp.
    assert (Hreach: areach src (Zlength src) room (a0 w) a').
    { eapply sf_areach_trans; [exact Har|]. eapply sf_areach_mono; [| |exact Har']; lia. }
    assert (HOa: a_O a' = O ++ m_ow m) by exact (br_O _ _ _ _ _ Hbr').
    assert (HOl: Zlength (O ++ m_ow m) <= room) by (rewrite Zlength_app; lia).
    split; [exact Hst'|].
    split; [lia|].
    split; [exact Howl|].
    split.
    { replace (P + (zf_ai z - (Zlength inp - m_snx m))) with (P + m_snx m) by lia.
      split; [auto|split; [auto|split; [auto|split; [exact HOl|]]]].
      exists a'. split; [exact Hreach|split; [exact Hawf'|exact Hbr']]. }
    split.
    { replace (zf_ai z - (Zlength inp - m_snx m)) with (m_snx m) by lia. reflexivity. }
    split.
    { rewrite Hsow. reflexivity. }
    split.
    { rewrite Haout, Hsow. reflexivity. }
    split.
    { rewrite Hmt, <- Zlength_app. apply sf_u64_small. pose proof (Zlength_nonneg (O ++ m_ow m)); lia. }
    split.
    { intros Hf. exists a'. split; [exact Hreach|split; [exact HOa|]].
      unfold astop. rewrite (Hfin Hf). reflexivity. }
    { intros Hf Hb Ht HPe HRe. exists a'. split; [exact Hreach|split; [exact HOa|]].
      destruct (Hnf Hf) as [_ [H|[H|H]]]; [contradiction|contradiction|].
      rewrite HPe, HRe in H. unfold astop.
      destruct (astep lenfix_list distfix_list src a') eqn:E.
      - split; [exact H|reflexivity].
      - destruct H as [H|[_ H]]; contradiction. }
  - (* uniqueness *)
    exact sf_max_unique.
Qed.

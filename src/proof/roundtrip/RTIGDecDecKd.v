(* RT-I: copy of rfc1951/DecDecKd.v over the generalized definitions RTIGDefs.v. *)
(* Helpers of the passes of DecDec: Kd from a state that keeps the fixed fields, at_mode
   introduction / elimination per mode, in_huff / dw transfer. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTIGDecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the fields no pass of this group changes *)
Definition same_fix (s s': istate) : Prop :=
  i_wrap s' = i_wrap s /\ i_head s' = i_head s /\ i_wbits s' = i_wbits s /\ i_flags s' = i_flags s /\
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\ i_wdata s' = i_wdata s /\
  i_check s' = i_check s /\ i_total s' = i_total s /\ i_last s' = i_last s /\
  i_codes s' = i_codes s /\ i_lencode s' = i_lencode s /\ i_lenbits s' = i_lenbits s /\
  i_distcode s' = i_distcode s /\ i_distbits s' = i_distbits s.

Lemma same_fix_refl s : same_fix s s.
Proof. repeat split. Qed.

Ltac sf_auto := unfold same_fix; cbn; repeat split.

(* the modes this group reaches *)
Definition dmd (md: Z) : Prop := md = Zlib.proof.inflate.Model.TYPE \/ md_dec md.

Lemma dmd_facts md : dmd md ->
  md <> HEAD /\ md <> FLAGS /\ md <> LENGTH /\ md <> DONE /\ md < CHECK.
Proof.
  unfold dmd, md_dec, Zlib.proof.inflate.Model.TYPE, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT,
    HEAD, FLAGS, LENGTH, DONE, CHECK.
  intros H. lia.
Qed.

Lemma md_dec_to md : md_dec md -> md <> TIME /\ md <> OS.
Proof. unfold md_dec, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, TIME, OS. intros H. lia. Qed.

Lemma win_ok_tr G s s' ob : same_fix s s' -> win_ok G s ob -> win_ok G s' ob.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) W. unfold win_ok, win_at in *.
  rewrite E3, E5, E6, E7, E8. exact W.
Qed.

Lemma kd_tr G pos inp ob m m' :
  Kd G pos inp ob m -> md_dec (m_mode m) ->
  m_inp m' = m_inp m -> m_out m' = m_out m -> m_aout m' = m_aout m -> m_tout m' = m_tout m ->
  m_ret m' = m_ret m ->
  same_fix (m_s m) (m_s m') -> dmd (i_mode (m_s m')) ->
  at_mode G (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m') ->
  Kd G pos inp ob m'.
Proof.
  intros K Hmd Hi Ho Ha Ht Hr F Hmd' At.
  assert (D : dmd (m_mode m)) by (right; exact Hmd).
  destruct (dmd_facts _ D) as (N1 & N2 & N3 & N4 & N5).
  destruct (dmd_facts _ Hmd') as (M1 & M2 & M3 & M4 & M5).
  pose proof F as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  assert (AC : after_check G (m_mode m) = false).
  { unfold after_check. apply Z.eqb_neq in N3. apply Z.eqb_neq in N4. rewrite N3, N4.
    apply andb_false_r. }
  assert (AC' : after_check G (m_mode m') = false).
  { unfold after_check, m_mode. apply Z.eqb_neq in M3. apply Z.eqb_neq in M4. rewrite M3, M4.
    apply andb_false_r. }
  destruct K as [Ki Kat Kg Kw Kc Kt Ko Kr]. constructor.
  - rewrite Hi; exact Ki.
  - exact At.
  - destruct Kg as ((wb0 & G1 & G2) & G3 & G4 & G5). split; [|split; [|split]].
    + exists wb0. rewrite E1. split; [exact G1|]. intros H; contradiction.
    + rewrite E2; exact G3.
    + intros _. rewrite E3. apply G4. exact N1.
    + intros W _ _. rewrite E4. apply G5; auto.
  - intros _. apply win_ok_tr with (m_s m); auto.
  - unfold chk_ok in *. intros W _ _ _ _.
    specialize (Kc W N1 N2).
    unfold m_mode in *.
    assert (X1 : (i_mode (m_s m) =? LENGTH) = false) by (apply Z.eqb_neq; exact N3).
    assert (X2 : (i_mode (m_s m) =? DONE) = false) by (apply Z.eqb_neq; exact N4).
    assert (X3 : (i_mode (m_s m') =? LENGTH) = false) by (apply Z.eqb_neq; exact M3).
    assert (X4 : (i_mode (m_s m') =? DONE) = false) by (apply Z.eqb_neq; exact M4).
    assert (Y1 : i_mode (m_s m) <> TIME /\ i_mode (m_s m) <> OS) by (apply md_dec_to; exact Hmd).
    destruct Y1 as [Y1 Y2]. specialize (Kc Y1 Y2).
    rewrite X1, X2 in Kc. rewrite X3, X4. cbn [orb] in *. rewrite E9, E10. exact Kc.
  - rewrite Ht, AC'. rewrite AC in Kt. exact Kt.
  - rewrite AC'. rewrite AC in Ko. rewrite Ho, Ha. exact Ko.
  - rewrite Hr, Kr. unfold m_mode in *.
    assert (X : (i_mode (m_s m) =? DONE) = false) by (apply Z.eqb_neq; exact N4).
    assert (X' : (i_mode (m_s m') =? DONE) = false) by (apply Z.eqb_neq; exact M4).
    rewrite X, X'. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tables: in_huff and dw only see the fixed fields                                               *)

Lemma tab_entry_tr fx dx s s' t : i_codes s' = i_codes s -> tab_entry fx dx s' t = tab_entry fx dx s t.
Proof. intros E. unfold tab_entry. rewrite E. reflexivity. Qed.

Lemma twalk_tr s s' t root pat : i_codes s' = i_codes s -> twalk s' t root pat = twalk s t root pat.
Proof. intros E. unfold twalk. rewrite !(tab_entry_tr _ _ s s' t E). reflexivity. Qed.

Lemma tdec_tr s s' t root type lens : i_codes s' = i_codes s -> tdec s t root type lens -> tdec s' t root type lens.
Proof.
  intros E. unfold tdec, twalk. rewrite !(tab_entry_tr _ _ s s' t E). auto.
Qed.

Lemma tvalid_tr kind s s' t rb :
  i_codes s' = i_codes s -> tvalid kind lenfix_list distfix_list s t rb -> tvalid kind lenfix_list distfix_list s' t rb.
Proof. intros E. unfold tvalid, tvalid_b. rewrite (tab_entry_tr _ _ s s' t E). auto. Qed.

Lemma in_huff_tr G s s' k j ll dl syms p0 :
  same_fix s s' -> in_huff G s k j ll dl syms p0 -> in_huff G s' k j ll dl syms p0.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & C & LC & LB & DC & DB) ((H1 & H2) & H3 & H4 & H5 & H6 & H7).
  split; [split; [exact H1|rewrite L; exact H2]|]. split; [exact H3|]. split; [exact H4|].
  rewrite LC, LB, DC, DB. split; [apply tdec_tr with s; auto|]. split; [apply tdec_tr with s; auto|].
  exact H7.
Qed.

Lemma dw_tr m m' :
  dw m -> same_fix (m_s m) (m_s m') -> m_inp m' = m_inp m -> 0 <= m_nx m' <= Zlength (m_inp m') ->
  m_aout m' = m_aout m -> Zlength (m_ow m') <= m_aout m' -> dw m'.
Proof.
  intros (T1 & T2 & _ & (_ & A) & W) (_ & _ & _ & _ & _ & _ & E7 & _ & _ & _ & _ & C & LC & LB & DC & DB) Hi Hn Ha Ho.
  unfold dw. rewrite LC, LB, DC, DB, E7. split; [apply tvalid_tr with (m_s m); auto|].
  split; [apply tvalid_tr with (m_s m); auto|]. split; [exact Hn|]. split; [lia|exact W].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* at_mode per mode                                                                               *)

Ltac am_contra E :=
  exfalso; rewrite E in *;
  unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
    LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia.

Ltac am_elim :=
  let H := fresh in let D := fresh in let E := fresh in let M := fresh in let A := fresh in
  intros [H D] E; split; [exact H|];
  repeat (destruct D as [D|D]; [destruct D as [M A]; first [exact A | am_contra E]|]);
  destruct D as [M A]; first [exact A | am_contra E].

Section AtMode.
Variables (G: dctx) (s: istate) (c hold bits: Z) (out: list Z).
Let q := 8 * c - bits.

Lemma at_mode_len_e : at_mode G s c hold bits out -> (i_mode s = LEN_ \/ i_mode s = LEN) ->
  hold_ok G c hold bits /\ at_len G s q bits out.
Proof.
  unfold at_mode. intros [H D] E. split; [exact H|].
  repeat (destruct D as [D|D]; [destruct D as [M A];
    first [exact A | exfalso; destruct E as [E|E]; rewrite E in *;
      unfold HEAD, FLAGS, TIME, OS, Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE,
        LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE in *; lia]|]).
  destruct D as [M A]. exfalso; destruct E as [E|E]; rewrite E in *;
  unfold LEN_, LEN, DONE in *; lia.
Qed.

Lemma at_mode_lenext_e : at_mode G s c hold bits out -> i_mode s = LENEXT ->
  hold_ok G c hold bits /\ at_lenext G s q bits out.
Proof. unfold at_mode. am_elim. Qed.

Lemma at_mode_dist_e : at_mode G s c hold bits out -> i_mode s = DIST ->
  hold_ok G c hold bits /\ at_dist G s q bits out.
Proof. unfold at_mode. am_elim. Qed.

Lemma at_mode_distext_e : at_mode G s c hold bits out -> i_mode s = DISTEXT ->
  hold_ok G c hold bits /\ at_distext G s q bits out.
Proof. unfold at_mode. am_elim. Qed.

Lemma at_mode_match_e : at_mode G s c hold bits out -> i_mode s = MATCH ->
  hold_ok G c hold bits /\ at_match G s q bits out.
Proof. unfold at_mode. am_elim. Qed.

Lemma at_mode_lit_e : at_mode G s c hold bits out -> i_mode s = LIT ->
  hold_ok G c hold bits /\ at_lit G s q bits out.
Proof. unfold at_mode. am_elim. Qed.

Lemma at_mode_type_i : hold_ok G c hold bits -> i_mode s = Zlib.proof.inflate.Model.TYPE ->
  at_type G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 2 right. left. auto. Qed.

Lemma at_mode_len_i : hold_ok G c hold bits -> (i_mode s = LEN_ \/ i_mode s = LEN) ->
  at_len G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 8 right. left. auto. Qed.

Lemma at_mode_lenext_i : hold_ok G c hold bits -> i_mode s = LENEXT ->
  at_lenext G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 9 right. left. auto. Qed.

Lemma at_mode_dist_i : hold_ok G c hold bits -> i_mode s = DIST ->
  at_dist G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 10 right. left. auto. Qed.

Lemma at_mode_distext_i : hold_ok G c hold bits -> i_mode s = DISTEXT ->
  at_distext G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 11 right. left. auto. Qed.

Lemma at_mode_match_i : hold_ok G c hold bits -> i_mode s = MATCH ->
  at_match G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 12 right. left. auto. Qed.

Lemma at_mode_lit_i : hold_ok G c hold bits -> i_mode s = LIT ->
  at_lit G s q bits out -> at_mode G s c hold bits out.
Proof. intros H E A. split; [exact H|]. do 13 right. left. auto. Qed.

End AtMode.

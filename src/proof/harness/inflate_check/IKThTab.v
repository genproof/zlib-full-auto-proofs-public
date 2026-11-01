(* Law inflate_check, theory part: cases TABLE, LENLENS, CODELENS keep Kx. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Import Zlib.proof.harness.inflate_codes.TheoryTab.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* What the pass keeps of Kx: the bit buffer (with the consumed bits growing) and the frozen fields *)

Definition ikt_frz (m0 m: mst) : Prop :=
  m_out m = m_out m0 /\ m_aout m = m_aout m0 /\ m_ow m = m_ow m0 /\ m_adler m = m_adler m0 /\
  m_tout m = m_tout m0 /\ i_flags (m_s m) = i_flags (m_s m0) /\ i_check (m_s m) = i_check (m_s m0) /\
  i_total (m_s m) = i_total (m_s m0).

Definition ikt_X (src: list Z) (pos: Z) (m0 m: mst) : Prop :=
  ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) /\
  8 * (pos + m_nx m0) - m_bits m0 <= 8 * (pos + m_nx m) - m_bits m /\ ikt_frz m0 m.

Lemma ikt_refl src pos m : ik_bitbuf src (pos + m_nx m) (m_hold m) (m_bits m) -> ikt_X src pos m m.
Proof. intros B. split; [exact B|]. split; [lia|]. repeat split; reflexivity. Qed.

Lemma ikt_same src pos m0 m m' : ikt_X src pos m0 m -> ik_same_but_buf m m' ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  ikt_X src pos m0 m'.
Proof.
  intros (B & C & F) (Ss & _ & Si & Sa & So & _ & Sout & _ & Sad & _ & _ & St & _) B' C'.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  split; [exact B'|]. split; [lia|]. unfold ikt_frz. rewrite Ss. repeat split; congruence.
Qed.

Lemma ikt_s src pos m0 m s : ikt_X src pos m0 m ->
  i_flags s = i_flags (m_s m) -> i_check s = i_check (m_s m) -> i_total s = i_total (m_s m) ->
  ikt_X src pos m0 (set_m_s m s).
Proof.
  intros (B & C & F) E1 E2 E3. destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  split; [exact B|]. split; [exact C|]. unfold ikt_frz. cbn [m_s set_m_s m_out m_aout m_ow m_adler m_tout].
  repeat split; congruence.
Qed.

Lemma ikt_ret src pos m0 m r : ikt_X src pos m0 m -> ikt_X src pos m0 (set_m_ret m r).
Proof. intros (B & C & F). split; [exact B|]. split; [exact C|]. exact F. Qed.

Lemma ikt_leave src pos m0 m : ikt_X src pos m0 m -> ikt_X src pos m0 (set_leave m).
Proof. intros (B & C & F). split; [exact B|]. split; [exact C|]. exact F. Qed.

Lemma ikt_bad src pos m0 m e : ikt_X src pos m0 m -> ikt_X src pos m0 (set_bad m e).
Proof.
  intros X. unfold set_bad, set_mode, upd_s. apply ikt_s; [|reflexivity..].
  destruct X as (B & C & F). split; [exact B|]. split; [exact C|]. exact F.
Qed.

Lemma ikt_drop (KIT: ik_kit) src pos m0 m n : ikt_X src pos m0 m -> 0 <= n <= m_bits m -> m_bits m <= 40 ->
  ikt_X src pos m0 (dropbits n m) /\ m_bits (dropbits n m) = m_bits m - n.
Proof.
  intros (B & C & F) Hn Hb.
  assert (E: m_bits (dropbits n m) = m_bits m - n).
  { unfold dropbits, u32. cbn [m_bits set_m_bits]. rewrite Z.mod_small; lia. }
  split; [|exact E]. split; [|split].
  - rewrite E. unfold dropbits. cbn [m_nx m_hold set_m_bits set_m_hold].
    apply (kk_bb_drop KIT); auto.
  - rewrite E. unfold dropbits. cbn [m_nx set_m_bits set_m_hold]. lia.
  - exact F.
Qed.

(* NEEDBITS and the root lookup under the kit *)
Lemma ikt_nb (KIT: ik_kit) src pos inp m0 m n : ctx_ok src pos inp -> m_inp m = inp ->
  0 <= m_nx m <= Zlength inp -> 0 <= n <= 32 -> 0 <= m_bits m <= 32 -> ikt_X src pos m0 m ->
  ikt_X src pos m0 (needbits n m) /\ ik_same_but_buf m (needbits n m) /\
  m_nx m <= m_nx (needbits n m) <= Zlength inp /\
  (m_bits m < n -> m_bits (needbits n m) < n + 8) /\ (n <= m_bits m -> needbits n m = m) /\
  ((m_leave (needbits n m) = 1 /\ m_bits (needbits n m) < n) \/
   (m_leave (needbits n m) = m_leave m /\ n <= m_bits (needbits n m))).
Proof.
  intros CX I N Hn Hb X.
  destruct (kk_needbits KIT src pos inp n m CX I N Hn Hb (proj1 X)) as (B' & S' & N' & D' & L1 & L2 & L3).
  split; [apply ikt_same with m; auto; lia|].
  split; [exact S'|]. split; [exact N'|]. split; [exact L1|]. split; [exact L2|].
  destruct L3 as [(A1 & _ & A3)|A]; [left; auto|right; exact A].
Qed.

Lemma ikt_lk (KIT: ik_kit) src pos inp m0 m t nb here m' ok : ctx_ok src pos inp -> m_inp m = inp ->
  0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 40 -> ikt_X src pos m0 m ->
  lookup1 lenfix_list distfix_list t nb m = (here, m', ok) ->
  ikt_X src pos m0 m' /\ ik_same_but_buf m m'.
Proof.
  intros CX I N Hb X E.
  destruct (kk_lookup1 KIT src pos inp _ _ t nb m here m' ok CX I N Hb (proj1 X) E) as (B' & S' & N' & D' & _).
  split; [apply ikt_same with m; auto; lia | exact S'].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx after the pass                                                                              *)

Ltac ikt_cst := unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
  Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT,
  DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *.

Ltac ikt_md := unfold ik_pre_mode, ik_gzhdr_mode, ik_post_mode, decode_mode, md_tab in *; ikt_cst; lia.

(* the modes the pass ends in *)
Definition ikt_tm (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS \/ md = LEN_ \/ md = BAD.

Lemma ikt_Kx wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> md_tab (m_mode m) -> ikt_X src pos m m' -> ikt_tm (m_mode m') ->
  Kx wrap src pos out a0 m'.
Proof.
  intros X Hmd (Hb & Hc & (Ho & Ha & Hw & Had & Ht & Hf & Hck & Htot)) Hpm.
  assert (Hpost : wrap <> 0 -> ik_post wrap src pos out m').
  { intros W. pose proof (kx_post _ _ _ _ _ _ X W) as P.
    assert (PM : ik_post_mode (m_mode m)) by ikt_md.
    specialize (P PM). unfold ik_post in *. rewrite Hf, Hck, Had, Ho, Ha, Hw.
    destruct P as [P1 [P2 P3]]. split; [|split; auto]. destruct P1 as [P1|P1]; [left|right]; intuition lia. }
  unfold ikt_tm in Hpm.
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ X).
  - exact Hb.
  - split; intros; exfalso; ikt_md.
  - unfold m_left. rewrite Ho, Ha, Hw. exact (kx_out _ _ _ _ _ _ X).
  - rewrite Htot, Ho, Ha. exact (kx_total _ _ _ _ _ _ X).
  - rewrite Ht, Ho, Ha. exact (kx_tout _ _ _ _ _ _ X).
  - intros W. destruct (kx_raw _ _ _ _ _ _ X W) as (A & _). split; [congruence|]. ikt_md.
  - intros _ P. exfalso. ikt_md.
  - intros _ P. exfalso. ikt_md.
  - intros _ P. exfalso. ikt_md.
  - intros W _. apply Hpost; auto.
  - intros W _. right. apply Hpost; auto.
  - intros W. unfold ik_trail. split; [|split]; intros E; exfalso; ikt_md.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENLENS's loop                                                                                 *)

Lemma ikt_llloop (KIT: ik_kit) src pos inp m0 : ctx_ok src pos inp -> forall k m,
  m_inp m = inp -> 0 <= m_nx m <= Zlength inp -> 0 <= m_bits m <= 31 -> ikt_X src pos m0 m ->
  let m1 := lenlens_loop k m in
  m_inp m1 = inp /\ 0 <= m_nx m1 <= Zlength inp /\ 0 <= m_bits m1 <= 31 /\ ikt_X src pos m0 m1 /\
  m_mode m1 = m_mode m.
Proof.
  intros CX. induction k; intros m I N B X; cbv zeta; cbn [lenlens_loop]; [tauto|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|tauto].
  destruct (ikt_nb KIT src pos inp m0 m 3 CX I N ltac:(lia) ltac:(lia) X) as (X2 & S2 & N2 & B1 & B2 & LL).
  destruct S2 as (Ss & _ & Si & _).
  assert (B3: 0 <= m_bits (needbits 3 m) <= 31).
  { destruct (Z.ltb_spec (m_bits m) 3) as [H|H]; [specialize (B1 H) | rewrite (B2 H)]; try lia.
    pose proof (proj1 (proj1 X2)). lia. }
  set (m2 := needbits 3 m) in *. clearbody m2.
  destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
  { split; [congruence|]. split; [lia|]. split; [lia|]. split; [exact X2|]. unfold m_mode; congruence. }
  destruct LL as [LL|(LL & NB)]; [lia|].
  unfold upd_s.
  set (s3 := set_i_have (set_i_lens (m_s m2) (upd_Znth (Znth (i_have (m_s m2)) order) (i_lens (m_s m2))
               (bitsn m2 3))) (i_have (m_s m2) + 1)).
  assert (X3: ikt_X src pos m0 (set_m_s m2 s3)) by (apply ikt_s; auto).
  destruct (ikt_drop KIT src pos m0 _ 3 X3 ltac:(cbn [m_bits set_m_s]; lia) ltac:(cbn [m_bits set_m_s]; lia))
    as (X4 & B4).
  cbn [m_bits set_m_s] in B4.
  destruct (IHk (dropbits 3 (set_m_s m2 s3))) as (A1 & A2 & A3 & A4 & A5); auto.
  - unfold dropbits. cbn [m_inp set_m_s set_m_bits set_m_hold]. congruence.
  - unfold dropbits. cbn [m_nx set_m_s set_m_bits set_m_hold]. lia.
  - lia.
  - split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. rewrite A5.
    unfold m_mode, dropbits. cbn [m_s set_m_s set_m_bits set_m_hold]. unfold s3. cbn. rewrite Ss. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* CODELENS's loop                                                                                *)

Definition ikt_clres src pos m0 (o: clout) : Prop :=
  match o with
  | CLnext m' => ikt_X src pos m0 m'
  | CLleave m' => ikt_X src pos m0 m' /\ m_mode m' = CODELENS
  | CLbad m' => ikt_X src pos m0 m' /\ m_mode m' = BAD
  end.

Lemma ikt_lens_fill : forall k len s,
  i_flags (lens_fill k len s) = i_flags s /\ i_check (lens_fill k len s) = i_check s /\
  i_total (lens_fill k len s) = i_total s.
Proof.
  induction k; intros len s; cbn [lens_fill]; [tauto|].
  destruct (IHk len (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1)))
    as (A & B & C). rewrite A, B, C. cbn. tauto.
Qed.

Lemma ikt_cltail src pos m0 m len copy :
  ikt_X src pos m0 m -> m_mode m = CODELENS ->
  ikt_clres src pos m0
    (if m_mode m =? BAD then CLbad m else
     if i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + copy then CLbad (set_bad m M_repeat) else
     CLnext (upd_s m (lens_fill (Z.to_nat copy) len))).
Proof.
  intros X Md. rewrite Md. replace (CODELENS =? BAD) with false by reflexivity.
  destruct (_ <? _); cbn [ikt_clres].
  - split; [apply ikt_bad; exact X | reflexivity].
  - destruct (ikt_lens_fill (Z.to_nat copy) len (m_s m)) as (A & B & C).
    unfold upd_s. apply ikt_s; auto.
Qed.

(* one repeat code: NEEDBITS(here.bits + x), DROPBITS(here.bits), [the have test], DROPBITS(x) *)
Lemma ikt_clrep (KIT: ik_kit) src pos inp aout wrap m0 m1 eb x :
  ctx_ok src pos inp -> ttab_fr wrap inp aout m1 -> m_leave m1 = 0 -> ikt_X src pos m0 m1 ->
  0 <= eb <= m_bits m1 -> eb <= 15 -> 2 <= x <= 7 ->
  let m2 := needbits (eb + x) m1 in
  ttab_fr wrap inp aout m2 /\ m_s m2 = m_s m1 /\ ikt_X src pos m0 m2 /\
  (m_leave m2 = 1 \/ (m_leave m2 = 0 /\ eb + x <= m_bits m2)).
Proof.
  intros CX F L X Hb He Hx. cbv zeta.
  destruct (ttcl_needbits 4 (eb + x) wrap inp aout m1 F L ltac:(lia)
              ltac:(pose proof (tf_bits _ _ _ _ F); simpl; lia)) as (F2 & S2 & R2 & LL).
  change (needbits_f 4 (eb + x) m1) with (needbits (eb + x) m1) in *.
  destruct (ikt_nb KIT src pos inp m0 m1 (eb + x) CX (tf_inp _ _ _ _ F) ltac:(rewrite <- (tf_inp _ _ _ _ F); apply (tf_nx _ _ _ _ F))
              ltac:(lia) ltac:(pose proof (tf_bits _ _ _ _ F); lia) X) as (X2 & _).
  auto.
Qed.

Lemma ikt_cliter (KIT: ik_kit) src pos inp aout wrap m0 m :
  ctx_ok src pos inp -> ttcl_inv wrap inp aout m -> ikt_X src pos m0 m ->
  ikt_clres src pos m0 (codelens_iter lenfix_list distfix_list m).
Proof.
  intros CX I X. pose proof I as (F & L & R & Md & Hb).
  unfold codelens_iter.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok] eqn:E.
  destruct (ttcl_lookup 3 _ _ wrap inp aout m F L Hb ltac:(pose proof (tf_bits _ _ _ _ F); simpl; lia)
              here m1 ok E) as (F1 & S1 & R1 & OKt & OKf).
  destruct (ikt_lk KIT src pos inp m0 m _ _ here m1 ok CX (tf_inp _ _ _ _ F)
              ltac:(rewrite <- (tf_inp _ _ _ _ F); apply (tf_nx _ _ _ _ F))
              ltac:(pose proof (tf_bits _ _ _ _ F); lia) X E) as (X1 & _).
  assert (Md1: m_mode m1 = CODELENS) by (unfold m_mode; rewrite S1; exact Md).
  pose proof (tf_bits _ _ _ _ F1) as B1.
  destruct ok; cbn [negb].
  2:{ cbn [ikt_clres]. auto. }
  destruct (OKt eq_refl) as (L1 & Bh & Bh15).
  destruct (Z.ltb_spec (e_val here) 16).
  - cbn [ikt_clres]. destruct (ikt_drop KIT src pos m0 m1 (e_bits here) X1 ltac:(lia) ltac:(lia)) as [X2 _].
    unfold upd_s. apply ikt_s; auto.
  - destruct (Z.eqb_spec (e_val here) 16); [|destruct (Z.eqb_spec (e_val here) 17)].
    + destruct (ikt_clrep KIT src pos inp aout wrap m0 m1 (e_bits here) 2 CX F1 L1 X1 ltac:(lia) ltac:(lia)
                  ltac:(lia)) as (F2 & S2 & X2 & LL).
      set (m2 := needbits (e_bits here + 2) m1) in *. clearbody m2.
      pose proof (tf_bits _ _ _ _ F2) as B2.
      assert (Md2: m_mode m2 = CODELENS) by (unfold m_mode in *; rewrite S2; exact Md1).
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ikt_clres]. auto.
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ikt_drop KIT src pos m0 m2 (e_bits here) X2 ltac:(lia) ltac:(lia)) as [X3 B3].
        change (m_s (dropbits (e_bits here) m2)) with (m_s m2).
        destruct (i_have (m_s m2) =? 0).
        -- cbv beta iota. cbn [negb]. change (m_mode (set_bad (dropbits (e_bits here) m2) M_repeat)) with BAD.
           rewrite Z.eqb_refl. cbn [ikt_clres]. split; [apply ikt_bad; exact X3 | reflexivity].
        -- cbv beta iota. cbn [negb]. apply ikt_cltail.
           ++ destruct (ikt_drop KIT src pos m0 _ 2 X3 ltac:(lia) ltac:(lia)) as [X4 _]. exact X4.
           ++ exact Md2.
    + destruct (ikt_clrep KIT src pos inp aout wrap m0 m1 (e_bits here) 3 CX F1 L1 X1 ltac:(lia) ltac:(lia)
                  ltac:(lia)) as (F2 & S2 & X2 & LL).
      set (m2 := needbits (e_bits here + 3) m1) in *. clearbody m2.
      pose proof (tf_bits _ _ _ _ F2) as B2.
      assert (Md2: m_mode m2 = CODELENS) by (unfold m_mode in *; rewrite S2; exact Md1).
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ikt_clres]. auto.
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ikt_drop KIT src pos m0 m2 (e_bits here) X2 ltac:(lia) ltac:(lia)) as [X3 B3].
        cbn [negb]. apply ikt_cltail.
        ++ destruct (ikt_drop KIT src pos m0 _ 3 X3 ltac:(lia) ltac:(lia)) as [X4 _]. exact X4.
        ++ exact Md2.
    + destruct (ikt_clrep KIT src pos inp aout wrap m0 m1 (e_bits here) 7 CX F1 L1 X1 ltac:(lia) ltac:(lia)
                  ltac:(lia)) as (F2 & S2 & X2 & LL).
      set (m2 := needbits (e_bits here + 7) m1) in *. clearbody m2.
      pose proof (tf_bits _ _ _ _ F2) as B2.
      assert (Md2: m_mode m2 = CODELENS) by (unfold m_mode in *; rewrite S2; exact Md1).
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ikt_clres]. auto.
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ikt_drop KIT src pos m0 m2 (e_bits here) X2 ltac:(lia) ltac:(lia)) as [X3 B3].
        cbn [negb]. apply ikt_cltail.
        ++ destruct (ikt_drop KIT src pos m0 _ 7 X3 ltac:(lia) ltac:(lia)) as [X4 _]. exact X4.
        ++ exact Md2.
Qed.

Lemma ikt_clloop (KIT: ik_kit) src pos inp aout wrap m0 : ctx_ok src pos inp -> forall k m,
  ttcl_inv wrap inp aout m -> ikt_X src pos m0 m ->
  ikt_clres src pos m0 (codelens_loop lenfix_list distfix_list k m).
Proof.
  intros CX. induction k; intros m I X; cbn [codelens_loop]; [exact X|].
  destruct (i_have (m_s m) <? i_nlen (m_s m) + i_ndist (m_s m)); [|exact X].
  pose proof (ttcl_iter wrap src pos inp aout m I) as IT.
  pose proof (ikt_cliter KIT src pos inp aout wrap m0 m CX I X) as IX.
  destruct (codelens_iter lenfix_list distfix_list m) as [m'|m'|m']; [apply IHk; auto | exact IX | exact IX].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The results of the pass                                                                        *)

Definition ikt_res src pos m0 (p: ttab_res) : Prop :=
  match p with
  | TTDone (IBrk m') => ikt_X src pos m0 m' /\ ikt_tm (m_mode m')
  | TTDone (IRet _ _) => False
  | TTLen m' => ikt_X src pos m0 m' /\ m_mode m' = LEN_
  end.

Lemma ikt_res_bad src pos m0 m e : ikt_X src pos m0 m -> ikt_res src pos m0 (TTDone (IBrk (set_bad m e))).
Proof. intros X. cbn [ikt_res]. split; [apply ikt_bad; exact X|]. unfold ikt_tm. right; right; right; right; reflexivity. Qed.

Ltac ikt_cbs := cbn [i_flags i_check i_total set_i_distbits set_i_next set_i_codes set_i_distcode set_i_lenbits
  set_i_lencode set_i_mode set_i_have set_i_lens set_i_ncode set_i_ndist set_i_nlen].

Lemma ikt_clpost src pos m0 m : ikt_X src pos m0 m -> ikt_res src pos m0 (ttab_clpost m).
Proof.
  intros X. unfold ttab_clpost. cbv zeta.
  destruct (Znth 256 (i_lens (m_s m)) =? 0); [apply ikt_res_bad; auto|].
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  match goal with |- context [set_m_ret (set_m_s m ?s1) r] =>
    assert (X1: ikt_X src pos m0 (set_m_ret (set_m_s m s1) r)) by (apply ikt_ret; apply ikt_s; [exact X | ..]; ikt_cbs; reflexivity);
    assert (S1: m_s (set_m_ret (set_m_s m s1) r) = s1) by reflexivity;
    generalize dependent (set_m_ret (set_m_s m s1) r) end.
  intros m1 X1 S1.
  destruct (negb (r =? 0)); [apply ikt_res_bad; auto|].
  destruct (call_table _ _ _ _ _) as [[[r2 c2] n2] b2].
  match goal with |- context [set_m_ret (set_m_s m1 ?s2) r2] =>
    assert (X2: ikt_X src pos m0 (set_m_ret (set_m_s m1 s2) r2))
      by (apply ikt_ret; apply ikt_s; [exact X1 | ..]; rewrite S1; ikt_cbs; reflexivity);
    generalize dependent (set_m_ret (set_m_s m1 s2) r2) end.
  intros m2 X2.
  destruct (negb (r2 =? 0)); [apply ikt_res_bad; auto|].
  cbn [ikt_res]. split; [|reflexivity]. unfold set_mode, upd_s. apply ikt_s; auto.
Qed.

Lemma ikt_cl (KIT: ik_kit) src pos inp aout wrap m0 m :
  ctx_ok src pos inp -> ttcl_inv wrap inp aout m -> ikt_X src pos m0 m -> ikt_res src pos m0 (ttab_cl m).
Proof.
  intros CX I X. unfold ttab_cl.
  pose proof (ikt_clloop KIT src pos inp aout wrap m0 CX 320 m I X) as LP.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1]; cbn [ikt_clres] in LP.
  - apply ikt_clpost; auto.
  - cbn [ikt_res]. destruct LP as [A B]. split; [exact A|]. unfold ikt_tm. tauto.
  - cbn [ikt_res]. destruct LP as [A B]. split; [exact A|]. unfold ikt_tm. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* LENLENS                                                                                        *)

Ltac ikt_xs := repeat first [ assumption | apply ikt_ret | apply ikt_s |
  (cbn [m_s set_m_s set_m_ret]; ikt_cbs; reflexivity) ].

Lemma ikt_llpost (KIT: ik_kit) (SM: stepf2_mwf3_stmt) wrap src pos inp aout m0 m1 :
  ctx_ok src pos inp ->
  ttab_fr wrap inp aout m1 -> mwf3 m1 -> m_leave m1 = 0 -> m_ret m1 = Z_OK -> m_mode m1 = LENLENS ->
  i_have (m_s m1) = i_ncode (m_s m1) -> ikt_X src pos m0 m1 ->
  ikt_res src pos m0 (ttab_llpost m1).
Proof.
  intros CX F W L R Md HH X.
  pose proof (mw_s _ (mwf3_mwf _ W)) as SW. pose proof (mw_md _ (mwf3_mwf _ W)) as MD.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ SW) as [ZL FL].
  destruct (ttab_lenlens_zero 19 (m_s m1) ltac:(lia) ltac:(simpl; lia) ZL FL LE) as (L0 & EZ & ZL0 & FL0 & LE0).
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
  { intros x Hx. destruct (ttab_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
    rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (ttab_order_range k Hk). lia. }
  unfold ttab_llpost. cbv zeta. rewrite EZ.
  set (s0 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens (m_s m1) L0) 19) 0)
                (TCodes 0)) (TCodes 0)) 7).
  assert (S0: swf s0) by (destruct SW; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  destruct (call_table CODES 0 19 7 s0) as [[[r codes] nxt] lb] eqn:CT.
  destruct (Z.eqb_spec r 0) as [R0|R0].
  2:{ cbn [negb]. apply ikt_res_bad. unfold s0. ikt_xs. }
  subst r. cbn [negb].
  pose proof (ttab_codes_ok s0 0 codes nxt lb S0 eq_refl LE7 CT eq_refl) as FC.
  set (s1 := set_i_lenbits (set_i_next (set_i_codes s0 codes) nxt) lb).
  set (mc := set_mode (upd_s (set_m_ret (set_m_s m1 s1) 0) (fun s => set_i_have s 0)) CODELENS).
  apply (ikt_cl KIT src pos inp aout wrap m0 mc CX);
    [refine (conj _ (conj _ (conj _ (conj _ _)))) | unfold mc, s1, s0, set_mode, upd_s; ikt_xs].
  - unfold mc, set_mode, upd_s. destruct F. constructor; cbn [m_s m_inp m_aout m_out m_nx m_hold m_bits
      set_m_ret set_m_s i_wrap i_head set_i_mode set_i_have]; auto.
  - exact L.
  - reflexivity.
  - reflexivity.
  - intros h Hh. change (m_s mc) with (set_i_mode (set_i_have s1 0) CODELENS).
    cbn [i_lencode i_lenbits i_codes set_i_mode set_i_have s1 s0 set_i_lenbits set_i_next set_i_codes
         set_i_distcode set_i_lencode set_i_lens tab_entry].
    split; [apply ttab_entry_bits_nonneg; exact FC|].
    destruct (Z.le_gt_cases (e_bits (Znth (0 + h mod 2 ^ lb) codes)) 15) as [B|B]; [exact B|exfalso].
    (* the hold-override trick: a LENLENS head with hold h, no bits, no input *)
    set (m' := set_m_nx (set_m_bits (set_m_hold m1 h) 0) (Zlength (m_inp m1))).
    assert (W': mwf3 m') by (apply ttab_mwf3_override; auto).
    assert (Ms: m_s m' = m_s m1) by reflexivity.
    assert (Md': m_mode m' = LENLENS) by exact Md.
    set (mc' := set_mode (upd_s (set_m_ret (set_m_s m' s1) 0) (fun s => set_i_have s 0)) CODELENS).
    assert (EP: ttab_ll m' = TTDone (IBrk (set_leave mc'))).
    { unfold ttab_ll. cbv zeta.
      replace (lenlens_loop 19 m') with m'
        by (change 19%nat with (S 18); rewrite ttab_ll_step, Ms, HH, Z.ltb_irrefl; reflexivity).
      replace (m_leave m' =? 1) with false by (cbn; rewrite L; reflexivity).
      unfold ttab_llpost. cbv zeta. rewrite Ms, EZ. fold s0. rewrite CT. cbn [negb Z.eqb].
      fold s1. fold mc'.
      apply ttab_cl_leave.
      - change (m_s mc') with (set_i_mode (set_i_have s1 0) CODELENS).
        unfold s1, s0. cbn [i_have i_nlen i_ndist set_i_mode set_i_have set_i_lenbits set_i_next set_i_codes
          set_i_distcode set_i_lencode set_i_lens]. lia.
      - unfold mc', m', set_mode, upd_s, m_have.
        cbn [m_inp m_nx set_m_s set_m_ret set_m_nx set_m_bits set_m_hold]. lia.
      - change (m_bits mc') with 0.
        change (tab_entry lenfix_list distfix_list (m_s mc') (i_lencode (m_s mc'))
                  (bitsn mc' (i_lenbits (m_s mc')))) with (Znth (0 + h mod 2 ^ lb) codes).
        lia. }
    pose proof (SM 0 m' W' ltac:(cbn; exact L)) as WE.
    assert (E0: stepf2 0 lenfix_list distfix_list m' = ttab_run 0 (ttab_ll m')).
    { rewrite <- (ttab_ll_eq 0 m'). unfold stepf2, step2. rewrite Md'. reflexivity. }
    rewrite E0, EP in WE. cbn [ttab_run] in WE.
    assert (MC: i_mode (m_s (set_leave mc')) = CODELENS) by reflexivity.
    destruct (md_codelens _ (mw_md _ (mwf3_mwf _ WE)) MC) as (_ & _ & _ & _ & TV & _).
    pose proof (ttab_tv_bits _ _ _ _ _ _ h TV) as TB.
    change (tab_entry lenfix_list distfix_list (m_s (set_leave mc')) (i_lencode (m_s (set_leave mc')))
              (h mod 2 ^ i_lenbits (m_s (set_leave mc')))) with (Znth (0 + h mod 2 ^ lb) codes) in TB.
    lia.
Qed.

Lemma ikt_ll (KIT: ik_kit) (SM: stepf2_mwf3_stmt) wrap src pos inp aout m0 m :
  ctx_ok src pos inp ->
  ttab_fr wrap inp aout m -> mwf3 m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = LENLENS ->
  ikt_X src pos m0 m -> ikt_res src pos m0 (ttab_ll m).
Proof.
  intros CX F W L R Md X.
  destruct (md_lenlens _ (mw_md _ (mwf3_mwf _ W)) Md) as (Hc & H0 & _).
  destruct (ttab_llloop 19 wrap inp aout m F W L R Md ltac:(simpl; lia)) as (F1 & W1 & R1 & M1 & LV).
  destruct (ikt_llloop KIT src pos inp m0 CX 19 m (tf_inp _ _ _ _ F)
              ltac:(rewrite <- (tf_inp _ _ _ _ F); apply (tf_nx _ _ _ _ F)) (tf_bits _ _ _ _ F) X)
    as (_ & _ & _ & X1 & _).
  unfold ttab_ll. cbv zeta. revert F1 W1 R1 M1 LV X1. generalize (lenlens_loop 19 m) as m1.
  intros m1 F1 W1 R1 M1 LV X1.
  destruct LV as [L1|[L1 HH]].
  - rewrite L1, Z.eqb_refl. cbn [ikt_res]. split; [exact X1|]. unfold ikt_tm. tauto.
  - rewrite L1. change (0 =? 1) with false. cbv iota.
    apply (ikt_llpost KIT SM wrap src pos inp aout); auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* TABLE                                                                                          *)

(* after NEEDBITS(14) and the three DROPBITS *)
Lemma ikt_tttb_post wrap src pos inp aout m0 (LL: mst -> ttab_res) m5 a1 a2 a3 :
  (forall m', ttab_fr wrap inp aout m' -> mwf3 m' -> m_leave m' = 0 -> m_ret m' = Z_OK ->
     m_mode m' = LENLENS -> ikt_X src pos m0 m' -> ikt_res src pos m0 (LL m')) ->
  ttab_fr wrap inp aout m5 -> mwf m5 -> m_leave m5 = 0 -> m_ret m5 = Z_OK -> m_out m5 = m_aout m5 ->
  0 <= a1 < 32 -> 0 <= a2 < 32 -> 0 <= a3 < 16 -> ikt_X src pos m0 m5 ->
  ikt_res src pos m0
    (let m := upd_s m5 (fun s => set_i_ncode (set_i_ndist (set_i_nlen s (a1 + 257)) (a2 + 1)) (a3 + 4)) in
     if orb (286 <? a1 + 257) (30 <? a2 + 1) then TTDone (IBrk (set_bad m M_toomany)) else
     LL (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS)).
Proof.
  intros HLL F5 W5 L5 R5 O5 X1 X2 X3 X5. cbv zeta.
  unfold upd_s. cbv beta.
  set (s' := set_i_ncode (set_i_ndist (set_i_nlen (m_s m5) (a1 + 257)) (a2 + 1)) (a3 + 4)).
  assert (XS: ikt_X src pos m0 (set_m_s m5 s')) by (unfold s'; ikt_xs).
  assert (XS2: ikt_X src pos m0 (set_m_s m5 (set_i_mode (set_i_have s' 0) LENLENS))) by (unfold s'; ikt_xs).
  destruct (tttb_s1 (m_s m5) (a1 + 257) (a2 + 1) (a3 + 4) (mw_s _ W5) ltac:(lia) ltac:(lia) ltac:(lia))
    as (SW' & Wr' & Hd' & Ls' & Ds' & Cs').
  fold s' in SW', Wr', Hd', Ls', Ds', Cs'. clearbody s'.
  assert (F6: ttab_fr wrap inp aout (set_m_s m5 s')) by (apply tttb_fr_s; auto).
  destruct (orb (286 <? a1 + 257) (30 <? a2 + 1)) eqn:TM.
  { apply ikt_res_bad; exact XS. }
  apply orb_false_iff in TM. destruct TM as [T1 T2]. apply Z.ltb_ge in T1. apply Z.ltb_ge in T2.
  rewrite tttb_E.
  destruct (tttb_s2 s' SW') as (SW'' & Ms'' & Hs'' & Wr'' & Hd'' & Ls'' & Ds'' & Cs'').
  set (s'' := set_i_mode (set_i_have s' 0) LENLENS) in *. clearbody s''.
  assert (ND: ~ decode_mode (i_mode s'')) by (rewrite Ms''; unfold decode_mode, LENLENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia).
  assert (MW: modewf s'').
  { constructor; rewrite ?Ms''; unfold LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST; try (intros; lia).
    - intros _. rewrite Hs'', Cs'', Ls'', Ds'', Cs', Ls', Ds'. repeat split; intros; lia.
    - intros D; exfalso; apply ND; rewrite Ms''; exact D. }
  apply HLL.
  - apply tttb_fr_s; auto; congruence.
  - split; [apply tttb_mwf_s; auto|].
    constructor; cbn [m_s set_m_s]; rewrite ?Ms''; unfold LENLENS, HEAD, LENEXT, DISTEXT; try (intros; lia).
    intros D; exfalso; apply ND; rewrite Ms''; exact D.
  - exact L5.
  - exact R5.
  - exact Ms''.
  - exact XS2.
Qed.

(* TABLE: from a loop head, given the LENLENS part *)
Lemma ikt_tab (KIT: ik_kit) wrap src pos inp aout m0 m :
  ctx_ok src pos inp ->
  (forall m', ttab_fr wrap inp aout m' -> mwf3 m' -> m_leave m' = 0 -> m_ret m' = Z_OK ->
     m_mode m' = LENLENS -> ikt_X src pos m0 m' -> ikt_res src pos m0 (ttab_ll m')) ->
  ttab_fr wrap inp aout m -> mwf3 m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = TABLE ->
  ikt_X src pos m0 m ->
  ikt_res src pos m0 (ttab_tab m).
Proof.
  intros CX HLL F W L R Md X.
  pose proof (mwf3_mwf _ W) as W1.
  pose proof (tf_bits _ _ _ _ F) as B0.
  unfold ttab_tab. cbv zeta.
  pose proof (tttb_nb 4 14 m ltac:(lia) ltac:(lia)) as (N1 & N2 & N3 & N4 & N5 & N6).
  change (needbits_f 4 14 m) with (needbits 14 m) in *.
  assert (W2: mwf (needbits 14 m)) by (apply mwf_needbits; auto; lia).
  assert (F2: ttab_fr wrap inp aout (needbits 14 m)).
  { destruct F. constructor; try congruence.
    - pose proof (mw_nx _ W2). congruence.
    - apply (mw_hold _ W2).
    - pose proof (mw_bits _ W2). lia. }
  assert (OK2: m_leave (needbits 14 m) <> 1 -> 14 <= m_bits (needbits 14 m) /\ m_leave (needbits 14 m) = 0)
    by (intros E; apply tttb_nb_ok; auto; lia).
  destruct (ikt_nb KIT src pos inp m0 m 14 CX (tf_inp _ _ _ _ F)
              ltac:(rewrite <- (tf_inp _ _ _ _ F); apply (tf_nx _ _ _ _ F)) ltac:(lia) ltac:(lia) X) as (XN & _).
  set (m2 := needbits 14 m) in *. clearbody m2.
  destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
  { cbn [ikt_res]. split; [exact XN|]. left. unfold m_mode. rewrite N4. exact Md. }
  destruct (OK2 EL) as [B2 L2]. clear OK2 EL.
  destruct (tttb_drop _ _ _ m2 5 F2 ltac:(lia)) as [F3 B3].
  destruct (tttb_drop _ _ _ (dropbits 5 m2) 5 F3 ltac:(lia)) as [F4 B4].
  destruct (tttb_drop _ _ _ (dropbits 5 (dropbits 5 m2)) 4 F4 ltac:(lia)) as [F5 B5].
  pose proof (tf_bits _ _ _ _ F2) as BB2.
  destruct (ikt_drop KIT src pos m0 m2 5 XN ltac:(lia) ltac:(lia)) as [XD3 _].
  destruct (ikt_drop KIT src pos m0 _ 5 XD3 ltac:(lia) ltac:(lia)) as [XD4 _].
  destruct (ikt_drop KIT src pos m0 _ 4 XD4 ltac:(lia) ltac:(lia)) as [XD5 _].
  assert (W5: mwf (dropbits 4 (dropbits 5 (dropbits 5 m2)))).
  { apply mwf_dropbits; [|lia]. apply mwf_dropbits; [|lia]. apply mwf_dropbits; auto; lia. }
  assert (S5: m_s (dropbits 4 (dropbits 5 (dropbits 5 m2))) = m_s m2) by reflexivity.
  assert (L5: m_leave (dropbits 4 (dropbits 5 (dropbits 5 m2))) = 0) by exact L2.
  assert (R5: m_ret (dropbits 4 (dropbits 5 (dropbits 5 m2))) = Z_OK) by (cbn; congruence).
  assert (O5: m_out (dropbits 4 (dropbits 5 (dropbits 5 m2))) = m_aout (dropbits 4 (dropbits 5 (dropbits 5 m2))))
    by (apply (tf_out _ _ _ _ F5)).
  pose proof (Z.mod_pos_bound (m_hold m2) (2 ^ 5) ltac:(lia)) as X1.
  pose proof (Z.mod_pos_bound (m_hold (dropbits 5 m2)) (2 ^ 5) ltac:(lia)) as X2.
  pose proof (Z.mod_pos_bound (m_hold (dropbits 5 (dropbits 5 m2))) (2 ^ 4) ltac:(lia)) as X3.
  unfold bitsn in *.
  set (a1 := m_hold m2 mod 2 ^ 5) in *. set (a2 := m_hold (dropbits 5 m2) mod 2 ^ 5) in *.
  set (a3 := m_hold (dropbits 5 (dropbits 5 m2)) mod 2 ^ 4) in *.
  clearbody a1 a2 a3.
  set (m5 := dropbits 4 (dropbits 5 (dropbits 5 m2))) in *. clearbody m5.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  exact (ikt_tttb_post wrap src pos inp aout m0 ttab_ll m5 a1 a2 a3 HLL F5 W5 L5 R5 O5 X1 X2 X3 XD5).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Assembly                                                                                        *)

Lemma ikt_final (SM: stepf2_mwf3_stmt) (DEC: groupx_ok decode_mode) wrap src pos out a0 inp aout flush m P :
  ctx_ok src pos inp -> Kc wrap src pos inp aout m -> Kx wrap src pos out a0 m -> mwf3 m -> m_leave m = 0 ->
  md_tab (m_mode m) ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->
  ttab_ok wrap src pos inp aout P -> ikt_res src pos m P ->
  stepx_post wrap src pos out a0 (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros CX K X W L Hmd E O XR.
  rewrite E. destruct P as [o|mX].
  - destruct o as [m'|r m']; [|destruct O].
    cbn [ttab_run stepx_post]. destruct XR as [XR TM]. exact (ikt_Kx _ _ _ _ _ m m' X Hmd XR TM).
  - destruct O as (FX & LX & RX & MX). destruct XR as [XR _].
    assert (KX: Kx wrap src pos out a0 mX)
      by (apply (ikt_Kx _ _ _ _ _ m mX X Hmd XR); unfold ikt_tm; tauto).
    pose proof (SM Z_TREES m W L) as WT. rewrite E in WT. cbn [ttab_run] in WT.
    rewrite Z.eqb_refl in WT.
    pose proof (ttab_mwf3_unleave mX WT LX) as WX.
    cbn [ttab_run]. destruct (flush =? Z_TREES).
    + cbn [stepx_post]. apply (ikt_Kx _ _ _ _ _ m (set_leave mX) X Hmd (ikt_leave _ _ _ _ XR)).
      unfold ikt_tm, set_leave, m_mode in *. cbn [m_s set_m_leave]. tauto.
    + assert (EE: stepf2 flush lenfix_list distfix_list mX =
                  c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) mX)
        by (unfold stepf2, Zlib.proof.inflate.Model2.step2; rewrite MX; reflexivity).
      rewrite <- EE. apply (DEC wrap src pos out a0 inp aout flush mX); auto.
      * apply ttab_Kc; auto.
      * rewrite MX. left; reflexivity.
Qed.

Lemma ikx_tab : tabx_stmt.
Proof.
  intros KIT SM DEC wrap src pos out a0 inp aout flush m CX K X W L Md.
  assert (N: m_mode m <> BAD /\ m_mode m <> MEM /\ m_mode m <> LENGTH /\ m_mode m <> DONE /\
             m_mode m <> DICT).
  { unfold md_tab in Md. unfold TABLE, LENLENS, CODELENS, BAD, MEM, LENGTH, DONE, DICT in *. lia. }
  destruct N as (N1 & N2 & N3 & N4 & N5).
  pose proof (ttab_fr_head wrap src pos inp aout m K W N1 N2 N3 N4) as F.
  pose proof (kc_ret _ _ _ _ _ _ K N1 N4) as R.
  pose proof (ikt_refl src pos m (kx_buf _ _ _ _ _ _ X)) as X0.
  pose proof Md as Md0.
  unfold md_tab in Md. destruct Md as [H|[H|H]].
  - apply (ikt_final SM DEC wrap src pos out a0 inp aout flush m (ttab_tab m) CX K X W L Md0).
    + intros fl. rewrite <- (ttab_tab_eq fl m). unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
    + apply ttab_tab_ok; auto. intros m' F' W' L' R' H'. apply ttab_ll_ok; auto.
    + apply (ikt_tab KIT wrap src pos inp aout); auto.
      intros m' F' W' L' R' H' X'. apply (ikt_ll KIT SM wrap src pos inp aout); auto.
  - apply (ikt_final SM DEC wrap src pos out a0 inp aout flush m (ttab_ll m) CX K X W L Md0).
    + intros fl. rewrite <- (ttab_ll_eq fl m). unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
    + apply ttab_ll_ok; auto.
    + apply (ikt_ll KIT SM wrap src pos inp aout); auto.
  - assert (Hb: forall h, lrange h ->
       0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m))
                     (h mod 2 ^ i_lenbits (m_s m))) <= 15).
    { intros h _. destruct (md_codelens _ (mw_md _ (mwf3_mwf _ W)) H) as (_ & _ & _ & _ & TV & _).
      apply (ttab_tv_bits _ _ _ _ _ _ h TV). }
    apply (ikt_final SM DEC wrap src pos out a0 inp aout flush m (ttab_cl m) CX K X W L Md0).
    + intros fl. rewrite <- (ttab_cl_eq fl m). unfold stepf2, Zlib.proof.inflate.Model2.step2. rewrite H. reflexivity.
    + apply ttab_cl_ok; auto.
    + apply (ikt_cl KIT src pos inp aout wrap m m CX); auto.
      exact (conj F (conj L (conj R (conj H Hb)))).
Qed.

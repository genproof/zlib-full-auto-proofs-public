(* The header simulation, the gzip strings EXTRA, NAME, COMMENT: one concrete pass copies k bytes of the
   input at once (as many as there are, up to the field's end); the abstract decoder reads them one byte
   per step, with the CRC of the chunk equal to the CRC of its bytes one after the other. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrKit.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrFix.
Require Import Zlib.proof.harness.api_split_invariant.SISimHdrEnd.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Several abstract steps in front of the goal                                                    *)

Lemma hgoal_reach flush src P0 O0 I R a a' o :
  areach src I R a a' -> hgoal flush src P0 O0 I R a' o -> hgoal flush src P0 O0 I R a o.
Proof.
  induction 1 as [a|a n w a1 a' ST NB AR IH]; intros G; [exact G|].
  eapply hgoal_step; [exact ST | exact NB | apply IH; exact G].
Qed.

Lemma awf_reach src I R a a' : awf_stmt -> awf src a -> areach src I R a a' -> awf src a'.
Proof.
  intros AW Aw AR. induction AR as [a|a n w a1 a' ST NB AR IH]; [exact Aw|].
  apply IH. eapply awf_go; eauto.
Qed.

Lemma areach_trans src I R a b c : areach src I R a b -> areach src I R b c -> areach src I R a c.
Proof.
  induction 1 as [a|a n w a1 b ST NB AR IH]; intros H; [exact H|].
  eapply ar_step; eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The input bytes                                                                                *)

Lemma sbyte_8 src p : sbyte src (8 * p) = Znth p src.
Proof. unfold sbyte. f_equal. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

Lemma sublist_snoc_src (src: list Z) p k : 0 <= p -> 0 <= k -> p + k < Zlength src ->
  sublist p (p + (k + 1)) src = sublist p (p + k) src ++ [Znth (p + k) src].
Proof.
  intros Hp Hk Hl. rewrite (sublist_split p (p + k) (p + (k + 1))) by lia.
  f_equal. rewrite sublist_one by lia. reflexivity.
Qed.

Lemma bytes_ok_sublist (src: list Z) i j : bytes_ok src -> bytes_ok (sublist i j src).
Proof. intros B. unfold bytes_ok in *. apply Forall_sublist. exact B. Qed.

(* the bytes of the call's input are those of the whole input *)
Lemma inp_byte src P0 m i : bitbuf src P0 m -> 0 <= i < Zlength (m_inp m) ->
  Znth i (m_inp m) = Znth (P0 + i) src.
Proof.
  intros BB Hi. destruct (bb_inp _ _ _ BB) as [L E]. pose proof (bb_P0 _ _ _ BB).
  rewrite E at 1. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma inbytes_src src P0 m c : bitbuf src P0 m -> 0 <= c -> m_nx m + c <= Zlength (m_inp m) ->
  inbytes m c = sublist (P0 + m_nx m) (P0 + m_nx m + c) src.
Proof.
  intros BB Hc Hl. destruct (bb_inp _ _ _ BB) as [L E]. pose proof (bb_P0 _ _ _ BB).
  pose proof (bb_nx _ _ _ BB). unfold inbytes. rewrite E at 1.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* moving over input bytes with an empty bit buffer *)
Lemma bitbuf_bytes src P0 m m' :
  bitbuf src P0 m -> m_bits m = 0 -> m_inp m' = m_inp m -> m_bits m' = 0 -> m_hold m' = m_hold m ->
  m_nx m <= m_nx m' <= Zlength (m_inp m) -> bitbuf src P0 m'.
Proof.
  intros [A B C D E F] B0 Ei Eb Eh Nx. unfold mq in *.
  constructor; rewrite ?Ei, ?Eb, ?Eh; auto; try lia.
  rewrite F, B0. unfold sbits. rewrite !Z.mod_1_r. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The string copy of NAME and COMMENT without a buffer                                           *)

Lemma zstr_nowr k bytes have len max buf j :
  0 <= j < have -> have - j <= Z.of_nat k ->
  forall c b ln bf, zstr_f k bytes have len max false buf j = (c, b, ln, bf) ->
  ln = len /\ bf = buf /\ j < c <= have /\ b = Znth (c - 1) bytes /\
  (forall i, j <= i < c - 1 -> Znth i bytes <> 0) /\ (b = 0 \/ c = have).
Proof.
  revert j. induction k as [|k IH]; intros j Hj Hk c b ln bf E; [lia|].
  cbn [zstr_f andb] in E.
  destruct (Z.eqb_spec (Znth j bytes) 0) as [Z0|Z0]; cbn [negb andb] in E.
  - inversion E; subst. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    split; [f_equal; lia|]. split; [intros i Hi; lia|]. left; exact Z0.
  - destruct (Z.ltb_spec (j + 1) have) as [Lt|Ge].
    + rewrite Nat2Z.inj_succ in Hk.
      destruct (IH (j + 1) ltac:(lia) ltac:(lia) c b ln bf E) as (L1 & L2 & L3 & L4 & L5 & L6).
      split; [exact L1|]. split; [exact L2|]. split; [lia|]. split; [exact L4|]. split; [|exact L6].
      intros i Hi. destruct (Z.eq_dec i j) as [->|Ne]; [exact Z0|]. apply L5. lia.
    + inversion E; subst. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [f_equal; lia|]. split; [intros i Hi; lia|]. right; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract run over the bytes of a string                                                    *)

(* one string byte at a byte boundary, not the last one *)
Lemma str_step (X fb: Z) (fin: istate -> istate) src I R s p O :
  (forall a, a_mode a = X -> Z.land (i_flags (a_s a)) fb <> 0 ->
     astep lenfix_list distfix_list src a =
     AGo (a_q a + 8) false
       (AS (if sbyte src (a_q a) =? 0 then fin (acrc (a_s a) [sbyte src (a_q a)])
            else acrc (a_s a) [sbyte src (a_q a)]) (a_q a + 8) (a_O a))) ->
  i_mode s = X -> Z.land (i_flags s) fb <> 0 -> p + 1 <= I -> Znth p src <> 0 ->
  astep lenfix_list distfix_list src (AS s (8 * p) O) = AGo (8 * p + 8) false (AS (acrc s [Znth p src]) (8 * p + 8) O) /\
  ~ blocked I R (AS s (8 * p) O) (AGo (8 * p + 8) false (AS (acrc s [Znth p src]) (8 * p + 8) O)).
Proof.
  intros ST Md Fl Lim Nz. split.
  - rewrite (ST (AS s (8 * p) O) Md Fl). cbn [a_q a_s a_O]. rewrite sbyte_8.
    destruct (Z.eqb_spec (Znth p src) 0); [contradiction|reflexivity].
  - cbn [blocked]. intros [B|[B _]]; [lia|discriminate].
Qed.

(* the steps of NAME / COMMENT through k + 1 nonzero bytes *)
Lemma str_run (X fb: Z) (fin: istate -> istate) src I R :
  (forall a, a_mode a = X -> Z.land (i_flags (a_s a)) fb <> 0 ->
     astep lenfix_list distfix_list src a =
     AGo (a_q a + 8) false
       (AS (if sbyte src (a_q a) =? 0 then fin (acrc (a_s a) [sbyte src (a_q a)])
            else acrc (a_s a) [sbyte src (a_q a)]) (a_q a + 8) (a_O a))) ->
  bytes_ok src ->
  forall k, 0 <= k -> forall s p O, i_mode s = X -> Z.land (i_flags s) fb <> 0 -> 0 <= p ->
    p + k + 1 <= I -> p + k + 1 <= Zlength src ->
    (forall i, 0 <= i <= k -> Znth (p + i) src <> 0) ->
    areach src I R (AS s (8 * p) O) (AS (acrc s (sublist p (p + k + 1) src)) (8 * (p + k + 1)) O).
Proof.
  intros ST Bs k Hk. pattern k. revert k Hk. apply natlike_ind.
  - intros s p O Md Fl Hp Lim Ls Nz.
    destruct (str_step X fb fin src I R s p O ST Md Fl ltac:(lia) ltac:(specialize (Nz 0 ltac:(lia)); rewrite Z.add_0_r in Nz; exact Nz))
      as (S1 & B1).
    eapply ar_step; [exact S1 | exact B1 | ].
    rewrite Z.add_0_r, sublist_one by lia. replace (8 * (p + 1)) with (8 * p + 8) by lia. apply ar_refl.
  - intros k Hk IH s p O Md Fl Hp Lim Ls Nz. unfold Z.succ in *.
    assert (N0: Znth p src <> 0) by (specialize (Nz 0 ltac:(lia)); rewrite Z.add_0_r in Nz; exact Nz).
    destruct (str_step X fb fin src I R s p O ST Md Fl ltac:(lia) N0) as (S1 & B1).
    eapply ar_step; [exact S1 | exact B1 | ].
    destruct (acrc_fields s [Znth p src]) as (F1 & F2 & _).
    replace (8 * p + 8) with (8 * (p + 1)) by lia.
    replace (acrc s (sublist p (p + (k + 1) + 1) src))
      with (acrc (acrc s [Znth p src]) (sublist (p + 1) (p + 1 + k + 1) src)).
    + replace (8 * (p + (k + 1) + 1)) with (8 * (p + 1 + k + 1)) by lia.
      apply IH; try lia; [rewrite F2; exact Fl |].
      intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Nz. lia.
    + assert (Bp: bytes_ok [Znth p src]).
      { constructor; [|constructor]. apply (proj1 (Forall_Znth src _) Bs). lia. }
      rewrite acrc_app by exact Bp.
      f_equal. rewrite (sublist_split p (p + 1) (p + (k + 1) + 1)) by lia. rewrite (sublist_one p (p + 1)) by lia.
      f_equal. f_equal. lia.
Qed.

(* the extra field: the length counts the bytes down *)
Lemma acrc_length s l d : acrc (set_i_length s l) d = set_i_length (acrc s d) l.
Proof. unfold acrc. cbn [i_flags i_wrap i_check set_i_length]. destruct (_ && _)%bool; destruct s; reflexivity. Qed.

Lemma length_length s l1 l2 : set_i_length (set_i_length s l1) l2 = set_i_length s l2.
Proof. destruct s; reflexivity. Qed.

Lemma ext_step src I R s p O :
  i_mode s = EXTRA -> Z.land (i_flags s) 1024 <> 0 -> i_length s <> 0 -> p + 1 <= I ->
  astep lenfix_list distfix_list src (AS s (8 * p) O) =
    AGo (8 * p + 8) false (AS (set_i_length (acrc s [Znth p src]) (i_length s - 1)) (8 * p + 8) O) /\
  ~ blocked I R (AS s (8 * p) O)
      (AGo (8 * p + 8) false (AS (set_i_length (acrc s [Znth p src]) (i_length s - 1)) (8 * p + 8) O)).
Proof.
  intros Md Fl Ln Lim. split.
  - rewrite astep_EXTRA by exact Md. unfold a_EXTRA. cbn [a_s a_q a_O].
    destruct (Z.eqb_spec (Z.land (i_flags s) 1024) 0); [contradiction|].
    destruct (Z.eqb_spec (i_length s) 0); [contradiction|]. cbn. rewrite sbyte_8. reflexivity.
  - cbn [blocked]. intros [B|[B _]]; [lia|discriminate].
Qed.

Lemma ext_run src I R : bytes_ok src ->
  forall k, 0 <= k -> forall s p O, i_mode s = EXTRA -> Z.land (i_flags s) 1024 <> 0 -> 0 <= p ->
    p + k + 1 <= I -> p + k + 1 <= Zlength src -> k + 1 <= i_length s ->
    areach src I R (AS s (8 * p) O)
      (AS (set_i_length (acrc s (sublist p (p + k + 1) src)) (i_length s - (k + 1))) (8 * (p + k + 1)) O).
Proof.
  intros Bs k Hk. pattern k. revert k Hk. apply natlike_ind.
  - intros s p O Md Fl Hp Lim Ls Ln.
    destruct (ext_step src I R s p O Md Fl ltac:(lia) ltac:(lia)) as (S1 & B1).
    eapply ar_step; [exact S1 | exact B1 | ].
    rewrite Z.add_0_r, (sublist_one p (p + 1)) by lia. replace (8 * (p + 1)) with (8 * p + 8) by lia.
    apply ar_refl.
  - intros k Hk IH s p O Md Fl Hp Lim Ls Ln. unfold Z.succ in *.
    destruct (ext_step src I R s p O Md Fl ltac:(lia) ltac:(lia)) as (S1 & B1).
    eapply ar_step; [exact S1 | exact B1 | ].
    destruct (acrc_fields s [Znth p src]) as (F1 & F2 & _ & _ & _ & F6 & _).
    replace (8 * p + 8) with (8 * (p + 1)) by lia.
    assert (Bp: bytes_ok [Znth p src]).
    { constructor; [|constructor]. apply (proj1 (Forall_Znth src _) Bs). lia. }
    replace (set_i_length (acrc s (sublist p (p + (k + 1) + 1) src)) (i_length s - (k + 1 + 1)))
      with (set_i_length (acrc (set_i_length (acrc s [Znth p src]) (i_length s - 1)) (sublist (p + 1) (p + 1 + k + 1) src))
              (i_length (set_i_length (acrc s [Znth p src]) (i_length s - 1)) - (k + 1))).
    + replace (8 * (p + (k + 1) + 1)) with (8 * (p + 1 + k + 1)) by lia.
      apply IH; cbn [i_mode i_flags i_length set_i_length]; try lia; [rewrite F2; exact Fl].
    + cbn [i_length set_i_length]. rewrite acrc_length, length_length, acrc_app by exact Bp.
      f_equal; [|lia]. f_equal.
      rewrite (sublist_split p (p + 1) (p + (k + 1) + 1)) by lia. rewrite (sublist_one p (p + 1)) by lia.
      f_equal. f_equal. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Small facts about the machine                                                                  *)

Lemma hbits_zero m : m_bits m = 0 -> hbits m.
Proof.
  intros B _. rewrite B. split; [reflexivity|]. split; [destruct (orb _ _); lia|]. auto.
Qed.

Lemma rel_leave src P0 O0 m a v : rel src P0 O0 m a -> rel src P0 O0 (set_m_leave m v) a.
Proof.
  intros Rl. destruct Rl as [BB0 Md0 Q0 BO0 O0' Ao In Out Ret S0 Ch Tt Tout Win Hd0].
  constructor; unfold m_mode, m_left, mq in *; cbn; auto.
  eapply bitbuf_ext; [exact BB0 | reflexivity ..].
Qed.

Lemma win_eq_length s t l : win_eq s t -> win_eq (set_i_length s l) t.
Proof. unfold win_eq. cbn. auto. Qed.

Lemma win_eq_mode s t v : win_eq s t -> win_eq (set_i_mode s v) t.
Proof. unfold win_eq. cbn. auto. Qed.

Lemma win_eq_refl s : win_eq s s.
Proof. unfold win_eq. repeat split; reflexivity. Qed.

Lemma nolive_NAME : ~ len_live NAME /\ ~ off_live NAME /\ ~ ext_live NAME /\ ~ data_mode NAME /\ hdr_mode NAME.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

(* EXTRA without (more) extra bytes: on to NAME, with the length 0 *)
Lemma extra_to_name flush src P0 O0 m a :
  hcase_ok (fun md => md = NAME) -> awf_stmt -> rel src P0 O0 m a -> awf src a -> m_leave m = 0 ->
  m_mode m = EXTRA -> m_bits m = 0 ->
  (Z.land (i_flags (m_s m)) 1024 = 0 \/ i_length (m_s m) = 0) ->
  hgoal flush src P0 O0 (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a
    (c_NAME2 (set_mode (upd_s m (fun s => set_i_length s 0)) NAME)).
Proof.
  intros CONT AW Rl Aw L0 Md B0 Fz.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = EXTRA) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  assert (LE: i_length (m_s m) = i_length (a_s a)) by (apply (se_length _ _ SQ); unfold len_live; do 7 right; exact MdA).
  set (a1 := AS (set_i_mode (set_i_length (a_s a) 0) NAME) (a_q a) (a_O a)).
  assert (ST: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
  { rewrite astep_EXTRA by exact MdA. unfold a_EXTRA.
    destruct Fz as [Fz|Fz]; [rewrite <- FE, Fz | rewrite <- LE, Fz]; cbn [negb andb];
      [reflexivity | destruct (_ =? 0); reflexivity]. }
  destruct nolive_NAME as (N1 & N2 & N3 & D1 & D2).
  eapply hgoal_go; [exact ST | exact (q_in _ _ _ _ _ Rl NB) | ].
  rewrite <- (stepf2_NAME flush lenfix_list distfix_list (set_mode (upd_s m (fun s => set_i_length s 0)) NAME))
    by reflexivity.
  eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | exact L0
                | reflexivity | reflexivity | reflexivity].
  - eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                         | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
    + eapply bitbuf_ext; [exact (rl_bb _ _ _ _ _ Rl) | reflexivity ..].
    + exact Q.
    + cbn. apply seq_mode_nolive; auto. apply seq_length. exact SQ.
    + intros _. cbn. exact (CK Hh).
    + intros H. exfalso. exact (D1 H).
    + left. exact D2.
    + reflexivity.
    + cbn. apply win_eq_mode, win_eq_length, win_eq_refl.
    + exact (rl_head _ _ _ _ _ Rl).
  - apply hbits_zero. exact B0.
Qed.

Lemma sh_extra : hcase_next EXTRA (fun md => md = NAME).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_EXTRA by exact Md. unfold c_EXTRA2. cbv zeta.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = EXTRA) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  pose proof (rl_head _ _ _ _ _ Rl) as HdF.
  assert (B0: m_bits m = 0) by (destruct (Hb Hh) as (_ & _ & B); apply B; left; exact Md).
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  assert (LE: i_length (m_s m) = i_length (a_s a)) by (apply (se_length _ _ SQ); unfold len_live; do 7 right; exact MdA).
  pose proof (bb_src _ _ _ BB) as Bs.
  pose proof (bb_nx _ _ _ BB) as Nx. pose proof (bb_P0 _ _ _ BB) as HP0.
  pose proof (proj1 (bb_inp _ _ _ BB)) as Li.
  set (p := P0 + m_nx m).
  assert (Qp: a_q a = 8 * p) by (rewrite Q; unfold mq, p; rewrite B0; lia).
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0) as [Fl|Fl]; cbn [negb]; cbv iota.
  { apply extra_to_name; auto. }
  rewrite HdF. cbn [andb]. cbv iota.
  set (c := Z.min (i_length (m_s m)) (m_have m)).
  destruct (Z.eqb_spec c 0) as [C0|C0]; cbn [negb]; cbv iota.
  - destruct (Z.eqb_spec (i_length (m_s m)) 0) as [Lz|Lz]; cbn [negb]; cbv iota.
    { apply extra_to_name; auto. }
    (* no input: the call stops before the next byte *)
    assert (Hv: m_have m = 0) by (unfold c in C0; lia).
    exists a. split; [apply ar_refl|]. split; [apply hrel_mk|].
    + intros _. apply rel_leave. exact Rl.
    + apply hbits_zero. exact B0.
    + unfold m_mode. cbn. exact (hdr_not_copy _ Hh).
    + intros _. eapply stop_need.
      * rewrite astep_EXTRA by exact MdA. unfold a_EXTRA. rewrite <- FE, <- LE.
        destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0); [contradiction|].
        destruct (Z.eqb_spec (i_length (m_s m)) 0); [contradiction|]. reflexivity.
      * rewrite Qp. unfold p, m_have in *. lia.
      * cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
  - (* c bytes of the extra field *)
    assert (Lr: 0 <= i_length (a_s a)) by (pose proof (sw_length _ (aw_swf _ _ Aw)) as U; unfold urange in U; lia).
    assert (Cr: 0 < c <= i_length (m_s m) /\ c <= m_have m) by (unfold c, m_have in *; lia).
    unfold m_have in Cr.
    rewrite crc_if_acrc.
    rewrite (inbytes_src src P0 m c BB ltac:(lia) ltac:(lia)). fold p.
    set (chunk := sublist p (p + c) src).
    destruct (acrc_fields (m_s m) chunk) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
    match goal with |- context [IBrk (set_leave ?X)] => set (m1 := X) end.
    assert (S1: m_s m1 = set_i_length (acrc (m_s m) chunk) (i_length (m_s m) - c))
      by (unfold m1; cbn; rewrite F6m; reflexivity).
    assert (BB1: bitbuf src P0 m1) by (eapply bitbuf_bytes; [exact BB | exact B0 | reflexivity | exact B0 | reflexivity | cbn; lia]).
    assert (Q1: mq P0 m1 = 8 * (p + c)) by (unfold mq, p; cbn; rewrite B0; lia).
    pose proof (ext_run src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) Bs (c - 1) ltac:(lia)
                  (a_s a) p (a_O a) MdA ltac:(rewrite <- FE; exact Fl) ltac:(unfold p; lia)
                  ltac:(unfold p; lia) ltac:(unfold p; lia) ltac:(rewrite <- LE; lia)) as AR.
    replace (p + (c - 1) + 1) with (p + c) in AR by lia. replace (c - 1 + 1) with c in AR by lia. fold chunk in AR.
    assert (Ea: AS (a_s a) (8 * p) (a_O a) = a) by (rewrite <- Qp; destruct a; reflexivity).
    rewrite Ea in AR.
    set (a' := AS (set_i_length (acrc (a_s a) chunk) (i_length (a_s a) - c)) (8 * (p + c)) (a_O a)) in AR.
    assert (Aw': awf src a') by (eapply awf_reach; eauto).
    assert (MdA': a_mode a' = EXTRA) by (unfold a', a_mode; cbn; destruct (acrc_fields (a_s a) chunk) as (G1 & _); rewrite G1; exact MdA).
    destruct (acrc_fields (a_s a) chunk) as (F1a & F2a & F3a & F4a & F5a & F6a & F7a & F8a).
    assert (SQ1: seq (m_s m1) (a_s a')).
    { rewrite S1. unfold a'. cbn [a_s]. rewrite LE. apply seq_length, seq_acrc. exact SQ. }
    assert (CK1: i_check (m_s m1) = i_check (a_s a')).
    { rewrite S1. unfold a'. cbn. apply acrc_check; [exact (CK Hh) | exact FE | apply (se_wrap _ _ SQ)]. }
    assert (R1: rel src P0 O0 m1 a').
    { eapply rel_hdr_next; [exact Rl | exact Hh | exact BB1 | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | | | reflexivity | exact SQ1 | intros _; exact CK1
                           | | | | | | ].
      - unfold m_mode. rewrite S1. cbn. rewrite F1m, F1a. exact (rl_mode _ _ _ _ _ Rl).
      - unfold a'. cbn [a_q]. rewrite Q1. reflexivity.
      - intros D. exfalso. revert D. unfold m_mode. rewrite S1. cbn. rewrite F1m.
        change (i_mode (m_s m)) with (m_mode m). rewrite Md. unfold data_mode, decode_mode. vm_compute. lia.
      - left. unfold m_mode. rewrite S1. cbn. rewrite F1m. exact Hh.
      - rewrite S1. cbn. exact F4m.
      - rewrite S1. apply win_eq_length. exact F8m.
      - rewrite S1. cbn. rewrite F5m. exact HdF.
      - apply bits_ok_hb.
        + apply hbits_zero. exact B0.
        + unfold m_mode. rewrite S1. cbn. rewrite F1m. exact (hdr_not_copy _ Hh). }
    eapply hgoal_reach; [exact AR|].
    rewrite S1. cbn [i_length set_i_length].
    destruct (Z.eqb_spec (i_length (m_s m) - c) 0) as [Ez|Ez]; cbn [negb]; cbv iota.
    + (* the end of the field: on to NAME *)
      destruct nolive_NAME as (N1 & N2 & N3 & D1 & D2).
      set (a2 := AS (set_i_mode (set_i_length (a_s a') 0) NAME) (a_q a') (a_O a')).
      assert (ST: astep lenfix_list distfix_list src a' = AGo (a_q a') false a2).
      { rewrite astep_EXTRA by exact MdA'. unfold a_EXTRA. unfold a'. cbn [a_s i_length set_i_length].
        rewrite <- LE, Ez. cbn [negb andb]. destruct (_ =? 0); reflexivity. }
      eapply hgoal_go; [exact ST | unfold a'; cbn [a_q]; unfold p; lia | ].
      match goal with |- context [c_NAME2 ?X] =>
        rewrite <- (stepf2_NAME flush lenfix_list distfix_list X) by reflexivity end.
      eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | exact L0
                    | reflexivity | reflexivity | reflexivity].
      * eapply rel_hdr_next; [exact R1 | | | reflexivity | reflexivity | reflexivity | reflexivity
                             | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
        -- unfold m_mode. rewrite S1. cbn. rewrite F1m. exact Hh.
        -- eapply bitbuf_ext; [exact BB1 | reflexivity ..].
        -- unfold a2. cbn [a_q]. rewrite (mq_ext P0 m1) by reflexivity. rewrite Q1. reflexivity.
        -- change (m_s (set_mode (upd_s m1 (fun s => set_i_length s 0)) NAME))
             with (set_i_mode (set_i_length (m_s m1) 0) NAME).
           apply seq_mode_nolive; auto. apply seq_length. exact SQ1.
        -- intros _. exact CK1.
        -- intros H. exfalso. exact (D1 H).
        -- left. exact D2.
        -- reflexivity.
        -- cbn. apply win_eq_mode, win_eq_length, win_eq_refl.
        -- change (i_head (m_s m1) = false). rewrite S1. cbn. rewrite F5m. exact HdF.
      * apply hbits_zero. exact B0.
    + (* the input ends in the field *)
      assert (Ch: c = Zlength (m_inp m) - m_nx m) by (unfold c, m_have in *; lia).
      exists a'. split; [apply ar_refl|]. split; [apply hrel_mk|].
      * intros _. apply rel_leave. exact R1.
      * apply hbits_zero. exact B0.
      * unfold m_mode. change (m_s (set_leave m1)) with (m_s m1). rewrite S1. cbn. rewrite F1m.
        exact (hdr_not_copy _ Hh).
      * intros _. eapply stop_need.
        -- rewrite astep_EXTRA by exact MdA'. unfold a_EXTRA. unfold a'. cbn [a_s i_length i_flags set_i_length].
           rewrite F2a, <- FE, <- LE.
           destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0); [contradiction|].
           destruct (Z.eqb_spec (i_length (m_s m) - c) 0); [contradiction|]. reflexivity.
        -- unfold a'. cbn [a_q]. unfold p. lia.
        -- cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
Qed.

(* the steps of NAME and COMMENT in the form of str_run *)
Lemma name_ST src a : a_mode a = NAME -> Z.land (i_flags (a_s a)) 2048 <> 0 ->
  astep lenfix_list distfix_list src a =
  AGo (a_q a + 8) false
    (AS (if sbyte src (a_q a) =? 0
         then (fun s => set_i_mode (set_i_length s 0) COMMENT) (acrc (a_s a) [sbyte src (a_q a)])
         else acrc (a_s a) [sbyte src (a_q a)]) (a_q a + 8) (a_O a)).
Proof.
  intros Md Fl. rewrite astep_NAME by exact Md. unfold a_NAME.
  destruct (Z.eqb_spec (Z.land (i_flags (a_s a)) 2048) 0); [contradiction|]. reflexivity.
Qed.

Lemma comment_ST src a : a_mode a = COMMENT -> Z.land (i_flags (a_s a)) 4096 <> 0 ->
  astep lenfix_list distfix_list src a =
  AGo (a_q a + 8) false
    (AS (if sbyte src (a_q a) =? 0
         then (fun s => set_i_mode s HCRC) (acrc (a_s a) [sbyte src (a_q a)])
         else acrc (a_s a) [sbyte src (a_q a)]) (a_q a + 8) (a_O a)).
Proof.
  intros Md Fl. rewrite astep_COMMENT by exact Md. unfold a_COMMENT.
  destruct (Z.eqb_spec (Z.land (i_flags (a_s a)) 4096) 0); [contradiction|]. reflexivity.
Qed.

(* k nonzero bytes, then the zero byte that ends the string *)
Lemma str_end (X fb: Z) (fin: istate -> istate) src I R :
  (forall a, a_mode a = X -> Z.land (i_flags (a_s a)) fb <> 0 ->
     astep lenfix_list distfix_list src a =
     AGo (a_q a + 8) false
       (AS (if sbyte src (a_q a) =? 0 then fin (acrc (a_s a) [sbyte src (a_q a)])
            else acrc (a_s a) [sbyte src (a_q a)]) (a_q a + 8) (a_O a))) ->
  bytes_ok src ->
  forall k s p O, 0 <= k -> i_mode s = X -> Z.land (i_flags s) fb <> 0 -> 0 <= p ->
    p + k + 1 <= I -> p + k + 1 <= Zlength src ->
    (forall i, 0 <= i < k -> Znth (p + i) src <> 0) -> Znth (p + k) src = 0 ->
    areach src I R (AS s (8 * p) O) (AS (fin (acrc s (sublist p (p + k + 1) src))) (8 * (p + k + 1)) O).
Proof.
  intros ST Bs k s p O Hk Md Fl Hp Lim Ls Nz Z0.
  assert (LAST: forall s' , i_mode s' = X -> Z.land (i_flags s') fb <> 0 ->
            astep lenfix_list distfix_list src (AS s' (8 * (p + k)) O) =
              AGo (8 * (p + k) + 8) false (AS (fin (acrc s' [0])) (8 * (p + k) + 8) O)).
  { intros s' M' F'. rewrite (ST (AS s' (8 * (p + k)) O) M' F'). cbn [a_q a_s a_O]. rewrite sbyte_8, Z0.
    reflexivity. }
  assert (NBk: forall s', ~ blocked I R (AS s' (8 * (p + k)) O)
                 (AGo (8 * (p + k) + 8) false (AS (fin (acrc s' [0])) (8 * (p + k) + 8) O))).
  { intros s'. cbn [blocked]. intros [B|[B _]]; [lia|discriminate]. }
  destruct (Z.eq_dec k 0) as [K0|K0].
  - subst k. rewrite Z.add_0_r in *.
    eapply ar_step; [exact (LAST s Md Fl) | exact (NBk s) | ].
    rewrite (sublist_one p (p + 1)) by lia. rewrite Z0. replace (8 * (p + 1)) with (8 * p + 8) by lia.
    apply ar_refl.
  - pose proof (str_run X fb fin src I R ST Bs (k - 1) ltac:(lia) s p O Md Fl Hp ltac:(lia) ltac:(lia)
                  ltac:(intros i Hi; apply Nz; lia)) as AR.
    replace (p + (k - 1) + 1) with (p + k) in AR by lia.
    eapply areach_trans; [exact AR|].
    destruct (acrc_fields s (sublist p (p + k) src)) as (F1 & F2 & _).
    eapply ar_step; [apply LAST; [rewrite F1; exact Md | rewrite F2; exact Fl] | apply NBk | ].
    rewrite acrc_app by (apply bytes_ok_sublist; exact Bs).
    rewrite (sublist_split p (p + k) (p + k + 1)) by lia. rewrite (sublist_one (p + k) (p + k + 1)) by lia.
    rewrite Z0. replace (8 * (p + k + 1)) with (8 * (p + k) + 8) by lia. apply ar_refl.
Qed.

Lemma set_length_same s : set_i_length s (i_length s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma nolive_COMMENT : ~ len_live COMMENT /\ ~ off_live COMMENT /\ ~ ext_live COMMENT /\
                       ~ data_mode COMMENT /\ hdr_mode COMMENT.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

Lemma nolive_HCRC : ~ len_live HCRC /\ ~ off_live HCRC /\ ~ ext_live HCRC /\
                    ~ data_mode HCRC /\ hdr_mode HCRC.
Proof. unfold len_live, off_live, ext_live, data_mode, decode_mode, hdr_mode. vm_compute. lia. Qed.

Lemma sh_name : hcase_next NAME (fun md => md = COMMENT).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_NAME by exact Md. unfold c_NAME2. cbv zeta.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = NAME) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  pose proof (rl_head _ _ _ _ _ Rl) as HdF.
  assert (B0: m_bits m = 0) by (destruct (Hb Hh) as (_ & _ & B); apply B; right; left; exact Md).
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  pose proof (bb_src _ _ _ BB) as Bs.
  pose proof (bb_nx _ _ _ BB) as Nx. pose proof (bb_P0 _ _ _ BB) as HP0.
  pose proof (proj1 (bb_inp _ _ _ BB)) as Li.
  set (p := P0 + m_nx m).
  assert (Qp: a_q a = 8 * p) by (rewrite Q; unfold mq, p; rewrite B0; lia).
  destruct nolive_COMMENT as (N1 & N2 & N3 & D1 & D2).
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 2048) 0) as [Fl|Fl]; cbn [negb]; cbv iota.
  - (* no file name *)
    rewrite HdF. cbv iota.
    set (a1 := AS (set_i_mode (set_i_length (a_s a) 0) COMMENT) (a_q a) (a_O a)).
    assert (ST: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
    { rewrite astep_NAME by exact MdA. unfold a_NAME. rewrite <- FE, Fl. reflexivity. }
    eapply hgoal_go; [exact ST | exact (q_in _ _ _ _ _ Rl NB) | ].
    match goal with |- context [c_COMMENT2 ?X] =>
      rewrite <- (stepf2_COMMENT flush lenfix_list distfix_list X) by reflexivity end.
    eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | exact L0
                  | reflexivity | reflexivity | reflexivity].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BB | reflexivity ..].
      * exact Q.
      * cbn. apply seq_mode_nolive; auto. apply seq_length. exact SQ.
      * intros _. cbn. exact (CK Hh).
      * intros H. exfalso. exact (D1 H).
      * left. exact D2.
      * reflexivity.
      * cbn. apply win_eq_mode, win_eq_length, win_eq_refl.
      * exact HdF.
    + apply hbits_zero. exact B0.
  - destruct (Z.eqb_spec (m_have m) 0) as [Hv|Hv]; cbv iota.
    + (* no input: the call stops before the next byte *)
      exists a. split; [apply ar_refl|]. split; [apply hrel_mk|].
      * intros _. apply rel_leave. exact Rl.
      * apply hbits_zero. exact B0.
      * unfold m_mode. cbn. exact (hdr_not_copy _ Hh).
      * intros _. eapply stop_need.
        -- apply name_ST; [exact MdA | rewrite <- FE; exact Fl].
        -- rewrite Qp. unfold p, m_have in *. lia.
        -- cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
    + rewrite HdF. cbn [andb].
      assert (Hv': 0 < m_have m) by (unfold m_have in *; lia).
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] bf] eqn:ZS.
      apply zstr_nowr in ZS; [| split; [lia | exact Hv'] | rewrite Z2Nat.id by lia; lia].
      destruct ZS as (Eln & Ebf & Cr & Eb & Nzc & Bend).
      subst ln bf.
      assert (BYT: forall i, 0 <= i < m_have m ->
                     Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (p + i) src).
      { intros i Hi. unfold m_have in Hi. rewrite Znth_sublist by lia.
        rewrite (inp_byte src P0 m) by (auto; lia). f_equal. unfold p. lia. }
      unfold m_have in Cr, BYT.
      rewrite crc_if_acrc, (inbytes_src src P0 m c BB ltac:(lia) ltac:(lia)). fold p.
      set (chunk := sublist p (p + c) src).
      destruct (acrc_fields (m_s m) chunk) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
      destruct (acrc_fields (a_s a) chunk) as (F1a & F2a & F3a & F4a & F5a & F6a & F7a & F8a).
      match goal with |- context [IBrk (set_leave ?X)] => set (m1 := X) end.
      assert (S1: m_s m1 = acrc (m_s m) chunk)
        by (unfold m1; cbn; rewrite <- F6m; apply set_length_same).
      assert (BB1: bitbuf src P0 m1)
        by (eapply bitbuf_bytes; [exact BB | exact B0 | reflexivity | exact B0 | reflexivity | cbn; lia]).
      assert (Q1: mq P0 m1 = 8 * (p + c)) by (unfold mq, p; cbn; rewrite B0; lia).
      assert (Ea: AS (a_s a) (8 * p) (a_O a) = a) by (rewrite <- Qp; destruct a; reflexivity).
      assert (Fla: Z.land (i_flags (a_s a)) 2048 <> 0) by (rewrite <- FE; exact Fl).
      assert (Hm1: hdr_mode (m_mode m1)) by (unfold m_mode; rewrite S1, F1m; exact Hh).
      destruct (Z.eqb_spec b 0) as [B0'|B0']; cbn [negb]; cbv iota.
      * (* the zero byte: on to COMMENT *)
        pose proof (str_end NAME 2048 (fun s => set_i_mode (set_i_length s 0) COMMENT) src
                      (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (name_ST src) Bs (c - 1)
                      (a_s a) p (a_O a) ltac:(lia) MdA Fla ltac:(unfold p; lia) ltac:(unfold p; lia)
                      ltac:(unfold p; lia)) as AR.
        specialize (AR ltac:(intros i Hi; rewrite <- BYT by lia; apply Nzc; lia)
                       ltac:(rewrite <- BYT by lia; rewrite <- Eb; exact B0')).
        replace (p + (c - 1) + 1) with (p + c) in AR by lia. fold chunk in AR. rewrite Ea in AR.
        cbv beta in AR.
        set (a2 := AS (set_i_mode (set_i_length (acrc (a_s a) chunk) 0) COMMENT) (8 * (p + c)) (a_O a)) in AR.
        eapply hgoal_reach; [exact AR|].
        match goal with |- context [c_COMMENT2 ?X] =>
          rewrite <- (stepf2_COMMENT flush lenfix_list distfix_list X) by reflexivity end.
        eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_reach; eauto | exact L0
                      | reflexivity | reflexivity | reflexivity].
        -- eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                               | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
           ++ eapply bitbuf_ext; [exact BB1 | reflexivity ..].
           ++ unfold a2. cbn [a_q]. rewrite (mq_ext P0 m1) by reflexivity. rewrite Q1. reflexivity.
           ++ change (m_s (set_mode (upd_s m1 (fun s => set_i_length s 0)) COMMENT))
                with (set_i_mode (set_i_length (m_s m1) 0) COMMENT).
              rewrite S1. apply seq_mode_nolive; auto. apply seq_length, seq_acrc. exact SQ.
           ++ intros _. change (i_check (m_s m1) = i_check (acrc (a_s a) chunk)). rewrite S1.
              apply acrc_check; [exact (CK Hh) | exact FE | apply (se_wrap _ _ SQ)].
           ++ intros H. exfalso. exact (D1 H).
           ++ left. exact D2.
           ++ change (i_total (m_s m1) = i_total (m_s m)). rewrite S1. exact F4m.
           ++ change (win_eq (set_i_mode (set_i_length (m_s m1) 0) COMMENT) (m_s m)). rewrite S1.
              apply win_eq_mode, win_eq_length. exact F8m.
           ++ change (i_head (m_s m1) = false). rewrite S1, F5m. exact HdF.
        -- apply hbits_zero. exact B0.
      * (* the input ends in the name *)
        destruct Bend as [Bz|Ch]; [contradiction|].
        pose proof (str_run NAME 2048 (fun s => set_i_mode (set_i_length s 0) COMMENT) src
                      (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (name_ST src) Bs (c - 1) ltac:(lia)
                      (a_s a) p (a_O a) MdA Fla ltac:(unfold p; lia) ltac:(unfold p; lia) ltac:(unfold p; lia))
          as AR.
        specialize (AR ltac:(intros i Hi; rewrite <- BYT by lia;
                             destruct (Z.eq_dec i (c - 1)) as [->|Ne]; [rewrite <- Eb; exact B0' | apply Nzc; lia])).
        replace (p + (c - 1) + 1) with (p + c) in AR by lia. fold chunk in AR. rewrite Ea in AR.
        set (a' := AS (acrc (a_s a) chunk) (8 * (p + c)) (a_O a)) in AR.
        exists a'. split; [exact AR|]. split; [apply hrel_mk|].
        -- intros _. apply rel_leave.
           eapply rel_hdr_next; [exact Rl | exact Hh | exact BB1 | reflexivity | reflexivity | reflexivity | reflexivity
                                | reflexivity | reflexivity | reflexivity | | | reflexivity | | | | | | | | ].
           ++ unfold m_mode, a_mode, a'. cbn [a_s]. rewrite S1, F1m, F1a. exact (rl_mode _ _ _ _ _ Rl).
           ++ unfold a'. cbn [a_q]. rewrite Q1. reflexivity.
           ++ rewrite S1. apply seq_acrc. exact SQ.
           ++ intros _. rewrite S1. apply acrc_check; [exact (CK Hh) | exact FE | apply (se_wrap _ _ SQ)].
           ++ intros D. exfalso. unfold m_mode in D. rewrite S1, F1m in D.
              change (i_mode (m_s m)) with (m_mode m) in D. rewrite Md in D. revert D.
              unfold data_mode, decode_mode. vm_compute. lia.
           ++ left. exact Hm1.
           ++ rewrite S1. exact F4m.
           ++ rewrite S1. exact F8m.
           ++ rewrite S1, F5m. exact HdF.
           ++ apply bits_ok_hb; [apply hbits_zero; exact B0 | exact (hdr_not_copy _ Hm1)].
        -- apply hbits_zero. exact B0.
        -- exact (hdr_not_copy _ Hm1).
        -- intros _. eapply stop_need.
           ++ apply name_ST; [unfold a', a_mode; cbn; rewrite F1a; exact MdA | unfold a'; cbn; rewrite F2a; exact Fla].
           ++ unfold a'. cbn [a_q]. unfold p, m_have in *. lia.
           ++ cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
Qed.

Lemma sh_comment : hcase_next COMMENT (fun md => md = HCRC).
Proof.
  intros KIT AW CONT flush src P0 O0 m a [Rl Hb] Aw L0 Md.
  rewrite stepf2_COMMENT by exact Md. unfold c_COMMENT2. cbv zeta.
  assert (Hh: hdr_mode (m_mode m)) by (rewrite Md; unfold hdr_mode; auto 20).
  destruct (hdr_not_bad _ Hh) as [NB _].
  assert (MdA: a_mode a = COMMENT) by (rewrite <- (rl_mode _ _ _ _ _ Rl); exact Md).
  pose proof (rl_s _ _ _ _ _ Rl NB) as SQ.
  destruct (rl_chk _ _ _ _ _ Rl) as (CK & _).
  pose proof (rl_bb _ _ _ _ _ Rl) as BB.
  pose proof (rl_q _ _ _ _ _ Rl NB) as Q.
  pose proof (rl_head _ _ _ _ _ Rl) as HdF.
  assert (B0: m_bits m = 0) by (destruct (Hb Hh) as (_ & _ & B); apply B; right; right; left; exact Md).
  assert (FE: i_flags (m_s m) = i_flags (a_s a)) by apply (se_flags _ _ SQ).
  pose proof (bb_src _ _ _ BB) as Bs.
  pose proof (bb_nx _ _ _ BB) as Nx. pose proof (bb_P0 _ _ _ BB) as HP0.
  pose proof (proj1 (bb_inp _ _ _ BB)) as Li.
  set (p := P0 + m_nx m).
  assert (Qp: a_q a = 8 * p) by (rewrite Q; unfold mq, p; rewrite B0; lia).
  destruct nolive_HCRC as (N1 & N2 & N3 & D1 & D2).
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 4096) 0) as [Fl|Fl]; cbn [negb]; cbv iota.
  - (* no comment *)
    rewrite HdF. cbv iota.
    set (a1 := AS (set_i_mode (a_s a) HCRC) (a_q a) (a_O a)).
    assert (ST: astep lenfix_list distfix_list src a = AGo (a_q a) false a1).
    { rewrite astep_COMMENT by exact MdA. unfold a_COMMENT. rewrite <- FE, Fl. reflexivity. }
    eapply hgoal_go; [exact ST | exact (q_in _ _ _ _ _ Rl NB) | ].
    match goal with |- context [c_HCRC ?X] =>
      rewrite <- (stepf2_HCRC flush lenfix_list distfix_list X) by reflexivity end.
    eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_go; eauto | exact L0
                  | reflexivity | reflexivity | reflexivity].
    + eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                           | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
      * eapply bitbuf_ext; [exact BB | reflexivity ..].
      * exact Q.
      * cbn. apply seq_mode_nolive; auto.
      * intros _. cbn. exact (CK Hh).
      * intros H. exfalso. exact (D1 H).
      * left. exact D2.
      * reflexivity.
      * cbn. apply win_eq_mode, win_eq_refl.
      * exact HdF.
    + apply hbits_zero. exact B0.
  - destruct (Z.eqb_spec (m_have m) 0) as [Hv|Hv]; cbv iota.
    + (* no input: the call stops before the next byte *)
      exists a. split; [apply ar_refl|]. split; [apply hrel_mk|].
      * intros _. apply rel_leave. exact Rl.
      * apply hbits_zero. exact B0.
      * unfold m_mode. cbn. exact (hdr_not_copy _ Hh).
      * intros _. eapply stop_need.
        -- apply comment_ST; [exact MdA | rewrite <- FE; exact Fl].
        -- rewrite Qp. unfold p, m_have in *. lia.
        -- cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
    + rewrite HdF. cbn [andb].
      assert (Hv': 0 < m_have m) by (unfold m_have in *; lia).
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[c b] ln] bf] eqn:ZS.
      apply zstr_nowr in ZS; [| split; [lia | exact Hv'] | rewrite Z2Nat.id by lia; lia].
      destruct ZS as (Eln & Ebf & Cr & Eb & Nzc & Bend).
      subst ln bf.
      assert (BYT: forall i, 0 <= i < m_have m ->
                     Znth i (sublist (m_nx m) (Zlength (m_inp m)) (m_inp m)) = Znth (p + i) src).
      { intros i Hi. unfold m_have in Hi. rewrite Znth_sublist by lia.
        rewrite (inp_byte src P0 m) by (auto; lia). f_equal. unfold p. lia. }
      unfold m_have in Cr, BYT.
      rewrite crc_if_acrc, (inbytes_src src P0 m c BB ltac:(lia) ltac:(lia)). fold p.
      set (chunk := sublist p (p + c) src).
      destruct (acrc_fields (m_s m) chunk) as (F1m & F2m & F3m & F4m & F5m & F6m & F7m & F8m).
      destruct (acrc_fields (a_s a) chunk) as (F1a & F2a & F3a & F4a & F5a & F6a & F7a & F8a).
      match goal with |- context [IBrk (set_leave ?X)] => set (m1 := X) end.
      assert (S1: m_s m1 = acrc (m_s m) chunk)
        by (unfold m1; cbn; rewrite <- F6m; apply set_length_same).
      assert (BB1: bitbuf src P0 m1)
        by (eapply bitbuf_bytes; [exact BB | exact B0 | reflexivity | exact B0 | reflexivity | cbn; lia]).
      assert (Q1: mq P0 m1 = 8 * (p + c)) by (unfold mq, p; cbn; rewrite B0; lia).
      assert (Ea: AS (a_s a) (8 * p) (a_O a) = a) by (rewrite <- Qp; destruct a; reflexivity).
      assert (Fla: Z.land (i_flags (a_s a)) 4096 <> 0) by (rewrite <- FE; exact Fl).
      assert (Hm1: hdr_mode (m_mode m1)) by (unfold m_mode; rewrite S1, F1m; exact Hh).
      destruct (Z.eqb_spec b 0) as [B0'|B0']; cbn [negb]; cbv iota.
      * (* the zero byte: on to HCRC *)
        pose proof (str_end COMMENT 4096 (fun s => set_i_mode s HCRC) src
                      (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (comment_ST src) Bs (c - 1)
                      (a_s a) p (a_O a) ltac:(lia) MdA Fla ltac:(unfold p; lia) ltac:(unfold p; lia)
                      ltac:(unfold p; lia)) as AR.
        specialize (AR ltac:(intros i Hi; rewrite <- BYT by lia; apply Nzc; lia)
                       ltac:(rewrite <- BYT by lia; rewrite <- Eb; exact B0')).
        replace (p + (c - 1) + 1) with (p + c) in AR by lia. fold chunk in AR. rewrite Ea in AR.
        cbv beta in AR.
        set (a2 := AS (set_i_mode (acrc (a_s a) chunk) HCRC) (8 * (p + c)) (a_O a)) in AR.
        eapply hgoal_reach; [exact AR|].
        match goal with |- context [c_HCRC ?X] =>
          rewrite <- (stepf2_HCRC flush lenfix_list distfix_list X) by reflexivity end.
        eapply hcont; [exact CONT | apply hrel_mk; [intros BO | | hrel_md] | eapply awf_reach; eauto | exact L0
                      | reflexivity | reflexivity | reflexivity].
        -- eapply rel_hdr_next; [exact Rl | exact Hh | | reflexivity | reflexivity | reflexivity | reflexivity
                               | reflexivity | reflexivity | reflexivity | reflexivity | | reflexivity | | | | | | | | exact BO].
           ++ eapply bitbuf_ext; [exact BB1 | reflexivity ..].
           ++ unfold a2. cbn [a_q]. rewrite (mq_ext P0 m1) by reflexivity. rewrite Q1. reflexivity.
           ++ change (m_s (set_mode m1 HCRC)) with (set_i_mode (m_s m1) HCRC).
              rewrite S1. apply seq_mode_nolive; auto. apply seq_acrc. exact SQ.
           ++ intros _. change (i_check (m_s m1) = i_check (acrc (a_s a) chunk)). rewrite S1.
              apply acrc_check; [exact (CK Hh) | exact FE | apply (se_wrap _ _ SQ)].
           ++ intros H. exfalso. exact (D1 H).
           ++ left. exact D2.
           ++ change (i_total (m_s m1) = i_total (m_s m)). rewrite S1. exact F4m.
           ++ change (win_eq (set_i_mode (m_s m1) HCRC) (m_s m)). rewrite S1.
              apply win_eq_mode. exact F8m.
           ++ change (i_head (m_s m1) = false). rewrite S1, F5m. exact HdF.
        -- apply hbits_zero. exact B0.
      * (* the input ends in the comment *)
        destruct Bend as [Bz|Ch]; [contradiction|].
        pose proof (str_run COMMENT 4096 (fun s => set_i_mode s HCRC) src
                      (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (comment_ST src) Bs (c - 1) ltac:(lia)
                      (a_s a) p (a_O a) MdA Fla ltac:(unfold p; lia) ltac:(unfold p; lia) ltac:(unfold p; lia))
          as AR.
        specialize (AR ltac:(intros i Hi; rewrite <- BYT by lia;
                             destruct (Z.eq_dec i (c - 1)) as [->|Ne]; [rewrite <- Eb; exact B0' | apply Nzc; lia])).
        replace (p + (c - 1) + 1) with (p + c) in AR by lia. fold chunk in AR. rewrite Ea in AR.
        set (a' := AS (acrc (a_s a) chunk) (8 * (p + c)) (a_O a)) in AR.
        exists a'. split; [exact AR|]. split; [apply hrel_mk|].
        -- intros _. apply rel_leave.
           eapply rel_hdr_next; [exact Rl | exact Hh | exact BB1 | reflexivity | reflexivity | reflexivity | reflexivity
                                | reflexivity | reflexivity | reflexivity | | | reflexivity | | | | | | | | ].
           ++ unfold m_mode, a_mode, a'. cbn [a_s]. rewrite S1, F1m, F1a. exact (rl_mode _ _ _ _ _ Rl).
           ++ unfold a'. cbn [a_q]. rewrite Q1. reflexivity.
           ++ rewrite S1. apply seq_acrc. exact SQ.
           ++ intros _. rewrite S1. apply acrc_check; [exact (CK Hh) | exact FE | apply (se_wrap _ _ SQ)].
           ++ intros D. exfalso. unfold m_mode in D. rewrite S1, F1m in D.
              change (i_mode (m_s m)) with (m_mode m) in D. rewrite Md in D. revert D.
              unfold data_mode, decode_mode. vm_compute. lia.
           ++ left. exact Hm1.
           ++ rewrite S1. exact F4m.
           ++ rewrite S1. exact F8m.
           ++ rewrite S1, F5m. exact HdF.
           ++ apply bits_ok_hb; [apply hbits_zero; exact B0 | exact (hdr_not_copy _ Hm1)].
        -- apply hbits_zero. exact B0.
        -- exact (hdr_not_copy _ Hm1).
        -- intros _. eapply stop_need.
           ++ apply comment_ST; [unfold a', a_mode; cbn; rewrite F1a; exact MdA | unfold a'; cbn; rewrite F2a; exact Fla].
           ++ unfold a'. cbn [a_q]. unfold p, m_have in *. lia.
           ++ cbn. apply (rl_ret _ _ _ _ _ Rl NB). rewrite Md. discriminate.
Qed.

Lemma sh_str : hcase_next EXTRA (fun md => md = NAME) /\ hcase_next NAME (fun md => md = COMMENT) /\
               hcase_next COMMENT (fun md => md = HCRC).
Proof. split; [exact sh_extra | split; [exact sh_name | exact sh_comment]]. Qed.

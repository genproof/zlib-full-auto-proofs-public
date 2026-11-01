(* Law uncompress_any, theory part: one inflate() call keeps ua_fd (no dictionary; a header with FDICT never
   gets past DICT), so Z_STREAM_END only without FDICT (UATheoryDefs.ua_fd_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.uncompress_any.UATheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryHead.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict.
Require Import Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.harness.inflate_codes.TheoryCall.
Require Import Zlib.proof.harness.inflate_check.IKTheoryCall.
Require Zlib.proof.harness.uncompress_any.UAStepMwf.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* No pass of the switch changes i_havedict (frame facts of the helpers, as TheoryNoDict.v's nd_)   *)

Definition uh_keep (m m': mst) : Prop := i_havedict (m_s m') = i_havedict (m_s m).

Lemma uh_keep_trans m1 m2 m3 : uh_keep m1 m2 -> uh_keep m2 m3 -> uh_keep m1 m3.
Proof. unfold uh_keep; intros F1 F2. rewrite F2; exact F1. Qed.

Lemma uh_keep_refl m : uh_keep m m.
Proof. reflexivity. Qed.

Lemma uh_needbits_f_s k n m : m_s (needbits_f k n m) = m_s m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [auto|].
  destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [cbn; auto|].
  rewrite IHk; reflexivity.
Qed.

Lemma uh_needbits_s n m : m_s (needbits n m) = m_s m.
Proof. apply uh_needbits_f_s. Qed.

Local Opaque needbits needbits_f.

Lemma uh_crc_if m d : i_havedict (m_s (crc_if m d)) = i_havedict (m_s m).
Proof. unfold crc_if; destruct (andb _ _); reflexivity. Qed.

Lemma uh_lens_fill k len s : i_havedict (lens_fill k len s) = i_havedict s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [auto|]. rewrite IHk; reflexivity. Qed.

Lemma uh_lenlens_zero k s : i_havedict (lenlens_zero k s) = i_havedict s.
Proof.
  revert s; induction k; intros s; cbn [lenlens_zero]; [auto|].
  destruct (_ <? 19); [|auto]. rewrite IHk; reflexivity.
Qed.

Lemma uh_lookup1_f k fx dx t nb m h m' ok : lookup1_f k fx dx t nb m = (h, m', ok) -> m_s m' = m_s m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; rewrite E; reflexivity.
Qed.

Lemma uh_lookup1 fx dx t nb m h m' ok : lookup1 fx dx t nb m = (h, m', ok) -> m_s m' = m_s m.
Proof. apply uh_lookup1_f. Qed.

Lemma uh_lookup2_f k fx dx t last m h m' ok : lookup2_f k fx dx t last m = (h, m', ok) -> m_s m' = m_s m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E.
  - inversion E; auto.
  - destruct (_ <=? _); [inversion E; auto|].
    destruct (m_have m =? 0); [inversion E; subst; cbn; auto|].
    apply IHk in E; rewrite E; reflexivity.
Qed.

Lemma uh_lookup2 fx dx t last m h m' ok : lookup2 fx dx t last m = (h, m', ok) -> m_s m' = m_s m.
Proof. apply uh_lookup2_f. Qed.

Lemma uh_fwalk_f fx dx k il t here m h' m' : fwalk_f fx dx k il t here m = (h', m') -> m_s m' = m_s m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E.
  - inversion E; subst; cbn; auto.
  - destruct (il (e_op here)).
    + apply IHk in E; rewrite E; reflexivity.
    + inversion E; subst; cbn; auto.
Qed.

Hint Rewrite uh_needbits_s uh_crc_if uh_lens_fill uh_lenlens_zero : uh_db.

Ltac uh_hdest x :=
  lazymatch x with
  | match ?c with _ => _ end => uh_hdest c
  | context [match ?c with _ => _ end] => uh_hdest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac uh_hsplit :=
  repeat (cbv beta iota zeta;
          match goal with
          | |- context [match ?x with _ => _ end] => uh_hdest x
          end).

Ltac uh_huse :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply uh_lookup1 in E
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply uh_lookup2 in E
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply uh_fwalk_f in E
  end.

Ltac uh_hcbn := cbn -[needbits_f needbits crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                    lenlens_loop codelens_iter codelens_loop zstr_f call_table copy_bytes
                    fwalk_f fast_iter fast_loop fast Zlength].

Ltac uh_hrw :=
  repeat match goal with
  | H: m_s ?a = _ |- context [m_s ?a] => rewrite H
  | H: i_havedict (m_s ?a) = _ |- context [i_havedict (m_s ?a)] => rewrite H
  end.

Ltac uh_close := unfold uh_keep in *; repeat progress (uh_hcbn; autorewrite with uh_db; uh_hrw); try reflexivity.

Definition uh_clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

Lemma uh_codelens_iter fx dx m : uh_keep m (uh_clm (codelens_iter fx dx m)).
Proof. unfold codelens_iter. uh_hsplit; uh_huse; uh_close. Qed.

Lemma uh_codelens_loop fx dx k m : uh_keep m (uh_clm (codelens_loop fx dx k m)).
Proof.
  revert m; induction k; intros m; cbn [codelens_loop]; [apply uh_keep_refl|].
  destruct (_ <? _); [|apply uh_keep_refl].
  pose proof (uh_codelens_iter fx dx m) as A.
  destruct (codelens_iter fx dx m) eqn:E; cbn in A |- *; auto.
  eapply uh_keep_trans; [exact A | apply IHk].
Qed.

Lemma uh_lenlens_loop k m : uh_keep m (lenlens_loop k m).
Proof.
  revert m; induction k; intros m; cbn [lenlens_loop]; [apply uh_keep_refl|].
  destruct (i_have (m_s m) <? i_ncode (m_s m)); [|apply uh_keep_refl].
  destruct (m_leave (needbits 3 m) =? 1); [unfold uh_keep; autorewrite with uh_db; reflexivity|].
  eapply uh_keep_trans; [|apply IHk]. uh_close.
Qed.

Lemma uh_fast_iter fx dx m : uh_keep m (snd (fast_iter fx dx m)).
Proof. unfold fast_iter. uh_hsplit; uh_huse; uh_close. Qed.

Lemma uh_fast_loop fx dx k m : uh_keep m (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m; cbn [fast_loop]; [apply uh_keep_refl|].
  pose proof (uh_fast_iter fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1] eqn:E; cbn in A |- *.
  destruct (andb _ _); [eapply uh_keep_trans; [exact A | apply IHk] | exact A].
Qed.

Lemma uh_fast fx dx m : uh_keep m (fast fx dx m).
Proof.
  unfold fast. cbv zeta.
  pose proof (uh_fast_loop fx dx (Z.to_nat (m_aout m) + 1) m) as A; revert A.
  generalize (fast_loop fx dx (Z.to_nat (m_aout m) + 1) m); intros m1 A.
  eapply uh_keep_trans; [exact A|]. uh_close.
Qed.

Definition uh_om (o: iout) : mst := match o with IBrk m' => m' | IRet _ m' => m' end.

Ltac uh_case := uh_hsplit; uh_huse; cbn [uh_om]; uh_close.

Section CasesUH.
Variables (fl: Z) (fx dx: list entry).

Lemma uh_c_DONE m : i_havedict (m_s (uh_om (c_DONE m))) = i_havedict (m_s m).
Proof. unfold c_DONE; uh_case. Qed.
#[local] Hint Rewrite uh_c_DONE : uh_db.
Lemma uh_c_BAD m : i_havedict (m_s (uh_om (c_BAD m))) = i_havedict (m_s m).
Proof. unfold c_BAD; uh_case. Qed.
#[local] Hint Rewrite uh_c_BAD : uh_db.
Lemma uh_c_LENGTH m : i_havedict (m_s (uh_om (c_LENGTH m))) = i_havedict (m_s m).
Proof. unfold c_LENGTH; uh_case. Qed.
#[local] Hint Rewrite uh_c_LENGTH : uh_db.
Lemma uh_c_CHECK m : i_havedict (m_s (uh_om (c_CHECK m))) = i_havedict (m_s m).
Proof. unfold c_CHECK; uh_case. Qed.
#[local] Hint Rewrite uh_c_CHECK : uh_db.
Lemma uh_c_LIT m : i_havedict (m_s (uh_om (c_LIT m))) = i_havedict (m_s m).
Proof. unfold c_LIT; uh_case. Qed.
#[local] Hint Rewrite uh_c_LIT : uh_db.
Lemma uh_c_MATCH m : i_havedict (m_s (uh_om (c_MATCH m))) = i_havedict (m_s m).
Proof. unfold c_MATCH; uh_case. Qed.
#[local] Hint Rewrite uh_c_MATCH : uh_db.
Lemma uh_c_DISTEXT m : i_havedict (m_s (uh_om (c_DISTEXT m))) = i_havedict (m_s m).
Proof. unfold c_DISTEXT; uh_case. Qed.
#[local] Hint Rewrite uh_c_DISTEXT : uh_db.
Lemma uh_c_DIST m : i_havedict (m_s (uh_om (c_DIST fx dx m))) = i_havedict (m_s m).
Proof. unfold c_DIST; uh_case. Qed.
#[local] Hint Rewrite uh_c_DIST : uh_db.
Lemma uh_c_LENEXT m : i_havedict (m_s (uh_om (c_LENEXT fx dx m))) = i_havedict (m_s m).
Proof. unfold c_LENEXT; uh_case. Qed.
#[local] Hint Rewrite uh_c_LENEXT : uh_db.
Lemma uh_c_LEN m : i_havedict (m_s (uh_om (c_LEN fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof.
  unfold c_LEN.
  pose proof (uh_fast fx dx (restore m)) as Hf; unfold uh_keep in Hf; uh_hcbn; revert Hf.
  generalize (fast fx dx (restore m)); intros mf Hf.
  uh_case.
Qed.
#[local] Hint Rewrite uh_c_LEN : uh_db.
Lemma uh_c_LEN_ m : i_havedict (m_s (uh_om (c_LEN_ fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof. unfold c_LEN_; uh_case. Qed.
#[local] Hint Rewrite uh_c_LEN_ : uh_db.
Lemma uh_c_CODELENS m : i_havedict (m_s (uh_om (c_CODELENS fl fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof.
  unfold c_CODELENS.
  pose proof (uh_codelens_loop fx dx 320 m) as Hc; revert Hc.
  generalize (codelens_loop fx dx 320 m); intros o Hc.
  destruct o as [m0|m0|m0]; cbn [uh_clm] in Hc; unfold uh_keep in Hc; uh_case.
Qed.
#[local] Hint Rewrite uh_c_CODELENS : uh_db.
Lemma uh_c_LENLENS m : i_havedict (m_s (uh_om (c_LENLENS fl fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof.
  unfold c_LENLENS. cbv beta zeta.
  pose proof (uh_lenlens_loop 19 m) as A; unfold uh_keep in A; revert A.
  generalize (lenlens_loop 19 m); intros ml A.
  destruct (m_leave ml =? 1); [exact A|].
  pose proof (uh_lenlens_zero 19 (m_s ml)) as Z0; revert Z0.
  generalize (lenlens_zero 19 (m_s ml)); intros sz Z0.
  set (s0 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next sz 0) (TCodes 0)) (TCodes 0)) 7).
  assert (Hs0 : i_havedict s0 = i_havedict (m_s m)) by (unfold s0; cbn [i_havedict set_i_lenbits set_i_distcode set_i_lencode set_i_next]; congruence).
  clearbody s0.
  destruct (call_table CODES 0 19 7 s0) as [[[r codes] nxt] lb].
  destruct (negb (r =? 0)).
  - exact Hs0.
  - rewrite uh_c_CODELENS. exact Hs0.
Qed.
#[local] Hint Rewrite uh_c_LENLENS : uh_db.
Lemma uh_c_TABLE m : i_havedict (m_s (uh_om (c_TABLE fl fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof. unfold c_TABLE; uh_case. Qed.
#[local] Hint Rewrite uh_c_TABLE : uh_db.
Lemma uh_c_COPY m : i_havedict (m_s (uh_om (c_COPY m))) = i_havedict (m_s m).
Proof. unfold c_COPY; uh_case. Qed.
#[local] Hint Rewrite uh_c_COPY : uh_db.
Lemma uh_c_COPY_ m : i_havedict (m_s (uh_om (c_COPY_ m))) = i_havedict (m_s m).
Proof. unfold c_COPY_; uh_case. Qed.
#[local] Hint Rewrite uh_c_COPY_ : uh_db.
Lemma uh_c_STORED m : i_havedict (m_s (uh_om (c_STORED fl m))) = i_havedict (m_s m).
Proof. unfold c_STORED; uh_case. Qed.
#[local] Hint Rewrite uh_c_STORED : uh_db.
Lemma uh_c_TYPEDO m : i_havedict (m_s (uh_om (c_TYPEDO fl m))) = i_havedict (m_s m).
Proof. unfold c_TYPEDO; uh_case. Qed.
#[local] Hint Rewrite uh_c_TYPEDO : uh_db.
Lemma uh_c_TYPE m : i_havedict (m_s (uh_om (c_TYPE fl m))) = i_havedict (m_s m).
Proof. unfold c_TYPE; uh_case. Qed.
#[local] Hint Rewrite uh_c_TYPE : uh_db.
Lemma uh_c_DICT m : i_havedict (m_s (uh_om (c_DICT fl m))) = i_havedict (m_s m).
Proof. unfold c_DICT; uh_case. Qed.
#[local] Hint Rewrite uh_c_DICT : uh_db.
Lemma uh_c_DICTID m : i_havedict (m_s (uh_om (c_DICTID fl m))) = i_havedict (m_s m).
Proof. unfold c_DICTID; uh_case. Qed.
#[local] Hint Rewrite uh_c_DICTID : uh_db.
Lemma uh_c_HCRC m : i_havedict (m_s (uh_om (c_HCRC m))) = i_havedict (m_s m).
Proof. unfold c_HCRC; uh_case. Qed.
#[local] Hint Rewrite uh_c_HCRC : uh_db.
Lemma uh_c_COMMENT2 m : i_havedict (m_s (uh_om (c_COMMENT2 m))) = i_havedict (m_s m).
Proof. unfold c_COMMENT2; uh_case. Qed.
#[local] Hint Rewrite uh_c_COMMENT2 : uh_db.
Lemma uh_c_NAME2 m : i_havedict (m_s (uh_om (c_NAME2 m))) = i_havedict (m_s m).
Proof. unfold c_NAME2; uh_case. Qed.
#[local] Hint Rewrite uh_c_NAME2 : uh_db.
Lemma uh_c_EXTRA2 m : i_havedict (m_s (uh_om (c_EXTRA2 m))) = i_havedict (m_s m).
Proof. unfold c_EXTRA2; uh_case. Qed.
#[local] Hint Rewrite uh_c_EXTRA2 : uh_db.
Lemma uh_c_EXLEN2 m : i_havedict (m_s (uh_om (c_EXLEN2 m))) = i_havedict (m_s m).
Proof. unfold c_EXLEN2; uh_case. Qed.
#[local] Hint Rewrite uh_c_EXLEN2 : uh_db.
Lemma uh_c_OS2 m : i_havedict (m_s (uh_om (c_OS2 m))) = i_havedict (m_s m).
Proof. unfold c_OS2; uh_case. Qed.
#[local] Hint Rewrite uh_c_OS2 : uh_db.
Lemma uh_c_TIME2 m : i_havedict (m_s (uh_om (c_TIME2 m))) = i_havedict (m_s m).
Proof. unfold c_TIME2; uh_case. Qed.
#[local] Hint Rewrite uh_c_TIME2 : uh_db.
Lemma uh_c_FLAGS2 m : i_havedict (m_s (uh_om (c_FLAGS2 m))) = i_havedict (m_s m).
Proof. unfold c_FLAGS2; uh_case. Qed.
#[local] Hint Rewrite uh_c_FLAGS2 : uh_db.
Lemma uh_c_HEAD2 m : i_havedict (m_s (uh_om (c_HEAD2 m))) = i_havedict (m_s m).
Proof. unfold c_HEAD2; uh_case. Qed.
#[local] Hint Rewrite uh_c_HEAD2 : uh_db.

Lemma uh_step2 m : i_havedict (m_s (uh_om (step2 fl fx dx (fast fx dx) m))) = i_havedict (m_s m).
Proof.
  unfold step2. cbv zeta.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota).
  all: autorewrite with uh_db; reflexivity.
Qed.

End CasesUH.

Lemma uh_stepf2 flush m :
  i_havedict (m_s (uh_om (stepf2 flush lenfix_list distfix_list m))) = i_havedict (m_s m).
Proof. apply uh_step2. Qed.

(* inf_leave keeps i_havedict *)
Lemma uh_uw (s: istate) (d: list Z) : i_havedict (updatewindow s d) = i_havedict s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma uh_leave_fin flush m : i_havedict (m_s (r_m (leave_fin flush m))) = i_havedict (m_s m).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok flush m); cbn [r_m m_s upd_s set_m_s set_m_tout set_m_tin set_m_adler set_i_total set_i_check
    set_i_win i_havedict restore set_m_sow set_m_snx set_i_bits set_i_hold];
  rewrite ?uh_uw;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; rewrite ?uh_uw; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* With FDICT, no pass leaves HEAD, DICTID, DICT, BAD, MEM (no dictionary is set)                  *)

Definition ua_S (md: Z) : Prop := md = HEAD \/ md = DICTID \/ md = DICT \/ md = BAD \/ md = MEM.

Lemma ua_head_mode src pos inp aout flush m :
  ctx_ok src pos inp -> Kc 5 src pos inp aout m -> mwf3 m -> m_leave m = 0 -> m_mode m = HEAD -> fdict src ->
  ua_S (m_mode (uh_om (stepf2 flush lenfix_list distfix_list m))).
Proof.
  intros Hc K Hw Hl Hmd FD.
  pose proof (Inv.mw_nx _ (proj1 Hw)) as Hnx.
  pose proof (kc_inp _ _ _ _ _ _ K) as Hinp. subst inp.
  pose proof Hc as (Hpos & Hsrc & Hbytes & _).
  assert (Hmd' : i_mode (m_s m) = HEAD) by exact Hmd.
  unfold stepf2, step2. cbv beta zeta. rewrite Hmd, Z.eqb_refl.
  unfold c_HEAD2. cbv beta zeta. rewrite (kc_wrap _ _ _ _ _ _ K).
  change (5 =? 0) with false. cbv iota.
  pose proof (kc_hd _ _ _ _ _ _ K ltac:(discriminate) Hmd) as Hhd.
  destruct (thh_nb m src pos Hc Hnx Hhd) as (nx' & Hn' & [[E Hp]|[E Hp]]); rewrite E.
  { rewrite thh_lv1. cbn [uh_om]. left. exact Hmd'. }
  set (H2 := le_val (sublist 0 2 src)).
  set (m2 := set_m_bits (set_m_hold (set_m_nx m nx') H2) 16).
  assert (E1 : (m_leave m2 =? 1) = false) by (cbn; rewrite Hl; reflexivity).
  assert (E2 : m_s m2 = m_s m) by reflexivity.
  assert (E3 : m_hold m2 = H2) by reflexivity.
  rewrite E1, E2, E3, (kc_wrap _ _ _ _ _ _ K), (kc_head _ _ _ _ _ _ K).
  cbv iota. change (Z.land 5 2 =? 0) with true. change (Z.land 5 1 =? 0) with false.
  cbn [negb andb orb].
  destruct (negb _); [cbn [uh_om]; right; right; right; left; reflexivity|].
  destruct (negb (m_hold m2 mod 16 =? 8)); [cbn [uh_om]; right; right; right; left; reflexivity|].
  destruct (orb _ _); [cbn [uh_om]; right; right; right; left; reflexivity|].
  match goal with |- context [if Z.land ?x 512 =? 0 then _ else _] => destruct (Z.land x 512 =? 0) eqn:G3 end.
  2: { cbn [uh_om]; right; left; reflexivity. }
  exfalso.
  assert (G3' : (Z.land (Z.shiftr H2 4) 512 =? 0) = true) by exact G3.
  assert (L2 : 2 <= Zlength src) by lia.
  assert (Bk : forall k, 0 <= k < 2 -> 0 <= Znth k src <= 255).
  { intros k Hk. unfold bytes_ok in Hbytes. rewrite Forall_forall in Hbytes.
    pose proof (Hbytes (Znth k src)) as X. replace Byte.max_unsigned with 255 in X by reflexivity.
    apply X, Znth_In; lia. }
  assert (EH : H2 = Znth 0 src + 256 * (Znth 1 src + 256 * 0)).
  { unfold H2. rewrite (sublist_split 0 1 2 src), (sublist_one 0 1 src), (sublist_one 1 2 src) by lia.
    reflexivity. }
  rewrite EH, thh_fdict in G3' by (apply Bk; lia).
  apply Z.eqb_eq in G3'. exact (FD G3').
Qed.

Lemma ua_pass src pos inp aout flush m :
  ctx_ok src pos inp -> Kc 5 src pos inp aout m -> mwf3 m -> m_leave m = 0 -> ua_fd src (m_s m) ->
  ua_fd src (m_s (uh_om (stepf2 flush lenfix_list distfix_list m))).
Proof.
  intros Hc K Hw Hl (H0 & HS).
  split; [rewrite uh_stepf2; exact H0|].
  intros FD. specialize (HS FD).
  change (ua_S (m_mode (uh_om (stepf2 flush lenfix_list distfix_list m)))).
  assert (HS' : ua_S (m_mode m)) by exact HS. clear HS.
  destruct HS' as [Hmd|[Hmd|[Hmd|[Hmd|Hmd]]]].
  - exact (ua_head_mode src pos inp aout flush m Hc K Hw Hl Hmd FD).
  - unfold stepf2, step2. rewrite Hmd. cbn -[c_DICTID].
    unfold c_DICTID. destruct (m_leave (needbits 32 m) =? 1).
    + cbn [uh_om]. right; left. unfold m_mode. rewrite uh_needbits_s. exact Hmd.
    + unfold c_DICT.
      replace (i_havedict (m_s (set_mode _ DICT))) with 0 by (cbn; rewrite uh_needbits_s; auto).
      cbn [Z.eqb uh_om]. right; right; left; reflexivity.
  - unfold stepf2, step2. rewrite Hmd. cbn -[c_DICT].
    unfold c_DICT. rewrite H0. cbn [Z.eqb uh_om]. right; right; left.
    unfold m_mode in *. cbn. exact Hmd.
  - unfold stepf2, step2. rewrite Hmd. cbn -[c_BAD].
    unfold c_BAD. cbn [uh_om]. right; right; right; left.
    unfold m_mode in *. cbn. exact Hmd.
  - unfold stepf2, step2. rewrite Hmd. cbn. right; right; right; right. exact Hmd.
Qed.

Lemma ua_loop : forall src pos inp aout flush m o,
  ctx_ok src pos inp -> loop2 flush lenfix_list distfix_list m o ->
  Kc 5 src pos inp aout m -> mwf3 m -> m_leave m = 0 -> ua_fd src (m_s m) ->
  ua_fd src (m_s (uh_om o)).
Proof.
  intros src pos inp aout flush m o C LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K W L0 F.
  - pose proof (ua_pass src pos inp aout flush m C K W L0 F) as P. rewrite E in P. exact P.
  - pose proof (ua_pass src pos inp aout flush m C K W L0 F) as P. rewrite E in P. exact P.
  - pose proof (ua_pass src pos inp aout flush m C K W L0 F) as P. rewrite E in P. cbn [uh_om] in P.
    pose proof (ikc_kc_all 5 src pos inp aout flush m C K W L0 I) as Q. rewrite E in Q. destruct Q as [K' _].
    pose proof (Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 flush m W L0) as W'. rewrite E in W'.
    assert (L': m_leave m' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ W')); lia).
    apply IH; auto.
Qed.

Lemma ua_fdict : ua_fd_stmt.
Proof.
  intros w src pos final indict z L strmp flush ib inp o ain aout r z' st' ow
    EW INV LV ZF SN P0 A0 PA SL BS AO FL NIB EINP FD0 REL.
  destruct REL as [(BD & Er & Ez' & Est & Eow) | (NB & L0 & o0 & res & winp & EL & EO & RUN & SNX & Er & Eow & Ez' & WIN & Est)].
  { exists L. subst st'. split; [reflexivity|]. split; [exact FD0|]. intros RS. rewrite Er in RS. ikc_md. }
  inversion EL; subst L0. clear EL. inversion EO; subst o0. clear EO.
  eexists. split; [exact Est|]. cbn [l_s].
  assert (CI: call_in_ok src pos ain ib inp) by (right; split; auto).
  destruct (cl_in_ok src pos ain ib inp P0 A0 PA BS CI) as (C & _ & _).
  destruct RUN as (ot & LP & RES).
  change (m_init (set_zf_call z (in_ptr ib 0) ain (ob_ptr (Some o)) aout) L inp)
    with (cl_m0 z L ib (Some o) ain aout inp) in LP.
  destruct (cl_init w src pos final indict z L ib (Some o) ain aout inp INV LV ZF AO C SL)
    as (W0 & K0 & L00 & OW0 & NX0 & SNX0 & SOW0 & OUT0 & MSG0 & RET0 & MD0).
  set (m0 := cl_m0 z L ib (Some o) ain aout inp) in *.
  assert (WR: wrap_of w = 5) by (subst w; reflexivity).
  rewrite WR in K0.
  assert (F0: ua_fd src (m_s m0)).
  { destruct FD0 as (H0 & HS). unfold m0, cl_m0, m_init. cbv zeta. cbn [m_s].
    destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) eqn:ET.
    - apply Z.eqb_eq in ET. split; [exact H0|]. intros FD. exfalso.
      destruct (HS FD) as [X|[X|[X|[X|X]]]]; rewrite ET in X; ikc_md.
    - split; [exact H0 | exact HS]. }
  pose proof (ua_loop src pos inp aout flush m0 ot C LP K0 W0 L00 F0) as FE.
  pose proof (rn_loop Zlib.proof.harness.uncompress_any.UAStepMwf.ua_stepf2_mwf3 ikc_kc_all th_nodict
                5 src pos inp aout flush _ ot C LP K0 W0 L00 (fun _ => OW0)) as LR.
  destruct ot as [mE | r' mE]; cbn [uh_om] in FE.
  - (* inf_leave *)
    destruct LR as (KE & WE & LE & DE).
    destruct RES as [LO WF | ].
    + subst r. cbn [r_m r_ret m_s set_mode upd_s set_m_s restore set_m_sow set_m_snx].
      destruct FE as (H0 & HS).
      split; [split; [cbn; exact H0 | intros _; cbn; right; right; right; right; reflexivity]|].
      intros RS; cbn in RS; ikc_md.
    + destruct FE as (H0 & HS).
      destruct (ikc_lf flush mE) as (G1 & _).
      split; [split; [rewrite uh_leave_fin; exact H0 | intros FD; rewrite G1; exact (HS FD)]|].
      intros RS FD. destruct (rn_leave_fin flush mE) as (R1 & _). rewrite Er, R1 in RS.
      unfold rn_bufret in RS. cbv zeta in RS.
      assert (D: m_mode mE = DONE).
      { destruct (andb _ (m_ret mE =? Z_OK)) eqn:C1 in RS; [ikc_md|].
        destruct (Z.eq_dec (m_mode mE) DONE) as [D|D]; [exact D|].
        destruct (Z.eq_dec (m_mode mE) BAD) as [B|B].
        - rewrite (proj2 (kc_retx _ _ _ _ _ _ KE LE) B) in RS. ikc_md.
        - rewrite (kc_ret _ _ _ _ _ _ KE B D) in RS. ikc_md. }
      destruct (HS FD) as [X|[X|[X|[X|X]]]]; change (i_mode (m_s mE)) with (m_mode mE) in X; rewrite D in X; ikc_md.
  - (* Z_NEED_DICT / Z_MEM_ERROR *)
    subst res. cbn [r_ret r_m] in Er |- *. subst r'.
    split; [exact FE|].
    destruct LR as (_ & _ & [(RR & _) | (RR & _)]); intros RS; rewrite RR in RS; ikc_md.
Qed.

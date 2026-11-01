(* Law rt_session, sessions with a dictionary and the zlib wrapper: inflate() calls before Z_NEED_DICT, on the
   model (Model2.run2), the input arriving in pieces of any size.

   After inflateInit2(strm, wb) (9 <= wb <= 15: the zlib wrapper, state->wbits = wb) the stream starts with the
   6 bytes [hdr] = [CMF; FLG] ++ DICTID (FLG with FDICT, DICTID the Adler-32 of the dictionary, big-endian).
   inflate() reads them in mode HEAD (NEEDBITS(16): CMF and FLG) and DICTID (NEEDBITS(32)); when the input runs
   out first, it leaves with the bytes read kept in state->hold / state->bits, nothing written, and returns
   Z_OK or Z_BUF_ERROR; the call that completes DICTID enters DICT and returns Z_NEED_DICT (havedict 0) having
   consumed exactly the rest of the 6 bytes.  [szd_hst wb hdr k]: the state after the first k < 6 bytes.
   DWIFirst.dwi_first is the case of a call offered all 6 bytes at once from k = 0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require compcert.lib.Integers.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictFirst.
Require Import Zlib.proof.harness.dictionary_w.DWIFirst.
Import ListNotations.
Local Open Scope Z_scope.

(* the little-endian value of bytes (the bit buffer hold after NEEDBITS) *)
Definition szd_le (l: list Z) : Z := fold_right (fun b a => b + 256 * a) 0 l.

Definition szd_byte (b: Z) : Prop := 0 <= b < 256.

Lemma szd_le_app1 P b : szd_le (P ++ [b]) = szd_le P + b * 256 ^ Zlength P.
Proof.
  induction P as [|x P IH]; cbn [app szd_le fold_right].
  - rewrite Zlength_nil. cbn. lia.
  - fold (szd_le (P ++ [b])) (szd_le P). rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg P); lia).
    lia.
Qed.

Lemma szd_le_bound P : Forall szd_byte P -> 0 <= szd_le P < 256 ^ Zlength P.
Proof.
  induction 1 as [|x P Hx _ IH]; cbn [szd_le fold_right].
  - rewrite Zlength_nil. cbn. lia.
  - fold (szd_le P). rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg P); lia).
    unfold szd_byte in Hx. lia.
Qed.

(* NEEDBITS(8 (|P| + d)) on a bit buffer holding the bytes P: it pulls the next a = min(d, have) bytes and
   leaves when that is fewer than d *)
Definition szd_nbr (d: Z) (m: mst) (P: list Z) : mst :=
  let a := Z.min d (m_have m) in
  let m' := set_m_bits (set_m_hold (set_m_nx m (m_nx m + a))
                          (szd_le (P ++ sublist (m_nx m) (m_nx m + a) (m_inp m)))) (8 * (Zlength P + a)) in
  if a <? d then set_leave m' else m'.

Lemma szd_nb (d: nat) : forall fuel m P,
  (d <= fuel)%nat -> m_bits m = 8 * Zlength P -> m_hold m = szd_le P -> Forall szd_byte P ->
  Zlength P + Z.of_nat d <= 4 -> 0 <= m_nx m <= Zlength (m_inp m) -> Forall szd_byte (m_inp m) ->
  needbits_f fuel (8 * (Zlength P + Z.of_nat d)) m = szd_nbr (Z.of_nat d) m P.
Proof.
  induction d as [|d IH]; intros fuel m P Hf Hb Hh BP HL Hn BI.
  - assert (E: szd_nbr (Z.of_nat 0) m P = m).
    { unfold szd_nbr, m_have. change (Z.of_nat 0) with 0.
      replace (Z.min 0 (Zlength (m_inp m) - m_nx m)) with 0 by lia.
      rewrite Z.add_0_r, sublist_nil, app_nil_r, Z.ltb_irrefl.
      destruct m; cbn in *; subst; rewrite ?Z.add_0_r; reflexivity. }
    rewrite E. destruct fuel; [reflexivity|]. cbn [needbits_f].
    rewrite Hb. replace (8 * (Zlength P + Z.of_nat 0)) with (8 * Zlength P) by lia.
    rewrite Z.ltb_irrefl. reflexivity.
  - destruct fuel as [|fuel]; [lia|]. cbn [needbits_f].
    pose proof (Zlength_nonneg P) as LP0. assert (Hd: Z.of_nat (S d) = Z.of_nat d + 1) by lia.
    replace (m_bits m <? 8 * (Zlength P + Z.of_nat (S d))) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold szd_nbr at 1.
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + rewrite H0. replace (Z.min (Z.of_nat (S d)) 0) with 0 by lia.
      replace (0 <? Z.of_nat (S d)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Z.add_0_r, sublist_nil, app_nil_r, Z.add_0_r.
      destruct m; cbn in *; subst; rewrite ?Z.add_0_r; reflexivity.
    + assert (Hn': m_nx m < Zlength (m_inp m)) by (unfold m_have in H0; lia).
      set (b := Znth (m_nx m) (m_inp m)).
      assert (Bb: szd_byte b) by (unfold b; apply Forall_Znth; [lia | exact BI]).
      pose proof (szd_le_bound P BP) as LB.
      assert (P256: 256 ^ Zlength P <= 256 ^ 3) by (apply Z.pow_le_mono_r; lia).
      assert (Ehold: m_hold (pull m) = szd_le (P ++ [b])).
      { unfold pull. cbn [m_hold set_m_bits set_m_hold set_m_nx]. rewrite szd_le_app1, Hh, Hb.
        fold b. unfold u64. rewrite Z.mod_small.
        - f_equal. f_equal. rewrite Z.pow_mul_r by (pose proof (Zlength_nonneg P); lia). reflexivity.
        - change (2 ^ 64) with 18446744073709551616. unfold szd_byte in Bb.
          rewrite Z.pow_mul_r by (pose proof (Zlength_nonneg P); lia). change (2 ^ 8) with 256. change (256 ^ 3) with 16777216 in P256. nia. }
      assert (Ebits: m_bits (pull m) = 8 * Zlength (P ++ [b])).
      { unfold pull. cbn [m_bits set_m_bits set_m_hold set_m_nx]. rewrite Hb, Zlength_app, Zlength_cons, Zlength_nil.
        unfold u32. rewrite Z.mod_small; [lia|]. change (2 ^ 32) with 4294967296. lia. }
      assert (BP': Forall szd_byte (P ++ [b])) by (apply Forall_app; split; [exact BP | constructor; [exact Bb | constructor]]).
      replace (8 * (Zlength P + Z.of_nat (S d))) with (8 * (Zlength (P ++ [b]) + Z.of_nat d))
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      rewrite (IH fuel (pull m) (P ++ [b])); try assumption.
      * unfold szd_nbr, m_have. cbn [m_inp m_nx pull set_m_bits set_m_hold set_m_nx].
        unfold m_have in H0.
        set (a := Z.min (Z.of_nat (S d)) (Zlength (m_inp m) - m_nx m)).
        assert (Ha: 1 <= a <= Z.of_nat (S d) /\ a <= Zlength (m_inp m) - m_nx m) by (unfold a; lia).
        replace (Z.min (Z.of_nat d) (Zlength (m_inp m) - (m_nx m + 1))) with (a - 1) by (unfold a; lia).
        replace (a - 1 <? Z.of_nat d) with (a <? Z.of_nat (S d)) by (destruct (Z.ltb_spec (a - 1) (Z.of_nat d)); destruct (Z.ltb_spec a (Z.of_nat (S d))); lia).
        assert (Ea: (P ++ [b]) ++ sublist (m_nx m + 1) (m_nx m + 1 + (a - 1)) (m_inp m) =
                    P ++ sublist (m_nx m) (m_nx m + a) (m_inp m)).
        { rewrite <- app_assoc. f_equal.
          rewrite (sublist_split (m_nx m) (m_nx m + 1) (m_nx m + a)) by lia.
          rewrite sublist_len_1 by lia. fold b. cbn [app]. f_equal. f_equal. lia. }
        rewrite Ea.
        replace (m_nx m + 1 + (a - 1)) with (m_nx m + a) by lia.
        replace (8 * (Zlength (P ++ [b]) + (a - 1))) with (8 * (Zlength P + a))
          by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
        destruct (a <? Z.of_nat (S d)); destruct m; reflexivity.
      * lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * unfold pull. cbn [m_nx m_inp set_m_bits set_m_hold set_m_nx]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass of the switch in HEAD and DICTID, from any position in the input                        *)

(* HEAD after NEEDBITS(16) got CMF and FLG (DWIFirst.dwi_head from any machine) *)
Lemma szd_head_step fl fx dx s h inp ao nx hold bits nin adl msg tin tout wb flg nx' :
  i_mode s = HEAD -> i_wrap s = 5 -> i_wbits s = wb -> i_head s = false -> 9 <= wb <= 15 ->
  RF.zflg_ok wb true flg ->
  needbits 16 (MS s h inp ao nx [] hold bits nin ao Z_OK 0 adl msg tin tout 0 0) =
    MS s h inp ao nx' [] (RF.zcmf wb + flg * 256) 16 nin ao Z_OK 0 adl msg tin tout 0 0 ->
  stepf2 fl fx dx (MS s h inp ao nx [] hold bits nin ao Z_OK 0 adl msg tin tout 0 0) =
  IBrk (MS (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s wb) (2 ^ wb)) 0) 1) DICTID)
           h inp ao nx' [] 0 0 nin ao Z_OK 0 1 msg tin tout 0 0).
Proof.
  intros Hm Hw Hb Hh Hwb Hf NB.
  pose proof (rtz_hdr wb flg Hwb Hf) as (H1 & H2 & H3 & H4 & Hc). cbv zeta in H1, H2, H3, H4.
  unfold stepf2, step2. unfold m_mode. cbn [m_s]. rewrite Hm. change (HEAD =? HEAD) with true. cbv beta iota.
  unfold c_HEAD2. cbn [m_s]. rewrite Hw. change (5 =? 0) with false. cbv beta iota.
  rewrite NB.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  rewrite Hh, Hw. change (0 =? 1) with false. change (Z.land 5 2 =? 0) with true. change (Z.land 5 1 =? 0) with false.
  cbv beta iota.
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits negb andb orb].
  rewrite H1, H2. cbn [negb orb]. rewrite H3, Hb.
  replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (wb <? wb) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (15 <? wb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb negb andb].
  rewrite H4. rewrite dwi_keep_wbits by (first [exact Hb | lia]).
  cbn [m_s m_leave m_hold m_bits set_mode upd_s set_m_s set_m_hold set_m_bits set_m_adler dropbits initbits].
  reflexivity.
Qed.

(* HEAD when NEEDBITS(16) runs out of input *)
Lemma szd_head_leave fl fx dx m :
  i_mode (m_s m) = HEAD -> i_wrap (m_s m) = 5 -> m_leave (needbits 16 m) = 1 ->
  stepf2 fl fx dx m = IBrk (needbits 16 m).
Proof.
  intros Hm Hw L. unfold stepf2, step2. unfold m_mode. rewrite Hm. change (HEAD =? HEAD) with true.
  cbv beta iota. unfold c_HEAD2. rewrite Hw. change (5 =? 0) with false. cbv beta iota zeta.
  rewrite L. reflexivity.
Qed.

(* DICTID after NEEDBITS(32) got the 4 bytes: DICT with havedict 0 returns Z_NEED_DICT *)
Lemma szd_dictid_step fl fx dx s h inp ao nx hold bits nin adl msg tin tout nx' q0 :
  i_mode s = DICTID -> i_havedict s = 0 ->
  needbits 32 (MS s h inp ao nx [] hold bits nin ao Z_OK 0 adl msg tin tout 0 0) =
    MS s h inp ao nx' [] q0 32 nin ao Z_OK 0 adl msg tin tout 0 0 ->
  exists tin', stepf2 fl fx dx (MS s h inp ao nx [] hold bits nin ao Z_OK 0 adl msg tin tout 0 0) =
  IRet Z_NEED_DICT (MS (set_i_bits (set_i_hold (set_i_mode (set_i_check s (swap32 q0)) DICT) 0) 0) h
                       inp ao nx' [] 0 0 nin ao Z_OK 0 (swap32 q0) msg tin' tout nx' 0).
Proof.
  intros Hm Hd NB.
  rewrite rtz_step_dictid by exact Hm. unfold c_DICTID. rewrite NB.
  unfold c_DICT. destruct s; cbn in Hd; subst. eexists. reflexivity.
Qed.

(* DICTID when NEEDBITS(32) runs out of input *)
Lemma szd_dictid_leave fl fx dx m :
  i_mode (m_s m) = DICTID -> m_leave (needbits 32 m) = 1 ->
  stepf2 fl fx dx m = IBrk (needbits 32 m).
Proof.
  intros Hm L. rewrite rtz_step_dictid by exact Hm. unfold c_DICTID. cbv zeta. rewrite L. reflexivity.
Qed.

(* inf_leave with no window and nothing written: no window update, the bit buffer saved, the counters kept;
   Z_OK or Z_BUF_ERROR *)
Lemma szd_leave flush s h inp ao nx hold bits nin adl msg tin tout res :
  i_wsize s = 0 -> i_total s = 0 -> 0 <= tout < 2 ^ 64 ->
  inf_leave flush (MS s h inp ao nx [] hold bits nin ao Z_OK 1 adl msg tin tout 0 0) res ->
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ m_snx (r_m res) = nx /\ m_ow (r_m res) = [] /\
  m_sow (r_m res) = 0 /\ m_aout (r_m res) = ao /\ m_tout (r_m res) = tout /\
  m_s (r_m res) = set_i_bits (set_i_hold s hold) bits.
Proof.
  intros Ws Tot Hto IL.
  assert (LO: leave_ok flush (MS s h inp ao nx [] hold bits nin ao Z_OK 1 adl msg tin tout 0 0) = false).
  { unfold leave_ok, m_left. cbn [m_s m_out m_aout m_ow]. rewrite Ws, Zlength_nil, Z.sub_0_r, !Z.eqb_refl.
    reflexivity. }
  inversion IL as [LO' _ | E]; [congruence|]. clear IL.
  unfold leave_fin. rewrite LO. cbv zeta. cbn - [u32 u64].
  replace (ao - (ao - 0)) with 0 by lia. change (u32 0) with 0. rewrite andb_false_r.
  cbn [m_ret m_snx m_ow m_sow m_aout m_tout m_s restore upd_s set_m_tout set_m_tin set_m_s set_m_sow set_m_snx].
  rewrite !Z.add_0_r. replace (u64 tout) with tout by (unfold u64; rewrite Z.mod_small; lia).
  repeat split.
  - match goal with |- context [if ?c then Z_BUF_ERROR else Z_OK] => destruct c end; cbn; auto.
  - destruct s; cbn in *; subst; reflexivity.
Qed.

(* NEEDBITS(8 n) with the bytes P (|P| < n <= 4) in the bit buffer, from any position of the input *)
Lemma szd_needbits n s h inp ao nx P nin out ret adl msg tin tout snx sow :
  Zlength P < n <= 4 -> Forall szd_byte P -> Forall szd_byte inp -> 0 <= nx <= Zlength inp ->
  needbits (8 * n) (MS s h inp ao nx [] (szd_le P) (8 * Zlength P) nin out ret 0 adl msg tin tout snx sow) =
  let a := Z.min (n - Zlength P) (Zlength inp - nx) in
  MS s h inp ao (nx + a) [] (szd_le (P ++ sublist nx (nx + a) inp)) (8 * (Zlength P + a)) nin out ret
     (if a <? n - Zlength P then 1 else 0) adl msg tin tout snx sow.
Proof.
  intros Hn BP BI Hx. unfold needbits.
  replace (8 * n) with (8 * (Zlength P + Z.of_nat (Z.to_nat (n - Zlength P)))) by lia.
  rewrite szd_nb; cbn [m_bits m_hold m_nx m_inp]; try (first [assumption | reflexivity | lia]).
  rewrite Z2Nat.id by lia. unfold szd_nbr, m_have. cbn [m_nx m_inp].
  - destruct (_ <? _); reflexivity.
  - pose proof (Zlength_nonneg P). lia.
Qed.

(* the calls from DICTID with the first |P| < 4 bytes of the dictionary id idb in the bit buffer: they read
   the next bytes of idb; with all four, DICT returns Z_NEED_DICT; otherwise inf_leave *)
Lemma szd_dictid_run flush s h inp ao nx P idb nin adl msg tin tout o res :
  i_mode s = DICTID -> i_havedict s = 0 -> i_wsize s = 0 -> i_total s = 0 -> 0 <= tout < 2 ^ 64 ->
  Zlength idb = 4 -> Forall szd_byte idb -> Zlength P < 4 -> P = sublist 0 (Zlength P) idb ->
  Forall szd_byte inp -> 0 <= nx <= Zlength inp ->
  let a := Z.min (4 - Zlength P) (Zlength inp - nx) in
  sublist nx (nx + a) inp = sublist (Zlength P) (Zlength P + a) idb ->
  loop2 flush lenfix_list distfix_list
    (MS s h inp ao nx [] (szd_le P) (8 * Zlength P) nin ao Z_OK 0 adl msg tin tout 0 0) o ->
  match o with IRet r m => res = Res r m None | IBrk m => inf_leave flush m res end ->
  (Zlength P + (Zlength inp - nx) < 4 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\
   m_snx (r_m res) = Zlength inp /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = ao /\
   m_tout (r_m res) = tout /\
   m_s (r_m res) = set_i_bits (set_i_hold s (szd_le (P ++ sublist nx (Zlength inp) inp)))
                              (8 * (Zlength P + (Zlength inp - nx)))) \/
  (4 <= Zlength P + (Zlength inp - nx) /\ r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = nx + (4 - Zlength P) /\
   m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = ao /\ m_tout (r_m res) = tout /\
   m_s (r_m res) = set_i_bits (set_i_hold (set_i_mode (set_i_check s (swap32 (szd_le idb))) DICT) 0) 0).
Proof.
  intros Hm Hd Ws Tot Hto Li Bi Lp EP BI Hx a Sa LP RS.
  assert (BP: Forall szd_byte P) by (rewrite EP; apply Forall_sublist; exact Bi).
  pose proof (Zlength_nonneg P) as P0.
  pose proof (szd_needbits 4 s h inp ao nx P nin ao Z_OK adl msg tin tout 0 0 ltac:(lia) BP BI Hx) as NB.
  change (8 * 4) with 32 in NB. cbv zeta in NB. fold a in NB.
  set (m0 := MS s h inp ao nx [] (szd_le P) (8 * Zlength P) nin ao Z_OK 0 adl msg tin tout 0 0) in *.
  destruct (Z.ltb_spec a (4 - Zlength P)) as [Lt|Ge].
  - (* the input runs out: inf_leave *)
    left.
    assert (Ea: a = Zlength inp - nx) by (unfold a in *; lia).
    assert (ST: stepf2 flush lenfix_list distfix_list m0 = IBrk (needbits 32 m0))
      by (apply szd_dictid_leave; [exact Hm | rewrite NB; reflexivity]).
    inversion LP as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 _]; subst; rewrite ST in S1; try discriminate.
    + injection S1 as <-. rewrite NB in RS.
      rewrite Ea in RS. replace (nx + (Zlength inp - nx)) with (Zlength inp) in RS by lia.
      destruct (szd_leave flush s h inp ao (Zlength inp) _ _ nin adl msg tin tout res Ws Tot Hto RS)
        as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      split; [lia|]. auto 8.
    + injection S1 as <-. rewrite NB in L1. cbn in L1. contradiction.
  - (* all four bytes: Z_NEED_DICT *)
    right.
    assert (Ea: a = 4 - Zlength P) by (unfold a in *; lia).
    assert (EI: P ++ sublist nx (nx + a) inp = idb).
    { rewrite Sa, Ea. rewrite EP at 1. rewrite <- sublist_split by lia.
      replace (Zlength P + (4 - Zlength P)) with 4 by lia. rewrite <- Li. apply sublist_same; lia. }
    replace (if a <? 4 - Zlength P then 1 else 0) with 0 in NB by (destruct (Z.ltb_spec a (4 - Zlength P)); lia).
    rewrite EI in NB. replace (8 * (Zlength P + a)) with 32 in NB by lia.
    destruct (szd_dictid_step flush lenfix_list distfix_list s h inp ao nx _ _ nin adl msg tin tout (nx + a)
                (szd_le idb) Hm Hd NB) as (tin' & ST).
    fold m0 in ST.
    inversion LP as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 _]; subst; rewrite ST in S1; try discriminate.
    injection S1 as <- <-. subst res. cbn [r_ret r_m m_snx m_ow m_sow m_aout m_tout m_s].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. auto 8.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The states before Z_NEED_DICT and a call from them                                              *)

(* the 6 bytes: CMF, FLG, the dictionary id (big-endian) *)
Definition szd_hdr (wb flg id: Z) : list Z := [RF.zcmf wb; flg] ++ be_bytes id 4.

(* after HEAD: DICTID, the window bits and the check value set *)
Definition szd_s1g (s0: istate) (wb: Z) : istate :=
  set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s0 wb) (2 ^ wb)) 0) 1) DICTID.
Definition szd_s1 (wb: Z) : istate := szd_s1g (init_s 5 wb) wb.

(* the state after the first k < 6 bytes: HEAD or DICTID, the bytes of the field being read in the bit buffer;
   [szd_hstg] over any states s0 (HEAD) and s1 (DICTID), [szd_hst] after inflateInit2 *)
Definition szd_hstg (s0 s1: istate) (hdr: list Z) (k: Z) : istate :=
  if k <? 2 then set_i_bits (set_i_hold s0 (szd_le (sublist 0 k hdr))) (8 * k)
  else set_i_bits (set_i_hold s1 (szd_le (sublist 2 k hdr))) (8 * (k - 2)).
Definition szd_hst (wb: Z) (hdr: list Z) (k: Z) : istate := szd_hstg (init_s 5 wb) (szd_s1 wb) hdr k.

(* the fields the calls depend on, of the state of inflateInit2 and of the state after HEAD *)
Definition szd_s0ok (wb: Z) (s0: istate) : Prop :=
  i_mode s0 = HEAD /\ i_wrap s0 = 5 /\ i_wbits s0 = wb /\ i_head s0 = false /\ i_havedict s0 = 0 /\
  i_last s0 = 0 /\ i_total s0 = 0 /\ i_wsize s0 = 0 /\ i_whave s0 = 0 /\ i_wnext s0 = 0 /\ i_win s0 = false /\
  i_wdata s0 = [].
Definition szd_s1ok (wb: Z) (s1: istate) : Prop :=
  i_mode s1 = DICTID /\ i_wrap s1 = 5 /\ i_wbits s1 = wb /\ i_head s1 = false /\ i_havedict s1 = 0 /\
  i_last s1 = 0 /\ i_total s1 = 0 /\ i_wsize s1 = 0 /\ i_whave s1 = 0 /\ i_wnext s1 = 0 /\ i_win s1 = false /\
  i_wdata s1 = [] /\ i_flags s1 = 0.

Lemma szd_minit z L inp : i_mode (l_s L) <> Zlib.proof.inflate.Model.TYPE ->
  m_init z L inp = MS (l_s L) (l_h L) inp (zf_ao z) 0 [] (i_hold (l_s L)) (i_bits (l_s L)) (Zlength inp)
                      (zf_ao z) Z_OK 0 (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0.
Proof.
  intros H. unfold m_init. cbv zeta. replace (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) with false
    by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
Qed.

Lemma szd_hb2 s h1 b1 h2 b2 : set_i_bits (set_i_hold (set_i_bits (set_i_hold s h1) b1) h2) b2 =
                              set_i_bits (set_i_hold s h2) b2.
Proof. destruct s; reflexivity. Qed.

Lemma szd_init_fields wb : 9 <= wb <= 15 -> szd_s0ok wb (init_s 5 wb).
Proof.
  intros Hwb. unfold szd_s0ok, init_s, reset2_s, reset2_wrap. replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  repeat split.
Qed.

Lemma szd_hb0 s : i_hold s = 0 -> i_bits s = 0 -> set_i_bits (set_i_hold s 0) 0 = s.
Proof. destruct s; cbn; intros; subst; reflexivity. Qed.

(* nothing read yet: the state of inflateInit2 *)
Lemma szd_init_hst wb hdr : 9 <= wb <= 15 -> szd_hst wb hdr 0 = init_s 5 wb.
Proof.
  intros Hwb. unfold szd_hst, szd_hstg. replace (0 <? 2) with true by reflexivity.
  rewrite sublist_nil. change (szd_le []) with 0. change (8 * 0) with 0.
  apply szd_hb0; unfold init_s, reset2_s, reset2_wrap; replace (wb =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
    reflexivity.
Qed.

Lemma szd_hdr_facts wb flg id : 9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 ->
  let hdr := szd_hdr wb flg id in
  Zlength hdr = 6 /\ Forall szd_byte hdr /\ sublist 2 6 hdr = be_bytes id 4 /\
  szd_le (sublist 0 2 hdr) = RF.zcmf wb + flg * 256 /\ swap32 (szd_le (be_bytes id 4)) = id.
Proof.
  intros Hwb Hf Hid hdr.
  pose proof (rtz_hdr wb flg Hwb Hf) as (_ & _ & _ & _ & Hc). pose proof Hf as (Hf8 & _).
  assert (E : be_bytes id 4 = [Z.shiftr id (8 * 3) mod 256; Z.shiftr id (8 * 2) mod 256; Z.shiftr id (8 * 1) mod 256;
                               Z.shiftr id (8 * 0) mod 256]) by reflexivity.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 3)) 256 ltac:(lia)) as B0.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 2)) 256 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 1)) 256 ltac:(lia)) as B2.
  pose proof (Z.mod_pos_bound (Z.shiftr id (8 * 0)) 256 ltac:(lia)) as B3.
  pose proof (rtz_swap (Z.shiftr id (8 * 3) mod 256) (Z.shiftr id (8 * 2) mod 256) (Z.shiftr id (8 * 1) mod 256)
                (Z.shiftr id (8 * 0) mod 256) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SW.
  rewrite (rtz_be id Hid) in SW.
  unfold hdr, szd_hdr. rewrite E.
  set (i0 := Z.shiftr id (8 * 3) mod 256) in *. set (i1 := Z.shiftr id (8 * 2) mod 256) in *.
  set (i2 := Z.shiftr id (8 * 1) mod 256) in *. set (i3 := Z.shiftr id (8 * 0) mod 256) in *.
  clearbody i0 i1 i2 i3.
  split; [reflexivity|].
  split; [repeat constructor; unfold szd_byte; lia|].
  split; [reflexivity|].
  split; [cbn; lia|].
  exact SW.
Qed.

(* sublists of sublists *)
Lemma szd_subsub (l: list Z) i j a b : 0 <= a <= b -> 0 <= i -> i + b <= j <= Zlength l ->
  sublist a b (sublist i j l) = sublist (i + a) (i + b) l.
Proof. intros. rewrite sublist_sublist by lia. f_equal; lia. Qed.

Lemma szd_app_sub (l: list Z) i j k : 0 <= i <= j -> j <= k <= Zlength l ->
  sublist i j l ++ sublist j k l = sublist i k l.
Proof. intros. rewrite <- sublist_split by lia. reflexivity. Qed.

Lemma szd_s1_eq s h1 b1 h2 b2 wb :
  set_i_bits (set_i_hold (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits
    (set_i_bits (set_i_hold s h1) b1) wb) (2 ^ wb)) 0) 1) DICTID) h2) b2 =
  set_i_bits (set_i_hold (set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits s wb) (2 ^ wb)) 0) 1)
    DICTID) h2) b2.
Proof. destruct s; reflexivity. Qed.

(* the state of Z_NEED_DICT from a DICTID state *)
Lemma szd_nd_of wb id S :
  i_wrap S = 5 -> i_head S = false -> i_last S = 0 -> i_havedict S = 0 -> i_total S = 0 -> i_wsize S = 0 ->
  i_whave S = 0 -> i_wnext S = 0 -> i_win S = false -> i_wdata S = [] -> i_wbits S = wb -> i_flags S = 0 ->
  dw_nd wb id (set_i_bits (set_i_hold (set_i_mode (set_i_check S id) DICT) 0) 0).
Proof. intros. unfold dw_nd. destruct S; cbn in *. repeat split; assumption. Qed.

(* the fields of a state built by the setters, without unfolding init_s (whose unfolding makes the kernel's
   conversion checks slow) *)
Ltac szd_fields :=
  cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
       i_win i_wdata i_hold i_bits set_i_mode set_i_check set_i_flags set_i_dmax set_i_wbits set_i_bits
       set_i_hold szd_s1].

Lemma szd_s1_ok wb s0 : szd_s0ok wb s0 -> szd_s1ok wb (szd_s1g s0 wb).
Proof.
  intros (Fm & Fw & Fb & Fh & Fd & Fl & Ft & Fws & Fwh & Fwn & Fwi & Fwd).
  unfold szd_s1ok, szd_s1g. szd_fields. repeat split; auto.
Qed.

Lemma szd_hcall_lo flush wb flg id k z L inp res s0 :
  9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 -> zf_ok z ->
  0 <= k < 6 -> k < 2 -> szd_s0ok wb s0 -> l_s L = szd_hstg s0 (szd_s1g s0 wb) (szd_hdr wb flg id) k -> Forall szd_byte inp ->
  sublist 0 (Z.min (Zlength inp) (6 - k)) inp =
    sublist k (k + Z.min (Zlength inp) (6 - k)) (szd_hdr wb flg id) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  (k + Zlength inp < 6 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ m_snx (r_m res) = Zlength inp /\
   m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   m_s (r_m res) = szd_hstg s0 (szd_s1g s0 wb) (szd_hdr wb flg id) (k + Zlength inp)) \/
  (6 <= k + Zlength inp /\ r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 - k /\ m_ow (r_m res) = [] /\
   m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   dw_nd wb id (m_s (r_m res))).
Proof.
  intros Hwb Hf Hid Hz Hk K2 F0 Hs BI Hpre (o & LP & RS).
  destruct (szd_hdr_facts wb flg id Hwb Hf Hid) as (HL & HB & H26 & H02 & SWP).
  destruct F0 as (Fm & Fw & Fb & Fh & Fd & Fl & Ft & Fws & Fwh & Fwn & Fwi & Fwd).
  set (hdr := szd_hdr wb flg id) in *.
  set (idb := be_bytes id 4) in *.
  destruct Hz as (_ & _ & _ & Zto & _).
  assert (Hto: 0 <= zf_tout z < 2 ^ 64)
    by (change Integers.Int64.max_unsigned with 18446744073709551615 in Zto; change (2 ^ 64) with 18446744073709551616; lia).
  pose proof (Zlength_nonneg inp) as I0.
  assert (Li: Zlength idb = 4) by (rewrite <- H26, Zlength_sublist; lia).
  assert (Bi: Forall szd_byte idb) by (rewrite <- H26; apply Forall_sublist; exact HB).
  set (a := Z.min (Zlength inp) (6 - k)) in *.
  (* the bytes the call reads are those of hdr *)
  assert (PRE: forall i j, 0 <= i <= j /\ j <= a -> sublist i j inp = sublist (k + i) (k + j) hdr).
  { intros i j Hij.
    assert (E1: sublist i j inp = sublist i j (sublist 0 a inp))
      by (rewrite szd_subsub by (unfold a in *; lia); f_equal; lia).
    rewrite E1, Hpre, szd_subsub by (unfold a in *; lia). reflexivity. }
  assert (Ha: a = Z.min (Zlength inp) (6 - k)) by reflexivity. clearbody a hdr idb.
  (* HEAD *)
  set (P := sublist 0 k hdr).
  assert (LPk: Zlength P = k) by (unfold P; rewrite Zlength_sublist; lia).
  assert (BP: Forall szd_byte P) by (apply Forall_sublist; exact HB).
  set (sA := set_i_bits (set_i_hold (s0) (szd_le P)) (8 * Zlength P)).
  assert (Es: l_s L = sA).
  { rewrite Hs. unfold szd_hstg. replace (k <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold sA. rewrite LPk. reflexivity. }
  assert (SA: i_mode sA = HEAD /\ i_wrap sA = 5 /\ i_wbits sA = wb /\ i_head sA = false /\
              i_hold sA = szd_le P /\ i_bits sA = 8 * Zlength P)
    by (unfold sA; cbn [i_mode i_wrap i_wbits i_head i_hold i_bits set_i_bits set_i_hold]; repeat split; auto).
  destruct SA as (Am & Aw & Ab & Ah & Aho & Abi).
  rewrite szd_minit in LP by (rewrite Es, Am; discriminate).
  rewrite Es, Aho, Abi in LP.
  set (m0 := MS sA (l_h L) inp (zf_ao z) 0 [] (szd_le P) (8 * Zlength P) (Zlength inp) (zf_ao z) Z_OK 0
                (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) 0 0) in LP.
  pose proof (szd_needbits 2 sA (l_h L) inp (zf_ao z) 0 P (Zlength inp) (zf_ao z) Z_OK (zf_adler z) (zf_msg z)
                (zf_tin z) (zf_tout z) 0 0 ltac:(lia) BP BI ltac:(lia)) as NB.
  change (8 * 2) with 16 in NB. cbv zeta in NB. fold m0 in NB.
  set (a2 := Z.min (2 - Zlength P) (Zlength inp - 0)) in NB.
  assert (PA: P ++ sublist 0 (0 + a2) inp = sublist 0 (k + a2) hdr).
  { rewrite Z.add_0_l. rewrite (PRE 0 a2) by (unfold a2 in *; lia). rewrite Z.add_0_r.
    unfold P. apply szd_app_sub; unfold a2 in *; lia. }
  rewrite PA in NB.
  destruct (Z.ltb_spec a2 (2 - Zlength P)) as [Lt|Ge].
  + (* the input runs out in HEAD *)
    left.
    assert (Ea: a2 = Zlength inp) by (unfold a2 in *; lia).
    assert (ST: stepf2 flush lenfix_list distfix_list m0 = IBrk (needbits 16 m0))
      by (apply szd_head_leave; [exact Am | exact Aw | rewrite NB; reflexivity]).
    inversion LP as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 _]; subst m o; rewrite ST in S1; try discriminate.
    * injection S1 as <-. rewrite NB in RS.
      destruct (szd_leave flush sA (l_h L) inp (zf_ao z) _ _ _ (Zlength inp) (zf_adler z) (zf_msg z) (zf_tin z)
                  (zf_tout z) res ltac:(unfold sA; szd_fields; exact Fws) ltac:(unfold sA; szd_fields; exact Ft) Hto RS)
        as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      split; [lia|]. split; [exact R1|]. split; [rewrite R2, Ea; lia|].
      do 4 (split; [assumption|]).
      rewrite R7. unfold sA. rewrite szd_hb2. unfold szd_hstg.
      replace (k + Zlength inp <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Ea, LPk. reflexivity.
    * injection S1 as <-. rewrite NB in L1. cbn in L1. contradiction.
  + (* CMF and FLG read: DICTID *)
    assert (Ea: a2 = 2 - k) by (unfold a2 in *; lia).
    replace (if a2 <? 2 - Zlength P then 1 else 0) with 0 in NB
      by (destruct (Z.ltb_spec a2 (2 - Zlength P)); lia).
    replace (k + a2) with 2 in NB by lia. rewrite H02 in NB.
    replace (8 * (Zlength P + a2)) with 16 in NB by lia.
    pose proof (szd_head_step flush lenfix_list distfix_list sA (l_h L) inp (zf_ao z) 0 (szd_le P) (8 * Zlength P)
                  (Zlength inp) (zf_adler z) (zf_msg z) (zf_tin z) (zf_tout z) wb flg (0 + a2)
                  Am Aw Ab Ah Hwb Hf NB) as ST.
    fold m0 in ST.
    inversion LP as [m r m' S1 | m m' S1 L1 | m m' o' S1 L1 LP2]; subst m o; rewrite ST in S1; try discriminate.
    { injection S1 as <-. cbn in L1. discriminate. }
    injection S1 as <-. clear L1.
    set (s1 := set_i_mode (set_i_check (set_i_flags (set_i_dmax (set_i_wbits sA wb) (2 ^ wb)) 0) 1) DICTID) in LP2.
    assert (S1F: i_mode s1 = DICTID /\ i_havedict s1 = 0 /\ i_wsize s1 = 0 /\ i_total s1 = 0)
      by (unfold s1, sA; szd_fields; repeat split; auto).
    destruct S1F as (S1m & S1d & S1w & S1t).
    assert (SUB: sublist (0 + a2) (0 + a2 + Z.min (4 - Zlength (@nil Z)) (Zlength inp - (0 + a2))) inp =
                 sublist (Zlength (@nil Z)) (Zlength (@nil Z) + Z.min (4 - Zlength (@nil Z)) (Zlength inp - (0 + a2))) idb).
    { rewrite Zlength_nil, !Z.add_0_l. rewrite Ea.
      rewrite (PRE (2 - k)) by (lia).
      rewrite <- H26. rewrite szd_subsub by lia. f_equal; lia. }
    destruct (szd_dictid_run flush s1 (l_h L) inp (zf_ao z) (0 + a2) [] idb (Zlength inp) 1 (zf_msg z) (zf_tin z)
                (zf_tout z) o' res S1m S1d S1w S1t Hto Li Bi ltac:(rewrite Zlength_nil; lia)
                ltac:(rewrite Zlength_nil; reflexivity) BI ltac:(lia) SUB LP2 RS)
      as [(R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7) | (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7)].
    * left. rewrite Zlength_nil in R0. split; [lia|]. do 6 (split; [assumption|]).
      rewrite R7. unfold s1, sA. rewrite szd_s1_eq. unfold szd_hstg.
      replace (k + Zlength inp <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
      unfold szd_s1g. f_equal; [f_equal|].
      -- rewrite app_nil_l, Ea, (PRE (2 - k)) by (lia). f_equal. f_equal; lia.
      -- rewrite Zlength_nil, Ea. lia.
    * right. rewrite Zlength_nil in R0, R2. split; [lia|]. split; [exact R1|]. split; [rewrite R2; lia|].
      do 4 (split; [assumption|]).
      rewrite R7, SWP. apply szd_nd_of; unfold s1, sA; szd_fields; auto.
Qed.

Lemma szd_hcall_hi flush wb flg id k z L inp res s0 s1 :
  9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 -> zf_ok z ->
  0 <= k < 6 -> 2 <= k -> szd_s1ok wb s1 -> l_s L = szd_hstg s0 s1 (szd_hdr wb flg id) k -> Forall szd_byte inp ->
  sublist 0 (Z.min (Zlength inp) (6 - k)) inp =
    sublist k (k + Z.min (Zlength inp) (6 - k)) (szd_hdr wb flg id) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  (k + Zlength inp < 6 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ m_snx (r_m res) = Zlength inp /\
   m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   m_s (r_m res) = szd_hstg s0 s1 (szd_hdr wb flg id) (k + Zlength inp)) \/
  (6 <= k + Zlength inp /\ r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 - k /\ m_ow (r_m res) = [] /\
   m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   dw_nd wb id (m_s (r_m res))).
Proof.
  intros Hwb Hf Hid Hz Hk K2 F1 Hs BI Hpre (o & LP & RS).
  destruct (szd_hdr_facts wb flg id Hwb Hf Hid) as (HL & HB & H26 & H02 & SWP).
  destruct F1 as (Fm & Fw & Fb & Fh & Fd & Fl & Ft & Fws & Fwh & Fwn & Fwi & Fwd & Ffl).
  set (hdr := szd_hdr wb flg id) in *.
  set (idb := be_bytes id 4) in *.
  destruct Hz as (_ & _ & _ & Zto & _).
  assert (Hto: 0 <= zf_tout z < 2 ^ 64)
    by (change Integers.Int64.max_unsigned with 18446744073709551615 in Zto; change (2 ^ 64) with 18446744073709551616; lia).
  pose proof (Zlength_nonneg inp) as I0.
  assert (Li: Zlength idb = 4) by (rewrite <- H26, Zlength_sublist; lia).
  assert (Bi: Forall szd_byte idb) by (rewrite <- H26; apply Forall_sublist; exact HB).
  set (a := Z.min (Zlength inp) (6 - k)) in *.
  (* the bytes the call reads are those of hdr *)
  assert (PRE: forall i j, 0 <= i <= j /\ j <= a -> sublist i j inp = sublist (k + i) (k + j) hdr).
  { intros i j Hij.
    assert (E1: sublist i j inp = sublist i j (sublist 0 a inp))
      by (rewrite szd_subsub by (unfold a in *; lia); f_equal; lia).
    rewrite E1, Hpre, szd_subsub by (unfold a in *; lia). reflexivity. }
  assert (Ha: a = Z.min (Zlength inp) (6 - k)) by reflexivity. clearbody a hdr idb.
  (* DICTID *)
  set (P := sublist 2 k hdr).
  assert (LPk: Zlength P = k - 2) by (unfold P; rewrite Zlength_sublist; lia).
  assert (BP: Forall szd_byte P) by (apply Forall_sublist; exact HB).
  set (sB := set_i_bits (set_i_hold (s1) (szd_le P)) (8 * Zlength P)).
  assert (Es: l_s L = sB).
  { rewrite Hs. unfold szd_hstg. replace (k <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold sB. rewrite LPk. reflexivity. }
  assert (SB: i_mode sB = DICTID /\ i_havedict sB = 0 /\ i_wsize sB = 0 /\ i_total sB = 0 /\
              i_hold sB = szd_le P /\ i_bits sB = 8 * Zlength P)
    by (unfold sB; szd_fields; repeat split; auto).
  destruct SB as (Bm & Bd & Bw & Bt & Bho & Bbi).
  rewrite szd_minit in LP by (rewrite Es, Bm; discriminate).
  rewrite Es, Bho, Bbi in LP.
  assert (EP: P = sublist 0 (Zlength P) idb).
  { rewrite LPk. unfold P. rewrite <- H26. rewrite szd_subsub by lia. f_equal; lia. }
  assert (SUB: sublist 0 (0 + Z.min (4 - Zlength P) (Zlength inp - 0)) inp =
               sublist (Zlength P) (Zlength P + Z.min (4 - Zlength P) (Zlength inp - 0)) idb).
  { rewrite Z.add_0_l. rewrite (PRE 0) by (lia). rewrite <- H26. rewrite szd_subsub by lia.
    f_equal; lia. }
  destruct (szd_dictid_run flush sB (l_h L) inp (zf_ao z) 0 P idb (Zlength inp) (zf_adler z) (zf_msg z) (zf_tin z)
              (zf_tout z) o res Bm Bd Bw Bt Hto Li Bi ltac:(lia) EP BI ltac:(lia) SUB LP RS)
    as [(R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7) | (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7)].
  + left. split; [lia|]. do 6 (split; [assumption|]).
    rewrite R7. unfold sB. rewrite szd_hb2. unfold szd_hstg.
    replace (k + Zlength inp <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
    f_equal; [f_equal|].
    * unfold P. rewrite (PRE 0) by lia. rewrite ?Z.add_0_r, ?Z.sub_0_r.
      f_equal. apply szd_app_sub; lia.
    * lia.
  + right. split; [lia|]. split; [exact R1|]. split; [rewrite R2; lia|].
    do 4 (split; [assumption|]).
    rewrite R7, SWP. apply szd_nd_of; unfold sB; szd_fields; auto.
Qed.

Lemma szd_hcall flush wb flg id k z L inp res :
  9 <= wb <= 15 -> RF.zflg_ok wb true flg -> 0 <= id < 2 ^ 32 -> zf_ok z ->
  0 <= k < 6 -> l_s L = szd_hst wb (szd_hdr wb flg id) k -> Forall szd_byte inp ->
  sublist 0 (Z.min (Zlength inp) (6 - k)) inp =
    sublist k (k + Z.min (Zlength inp) (6 - k)) (szd_hdr wb flg id) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  (k + Zlength inp < 6 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ m_snx (r_m res) = Zlength inp /\
   m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   m_s (r_m res) = szd_hst wb (szd_hdr wb flg id) (k + Zlength inp)) \/
  (6 <= k + Zlength inp /\ r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 - k /\ m_ow (r_m res) = [] /\
   m_sow (r_m res) = 0 /\ m_aout (r_m res) = zf_ao z /\ m_tout (r_m res) = zf_tout z /\
   dw_nd wb id (m_s (r_m res))).
Proof.
  intros Hwb Hf Hid Hz Hk Hs BI Hpre RUN.
  pose proof (szd_init_fields wb Hwb) as F0. pose proof (szd_s1_ok wb (init_s 5 wb) F0) as F1.
  unfold szd_hst, szd_s1 in *.
  destruct (Z.ltb_spec k 2) as [K2|K2].
  - exact (szd_hcall_lo flush wb flg id k z L inp res (init_s 5 wb) Hwb Hf Hid Hz Hk K2 F0 Hs BI Hpre RUN).
  - exact (szd_hcall_hi flush wb flg id k z L inp res (init_s 5 wb) (szd_s1g (init_s 5 wb) wb)
             Hwb Hf Hid Hz Hk K2 F1 Hs BI Hpre RUN).
Qed.

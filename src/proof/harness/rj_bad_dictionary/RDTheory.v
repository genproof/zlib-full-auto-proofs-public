(* Law rj_bad_dictionary, theory: the one inflate() call on a stream with an FDICT zlib header stops in DICT
   after the six header bytes with Z_NEED_DICT, its check = the dictionary id, so that inflateSetDictionary
   refuses a dictionary of another Adler-32 (rbd_theory_stmt of RDFacts.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rj_bad_dictionary.RDFacts.
Require Zlib.proof.harness.inflate_codes.TheoryHead.
Require Zlib.proof.harness.inflate_codes.TheoryDict.
Import ListNotations.
Local Open Scope Z_scope.

Module TD := Zlib.proof.harness.inflate_codes.TheoryDefs.
Module TH := Zlib.proof.harness.inflate_codes.TheoryHead.
Module TDi := Zlib.proof.harness.inflate_codes.TheoryDict.

(* ---------------------------------------------------------------------------------------------- *)
(* The header the harness writes                                                                  *)

(* the 16 bits HEAD's NEEDBITS(16) collects: CMF + 256 * FLG *)
Definition rbd_hv (c x: Z) : Z := rbd_b0 c + 256 * (rbd_b1 c x + 256 * 0).

(* what c_HEAD2 tests of them: FLG is a byte, the FCHECK test, CM = 8, CINFO = c, FDICT *)
Definition rbd_hdr_okb (c x: Z) : bool :=
  let hv := rbd_hv c x in
  (0 <=? rbd_b1 c x) && (rbd_b1 c x <=? 255) &&
  (((hv mod 256) * 256 + Z.shiftr hv 8) mod 31 =? 0) && (hv mod 16 =? 8) &&
  (Z.shiftr hv 4 mod 16 =? c) && negb (Z.land (Z.shiftr hv 4) 512 =? 0).

(* all 8 * 256 headers, by enumeration *)
Lemma rbd_hdr_tab :
  forallb (fun c => forallb (fun x => rbd_hdr_okb c x) (TH.thh_upto 256)) (TH.thh_upto 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rbd_hdr c x : 0 <= c <= 7 -> 0 <= x <= 255 ->
  0 <= rbd_b1 c x <= 255 /\
  (((rbd_hv c x mod 256) * 256 + Z.shiftr (rbd_hv c x) 8) mod 31 =? 0) = true /\
  (rbd_hv c x mod 16 =? 8) = true /\ Z.shiftr (rbd_hv c x) 4 mod 16 = c /\
  (Z.land (Z.shiftr (rbd_hv c x) 4) 512 =? 0) = false.
Proof.
  intros Hc Hx. pose proof rbd_hdr_tab as T. rewrite forallb_forall in T.
  specialize (T c (TH.thh_in_upto c 8 ltac:(change (Z.of_nat 8) with 8; lia))).
  rewrite forallb_forall in T. specialize (T x (TH.thh_in_upto x 256 ltac:(change (Z.of_nat 256) with 256; lia))).
  unfold rbd_hdr_okb in T. cbv zeta in T. repeat rewrite andb_true_iff in T.
  destruct T as [[[[[A0 A1] B1] B2] B3] B4]. rewrite negb_true_iff in B4. rewrite Z.leb_le in A0, A1.
  apply Z.eqb_eq in B3. repeat split; auto; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS with enough input does not leave                                                      *)

Lemma rbd_nb_leave k n : forall m, Z.of_nat k <= m_have m -> m_leave (needbits_f k n m) = m_leave m.
Proof.
  induction k as [|k IH]; intros m H; [reflexivity|].
  rewrite TH.thh_nbS. destruct (m_bits m <? n); [|reflexivity].
  replace (m_have m =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite IH; [destruct m; reflexivity|].
  unfold m_have, pull in *. cbn [m_inp m_nx set_m_bits set_m_hold set_m_nx]. lia.
Qed.

Ltac rbd_red :=
  unfold m_mode in *; cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler m_ow m_in m_tout
       m_tin m_snx m_sow m_h set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg
       set_m_adler set_leave set_m_leave initbits dropbits restore set_m_tin set_m_snx set_m_sow TDi.td_sh
       i_mode i_wrap i_head i_havedict i_wbits i_flags i_check
       set_i_mode set_i_check set_i_wbits set_i_flags set_i_dmax set_i_bits set_i_hold] in *.

(* ---------------------------------------------------------------------------------------------- *)
(* The two passes of the switch                                                                   *)

Section Pass.
Variables (fl w c x: Z) (m: mst).
Hypotheses (Hw: 8 <= w <= 15) (Hcw: 0 <= c <= w - 8) (Hx: 0 <= x <= 255)
  (Hb: bytes_ok (m_inp m)) (Hl6: 6 <= Zlength (m_inp m))
  (H0: Znth 0 (m_inp m) = rbd_b0 c) (H1: Znth 1 (m_inp m) = rbd_b1 c x).

Lemma rbd_ctx : TD.ctx_ok (m_inp m) 0 (m_inp m).
Proof. split; [lia|]. split; [lia|]. split; [exact Hb|]. intros k _. f_equal; lia. Qed.

(* HEAD: the two header bytes pass every test, FDICT: DICTID with nothing in the bit buffer *)
Lemma rbd_pass_head :
  m_mode m = HEAD -> i_wrap (m_s m) = 5 -> i_wbits (m_s m) = w -> i_head (m_s m) = false ->
  m_nx m = 0 -> m_bits m = 0 -> m_hold m = 0 -> m_leave m = 0 ->
  exists m1, stepf2 fl lenfix_list distfix_list m = IBrk m1 /\ m_inp m1 = m_inp m /\ m_mode m1 = DICTID /\
    i_wrap (m_s m1) = 5 /\ i_havedict (m_s m1) = i_havedict (m_s m) /\
    m_nx m1 = 2 /\ m_bits m1 = 0 /\ m_hold m1 = 0 /\ m_leave m1 = 0.
Proof.
  intros Hmd Hwr Hwb Hhd Hn Hbi Hho Hlv.
  assert (S : stepf2 fl lenfix_list distfix_list m = c_HEAD2 m)
    by (unfold stepf2, step2; rewrite Hmd; reflexivity).
  rewrite S. unfold c_HEAD2. rewrite Hwr. cbv beta iota zeta.
  assert (Hd : TD.hd_head (m_inp m) (0 + m_nx m) (m_hold m) (m_bits m)).
  { rewrite Hn, Hbi, Hho. unfold TD.hd_head. rewrite sublist_nil. cbn. lia. }
  destruct (TH.thh_nb m (m_inp m) 0 rbd_ctx ltac:(lia) Hd) as (nx' & Hn' & [[E Hp']|[E Hp']]).
  { exfalso. pose proof (rbd_nb_leave 4 16 m ltac:(unfold m_have; cbn; lia)) as L.
    fold (needbits 16 m) in L. rewrite E, Hlv in L. discriminate. }
  rewrite E.
  assert (EH : TD.le_val (sublist 0 2 (m_inp m)) = rbd_hv c x).
  { rewrite (sublist_split 0 1 2), !sublist_one by lia. cbn [TD.le_val app]. rewrite H0, H1. reflexivity. }
  destruct (rbd_hdr c x ltac:(lia) Hx) as (B1 & C1 & C2 & C3 & C4).
  rbd_red. rewrite Hlv, Hwr, Hhd, EH. cbv iota.
  change (m_hold (set_m_bits (set_m_hold (set_m_nx m nx') (rbd_hv c x)) 16)) with (rbd_hv c x).
  change (m_s (set_m_bits (set_m_hold (set_m_nx m nx') (rbd_hv c x)) 16)) with (m_s m).
  rewrite C1, C2, C3, C4, Hwb.
  replace (15 <? c + 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (w <? c + 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (w =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb orb andb Z.land Z.eqb]. cbv iota.
  eexists; split; [reflexivity|]. unfold dropbits. rbd_red. repeat split; auto; lia.
Qed.

(* DICTID: NEEDBITS(32) collects the id, check = ZSWAP32(hold); DICT without a dictionary returns
   Z_NEED_DICT *)
Lemma rbd_pass_dictid (m1: mst) :
  m_inp m1 = m_inp m -> m_mode m1 = DICTID -> i_wrap (m_s m1) = 5 -> i_havedict (m_s m1) = 0 ->
  m_nx m1 = 2 -> m_bits m1 = 0 -> m_hold m1 = 0 -> m_leave m1 = 0 ->
  exists m2, stepf2 fl lenfix_list distfix_list m1 = IRet Z_NEED_DICT m2 /\
    i_mode (m_s m2) = DICT /\ i_wrap (m_s m2) = 5 /\ i_check (m_s m2) = TD.dict_id (m_inp m).
Proof.
  intros Hi Hmd Hwr Hhv Hn Hbi Hho Hlv.
  rewrite (TDi.td_step_DICTID fl lenfix_list distfix_list m1 Hmd). unfold c_DICTID, needbits.
  assert (Hc : TD.ctx_ok (m_inp m) 0 (m_inp m1)) by (rewrite Hi; apply rbd_ctx).
  destruct (TDi.td_nbk (m_inp m) 0 4 m1 Hc ltac:(rewrite Hn, Hi; lia) ltac:(rewrite Hn; lia)
              ltac:(rewrite Hbi, Hn; lia) ltac:(rewrite Hho, Hn, sublist_nil; reflexivity)
              ltac:(rewrite Hn; cbn; lia)) as (nx' & Hn' & [[E Hp']|[E Hp']]).
  { exfalso. pose proof (rbd_nb_leave 4 32 m1 ltac:(unfold m_have; rewrite Hn, Hi; cbn; lia)) as L.
    rewrite E, Hlv in L. discriminate. }
  rewrite E.
  replace (m_leave (TDi.td_sh (m_inp m) 0 m1 nx') =? 1) with false by (rbd_red; rewrite Hlv; reflexivity).
  cbv zeta iota.
  assert (Ec : swap32 (m_hold (TDi.td_sh (m_inp m) 0 m1 nx')) = TD.dict_id (m_inp m)).
  { rbd_red. rewrite Hp'. apply TDi.td_dict_id; auto. }
  rewrite Ec. unfold c_DICT. rbd_red. rewrite Hhv. cbv iota.
  eexists; split; [reflexivity|]. rbd_red. repeat split; auto.
Qed.

End Pass.

(* the loop: one pass to DICTID (no leave), then a return *)
Lemma rbd_loop2 fl m m1 r m2 o :
  stepf2 fl lenfix_list distfix_list m = IBrk m1 -> m_leave m1 = 0 ->
  stepf2 fl lenfix_list distfix_list m1 = IRet r m2 ->
  loop2 fl lenfix_list distfix_list m o -> o = IRet r m2.
Proof.
  intros S1 L1 S2 HL.
  inversion HL as [? ? ? E | ? ? E L | ? ? ? E L HL']; subst; rewrite S1 in E; try discriminate.
  - injection E as <-. rewrite L1 in L. discriminate.
  - injection E as <-.
    inversion HL' as [? ? ? E' | ? ? E' _ | ? ? ? E' _ _]; subst; rewrite S2 in E'; try discriminate.
    injection E' as <- <-. reflexivity.
Qed.

(* the state inflateInit2_(w) leaves, for a zlib windowBits *)
Lemma rbd_init sp w : 8 <= w <= 15 ->
  let s := l_s (init_live sp w) in
  i_mode s = HEAD /\ i_wrap s = 5 /\ i_wbits s = w /\ i_head s = false /\ i_hold s = 0 /\ i_bits s = 0 /\
  i_havedict s = 0.
Proof.
  intros Hw.
  assert (w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12 \/ w = 13 \/ w = 14 \/ w = 15) as Ew by lia.
  destruct Ew as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; repeat split; reflexivity.
Qed.

Lemma rbd_dictid_be src : 6 <= Zlength src -> TD.dict_id src = rbd_dictid src.
Proof.
  intros Hl. unfold TD.dict_id, Zlib.proof.harness.inflate_common.HDefs.be32, rbd_dictid.
  rewrite !Znth_sublist by lia. change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  reflexivity.
Qed.

Lemma rbd_theory : rbd_theory_stmt.
Proof.
  intros w cinfo x src flush strmp sp z ib o r z' st' ow Hw Hc Hx Hb Hl H0 H1 Hs Hib Hz Hai Hrel.
  destruct Hrel as [(Bad & _) | (_ & L & o0 & res & winp & Est & Eob & Hrun & _ & Hr & _ & _ & _ & Hst')].
  { exfalso. destruct Bad as [B|[B|[B _]]]; [| discriminate | contradiction].
    unfold is_live in B. destruct (eq_dec strmp nullval); [contradiction | discriminate]. }
  injection Est as <-.
  destruct (rbd_init sp w Hw) as (Imd & Iwr & Iwb & Ihd & Iho & Ibi & Ihv).
  set (s := l_s (init_live sp w)) in *.
  set (m := m_init z (init_live sp w) src).
  assert (Ms : m_s m = s).
  { unfold m, m_init. fold s. rewrite Imd. reflexivity. }
  assert (Mi : m_inp m = src) by reflexivity.
  destruct (rbd_pass_head flush w cinfo x m Hw Hc Hx ltac:(rewrite Mi; exact Hb) ltac:(rewrite Mi; lia)
              ltac:(rewrite Mi; exact H0) ltac:(rewrite Mi; exact H1)
              ltac:(unfold m_mode; rewrite Ms; exact Imd) ltac:(rewrite Ms; exact Iwr)
              ltac:(rewrite Ms; exact Iwb) ltac:(rewrite Ms; exact Ihd) eq_refl
              ltac:(unfold m, m_init; fold s; rewrite Imd; exact Ibi)
              ltac:(unfold m, m_init; fold s; rewrite Imd; exact Iho) eq_refl)
    as (m1 & S1 & E1i & E1md & E1wr & E1hv & E1n & E1b & E1h & E1l).
  destruct (rbd_pass_dictid flush m ltac:(rewrite Mi; exact Hb) ltac:(rewrite Mi; lia) m1 E1i E1md E1wr
              ltac:(rewrite E1hv, Ms; exact Ihv) E1n E1b E1h E1l)
    as (m2 & S2 & E2md & E2wr & E2ck).
  destruct Hrun as (o1 & HL & Ho).
  rewrite (rbd_loop2 flush m m1 Z_NEED_DICT m2 o1 S1 E1l S2 HL) in Ho. subst res. cbn [r_ret r_m] in Hr, Hst'.
  split; [exact Hr|]. eexists; split; [exact Hst'|].
  intros dict Hd. cbn [l_s]. unfold setdict_check. rewrite E2md, E2wr, E2ck, Mi, rbd_dictid_be by lia.
  rewrite Z.eqb_refl. cbn [negb andb]. replace (adler32_z_val 1 dict =? rbd_dictid src) with false
    by (symmetry; apply Z.eqb_neq; exact Hd).
  reflexivity.
Qed.

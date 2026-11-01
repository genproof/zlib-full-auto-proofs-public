(* Law uncompress_any, the theory: ua_facts_stmt (UAFacts.v) from the call-level parts (UATheoryDefs.v), law
   inflate_check's call lemma (IKTheoryCall.ikc_inflate with IKBits.ik_kit_proof and IKTheory.ik_all) and law
   inflate_codes' (TheoryCall.cl_inflate). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.uncompress_any.UATheoryDefs.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Require Import Zlib.proof.harness.inflate_check.IKBits Zlib.proof.harness.inflate_check.IKTheoryCall
               Zlib.proof.harness.inflate_check.IKTheory.
Require Import Zlib.proof.harness.inflate_codes.TheoryNoDict Zlib.proof.harness.inflate_codes.TheoryRun
               Zlib.proof.harness.inflate_codes.TheoryCall.
Require Import Zlib.proof.harness.uncompress_any.UAStepMwf.
Import ListNotations.
Local Open Scope Z_scope.


(* ---------------------------------------------------------------------------------------------- *)
(* One run2 from a call boundary: consumption and output ranges, for every outcome (Z_MEM_ERROR too) *)

Lemma ua_run (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (ib: inbuf) (ob: option outbuf)
    (ain aout flush: Z) (inp: list Z) (res: result) :
  inv w src pos final indict z L -> live_ok L -> zf_ok z -> 0 <= aout <= 2 ^ 20 ->
  ctx_ok src pos inp -> Zlength src <= 2 ^ 24 ->
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (cl_m0 z L ib ob ain aout inp) res ->
  0 <= m_snx (r_m res) <= Zlength inp /\ m_inp (r_m res) = inp /\
  Zlength (m_ow (r_m res)) <= aout /\ bytes_ok (m_ow (r_m res)).
Proof.
  intros IV LV ZF AO C SL RUN.
  destruct (cl_init w src pos final indict z L ib ob ain aout inp IV LV ZF AO C SL)
    as (W0 & K0 & L00 & OW0 & NX0 & SNX0 & SOW0 & OUT0 & MSG0 & RET0 & MD0).
  destruct RUN as (ot & LP & RES).
  pose proof (rn_loop ua_stepf2_mwf3 ikc_kc_all th_nodict (wrap_of w) src pos inp aout flush _ ot C LP K0 W0 L00
                (fun _ => OW0)) as LR.
  destruct ot as [mE | r' mE].
  - destruct LR as (KE & WE & LE & DE).
    pose proof (mwf3_mwf _ WE) as M.
    pose proof (kc_inp _ _ _ _ _ _ KE) as KI. pose proof (kc_aout _ _ _ _ _ _ KE) as KA.
    destruct (mw_ow _ M) as [OWL OWB]. pose proof (mw_nx _ M) as NX.
    destruct RES as [LO WF | ].
    + cbn. rewrite KI in NX. rewrite KA in OWL. auto.
    + destruct (rn_leave_fin flush mE) as (_ & R2 & _ & R4 & _ & _ & R7 & _).
      rewrite R2, R4, R7. rewrite KI in NX. rewrite KA in OWL. auto.
  - subst res. cbn [r_m]. destruct LR as (WE & KE & _).
    pose proof (mwf3_mwf _ WE) as M.
    pose proof (kc_inp _ _ _ _ _ _ KE) as KI. pose proof (kc_aout _ _ _ _ _ _ KE) as KA.
    destruct (mw_ow _ M) as [OWL OWB]. pose proof (mw_snx _ M) as NX.
    rewrite KI in NX. rewrite KA in OWL. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Determinism                                                                                    *)

Lemma ua_loop2_det (flush: Z) (fx dx: list entry) (m: mst) (o1 o2: iout) :
  loop2 flush fx dx m o1 -> loop2 flush fx dx m o2 -> o1 = o2.
Proof.
  intros L1. revert o2.
  induction L1 as [m r m' E | m m' E L | m m' o E L LP IH]; intros o2 L2;
    inversion L2; subst; congruence || (rewrite E in *; match goal with H: IBrk _ = IBrk _ |- _ => inversion H; subst end;
      first [congruence | apply IH; auto]).
Qed.

Lemma ua_run2_det (m: mst) (res1 res2: result) :
  Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list m res1 ->
  Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list m res2 ->
  r_ret res1 <> Z_MEM_ERROR -> r_ret res2 <> Z_MEM_ERROR -> res1 = res2.
Proof.
  intros (o1 & L1 & R1) (o2 & L2 & R2) N1 N2.
  rewrite <- (ua_loop2_det _ _ _ _ _ _ L1 L2) in R2.
  destruct o1 as [mE | r mE].
  - destruct R1 as [ | ]; [cbn in N1; contradiction|].
    destruct R2 as [ | ]; [cbn in N2; contradiction|]. reflexivity.
  - congruence.
Qed.

Lemma ua_loop_det (src: list Z) (cap: Z) : forall m used out err used' out',
  unc_loop src cap m used out err used' out' -> err <> Z_MEM_ERROR ->
  forall err2 used2 out2, unc_loop src cap m used out err2 used2 out2 -> err2 <> Z_MEM_ERROR ->
  err2 = err /\ used2 = used' /\ out2 = out'.
Proof.
  intros m used out err used' out' U.
  induction U as [m used out res RUN NOK | m used out res err used' out' RUN OK U IH];
    intros NM err2 used2 out2 U2 NM2; inversion U2 as [m2 used2' out2' res2 RUN2 NOK2 | m2 used2' out2' res2 err2' used2'' out2'' RUN2 OK2 U2'];
    subst.
  - assert (res2 = res) by (apply (ua_run2_det _ _ _ RUN2 RUN); auto). subst. auto.
  - assert (res2 = res) by (apply (ua_run2_det _ _ _ RUN2 RUN); auto; rewrite OK2; discriminate). subst.
    contradiction.
  - assert (res2 = res) by (apply (ua_run2_det _ _ _ RUN2 RUN); auto; rewrite OK; discriminate). subst.
    contradiction.
  - assert (res2 = res) by (apply (ua_run2_det _ _ _ RUN2 RUN); [rewrite OK2 | rewrite OK]; discriminate). subst.
    apply IH; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The call-boundary invariant                                                                    *)

Lemma ua_next_eq (m: mst) (z: zfields) (L: live) (inp: list Z) (ni no: val) (ain aout: Z) :
  l_s L = m_s m -> l_h L = m_h m -> zf_adler z = m_adler m -> zf_msg z = m_msg m -> zf_tin z = m_tin m ->
  zf_tout z = m_tout m ->
  m_next m inp aout = m_init (set_zf_call z ni ain no aout) L inp.
Proof.
  intros E1 E2 E3 E4 E5 E6. unfold m_next, m_init. cbn [set_zf_call zf_ao zf_adler zf_msg zf_tin zf_tout].
  rewrite E1, E2, E3, E4, E5, E6. reflexivity.
Qed.

Definition UI (src: list Z) (cap: Z) (used: Z) (out: list Z) (m: mst) : Prop :=
  exists z L, l_s L = m_s m /\ l_h L = m_h m /\ zf_adler z = m_adler m /\ zf_msg z = m_msg m /\
    zf_tin z = m_tin m /\ zf_tout z = m_tout m /\
    ikc_I 15 src used out z L /\ live_ok L /\ zf_ok z /\ ua_fd src (l_s L) /\
    0 <= used <= Zlength src /\ Zlength out <= cap.

Lemma ua_wrap15 : wrap_of 15 = 5.
Proof. reflexivity. Qed.

Lemma ua_step (src: list Z) (cap: Z) (used: Z) (out: list Z) (m: mst) (res: result) :
  ua_live_stmt -> ua_fd_stmt ->
  bytes_ok src -> Zlength src <= 2 ^ 24 -> 0 <= cap <= 2 ^ 20 ->
  UI src cap used out m ->
  Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list
    (m_next m (sublist used (Zlength src) src) (cap - Zlength out)) res ->
  0 <= used + m_snx (r_m res) <= Zlength src /\ Zlength (out ++ m_ow (r_m res)) <= cap /\
  bytes_ok (out ++ m_ow (r_m res)) /\
  code_okb (r_ret res) = true /\ r_ret res <> Z_STREAM_ERROR /\
  (r_ret res <> Z_MEM_ERROR -> UI src cap (used + m_snx (r_m res)) (out ++ m_ow (r_m res)) (r_m res)) /\
  (r_ret res = Z_STREAM_END ->
     6 <= used + m_snx (r_m res) /\ ua_hdr src /\
     be32 (sublist (used + m_snx (r_m res) - 4) (used + m_snx (r_m res)) src) = ref_adler32 1 (out ++ m_ow (r_m res))).
Proof.
  intros LIVE FD BS SL CAP (z & L & ES & EH & EA & EM & ETI & ETO & IK & LV & ZF & UF & U0 & OC) RUN.
  set (inp := sublist used (Zlength src) src) in *.
  set (ain := Zlength src - used).
  set (aout := cap - Zlength out) in *.
  set (ib := InBuf Ews nullval 0 ain []).
  set (o := OutBuf Ews nullval 0 aout []).
  set (strmp := Vptr xH Ptrofs.zero).
  set (zc := set_zf_call z (in_ptr ib 0) ain (ob_ptr (Some o)) aout).
  rewrite (ua_next_eq m z L inp (in_ptr ib 0) (ob_ptr (Some o)) ain aout ES EH EA EM ETI ETO) in RUN.
  pose proof IK as IK0. destruct IK0 as ((final & indict & INV) & BO & KX).
  assert (AOr: 0 <= aout <= 2 ^ 20) by (pose proof (Zlength_nonneg out); unfold aout; lia).
  assert (EI: inp = sublist used (used + ain) src) by (unfold inp, ain; f_equal; lia).
  assert (CI: call_in_ok src used ain ib inp) by (right; split; [discriminate | exact EI]).
  assert (P0: 0 <= used) by lia. assert (A0: 0 <= ain) by (unfold ain; lia).
  assert (PA: used + ain <= Zlength src) by (unfold ain; lia).
  destruct (cl_in_ok src used ain ib inp P0 A0 PA BS CI) as (C & LI & _).
  assert (LA: Zlength inp = ain) by (apply LI; discriminate).
  change (m_init zc L inp) with (cl_m0 z L ib (Some o) ain aout inp) in RUN.
  destruct (ua_run 15 src used final indict z L ib (Some o) ain aout 0 inp res INV LV ZF AOr C SL RUN)
    as (SNX & INP & OWL & OWB).
  set (L' := Live (l_sp L) (l_winp L) (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  set (z' := z_after zc ib o res).
  assert (SN: strmp <> nullval) by discriminate.
  assert (REL: inflate_rel 0 strmp zc (Some L) ib inp (Some o) (r_ret res) z' (Some L') (m_ow (r_m res))).
  { right. split.
    - unfold inflate_bad, is_live. destruct (eq_dec strmp nullval) as [E|_]; [contradiction|].
      intros [B|[B|(B & _)]]; discriminate.
    - exists L, o, res, (l_winp L). split; [reflexivity|]. split; [reflexivity|].
      split; [exact RUN|]. split; [exact SNX|].
      repeat split; auto. }
  assert (FL: Int.min_signed <= 0 <= Int.max_signed) by rep_lia.
  destruct (cl_inflate ua_stepf2_mwf3 ikc_kc_all th_nodict 15 src used final indict z L strmp 0 ib inp (Some o)
              ain aout (r_ret res) z' (Some L') (m_ow (r_m res)) INV LV ZF SN P0 A0 PA SL BS AOr FL CI REL)
    as (L1 & EL1 & IP).
  inversion EL1; subst L1; clear EL1.
  assert (BP: badptr ib (Some o) ain = false) by reflexivity. rewrite BP in IP.
  destruct IP as (CO & RI & RO & SE & _ & _ & _ & _ & _ & INV').
  assert (NSE: r_ret res <> Z_STREAM_ERROR) by (intros E; apply SE in E; discriminate).
  assert (ZAI: zf_ai z' = ain - m_snx (r_m res)) by (unfold z'; cbn; rewrite INP, LA; reflexivity).
  assert (U': ain - zf_ai z' = m_snx (r_m res)) by lia.
  split; [lia|]. split; [rewrite Zlength_app; unfold aout in OWL; lia|].
  split; [apply Forall_app; auto|].
  split; [exact CO|]. split; [exact NSE|].
  destruct (ikc_inflate ik_kit_proof ik_all 15 src used out z L strmp 0 ib inp o ain aout (r_ret res) z' (Some L')
              (m_ow (r_m res)) IK LV ZF SN P0 A0 PA SL BS AOr FL ltac:(discriminate) EI REL)
    as (L2 & EL2 & CP).
  inversion EL2; subst L2; clear EL2.
  assert (ZFc: zf_ok zc).
  { destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zc, zf_ok. cbn [set_zf_call zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
    repeat split; rep_lia. }
  assert (BI: bytes_ok inp) by exact (cl_bytes_ok _ _ _ C).
  destruct (FD 15 src used final indict z L strmp 0 ib inp o ain aout (r_ret res) z' (Some L') (m_ow (r_m res))
              eq_refl INV LV ZF SN P0 A0 PA SL BS AOr FL ltac:(discriminate) EI UF REL) as (L3 & EL3 & UF' & NF).
  inversion EL3; subst L3; clear EL3.
  split.
  - intros NM.
    destruct (LIVE 0 strmp zc L ib inp o (r_ret res) z' (Some L') (m_ow (r_m res)) LV ZFc SN ltac:(discriminate)
                ltac:(unfold zc; cbn; lia) ltac:(rep_lia) BI ltac:(unfold zc; cbn; rep_lia) REL NM)
      as (L4 & EL4 & LV' & ZF').
    inversion EL4; subst L4; clear EL4.
    destruct (CP NM) as (_ & _ & _ & _ & _ & _ & _ & _ & IK'). rewrite U' in IK'.
    exists z', L'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact IK'|]. split; [exact LV'|]. split; [exact ZF'|]. split; [exact UF'|].
    split; [lia|]. rewrite Zlength_app. unfold aout in OWL. lia.
  - intros RSE.
    assert (NM: r_ret res <> Z_MEM_ERROR) by (rewrite RSE; discriminate).
    destruct (CP NM) as (_ & _ & _ & _ & _ & _ & _ & TR & IK').
    destruct (TR ltac:(lia) RSE) as (_ & TRL). rewrite U' in TRL, IK'.
    change (ik_gz 15 src) with false in TRL. destruct TRL as (T1 & T2).
    split; [exact T1|]. split; [|exact T2].
    destruct INV' as (_ & _ & _ & _ & FM & _). rewrite RSE in FM. cbn in FM.
    assert (MD: i_mode (l_s L') = DONE).
    { unfold final_mode in FM. destruct FM as [(F & _)|[(_ & F)|[(F & _)|(F & _)]]]; try discriminate; exact F. }
    assert (MM: m_mode (m_init z' L' []) = DONE).
    { unfold m_mode, m_init. cbn [m_s]. rewrite MD. cbn. exact MD. }
    destruct IK' as (_ & _ & KX'). rewrite ua_wrap15 in KX'.
    assert (PM: ik_post_mode (m_mode (m_init z' L' []))).
    { rewrite MM. unfold ik_post_mode. do 11 right. reflexivity. }
    destruct (kx_post _ _ _ _ _ _ KX' ltac:(discriminate) PM) as (H & _).
    destruct H as [(_ & ZH & _)|(_ & _ & G & _)]; [|cbn in G; discriminate].
    destruct ZH as (H1 & H2 & H3 & H4).
    unfold ua_hdr. repeat split; auto.
    destruct (Z.eq_dec (Z.land (Znth 1 src) 32) 0) as [E|E]; [exact E|].
    exfalso. exact (NF RSE E).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Lemma ua_loop (src: list Z) (cap: Z) :
  ua_live_stmt -> ua_fd_stmt -> bytes_ok src -> Zlength src <= 2 ^ 24 -> 0 <= cap <= 2 ^ 20 ->
  forall m used out err used' out',
  unc_loop src cap m used out err used' out' -> UI src cap used out m ->
  0 <= used' <= Zlength src /\ Zlength out' <= cap /\ bytes_ok out' /\
  (err = Z_STREAM_END \/ err = Z_NEED_DICT \/ err = Z_BUF_ERROR \/ err = Z_DATA_ERROR \/ err = Z_MEM_ERROR) /\
  (err = Z_STREAM_END -> 6 <= used' /\ ua_hdr src /\ be32 (sublist (used' - 4) used' src) = ref_adler32 1 out').
Proof.
  intros LIVE FD BS SL CAP m used out err used' out' U.
  induction U as [m used out res RUN NOK | m used out res err used' out' RUN OK U IH]; intros UI0;
    destruct (ua_step src cap used out m res LIVE FD BS SL CAP UI0 RUN) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  - split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [|exact S7].
    revert S4 S5 NOK. unfold code_okb. generalize (r_ret res). intros r.
    destruct (Z.eqb_spec r Z_OK); destruct (Z.eqb_spec r Z_STREAM_END); destruct (Z.eqb_spec r Z_NEED_DICT);
      destruct (Z.eqb_spec r Z_DATA_ERROR); destruct (Z.eqb_spec r Z_STREAM_ERROR); destruct (Z.eqb_spec r Z_MEM_ERROR);
      destruct (Z.eqb_spec r Z_BUF_ERROR); cbn; intros; try discriminate; tauto.
  - apply IH. apply S6. rewrite OK. discriminate.
Qed.

(* the stream after inflateInit_ *)
Lemma ua_init_live_ok (sp: val) : isptr sp -> live_ok (init_live sp 15).
Proof.
  intros Hsp.
  unfold live_ok, init_live. simpl l_sp; simpl l_s; simpl l_h; simpl l_hsh.
  assert (Hl: Forall (fun x => 0 <= x <= 65535) (Zrepeat 0 320)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  assert (Hc: Forall entry_ok (Zrepeat (mkE 0 0 0) ENOUGH_CODES)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. cbv; repeat split; congruence. }
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap, reset_s, reset_keep_s, zero_s. simpl.
  split; [exact Hsp | ]. split; [ | split; [ | split; [ | split; [ | split]]]].
  - constructor; simpl; unfold urange, srange, lrange, tref_ok, ENOUGH_CODES, HEAD, SYNC in *; try rep_lia.
    all: try (split; [reflexivity | auto]).
    all: try (left; reflexivity).
    all: try lia.
    all: try (intros; lia).
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
  - constructor; simpl; unfold urange, srange, lrange; try rep_lia; try (split; [reflexivity | constructor]).
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; try lia; auto.
  - apply writable_Ews.
  - simpl. split; [intros H0; discriminate | ].
    split; [discriminate | ].
    intros; discriminate.
Qed.

Lemma ua_UI_first (src: list Z) (cap: Z) : 0 <= cap -> UI src cap 0 [] m_first.
Proof.
  intros CAP.
  set (z0 := ZF nullval 0 0 nullval 0 0 None 0 1 nullval).
  set (sp := Vptr xH Ptrofs.zero).
  exists z0, (init_live sp 15).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [apply ikc_init; reflexivity|].
  split; [apply ua_init_live_ok; exact I|].
  split; [unfold zf_ok; cbn; rep_lia|].
  split; [split; [reflexivity | intros _; left; reflexivity]|].
  split; [pose proof (Zlength_nonneg src); lia|]. rewrite Zlength_nil. lia.
Qed.

Lemma ua_unc_ret_mem (err rest: Z) : unc_ret err rest <> Z_MEM_ERROR -> err <> Z_MEM_ERROR.
Proof. intros H E. subst err. apply H. reflexivity. Qed.

Lemma ua_unc_ret_ok (err rest: Z) :
  (err = Z_STREAM_END \/ err = Z_NEED_DICT \/ err = Z_BUF_ERROR \/ err = Z_DATA_ERROR \/ err = Z_MEM_ERROR) ->
  (unc_ret err rest = Z_OK \/ unc_ret err rest = Z_MEM_ERROR \/ unc_ret err rest = Z_BUF_ERROR \/
   unc_ret err rest = Z_DATA_ERROR) /\ (unc_ret err rest = Z_OK -> err = Z_STREAM_END).
Proof.
  intros [E|[E|[E|[E|E]]]]; subst err; unfold unc_ret; cbn -[Z.eqb];
    try (destruct (rest =? 0); cbn); split; try tauto; intros H; discriminate.
Qed.

Lemma ua_theory_of : ua_live_stmt -> ua_fd_stmt -> ua_facts_stmt.
Proof.
  intros LIVE FD src cap r slen dlen out BS SL CAP REL.
  destruct REL as [(-> & -> & -> & ->) | (err & UL & -> & ->)].
  - split; [tauto|]. split; [pose proof (Zlength_nonneg src); lia|].
    split; [rewrite Zlength_nil; lia|]. split; [constructor|].
    split; [intros N; contradiction N; reflexivity|]. intros E; discriminate.
  - destruct (ua_loop src cap LIVE FD BS SL CAP _ _ _ _ _ _ UL (ua_UI_first src cap ltac:(lia)))
      as (P1 & P2 & P3 & P4 & P5).
    destruct (ua_unc_ret_ok err (Zlength src - slen) P4) as (R1 & R2).
    split; [exact R1|]. split; [exact P1|]. split; [lia|]. split; [exact P3|].
    split; [reflexivity|].
    intros ROK. pose proof (R2 ROK) as ESE.
    destruct (P5 ESE) as (H1 & H2 & H3).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros r2 slen2 dlen2 out2 REL2 NM2.
    destruct REL2 as [(E & _) | (err2 & UL2 & -> & ->)]; [contradiction|].
    destruct (ua_loop_det src cap _ _ _ _ _ _ UL ltac:(rewrite ESE; discriminate) err2 slen2 out2 UL2
                (ua_unc_ret_mem _ _ NM2)) as (-> & -> & ->).
    auto.
Qed.

(* uncompress2 for any sizes on a well-formed zlib stream: the loop of inflate() calls of UModelW.uncw_loop, call
   by call by the decode theory for calls of up to 2^32 - 1 bytes (rfc1951/Decode7.v decode_call7_stmt).

   Between two calls the stream m has consumed `used` bytes of the input dc_src G and written `out`; ai / ao are
   the avail_in / avail_out the last call left ([uw_RI]: a live stream, UWLive.uw_mlive, in the decoder's
   invariant dinv, with the counters in range).  One call ([uw_step]) extends a prefix of the data; Z_STREAM_END
   comes with all of the data written, within the space offered, and the whole stream read; Z_BUF_ERROR (no
   progress, UWBuf.uw_buf) comes only when the call was offered no output space, i.e. with the space full, the
   data not all written and so (UWPos.uw_pos) input left.  [uw_loop]: the loop ends with Z_MEM_ERROR,
   Z_STREAM_END there, or Z_BUF_ERROR with the space full of the first bytes of the data. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.uncompr.UModelW.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.uncompr.UWLive Zlib.proof.uncompr.UWBuf Zlib.proof.uncompr.UWPos.
Require Zlib.proof.roundtrip.RTUTheory.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The pieces offered to a call                                                                   *)

Lemma uw_ain_range (src: list Z) (used ai: Z) :
  0 <= used -> 0 <= ai <= uw_max -> used + ai <= Zlength src ->
  0 <= uw_ain src used ai <= uw_max /\ used + uw_ain src used ai <= Zlength src /\
  (uw_ain src used ai = 0 -> used = Zlength src).
Proof.
  intros U A L. unfold uw_ain, uw_max in *.
  destruct (Z.eqb_spec ai 0); [|lia].
  split; [lia|]. split; [lia|]. intros E. lia.
Qed.

Lemma uw_aout_range (cap: Z) (out: list Z) (ao: Z) :
  0 <= ao <= uw_max -> Zlength out + ao <= cap ->
  0 <= uw_aout cap out ao <= uw_max /\ Zlength out + uw_aout cap out ao <= cap /\
  (uw_aout cap out ao = 0 -> Zlength out = cap).
Proof.
  intros A L. unfold uw_aout, uw_max in *.
  destruct (Z.eqb_spec ao 0); [|lia].
  split; [lia|]. split; [lia|]. intros E. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

(* the stream between two calls *)
Definition uw_RI (G: dctx) (cap: Z) (m: mst) (used: Z) (out: list Z) (ai ao: Z) : Prop :=
  uw_mlive m /\ dinv G used out (m_s m) (m_tout m) /\
  0 <= used /\ 0 <= ai <= uw_max /\ used + ai <= Zlength (dc_src G) /\
  0 <= ao <= uw_max /\ Zlength out + ao <= cap.

Lemma uw_step (DK: decode_call7_stmt) (G: dctx) (wb fl: Z) (did: option Z) (cap: Z) (m: mst) (used: Z)
    (out: list Z) (ai ao: Z) (res: result) :
  dctx_ok7 G -> dc_w G = WZlib wb fl did -> uw_RI G cap m used out ai ao ->
  run2 0 lenfix_list distfix_list (uw_call (dc_src G) cap m used out ai ao) res ->
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   (r_ret res = Z_OK ->
      uw_RI G cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
        (uw_ain (dc_src G) used ai - m_snx (r_m res)) (uw_aout cap out ao - Zlength (m_ow (r_m res)))) /\
   (exists rest, full G = out ++ m_ow (r_m res) ++ rest) /\
   (r_ret res = Z_STREAM_END ->
      out ++ m_ow (r_m res) = full G /\ used + m_snx (r_m res) = slen G /\ Zlength (out ++ m_ow (r_m res)) <= cap) /\
   (r_ret res = Z_BUF_ERROR ->
      m_snx (r_m res) = 0 /\ m_ow (r_m res) = [] /\ Zlength out = cap /\ Zlength out < Zlength (full G) /\
      used < slen G)).
Proof.
  intros OK W (ML & DI & U0 & AI & UA & AO & OA) RUN.
  pose proof OK as (_ & _ & _ & _ & SL & _ & BY & _).
  destruct (uw_ain_range (dc_src G) used ai U0 AI UA) as (AIN & UAIN & AIN0).
  destruct (uw_aout_range cap out ao AO OA) as (AOUT & OAOUT & AOUT0).
  unfold uw_call in RUN.
  set (ain := uw_ain (dc_src G) used ai) in *.
  set (aout := uw_aout cap out ao) in *.
  set (inp := sublist used (used + ain) (dc_src G)) in *.
  assert (LI: Zlength inp = ain) by (unfold inp; rewrite Zlength_sublist; lia).
  destruct ML as ((L & LV & ES & EH) & SW & HD & TI & TO & AD).
  set (z0 := ZF nullval 0 (m_tin m) nullval 0 (m_tout m) (m_msg m) 0 (m_adler m) nullval).
  set (zc := Zlib.proof.roundtrip.RTUTheory.rtu_zc z0 (Zlength inp) aout).
  pose proof RUN as RUN0.
  rewrite (Zlib.proof.roundtrip.RTUTheory.rtu_next_eq m z0 L inp aout ES EH eq_refl eq_refl eq_refl eq_refl)
    in RUN.
  fold zc in RUN.
  assert (ZF: zf_ok zc).
  { unfold zc, Zlib.proof.roundtrip.RTUTheory.rtu_zc, z0, zf_ok, lrange, uw_max in *.
    cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler]. rep_lia. }
  assert (DI': dinv G used out (l_s L) (zf_tout zc)) by (rewrite ES; exact DI).
  assert (IE: inp = sublist used (used + Zlength inp) (dc_src G)) by (rewrite LI; reflexivity).
  assert (BI: bytes_ok inp) by (unfold inp; apply Forall_sublist; exact BY).
  assert (NG: forall h, dc_w G <> WGzip h) by (intros h E; rewrite W in E; discriminate).
  unfold uw_max in *.
  pose proof (DK G used out L zc inp 0 res OK DI' LV ZF ltac:(unfold zc; cbn; lia) ltac:(lia) U0
                ltac:(lia) IE RUN) as P.
  cbv zeta in P.
  destruct P as [P|(R & SNX & SOW & MAO & PFX & DV' & _ & SE & NSE & _)]; [left; exact P|right].
  assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [E|[E|E]]; rewrite E; discriminate).
  destruct (uw_live 0 m inp aout res
              ltac:(split; [exists L; auto|auto]) ltac:(rep_lia) BI ltac:(rep_lia) RUN0 NM) as (ML' & OW).
  split; [exact R|]. split; [|split; [exact PFX|split]].
  2:{ intros E. destruct (SE E) as (A & B). split; [exact A|]. split; [exact B|].
      rewrite Zlength_app. lia. }
  - intros _. split; [exact ML'|]. split; [exact DV'|].
    rewrite Zlength_app. pose proof (Zlength_nonneg (m_ow (r_m res))). unfold uw_max. rewrite LI in SNX.
    repeat split; lia.
  - intros EB.
    destruct (uw_buf G used out L zc inp res OK DI' LV ZF ltac:(lia) U0 ltac:(lia) IE NG RUN EB) as (S0 & O0).
    assert (NE: r_ret res <> Z_STREAM_END) by (rewrite EB; discriminate).
    assert (LT: Zlength out = cap /\ Zlength out < Zlength (full G)).
    { destruct (NSE NE) as [(A & B)|[(A & B)|[F|F]]]; try discriminate.
      - exfalso. rewrite S0 in A. specialize (AIN0 ltac:(lia)). lia.
      - rewrite O0, app_nil_r in B. rewrite O0, Zlength_nil in A. unfold zc in A; cbn in A.
        split; [apply AOUT0; lia | exact B]. }
    split; [exact S0|]. split; [exact O0|]. split; [apply LT|]. split; [apply LT|].
    exact (uw_pos G (m_s m) used (i_hold (m_s m)) (i_bits (m_s m)) out wb fl did OK W (proj1 DI) (proj2 LT)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Lemma uw_loop (DK: decode_call7_stmt) (G: dctx) (wb fl: Z) (did: option Z) (cap: Z) :
  dctx_ok7 G -> dc_w G = WZlib wb fl did ->
  forall m used out ai ao err used' out',
  uncw_loop (dc_src G) cap m used out ai ao err used' out' -> uw_RI G cap m used out ai ao ->
  err = Z_MEM_ERROR \/
  (err = Z_STREAM_END /\ out' = full G /\ used' = slen G /\ Zlength out' <= cap) \/
  (err = Z_BUF_ERROR /\ Zlength out' = cap /\ cap < Zlength (full G) /\ 0 <= used' < slen G /\
   exists rest, full G = out' ++ rest).
Proof.
  intros OK W m used out ai ao err used' out' U.
  induction U as [m used out ai ao res RUN NOK | m used out ai ao res err used' out' RUN EOK U IH]; intros RI.
  - destruct (uw_step DK G wb fl did cap m used out ai ao res OK W RI RUN)
      as [M|(R & _ & (rest & PFX) & SE & BE)]; [left; exact M|right].
    destruct R as [E|[E|E]]; [contradiction| |].
    + right. destruct (BE E) as (S0 & O0 & C & LT & UL).
      rewrite S0, O0, app_nil_r, Z.add_0_r. rewrite O0 in PFX.
      split; [exact E|]. split; [exact C|]. split; [lia|].
      split; [split; [destruct RI as (_ & _ & U0 & _); exact U0 | exact UL]|].
      exists rest. exact PFX.
    + left. destruct (SE E) as (A & B & C). auto.
  - destruct (uw_step DK G wb fl did cap m used out ai ao res OK W RI RUN) as [M|(R & RI' & _)].
    + rewrite EOK in M. discriminate.
    + apply IH. apply RI'. exact EOK.
Qed.

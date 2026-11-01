(* The laws rt_dictionary and api_dict_id: one inflate(Z_FINISH) call of rt_dictionary's loop after the
   dictionary, on the model (Model2.run2), from the decode theory for calls of any size (Decode7).

   The call starts at pos >= 6 in O with out written (the decode invariant's output is dict ++ out), offered the
   next clip(|O| - pos) bytes of O and clip(|D| - |out|) bytes of output space.  It returns Z_STREAM_END (all of
   O read, D written) or Z_BUF_ERROR, never Z_OK: with Z_FINISH inf_leave turns Z_OK into Z_BUF_ERROR, and a
   call that leaves through inf_leave (not a return from the switch) is the only one that sets data_type.
   Z_BUF_ERROR comes only from a call that was offered less than the rest of O or of the output. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.harness.clip_streams.PfxTheory.
Require Import Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.harness.dictionary_w.DWISet.
Require Import Zlib.proof.harness.dictionary_w.DWIKit.
Import ListNotations.
Local Open Scope Z_scope.

(* inflate(Z_FINISH) returns Z_OK neither from the switch (no case returns Z_OK: those runs have no data_type)
   nor from inf_leave *)
Lemma dwi_fin_nok fx dx m0 res :
  run2 Z_FINISH fx dx m0 res -> r_dtype res <> None -> r_ret res <> Z_OK.
Proof.
  intros (o & _ & E) DT.
  destruct o as [m|r m].
  - destruct E as [_ _ | ].
    + cbn in DT. congruence.
    + unfold leave_fin. cbv zeta. cbn [r_ret].
      rewrite (proj2 (Z.eqb_eq Z_FINISH Z_FINISH) eq_refl), orb_true_r. cbn [andb].
      match goal with |- (if ?c then _ else ?x) <> _ => destruct c eqn:C end.
      * cbv. discriminate.
      * apply Z.eqb_neq in C. exact C.
  - subst res. cbn in DT. congruence.
Qed.

(* the wrapper fields between calls: zlib (inflateInit2 with windowBits 9..15), no gz_header *)
Lemma dwi_glob G pos out s tout :
  dinv G pos out s tout -> 9 <= dc_iw G <= 15 -> i_wrap s = 5 /\ i_head s = false.
Proof.
  intros (_ & ((wb0 & R & _) & HD & _) & _) IW.
  rewrite dwi_init_wrap_wb in R by exact IW. injection R as R _. auto.
Qed.

(* clip(): at most UINT_MAX and at most its argument; less than its argument only above UINT_MAX *)
Lemma dwi_clip_le n : clipz n <= umax /\ clipz n <= 2 ^ 32 - 1 /\ clipz n <= n.
Proof. unfold clipz, umax. lia. Qed.

Lemma dwi_clip_lt n : clipz n < n -> umax < n.
Proof. unfold clipz, umax. lia. Qed.

Lemma dwi_call_core (DK: decode_call7_stmt) wbits dict D O G pos out L0 z1 inp res aout :
  dw_gok wbits dict D O G -> 6 <= pos <= Zlength O ->
  dinv G pos (dict ++ out) (l_s L0) (zf_tout z1) -> live_ok L0 -> zf_ok z1 -> zf_ao z1 = aout ->
  Zlength inp = clipz (Zlength O - pos) -> aout = clipz (Zlength D - Zlength out) ->
  inp = sublist pos (pos + Zlength inp) O ->
  run2 Z_FINISH lenfix_list distfix_list (m_init z1 L0 inp) res ->
  r_ret res <> Z_MEM_ERROR ->
  let m := r_m res in
  m_inp m = inp /\ 0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = aout /\
  (r_ret res = Z_STREAM_END \/ r_ret res = Z_BUF_ERROR) /\
  (r_ret res = Z_STREAM_END -> pos + m_snx m = Zlength O /\ out ++ m_ow m = D) /\
  (r_ret res = Z_BUF_ERROR ->
     (umax < Zlength O - pos \/ umax < Zlength D - Zlength out) /\
     dinv G (pos + m_snx m) (dict ++ (out ++ m_ow m)) (m_s m) (m_tout m) /\
     exists rest, D = (out ++ m_ow m) ++ rest).
Proof.
  intros GOK POS DV LV ZF AO LI LA INP RUN NM.
  pose proof GOK as (OK & HI & IW & IWR & FU & SL & LS & _ & L6).
  pose proof (dwi_clip_le (Zlength O - pos)) as (CI1 & CI2 & CI3).
  pose proof (dwi_clip_le (Zlength D - Zlength out)) as (CO1 & CO2 & CO3).
  rewrite <- LI in CI1, CI2, CI3. rewrite <- LA in CO1, CO2, CO3.
  assert (PL: pos + Zlength inp <= Zlength O) by lia.
  pose proof (dwi_inp wbits dict D O G pos inp GOK ltac:(lia) PL INP) as INP'.
  assert (A1: zf_ao z1 <= 2 ^ 32 - 1) by (rewrite AO; exact CO2).
  assert (A3: 0 <= pos) by lia.
  assert (A4: pos + Zlength inp <= Zlength (dc_src G)) by (rewrite LS; exact PL).
  destruct (DK G pos (dict ++ out) L0 z1 inp Z_FINISH res OK DV LV ZF A1 CI2 A3 A4 INP' RUN)
    as [MEM | (RC & SNX & SOW & MAO & (rest & PRE) & DV' & _ & SE & NFIN & (dt & DT & _))].
  { contradiction. }
  assert (VM: vmode (i_mode (m_s (m_init z1 L0 inp)))).
  { pose proof (pfx_vmode _ _ _ _ _ DV) as V. unfold m_init. cbv zeta.
    destruct (i_mode (l_s L0) =? Zlib.proof.inflate.Model.TYPE); [compute; split; discriminate | exact V]. }
  destruct (run2_frame _ _ _ _ _ VM RUN) as (MI & _ & _).
  cbn [m_init m_inp] in MI.
  assert (NOK: r_ret res <> Z_OK) by (apply (dwi_fin_nok _ _ _ _ RUN); rewrite DT; discriminate).
  cbv zeta.
  split; [exact MI|]. split; [exact SNX|]. split; [exact SOW|]. split; [rewrite MAO; exact AO|].
  split; [destruct RC as [R|[R|R]]; [contradiction|right; exact R|left; exact R]|].
  split.
  - intros ES. destruct (SE ES) as [F1 F2]. split; [lia|].
    rewrite FU, <- app_assoc in F1. apply app_inv_head in F1. exact F1.
  - intros EB. split; [|split; [rewrite app_assoc; exact DV'|]].
    + assert (NE: r_ret res <> Z_STREAM_END) by (rewrite EB; discriminate).
      destruct (NFIN NE) as [(A & B) | [(A & B) | B]].
      * left. apply dwi_clip_lt. rewrite <- LI. lia.
      * right. apply dwi_clip_lt. rewrite <- LA.
        rewrite FU, !Zlength_app in B. rewrite A, AO in B. lia.
      * unfold Z_FINISH, Z_BLOCK, Z_TREES in B. lia.
    + exists rest. rewrite FU, <- app_assoc in PRE. apply app_inv_head in PRE. rewrite <- app_assoc. exact PRE.
Qed.

(* The laws rt_dictionary and api_dict_id: the inflate facts (DWIFacts.dict_ifacts) from the decode theory for
   inputs of any length and calls of up to 2^32 - 1 bytes (Decode7: decode_init7_stmt, decode_call7_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictKit.
Require Import Zlib.proof.roundtrip.RTIZDictD1.
Require Import Zlib.proof.uncompr.URunFrame.
Require Import Zlib.proof.harness.dictionary_w.DWIFirst.
Require Import Zlib.proof.harness.dictionary_w.DWISet.
Require Import Zlib.proof.harness.dictionary_w.DWIKit.
Require Import Zlib.proof.harness.dictionary_w.DWICall.
(* clip_streams' umax and clipz (DWIFacts' interface), not the homonyms of DFacts and RTDIface *)
Import Zlib.proof.harness.clip_streams.IFacts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariants                                                                                  *)

(* after the first call: Z_NEED_DICT's state (DICT, no window, check = DICTID), nothing counted out *)
Definition dw_q : qinv_t := fun wbits dict D O z L =>
  dw_nd (iwb wbits) (Zlib.proof.adler32.Model.ref_adler32 1 dict) (l_s L) /\ zf_tout z = 0 /\
  dfinal_dict wbits dict D O /\ 1 <= Zlength dict /\ Zlength O <= 2 ^ 64 - 1.

(* between the calls of the loop: pos bytes of O read, out written after the dictionary; right after
   inflateSetDictionary the state is still DICT (havedict 1), whose TYPE version satisfies the decode
   invariant at pos 6 (the next call goes through DICT to TYPE: RTIZDictD1.rtz_d1) *)
Definition dw_p : dinv_t := fun wbits dict D O pos out z L =>
  6 <= pos <= Zlength O /\ (exists rest, D = out ++ rest) /\
  exists G, dw_gok wbits dict D O G /\
    ((pos = 6 /\ out = [] /\ i_mode (l_s L) = DICT /\ i_havedict (l_s L) = 1 /\ i_bits (l_s L) = 0 /\
      dinv G 6 dict (d1_ty (l_s L)) (zf_tout z)) \/
     dinv G pos (dict ++ out) (l_s L) (zf_tout z)).

Lemma dwi_p_ok wbits dict D O pos out z L : dw_p wbits dict D O pos out z L ->
  i_head (l_s L) = false /\ i_wrap (l_s L) <> 0 /\ 0 <= pos <= Zlength O /\ exists rest, D = out ++ rest.
Proof.
  intros (POS & HPR & G & GOK & DV). pose proof GOK as (_ & _ & IW & IWR & _).
  assert (W: i_wrap (l_s L) = 5 /\ i_head (l_s L) = false).
  { rewrite <- IW in IWR. destruct DV as [(_ & _ & _ & _ & _ & DV) | DV].
    - exact (dwi_glob _ _ _ _ _ DV IWR).
    - exact (dwi_glob _ _ _ _ _ DV IWR). }
  destruct W as [W H]. split; [exact H|]. split; [lia|]. split; [lia|exact HPR].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers                                                                                         *)

Lemma dwi_offer_ok z ib (inp: list Z) o aout :
  zf_ok z -> 0 <= aout <= umax -> Zlength inp <= umax ->
  zf_ok (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout).
Proof.
  intros (Z1 & Z2 & Z3 & Z4 & Z5 & Z6) A I. unfold offer_z, zf_ok; cbn.
  unfold umax in *. pose proof (Zlength_nonneg inp).
  split; [rep_lia|]. split; [rep_lia|]. exact (conj Z3 (conj Z4 (conj Z5 Z6))).
Qed.

(* the first n >= 6 bytes of O *)
Lemma dwi_pfx6 (A T: list Z) n : Zlength A = 6 -> 6 <= n <= 6 + Zlength T ->
  sublist 0 n (A ++ T) = A ++ sublist 0 (n - 6) T.
Proof.
  intros HA Hn. pose proof (Zlength_nonneg T).
  rewrite (sublist_split 0 6 n) by (rewrite ?Zlength_app; lia).
  rewrite sublist_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite HA. reflexivity.
Qed.

(* inflate_rel on a live stream offered an input object and an output object is a run of the model *)
Lemma dwi_rel flush strmp z L ib (inp: list Z) o r z' st' ow :
  strmp <> nullval -> ib <> InNull ->
  inflate_rel flush strmp z (Some L) ib inp (Some o) r z' st' ow ->
  exists res winp,
    run2 flush lenfix_list distfix_list (m_init z L inp) res /\ r = r_ret res /\ ow = m_ow (r_m res) /\
    z' = z_after z ib o res /\
    st' = Some (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L)
                     (l_nb L) (l_cb L)).
Proof.
  intros SN IB [(BAD & _) | (_ & L0 & o0 & res & winp & EL & EO & RUN & _ & ER & EOW & EZ & _ & EST)].
  - exfalso. destruct BAD as [B | [B | [B _]]].
    + unfold is_live in B. destruct (eq_dec strmp nullval); congruence.
    + discriminate.
    + contradiction.
  - injection EL as <-. injection EO as <-. exists res, winp. auto.
Qed.

(* the stream after a call of the loop *)
Lemma dwi_post wbits (dict D O: list Z) G pos (out: list Z) L z ib (inp: list Z) o aout res winp :
  dw_gok wbits dict D O G -> 6 <= pos <= Zlength O ->
  let m := r_m res in
  m_inp m = inp -> 0 <= m_snx m <= Zlength inp -> m_sow m = Zlength (m_ow m) -> m_aout m = aout ->
  (r_ret res = Z_STREAM_END \/ r_ret res = Z_BUF_ERROR) ->
  (r_ret res = Z_STREAM_END -> pos + m_snx m = Zlength O /\ out ++ m_ow m = D) ->
  (r_ret res = Z_BUF_ERROR ->
     (umax < Zlength O - pos \/ umax < Zlength D - Zlength out) /\
     dinv G (pos + m_snx m) (dict ++ (out ++ m_ow m)) (m_s m) (m_tout m) /\
     exists rest, D = (out ++ m_ow m) ++ rest) ->
  zf_ok (z_after (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) ib o res) ->
  let z' := z_after (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) ib o res in
  let L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L) in
  call_post ib inp o aout z' (Some L') (m_ow m) L' /\
  (r_ret res = Z_STREAM_END \/ r_ret res = Z_BUF_ERROR) /\
  (r_ret res = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O /\ out ++ m_ow m = D) /\
  (r_ret res = Z_BUF_ERROR ->
     (umax < Zlength O - pos \/ umax < Zlength D - Zlength out) /\
     dw_p wbits dict D O (pos + (Zlength inp - zf_ai z')) (out ++ m_ow m) z' L').
Proof.
  intros GOK POS m MI SNX SOW MAO RC SE BU ZF' z' L'.
  assert (AI: zf_ai z' = Zlength inp - m_snx m)
    by (unfold z', z_after; cbv zeta; cbn [zf_ai]; fold m; rewrite MI; reflexivity).
  assert (AO: zf_ao z' = aout - Zlength (m_ow m))
    by (unfold z', z_after; cbv zeta; cbn [zf_ao]; fold m; rewrite MAO, SOW; reflexivity).
  assert (EP: pos + (Zlength inp - zf_ai z') = pos + m_snx m) by lia.
  pose proof (Zlength_nonneg (m_ow m)).
  destruct ZF' as (_ & ZA & _). fold z' in ZA.
  split; [|split; [exact RC|split]].
  - split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [rewrite AI; unfold z', z_after; cbv zeta; cbn [zf_ni]; fold m; f_equal; lia|].
    split; [rewrite AO; unfold z', z_after; cbv zeta; cbn [zf_no]; fold m; f_equal; rewrite SOW; lia|].
    lia.
  - intros ES. rewrite EP. exact (SE ES).
  - intros EB. destruct (BU EB) as (CL & DV & HPR). split; [exact CL|].
    rewrite EP. pose proof GOK as (_ & _ & _ & _ & _ & _ & LS & _).
    split; [|split; [exact HPR|]].
    + pose proof (proj1 (proj1 DV)) as (_ & HC & _). lia.
    + exists G. split; [exact GOK|]. right. exact DV.
Qed.

Lemma dwi_clip_ge m n : m <= n -> m <= umax -> m <= clipz n.
Proof. unfold clipz, umax. lia. Qed.

(* the fields after DICT's adler32(0, Z_NULL, 0) *)
Lemma dwi_adl_ok z : zf_ok z -> zf_ok (z_adl z 1).
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6). unfold zf_ok, z_adl. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
  repeat split; try lia; rep_lia.
Qed.

Lemma dwi_clip_pos n : 0 < n -> 0 < clipz n.
Proof. unfold clipz, umax. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The first call: HEAD, DICTID, then DICT returns Z_NEED_DICT                                      *)

Lemma dwi_first_call wbits dict D O z sp strmp flush ib inp o aout r z' st' ow :
  dfinal_dict wbits dict D O -> 1 <= Zlength dict <= dict_max -> Zlength O <= 2 ^ 64 - 1 ->
  init_ok (iwb wbits) z sp ->
  call_pre O 0 z (init_live sp (iwb wbits)) strmp flush ib inp o aout ->
  Zlength inp = clipz (Zlength O) ->
  inflate_rel flush strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout)
    (Some (init_live sp (iwb wbits))) ib inp (Some o) r z' st' ow ->
  zf_ok z' ->
  r = Z_NEED_DICT /\ zf_adler z' = Zlib.proof.adler32.Model.ref_adler32 1 dict /\
  exists L', call_post ib inp o aout z' st' ow L' /\ Zlength inp - zf_ai z' = 6 /\ ow = [] /\
    i_head (l_s L') = false /\ i_wrap (l_s L') <> 0 /\ dw_q wbits dict D O z' L'.
Proof.
  intros DF DL L64 IO CP LI REL ZF'.
  assert (Hne: dict <> []) by (intro E; subst dict; rewrite Zlength_nil in DL; lia).
  destruct (dwi_stream wbits dict D O DF Hne L64) as (flg & T & FL & EO & HT & bs & WF & GOK).
  pose proof GOK as (_ & _ & _ & IWR & _ & _ & _ & _ & L6).
  destruct IO as (_ & _ & ZF & _ & _ & T0 & _).
  destruct CP as (LV & _ & SN & _ & IB & _ & OUTOK & LIu & LAu & INP).
  destruct (dwi_rel _ _ _ _ _ _ _ _ _ _ _ SN IB REL) as (res & winp & RUN & ER & EOW & EZ & EST).
  assert (AO: 0 <= aout) by (destruct o; apply OUTOK).
  set (wb := iwb wbits) in *.
  set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  assert (ZF0: zf_ok z0) by (apply dwi_offer_ok; [exact ZF | lia | exact LIu]).
  set (id := Zlib.proof.adler32.Model.ref_adler32 1 dict) in *.
  assert (L6i: 6 <= Zlength inp) by (rewrite LI; apply dwi_clip_ge; [lia | unfold umax; apply Z.leb_le; reflexivity]).
  assert (HBE: Zlength (be_bytes id 4) = 4) by (unfold be_bytes, le_bytes; rewrite Zlength_rev, Zlength_map; reflexivity).
  assert (HOL: Zlength O = 6 + Zlength T) by (rewrite EO, !Zlength_app, HBE; cbn; lia).
  assert (LIO: Zlength inp <= Zlength O) by (rewrite LI; apply dwi_clip_le).
  assert (EI: inp = [RF.zcmf wb; flg] ++ be_bytes id 4 ++ sublist 0 (Zlength inp - 6) T).
  { rewrite INP at 1. rewrite Z.add_0_l, EO, app_assoc. rewrite dwi_pfx6.
    - rewrite <- app_assoc. reflexivity.
    - rewrite Zlength_app, HBE. reflexivity.
    - lia. }
  pose proof (dwi_first flush wb flg id (sublist 0 (Zlength inp - 6) T) z0 sp res IWR FL
                (rtzk_adler_range dict) ZF0) as R1.
  rewrite <- EI in R1. specialize (R1 RUN).
  destruct R1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & ND).
  assert (HM: i_mode (l_s (init_live sp wb)) = HEAD) by (rewrite (dwi_init_s sp wb IWR); reflexivity).
  assert (VM: vmode (i_mode (m_s (m_init z0 (init_live sp wb) inp)))).
  { unfold m_init. cbv zeta. rewrite HM. cbn [m_s].
    change (HEAD =? Zlib.proof.inflate.Model.TYPE) with false. cbv iota. rewrite HM.
    unfold vmode. cbv. split; discriminate. }
  destruct (run2_frame _ _ _ _ _ VM RUN) as (MI & _ & _).
  cbn [m_init m_inp] in MI.
  assert (AI: zf_ai z' = Zlength inp - 6) by (rewrite EZ; unfold z_after; cbn [zf_ai]; rewrite MI, R2; reflexivity).
  assert (AOz: zf_ao z' = aout) by (rewrite EZ; unfold z_after; cbn [zf_ao]; rewrite R5, R4; unfold z0, offer_z; cbn; lia).
  split; [rewrite ER; exact R1|].
  split; [rewrite EZ; unfold z_after; cbn [zf_adler]; exact R7|].
  eexists. split; [|split; [lia|split; [rewrite EOW; exact R3|]]].
  - split; [exact EST|]. split; [lia|]. split; [lia|].
    split; [rewrite AI, EZ; unfold z_after; cbn [zf_ni]; rewrite R2; f_equal; lia|].
    split; [rewrite AOz, EZ; unfold z_after; cbn [zf_no]; rewrite R4; f_equal; lia|].
    rewrite EOW, R3, AOz, Zlength_nil. lia.
  - cbn [l_s].
    pose proof ND as (_ & NW & NH & _).
    split; [exact NH|]. split; [rewrite NW; discriminate|].
    split; [exact ND|]. split; [rewrite EZ; unfold z_after; cbn [zf_tout]; rewrite R6; unfold z0, offer_z; cbn; exact T0|].
    split; [exact DF|]. split; [lia|exact L64].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSetDictionary with the dictionary                                                         *)

Lemma dwi_set_call wbits dict D O z L alloc_ok winp :
  dw_q wbits dict D O z L -> live_ok L ->
  let sd := setdict_f dict alloc_ok winp z L in
  (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
  (fst3 sd = Z_OK -> snd3 sd = z /\ swfW (l_s (thd3 sd)) /\ dw_p wbits dict D O 6 [] z (thd3 sd)).
Proof.
  intros (ND & T0 & DF & DL & L64) LV. cbv zeta.
  assert (Hne: dict <> []) by (intro E; subst dict; rewrite Zlength_nil in DL; lia).
  destruct (dwi_stream wbits dict D O DF Hne L64) as (flg & T & FL & EO & HT & bs & WF & GOK).
  pose proof GOK as (_ & _ & _ & IWR & _ & _ & _ & _ & L6).
  destruct (dwi_set (iwb wbits) dict bs (l_s L) IWR WF Hne ND) as (SC & DI).
  pose proof ND as (Nm & _ & _ & _ & _ & _ & _ & _ & _ & Nw & _ & _ & _ & _ & Nb & _).
  destruct (rtzk_uw_keep (l_s L) dict) as (K1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & _).
  unfold setdict_f. rewrite SC, Nw.
  destruct alloc_ok; [|split; [right; reflexivity | intros X; discriminate X]].
  split; [left; reflexivity|]. intros _. unfold snd3, thd3. cbn [fst snd l_s set_l_winp set_l_s].
  assert (Sm: i_mode (setdict_s (l_s L) dict) = DICT) by (unfold setdict_s; cbn; rewrite K1; exact Nm).
  split; [reflexivity|]. split.
  - unfold swfW. rewrite Sm. split; intros E; discriminate E.
  - split; [lia|]. split; [exists D; reflexivity|].
    exists (dw_ctx (iwb wbits) dict bs). split; [exact GOK|]. left.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Sm|]. split; [reflexivity|].
    split; [unfold setdict_s; cbn; rewrite K11; exact Nb|].
    rewrite T0. exact DI.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* A call of the loop                                                                               *)

Lemma dwi_loop_call (DK: decode_call7_stmt) wbits dict D O pos out z L strmp ib inp o aout r z' st' ow :
  dw_p wbits dict D O pos out z L -> call_pre O pos z L strmp Z_FINISH ib inp o aout ->
  Zlength inp = clipz (Zlength O - pos) -> aout = clipz (Zlength D - Zlength out) ->
  inflate_rel Z_FINISH strmp (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) (Some L) ib inp
    (Some o) r z' st' ow ->
  r <> Z_MEM_ERROR -> zf_ok z' ->
  exists L', call_post ib inp o aout z' st' ow L' /\
    (r = Z_STREAM_END \/ r = Z_BUF_ERROR) /\
    (r = Z_STREAM_END -> pos + (Zlength inp - zf_ai z') = Zlength O /\ out ++ ow = D) /\
    (r = Z_BUF_ERROR ->
       (umax < Zlength O - pos \/ umax < Zlength D - Zlength out) /\
       dw_p wbits dict D O (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L').
Proof.
  intros HP CP LI LA REL NM ZF'.
  destruct CP as (LV & ZF & SN & _ & IB & _ & OUTOK & LIu & LAu & INP).
  destruct (dwi_rel _ _ _ _ _ _ _ _ _ _ _ SN IB REL) as (res & winp & RUN & ER & EOW & EZ & EST).
  subst r ow z' st'.
  assert (AO: 0 <= aout) by (destruct o; apply OUTOK).
  set (z0 := offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) aout) in *.
  assert (ZF0: zf_ok z0) by (apply dwi_offer_ok; [exact ZF | lia | exact LIu]).
  destruct HP as (POS & HPR & G & GOK & [(E6 & Eo & MD & HD & BI & DV) | DV]).
  - subst pos out.
    pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & L6).
    assert (LI0: 0 < Zlength inp) by (rewrite LI; apply dwi_clip_pos; lia).
    pose proof (rtz_d1 z0 L inp res MD HD ltac:(lia) LI0 RUN) as RUN'.
    pose proof (dwi_adl_ok z0 ZF0) as ZF1.
    assert (DV1: dinv G 6 (dict ++ []) (l_s (set_l_s L (d1_ty (l_s L)))) (zf_tout (z_adl z0 1)))
      by (rewrite app_nil_r; exact DV).
    destruct (dwi_call_core DK wbits dict D O G 6 [] (set_l_s L (d1_ty (l_s L))) (z_adl z0 1) inp res aout
                GOK ltac:(lia) DV1 (rtzk_live L LV MD) ZF1 eq_refl LI LA INP RUN' NM)
      as (MI & SNX & SOW & MAO & RC & SE & BU).
    eexists. exact (dwi_post wbits dict D O G 6 [] L z ib inp o aout res winp GOK ltac:(lia)
                      MI SNX SOW MAO RC SE BU ZF').
  - destruct (dwi_call_core DK wbits dict D O G pos out L z0 inp res aout
                GOK POS DV LV ZF0 eq_refl LI LA INP RUN NM)
      as (MI & SNX & SOW & MAO & RC & SE & BU).
    eexists. exact (dwi_post wbits dict D O G pos out L z ib inp o aout res winp GOK POS
                      MI SNX SOW MAO RC SE BU ZF').
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                       *)

(* DWIFacts' statement names clip_streams/DFacts' clipz, RTDIface's umax and deflate's return codes, homonyms
   of the inflate-side constants used above, with the same values.  The hypotheses and goals are rewritten from
   the ones to the others pointwise: converting the two clipz functions directly makes the conversion check
   unfold Z.min and does not terminate in practice. *)
Lemma dwi_clipz_eq n : Zlib.proof.harness.clip_streams.DFacts.clipz n = clipz n.
Proof.
  transitivity (Z.min n Zlib.proof.roundtrip.RTDIface.umax);
    [exact (eq_refl : Zlib.proof.harness.clip_streams.DFacts.clipz n = Z.min n Zlib.proof.roundtrip.RTDIface.umax)|].
  transitivity (Z.min n umax); [exact (eq_refl : Z.min n Zlib.proof.roundtrip.RTDIface.umax = Z.min n umax)|].
  exact (eq_refl : Z.min n umax = clipz n).
Qed.
Lemma dwi_umax_eq : Zlib.proof.roundtrip.RTDIface.umax = umax.
Proof. exact eq_refl. Qed.
Lemma dwi_finish_eq : Zlib.proof.deflate.DState.Z_FINISH = Zlib.proof.inflate.Model.Z_FINISH.
Proof. exact eq_refl. Qed.
Lemma dwi_ok_eq : Zlib.proof.deflate.DState.Z_OK = Zlib.proof.inflate.Model.Z_OK.
Proof. exact eq_refl. Qed.
Lemma dwi_mem_eq : Zlib.proof.deflate.DState.Z_MEM_ERROR = Zlib.proof.inflate.Model.Z_MEM_ERROR.
Proof. exact eq_refl. Qed.
Lemma dwi_end_eq : Zlib.proof.deflate.DState.Z_STREAM_END = Zlib.proof.inflate.Model.Z_STREAM_END.
Proof. exact eq_refl. Qed.
Lemma dwi_buf_eq : Zlib.proof.deflate.DState.Z_BUF_ERROR = Zlib.proof.inflate.Model.Z_BUF_ERROR.
Proof. exact eq_refl. Qed.

Lemma dict_itheory : decode_init7_stmt -> decode_call7_stmt -> dict_ifacts_stmt.
Proof.
  intros _ DK. exists dw_q, dw_p. constructor.
  - exact dwi_p_ok.
  - intros wbits dict D O z sp strmp flush ib inp o aout r z' st' ow DF DL L64 IO CP LI REL ZF'.
    rewrite dwi_clipz_eq in LI.
    exact (dwi_first_call wbits dict D O z sp strmp flush ib inp o aout r z' st' ow DF DL L64 IO CP LI REL ZF').
  - intros wbits dict D O z L alloc_ok winp HQ LV.
    rewrite dwi_ok_eq, dwi_mem_eq.
    exact (dwi_set_call wbits dict D O z L alloc_ok winp HQ LV).
  - intros wbits dict D O pos out z L strmp ib inp o aout r z' st' ow HP CP LI LA REL NM ZF'.
    rewrite dwi_finish_eq in CP, REL. rewrite dwi_clipz_eq in LI, LA. rewrite dwi_mem_eq in NM.
    rewrite dwi_end_eq, dwi_buf_eq, dwi_umax_eq.
    exact (dwi_loop_call DK wbits dict D O pos out z L strmp ib inp o aout r z' st' ow HP CP LI LA REL NM ZF').
Qed.

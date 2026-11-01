(* Law rt_session, sessions with a dictionary and the zlib wrapper: the inflate side's facts (SIFacts.ses_ifacts
   sk_zdict) from the phase before Z_NEED_DICT (SZdHead.v: the zlib header and DICTID in any pieces), the
   dictionary (SZdKit.szd_set) and the decode theory for calls of any size (Decode7) on the context of the input
   object whose history is the dictionary (SZdKit.szd_ctx). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require compcert.lib.Integers.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.wide.Decode7.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictKit.
Require Import Zlib.proof.roundtrip.RTIZDictSet.
Require Import Zlib.proof.harness.dictionary_w.DWIFirst.
Require Import Zlib.proof.harness.dictionary_w.DWISet.
Require Zlib.proof.harness.clip_streams.IFacts.
Require Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.harness.rt_stream.UIIdle.
Require Import Zlib.proof.harness.rt_session.SZdKit.
Require Import Zlib.proof.harness.rt_session.SZdHead.
Require Import Zlib.proof.harness.rt_session.SZdCall.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The session                                                                                     *)

(* inflateInit2's windowBits and the dictionary id *)
Definition szd_wb (c: scase) : Z := rts_iw (sc_wbits c).
Definition szd_id (c: scase) : Z := Zlib.proof.adler32.Model.ref_adler32 1 (sc_dict c).

(* what the kind and the session give: deflateInit2's windowBits 8..15, no gzip header, the finished zlib stream
   with the dictionary, the input object O ++ any bytes *)
Lemma szd_case c D O src : sk_zdict c -> sc_ok c D O -> src_ok O src ->
  8 <= sc_wbits c <= 15 /\ sc_gh c = None /\ dfinal_dict (sc_wbits c) (sc_dict c) D O /\ sc_dict c <> [] /\
  szd_wb c = Zlib.proof.harness.clip_streams.IFacts.iwb (sc_wbits c) /\
  Zlength src <= 2 ^ 64 - 1 /\ Zlength O <= Zlength src /\ sublist 0 (Zlength O) src = O /\ bytes_ok src /\
  Forall szd_byte src.
Proof.
  intros (NE & W1) ((lv & mem & st & RP) & DF & _ & GH & _ & _) (LS & SB & RB).
  unfold sc_wrap, rwrap_of in W1.
  assert (WR: 0 <= sc_wbits c <= 15).
  { destruct (Z.ltb_spec (sc_wbits c) 0); [discriminate|].
    destruct (Z.gtb_spec (sc_wbits c) 15); [discriminate|]. lia. }
  assert (W8: 8 <= sc_wbits c).
  { unfold rparams_ok in RP. repeat rewrite andb_true_iff in RP.
    destruct RP as ((((((((((_ & _) & _) & _) & R8) & _) & _) & _) & _) & _) & _).
    apply Z.leb_le in R8. unfold rwb_of in R8.
    destruct (Z.ltb_spec (sc_wbits c) 0); [lia|]. destruct (Z.gtb_spec (sc_wbits c) 15); lia. }
  assert (G0: sc_gh c = None).
  { destruct (sc_gh c) eqn:E; [|reflexivity]. exfalso.
    assert (X: sc_wrap c = 2) by (apply GH; discriminate).
    unfold sc_wrap, rwrap_of in X. rewrite W1 in X. discriminate. }
  unfold sc_wrap, rwrap_of in DF. rewrite W1, G0 in DF.
  assert (BY: Forall szd_byte src).
  { eapply Forall_impl; [|exact RB]. intros b Hb. exact Hb. }
  split; [lia|]. split; [exact G0|]. split; [split; [lia | exact DF]|]. split; [exact NE|].
  split; [reflexivity|].
  unfold Zlib.proof.harness.rt_stream.UDFacts.max_size in LS.
  split; [lia|]. split; [lia|]. split; [exact SB|]. split; [|exact BY].
  eapply Forall_impl; [|exact RB]. intros b Hb. cbv beta in Hb. cbn. lia.
Qed.

(* the session's stream inside the input object: its first 6 bytes and its decode context *)
Lemma szd_stream_c c D O src : sk_zdict c -> sc_ok c D O -> src_ok O src ->
  exists flg T bs, RF.zflg_ok (szd_wb c) true flg /\
    O = [RF.zcmf (szd_wb c); flg] ++ be_bytes (szd_id c) 4 ++ T /\
    sublist 0 6 O = szd_hdr (szd_wb c) flg (szd_id c) /\
    wf (2 ^ szd_wb c) (sc_dict c) bs /\ 9 <= szd_wb c <= 15 /\
    szd_gok (szd_wb c) (sc_dict c) D O src
      (szd_ctx (szd_wb c) (sc_dict c) bs (sublist (Zlength O) (Zlength src) src)).
Proof.
  intros K OK SR.
  destruct (szd_case c D O src K OK SR) as (W8 & G0 & DF & NE & EW & L64 & LO & PO & BY & _).
  rewrite EW. unfold szd_id.
  destruct (szd_stream (sc_wbits c) (sc_dict c) D O src DF NE L64 LO PO BY)
    as (flg & T & FL & EO & bs & WF & IWR & GOK).
  exists flg, T, bs. split; [exact FL|]. split; [exact EO|]. split.
  - rewrite EO. unfold szd_hdr. rewrite app_assoc. rewrite sublist_app1.
    + apply sublist_same; [reflexivity|]. rewrite Zlength_app. reflexivity.
    + lia.
    + rewrite Zlength_app. cbn. lia.
  - auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariants                                                                                  *)

(* between the calls: no gzip header, inflate_pieces' pinv (no gz_header, a mode of the decoder, swfW: what the zero-length
   call's lemma UIIdle.ui_idle_call needs) and
   - before Z_NEED_DICT (asked = false): the first pos < 6 bytes of O read (SZdHead.szd_hst), nothing written;
   - after inflateSetDictionary (asked = true): the decode invariant on the context of src with the history
     dict, from byte 6 on; right after inflateSetDictionary the state is still DICT (havedict 1), whose TYPE
     version satisfies the decode invariant at byte 6 (the next call goes through DICT to TYPE: SZdCall.szd_d1) *)
Definition szd_P : ses_iinv := fun c D O src pos out asked L tout =>
  sk_zdict c /\ sc_gh c = None /\ i_head (l_s L) = false /\ HEAD <= i_mode (l_s L) <= BAD /\ swfW (l_s L) /\
  ((asked = false /\ out = [] /\ tout = 0 /\ 0 <= pos < 6 /\ l_s L = szd_hst (szd_wb c) (sublist 0 6 O) pos) \/
   (asked = true /\ 6 <= pos /\ exists G, szd_gok (szd_wb c) (sc_dict c) D O src G /\
     ((pos = 6 /\ out = [] /\ i_mode (l_s L) = DICT /\ i_havedict (l_s L) = 1 /\ i_wsize (l_s L) <> 0 /\
       rtzs_wstruct (l_s L) /\ i_win (l_s L) = true /\ 0 <= i_total (l_s L) <= Integers.Int64.max_unsigned /\
       dinv G 6 (sc_dict c) (d1_ty (l_s L)) tout) \/
      dinv G pos (sc_dict c ++ out) (l_s L) tout))).

(* right after Z_NEED_DICT: the 6 bytes read, DICT with havedict 0 and the dictionary id, nothing written *)
Definition szd_PN : ses_ninv := fun c D O src pos out L tout =>
  sk_zdict c /\ pos = 6 /\ out = [] /\ tout = 0 /\ dw_nd (szd_wb c) (szd_id c) (l_s L).

(* what si_call asks of a call, for these invariants *)
Definition szd_concl (c: scase) (D O src: list Z) (pos: Z) (out: list Z) (asked: bool) (L: live) (z: zfields)
    (inp: list Z) (res: result) (winp: Values.val) : Prop :=
  let m := r_m res in
  let L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L) in
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END \/ r_ret res = Z_NEED_DICT) /\
   0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
   (exists rest, D = out ++ m_ow m ++ rest) /\
   (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR ->
      szd_P c D O src (pos + m_snx m) (out ++ m_ow m) asked L' (m_tout m)) /\
   (r_ret res = Z_NEED_DICT ->
      sk_zdict c /\ asked = false /\ szd_PN c D O src (pos + m_snx m) (out ++ m_ow m) L' (m_tout m)) /\
   (r_ret res = Z_STREAM_END ->
      out ++ m_ow m = D /\ pos + m_snx m = Zlength O /\ (asked = true <-> sk_zdict c) /\
      (forall gh, sc_gh c = Some gh -> g2_hdr_out gh (sc_h0 c) (m_s m) (m_h m))) /\
   (Zlength inp = 0 -> zf_ao z = 0 ->
      r_ret res <> Z_OK /\ m_ow m = [] /\ m_tin m = zf_tin z /\ m_tout m = zf_tout z)).

(* ---------------------------------------------------------------------------------------------- *)
(* Calls before Z_NEED_DICT                                                                         *)

Lemma szd_bytes_ok (l: list Z) : Forall szd_byte l -> bytes_ok l.
Proof. intros H. eapply Forall_impl; [|exact H]. intros b Hb. unfold szd_byte in Hb. cbn. lia. Qed.

Lemma szd_call_A c D O src pos L z inp flush res winp :
  sk_zdict c -> sc_ok c D O -> src_ok O src -> live_ok L -> zf_ok z -> Zlength inp <= 4294967295 ->
  0 <= pos -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  Zlib.proof.harness.inflate_pieces.Theory.pinv z L -> zf_tout z = 0 -> 0 <= pos < 6 ->
  l_s L = szd_hst (szd_wb c) (sublist 0 6 O) pos ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  szd_concl c D O src pos [] false L z inp res winp.
Proof.
  intros K OK SR LV ZF LI P0 PL IE PI T0 PR HS RUN.
  destruct (szd_case c D O src K OK SR) as (W8 & G0 & DF & NE & EW & L64 & LO & PO & BY & BS).
  destruct (szd_stream_c c D O src K OK SR) as (flg & T & bs & FL & EO & H6 & WF & IWR & GOK).
  pose proof GOK as (_ & _ & _ & _ & _ & _ & _ & _ & L6).
  rewrite H6 in HS.
  assert (BI: Forall szd_byte inp) by (rewrite IE; apply Forall_sublist; exact BS).
  pose proof (Zlength_nonneg inp) as I0.
  assert (S6: sublist 0 6 src = sublist 0 6 O).
  { rewrite <- PO. rewrite sublist_sublist by lia. f_equal; lia. }
  set (a := Z.min (Zlength inp) (6 - pos)).
  assert (PRE: sublist 0 a inp = sublist pos (pos + a) (szd_hdr (szd_wb c) flg (szd_id c))).
  { rewrite <- H6, <- S6. rewrite IE at 1. rewrite szd_subsub by (unfold a; lia).
    rewrite szd_subsub by (unfold a; lia). f_equal; lia. }
  pose proof (ui_call_ppost flush z L inp res PI LV ZF ltac:(lia) (szd_bytes_ok inp BI) RUN)
    as (_ & _ & _ & _ & Q5 & _ & Q7).
  pose proof PI as (PH & _).
  destruct (szd_hcall flush (szd_wb c) flg (szd_id c) pos z L inp res IWR FL
              (rtzk_adler_range (sc_dict c)) ZF ltac:(lia) HS BI PRE RUN)
    as [(R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7) | (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7)].
  - (* the input ran out *)
    assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R1 as [E|E]; rewrite E; discriminate).
    destruct (Q7 NM) as (_ & _ & Q9 & _ & Q11).
    right. cbv zeta. rewrite R3, app_nil_l.
    split; [destruct R1 as [E|E]; auto|].
    split; [lia|]. split; [rewrite R4; reflexivity|]. split; [exact R5|].
    split; [exists D; reflexivity|].
    split.
    { intros _. split; [exact K|]. split; [exact G0|]. cbn [l_s]. split; [rewrite Q5; exact PH|].
      split; [exact Q9|]. split; [exact Q11|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite R6; exact T0|].
      split; [lia|]. rewrite R7, H6, R2. reflexivity. }
    split; [intros E; destruct R1 as [E'|E']; rewrite E in E'; discriminate|].
    split; [intros E; destruct R1 as [E'|E']; rewrite E in E'; discriminate|].
    intros I1 A1. destruct (ui_idle_call flush z L inp res PI LV ZF I1 A1 RUN) as (J1 & J2 & J3).
    split; [exact J1|]. split; [reflexivity|]. exact (J3 NM).
  - (* Z_NEED_DICT *)
    right. cbv zeta. rewrite R3, app_nil_l.
    split; [auto|].
    split; [lia|]. split; [rewrite R4; reflexivity|]. split; [exact R5|].
    split; [exists D; reflexivity|].
    split; [intros [E|E]; rewrite R1 in E; discriminate|].
    split.
    { intros _. split; [exact K|]. split; [reflexivity|]. split; [exact K|].
      split; [lia|]. split; [reflexivity|]. split; [rewrite R6; exact T0|]. exact R7. }
    split; [intros E; rewrite R1 in E; discriminate|].
    intros I1 _. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Calls after the dictionary                                                                       *)

(* the input of a call at pos >= 6 is the same in src and in the context *)
Lemma szd_inp wb dict D O src G pos inp :
  szd_gok wb dict D O src G -> 6 <= pos -> pos + Zlength inp <= Zlength src ->
  inp = sublist pos (pos + Zlength inp) src -> inp = sublist pos (pos + Zlength inp) (dc_src G).
Proof.
  intros (_ & _ & _ & _ & _ & _ & LS & SB & _) P6 PL E.
  rewrite E at 1.
  assert (A: forall l : list Z, Zlength l = Zlength src ->
             sublist pos (pos + Zlength inp) l =
             sublist (pos - 6) (pos + Zlength inp - 6) (sublist 6 (Zlength src) l)).
  { intros l Hl. pose proof (Zlength_nonneg inp). rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite (A src eq_refl), (A (dc_src G) LS), SB. reflexivity.
Qed.

(* a call from the decode invariant (Decode7.decode_call7_stmt), in the terms of the session *)
Lemma szd_dec (DK: decode_call7_stmt) wb dict D O src G pos out L z inp flush res :
  szd_gok wb dict D O src G -> 6 <= pos -> dinv G pos (dict ++ out) (l_s L) (zf_tout z) -> live_ok L ->
  zf_ok z -> zf_ao z <= 4294967295 -> Zlength inp <= 4294967295 -> pos + Zlength inp <= Zlength src ->
  inp = sublist pos (pos + Zlength inp) src ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx (r_m res) <= Zlength inp /\ m_sow (r_m res) = Zlength (m_ow (r_m res)) /\
   m_aout (r_m res) = zf_ao z /\ (exists rest, D = out ++ m_ow (r_m res) ++ rest) /\
   dinv G (pos + m_snx (r_m res)) (dict ++ (out ++ m_ow (r_m res))) (m_s (r_m res)) (m_tout (r_m res)) /\
   (r_ret res = Z_STREAM_END -> out ++ m_ow (r_m res) = D /\ pos + m_snx (r_m res) = Zlength O)).
Proof.
  intros GOK P6 DV LV ZF AO LI PL IE RUN.
  pose proof GOK as (OK & _ & _ & _ & FU & SL & LS & _).
  pose proof (szd_inp wb dict D O src G pos inp GOK P6 PL IE) as IE'.
  destruct (DK G pos (dict ++ out) L z inp flush res OK DV LV ZF ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite LS; exact PL) IE' RUN)
    as [M | (R & SNX & SOW & MAO & (rest & PRE) & DV' & _ & SE & _)]; [left; exact M|].
  right. split; [exact R|]. split; [exact SNX|]. split; [exact SOW|]. split; [exact MAO|].
  split; [|split].
  - exists rest. rewrite FU, <- !app_assoc in PRE. apply app_inv_head in PRE. exact PRE.
  - rewrite app_assoc. exact DV'.
  - intros E. destruct (SE E) as [F1 F2]. split; [|lia].
    rewrite FU, <- app_assoc in F1. apply app_inv_head in F1. exact F1.
Qed.

(* the conclusion after the dictionary from a call's decode facts *)
Lemma szd_fin c D O src G pos out L z inp flush res winp :
  sk_zdict c -> sc_gh c = None -> szd_gok (szd_wb c) (sc_dict c) D O src G -> 6 <= pos ->
  Zlib.proof.harness.inflate_pieces.Theory.pinv z L -> live_ok L -> zf_ok z -> Zlength inp <= 4294967295 ->
  bytes_ok inp -> run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) ->
  0 <= m_snx (r_m res) <= Zlength inp -> m_sow (r_m res) = Zlength (m_ow (r_m res)) ->
  m_aout (r_m res) = zf_ao z -> (exists rest, D = out ++ m_ow (r_m res) ++ rest) ->
  dinv G (pos + m_snx (r_m res)) (sc_dict c ++ (out ++ m_ow (r_m res))) (m_s (r_m res)) (m_tout (r_m res)) ->
  (r_ret res = Z_STREAM_END -> out ++ m_ow (r_m res) = D /\ pos + m_snx (r_m res) = Zlength O) ->
  szd_concl c D O src pos out true L z inp res winp.
Proof.
  intros K G0 GOK P6 PI LV ZF LI BI RUN R SNX SOW MAO EX DV END.
  pose proof (ui_call_ppost flush z L inp res PI LV ZF ltac:(lia) BI RUN) as (_ & _ & _ & _ & Q5 & _ & Q7).
  pose proof PI as (PH & _).
  assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [E|[E|E]]; rewrite E; discriminate).
  destruct (Q7 NM) as (_ & _ & Q9 & _ & Q11).
  right. cbv zeta.
  split; [destruct R as [E|[E|E]]; auto|].
  split; [exact SNX|]. split; [exact SOW|]. split; [exact MAO|]. split; [exact EX|].
  split.
  { intros _. split; [exact K|]. split; [exact G0|]. cbn [l_s]. split; [rewrite Q5; exact PH|].
    split; [exact Q9|]. split; [exact Q11|].
    right. split; [reflexivity|]. split; [lia|]. exists G. split; [exact GOK|]. right. exact DV. }
  split; [intros E; destruct R as [E'|[E'|E']]; rewrite E in E'; discriminate|].
  split.
  { intros E. destruct (END E) as [E1 E2]. split; [exact E1|]. split; [exact E2|].
    split; [split; [intros _; exact K | intros _; reflexivity]|].
    intros gh Eg. rewrite G0 in Eg. discriminate. }
  intros I1 A1. destruct (ui_idle_call flush z L inp res PI LV ZF I1 A1 RUN) as (J1 & J2 & J3).
  split; [exact J1|]. split; [exact J2|]. exact (J3 NM).
Qed.

Lemma szd_adl_ok z : zf_ok z -> zf_ok (z_adl z 1).
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6). unfold zf_ok, z_adl. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
  repeat split; try lia. all: change Integers.Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Lemma szd_call_B (DK: decode_call7_stmt) c D O src pos out L z inp flush res winp :
  sk_zdict c -> sc_ok c D O -> src_ok O src -> live_ok L -> zf_ok z -> zf_ao z <= 4294967295 ->
  Zlength inp <= 4294967295 -> pos + Zlength inp <= Zlength src -> inp = sublist pos (pos + Zlength inp) src ->
  Zlib.proof.harness.inflate_pieces.Theory.pinv z L -> 6 <= pos ->
  forall G, szd_gok (szd_wb c) (sc_dict c) D O src G ->
  ((pos = 6 /\ out = [] /\ i_mode (l_s L) = DICT /\ i_havedict (l_s L) = 1 /\ i_wsize (l_s L) <> 0 /\
    rtzs_wstruct (l_s L) /\ i_win (l_s L) = true /\ 0 <= i_total (l_s L) <= Integers.Int64.max_unsigned /\
    dinv G 6 (sc_dict c) (d1_ty (l_s L)) (zf_tout z)) \/
   dinv G pos (sc_dict c ++ out) (l_s L) (zf_tout z)) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  szd_concl c D O src pos out true L z inp res winp.
Proof.
  intros K OK SR LV ZF AO LI PL IE PI P6 G GOK DV RUN.
  destruct (szd_case c D O src K OK SR) as (W8 & G0 & DF & NE & EW & L64 & LO & PO & BY & BS).
  assert (BI: bytes_ok inp) by (rewrite IE; apply szd_bytes_ok; apply Forall_sublist; exact BS).
  destruct DV as [(E6 & Eo & MD & HD & WN & WS & WI & TT & DV) | DV].
  - subst pos out.
    destruct (szd_d1 flush z L inp res MD HD WN WS WI TT LV ZF RUN)
      as [RUN' | (R1 & R2 & R3 & R4 & R5 & R6 & R7)].
    + assert (DV1: dinv G 6 (sc_dict c ++ []) (l_s (set_l_s L (d1_ty (l_s L)))) (zf_tout (z_adl z 1)))
        by (rewrite app_nil_r; exact DV).
      destruct (szd_dec DK _ _ D O src G 6 [] _ _ inp flush res GOK ltac:(lia) DV1 (rtzk_live L LV MD)
                  (szd_adl_ok z ZF) AO LI PL IE RUN')
        as [M | (R & SNX & SOW & MAO & EX & DV' & END)].
      * left. exact M.
      * exact (szd_fin c D O src G 6 [] L z inp flush res winp K G0 GOK ltac:(lia) PI LV ZF LI BI RUN
                 R SNX SOW MAO EX DV' END).
    + apply (szd_fin c D O src G 6 [] L z inp flush res winp K G0 GOK ltac:(lia) PI LV ZF LI BI RUN).
      * right; left; exact R1.
      * rewrite R2. pose proof (Zlength_nonneg inp). lia.
      * rewrite R3, R4. reflexivity.
      * exact R5.
      * rewrite R3. exists D. reflexivity.
      * rewrite R2, R3, R6, R7, Z.add_0_r, app_nil_r. exact DV.
      * intros E. rewrite R1 in E. discriminate.
  - destruct (szd_dec DK _ _ D O src G pos out L z inp flush res GOK P6 DV LV ZF AO LI PL IE RUN)
      as [M | (R & SNX & SOW & MAO & EX & DV' & END)].
    + left. exact M.
    + exact (szd_fin c D O src G pos out L z inp flush res winp K G0 GOK P6 PI LV ZF LI BI RUN
               R SNX SOW MAO EX DV' END).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateInit2 and inflateSetDictionary                                                            *)

Lemma szd_mode_rng m : m = HEAD \/ m = DICTID \/ m = DICT -> HEAD <= m <= BAD.
Proof. unfold HEAD, DICTID, DICT, BAD. lia. Qed.

Lemma szd_swfW s : i_mode s = HEAD \/ i_mode s = DICTID \/ i_mode s = DICT -> swfW s.
Proof.
  intros M. unfold swfW. unfold HEAD, DICTID, DICT in M.
  split; intros E; rewrite E in M; unfold EXLEN, EXTRA in M; lia.
Qed.

Lemma szd_init c D O src sp :
  sk_zdict c -> sc_ok c D O -> src_ok O src ->
  wbits_ok (rts_iw (sc_wbits c)) = true /\ swfW (l_s (init_live sp (rts_iw (sc_wbits c)))) /\
  (sc_gh c = None -> ~ sk_raw c ->
   szd_P c D O src 0 [] false (init_live sp (rts_iw (sc_wbits c))) 0).
Proof.
  intros K OK SR.
  destruct (szd_case c D O src K OK SR) as (W8 & G0 & _).
  destruct (szd_stream_c c D O src K OK SR) as (flg & T & bs & FL & EO & H6 & WF & IWR & GOK).
  change (rts_iw (sc_wbits c)) with (szd_wb c).
  pose proof (dwi_init_s sp (szd_wb c) IWR) as ES.
  destruct (szd_init_fields (szd_wb c) IWR) as (Fm & _ & _ & Fh & _).
  assert (SW: swfW (l_s (init_live sp (szd_wb c)))) by (apply szd_swfW; rewrite ES, Fm; auto).
  split; [unfold wbits_ok; rewrite dwi_reset2_wb by exact IWR; reflexivity|].
  split; [exact SW|].
  intros _ _. split; [exact K|]. split; [exact G0|]. rewrite ES in SW |- *.
  split; [exact Fh|]. split; [rewrite Fm; apply szd_mode_rng; auto|]. split; [exact SW|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  rewrite szd_init_hst by exact IWR. reflexivity.
Qed.

Lemma szd_setdict c D O src pos out L tout z alloc_ok winp :
  sk_zdict c -> sc_ok c D O -> src_ok O src -> szd_PN c D O src pos out L tout -> live_ok L -> zf_tout z = tout ->
  let sd := setdict_f (sc_dict c) alloc_ok winp z L in
  (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
  (fst3 sd = Z_OK -> snd3 sd = z /\ swfW (l_s (thd3 sd)) /\ szd_P c D O src pos out true (thd3 sd) tout).
Proof.
  intros K OK SR (_ & E6 & Eo & T0 & ND) LV ZT. subst pos out tout. cbv zeta.
  destruct (szd_case c D O src K OK SR) as (W8 & G0 & DF & NE & _).
  destruct (szd_stream_c c D O src K OK SR) as (flg & T & bs & FL & EO & H6 & WF & IWR & GOK).
  destruct (szd_set (szd_wb c) (sc_dict c) bs (sublist (Zlength O) (Zlength src) src) (l_s L) IWR WF NE ND)
    as (SC & DI).
  pose proof ND as (Nm & _ & Nh & _ & _ & Nt & Nws & _ & _ & Nw & Nwd & Nb & _ & _ & _ & _).
  destruct (rtzs_sd_fields (l_s L) (sc_dict c) Nws Nwd ltac:(lia))
    as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16).
  unfold setdict_f. rewrite SC, Nw.
  destruct alloc_ok; [|split; [right; reflexivity | intros X; discriminate X]].
  split; [left; reflexivity|]. intros _. unfold snd3, thd3. cbn [fst snd l_s set_l_winp set_l_s].
  set (s' := setdict_s (l_s L) (sc_dict c)) in *.
  assert (Sm: i_mode s' = DICT) by (rewrite S1; exact Nm).
  assert (SW: swfW s') by (apply szd_swfW; auto).
  split; [reflexivity|]. split; [exact SW|].
  split; [exact K|]. split; [exact G0|].
  change (l_s (set_l_winp (set_l_s L s') winp)) with s'.
  split; [rewrite S8; exact Nh|].
  split; [rewrite Sm; apply szd_mode_rng; auto|]. split; [exact SW|].
  right. split; [reflexivity|]. split; [lia|].
  eexists. split; [exact GOK|]. left.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Sm|]. split; [exact S4|].
  split; [rewrite S13, Nb; pose proof (Z.pow_pos_nonneg 2 (szd_wb c) ltac:(lia) ltac:(lia)); lia|].
  split; [exact S15|]. split; [exact S12|].
  split; [rewrite S7, Nt; change Integers.Int64.max_unsigned with 18446744073709551615; lia|].
  exact DI.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                       *)

Theorem szd_itheory : decode_call7_stmt -> ses_itheory_zdict_stmt.
Proof.
  intros DK. exists szd_P, szd_PN. constructor.
  - exact szd_init.
  - intros c D O src sp gh headp hsh xb nb cb K OK SR GH.
    destruct (szd_case c D O src K OK SR) as (_ & G0 & _). rewrite G0 in GH. discriminate.
  - intros c D O src sp z alloc_ok winp (_ & W1) _ _ (_ & W0). rewrite W0 in W1. discriminate.
  - intros c D O src pos out asked L tout _ (_ & G0 & PH & _). rewrite G0. exact PH.
  - intros c D O src pos out asked L z inp flush res winp K OK SR HP LC SW ZF AO LI P0 PL IE RUN.
    destruct HP as (_ & G0 & PH & PM & PS & [(Ea & Eo & Et & Pr & Hs) | (Ea & P6 & G & GOK & DV)]).
    + subst asked out.
      assert (LV: live_ok L) by (unfold live_c in LC; rewrite G0 in LC; exact LC).
      exact (szd_call_A c D O src pos L z inp flush res winp K OK SR LV ZF LI P0 PL IE (conj PH (conj PM PS))
               Et Pr Hs RUN).
    + subst asked.
      assert (LV: live_ok L) by (unfold live_c in LC; rewrite G0 in LC; exact LC).
      exact (szd_call_B DK c D O src pos out L z inp flush res winp K OK SR LV ZF AO LI PL IE
               (conj PH (conj PM PS)) P6 G GOK DV RUN).
  - intros c D O src pos out L tout _ (_ & _ & _ & _ & ND). apply ND.
  - exact szd_setdict.
Qed.

Theorem szd_itheory_closed : ses_itheory_zdict_stmt.
Proof. exact (szd_itheory (proj2 Zlib.proof.wide.Decode7.decode7)). Qed.

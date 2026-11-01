(* RT-I, part rti_zdict: RTIIface.if_zdict (zlib stream with FDICT: Z_NEED_DICT after the 6 header bytes, inflateSetDictionary, the second call), from the decode theory.  NB the zlib header FLG may have FCHECK = 31 (78 3f), which Format.zlib_hdr does not produce: the second call does not read the first 2 bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.rfc1951.Decode.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTIZDictDefs Zlib.proof.roundtrip.RTIZDictKit Zlib.proof.roundtrip.RTIZDictD1 Zlib.proof.roundtrip.RTIZDictFirst Zlib.proof.roundtrip.RTIZDictSet.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rtz_sub6 (h X : list Z) : Zlength h = 2 -> 4 <= Zlength X ->
  sublist 6 (Zlength (h ++ X)) (h ++ X) = sublist 4 (Zlength X) X.
Proof.
  intros Hh HX. rewrite Zlength_app, Hh. rewrite sublist_app2 by lia. rewrite Hh. f_equal; lia.
Qed.

Lemma rti_zdict : decode_parts ->
  forall wb dict D O sp z res,
    RF.dfinal dict 1 wb None D O -> dict <> [] -> Zlength dict <= 32768 ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 -> live_ok (init_live sp 0) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (init_live sp 0) O) res ->
    r_ret res = Z_MEM_ERROR \/
    (r_ret res = Z_NEED_DICT /\ m_snx (r_m res) = 6 /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\
     m_aout (r_m res) = Zlength D /\ m_tout (r_m res) = 0 /\
     m_adler (r_m res) = Zlib.proof.adler32.Model.ref_adler32 1 dict /\
     forall L1 z1 alloc_ok winp,
       l_s L1 = m_s (r_m res) -> l_h L1 = m_h (r_m res) -> live_ok L1 ->
       let sd := setdict_f dict alloc_ok winp z1 L1 in
       (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
       (fst3 sd = Z_OK -> forall z2 res2,
          live_ok (thd3 sd) -> zcall_ok z2 (sublist 6 (Zlength O) O) D ->
          run2 4 lenfix_list distfix_list (m_init z2 (thd3 sd) (sublist 6 (Zlength O) O)) res2 ->
          rdone (sublist 6 (Zlength O) O) D res2)).
Proof.
  intros DP wb dict D O sp z res DF Hne Hdl HD HO LV ZC RUN.
  destruct (decode_of_parts DP) as [_ DC].
  destruct DF as (Hwb & bs & WF & Hdata & DW).
  destruct DW as (_ & flg & FL & HOeq).
  assert (EM : negb (match dict with [] => true | _ => false end) = true) by (destruct dict; [congruence|reflexivity]).
  assert (EB : match dict with [] => [] | _ => be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 end =
               be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4) by (destruct dict; [congruence|reflexivity]).
  rewrite EM in FL. rewrite EB in HOeq. clear EM EB.
  set (id := Zlib.proof.adler32.Model.ref_adler32 1 dict) in *.
  set (T := deflate_bytes bs ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 D) 4) in *.
  assert (HT : 4 <= Zlength T).
  { unfold T. rewrite Zlength_app. unfold be_bytes, le_bytes. rewrite Zlength_rev, Zlength_map.
    pose proof (Zlength_nonneg (deflate_bytes bs)). cbn. lia. }
  assert (HBE : Zlength (be_bytes id 4) = 4) by (unfold be_bytes, le_bytes; rewrite Zlength_rev, Zlength_map; reflexivity).
  assert (HOL : Zlength O = 6 + Zlength T).
  { rewrite HOeq, !Zlength_app, HBE. cbn. lia. }
  destruct ZC as (ZF & ZA & ZO & ZT).
  pose proof (rtz_first Z_FINISH wb flg id T z sp res Hwb FL (rtzk_adler_range dict) ZF) as R1.
  rewrite HOeq in RUN. specialize (R1 RUN).
  destruct R1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & ND).
  right. rewrite R1, R2, R3, R4, R5, R6, R7, ZO, ZT.
  do 7 (split; [reflexivity|]).
  intros L1 z1 alloc_ok winp HL1s HL1h LV1.
  rewrite <- HL1s in ND.
  destruct (rtz_set wb dict bs (l_s L1) Hwb WF Hne Hdl ND) as (SC & DI).
  pose proof ND as (Nm & _ & _ & _ & _ & _ & _ & _ & _ & Nw & _ & _ & _ & _ & Nb & _).
  cbv zeta. unfold setdict_f. rewrite SC, Nw.
  destruct alloc_ok; [|split; [right; reflexivity | intros X; discriminate X]].
  split; [left; reflexivity|]. intros _ z2 res2 LV2 ZC2 RUN2.
  cbn [thd3 fst3] in *.
  set (s' := setdict_s (l_s L1) dict) in *.
  set (L2 := set_l_winp (set_l_s L1 s') winp) in *.
  change (thd3 (Z_OK, z1, L2)) with L2 in LV2, RUN2.
  assert (EL2 : l_s L2 = s') by reflexivity.
  destruct (rtzk_uw_keep (l_s L1) dict) as (K1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & _).
  assert (Sm : i_mode s' = DICT) by (unfold s', setdict_s; cbn; rewrite K1; exact Nm).
  assert (Sb : i_bits s' = 0) by (unfold s', setdict_s; cbn; rewrite K11; exact Nb).
  assert (Sh : i_havedict s' = 1) by reflexivity.
  set (inp := sublist 6 (Zlength O) O) in *.
  assert (Hinp : Zlength inp = Zlength T).
  { unfold inp. rewrite Zlength_sublist by lia. lia. }
  apply rtz_d1 in RUN2; [| rewrite EL2; exact Sm | rewrite EL2; exact Sh | rewrite EL2, Sb; lia | lia].
  set (G := zd_ctx wb dict bs).
  set (src := stream_bytes (zd_w dict wb) dict bs).
  assert (Esrc : src = zlib_hdr wb 0 true ++ be_bytes id 4 ++ T).
  { unfold src, stream_bytes, zd_w. cbv zeta. rewrite Hdata. reflexivity. }
  assert (HSL : Zlength src = 6 + Zlength T).
  { rewrite Esrc, !Zlength_app, HBE, rtzk_len_hdr. lia. }
  assert (Einp : inp = sublist 6 (6 + Zlength inp) src).
  { assert (E1 : inp = sublist 4 (Zlength (be_bytes id 4 ++ T)) (be_bytes id 4 ++ T)).
    { unfold inp. rewrite HOeq. apply rtz_sub6; [reflexivity | rewrite Zlength_app; lia]. }
    replace (6 + Zlength inp) with (Zlength src) by lia.
    rewrite E1 at 1. rewrite Esrc. symmetry. apply rtz_sub6; [apply rtzk_len_hdr | rewrite Zlength_app; lia]. }
  assert (Hslen : slen G = 6 + Zlength T) by (unfold slen; exact HSL).
  assert (GOK : dctx_ok G).
  { unfold dctx_ok, G, zd_ctx. cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src]. fold src.
    split; [unfold stream_ok, zd_w; cbn; split; [lia|]; split; [split; [lia|split; [lia|reflexivity]]|];
            split; [reflexivity|exact WF]|].
    split; [unfold accepts; cbn; right; left; reflexivity|].
    split; [intros h E; discriminate E|].
    split; [intros wb' fl did E; inversion E; right; reflexivity|].
    split; [apply Z.le_refl|]. split; [lia|]. split.
    - rewrite Esrc. apply Forall_app; split; [apply rtzk_hdr; lia|].
      apply Forall_app; split; [apply rtzk_be_bytes|]. unfold T.
      apply Forall_app; split; [unfold deflate_bytes; apply rtzk_pack | apply rtzk_be_bytes].
    - apply sublist_same; reflexivity. }
  destruct ZC2 as (ZF2 & ZA2 & ZO2 & ZT2).
  assert (ZFa : zf_ok (z_adl z2 1)).
  { destruct ZF2 as (A1 & A2 & A3 & A4 & A5 & A6). unfold zf_ok, z_adl. cbn. repeat split; try lia; rep_lia. }
  assert (LVa : live_ok (set_l_s L2 (d1_ty (l_s L2)))) by (apply rtzk_live; [exact LV2 | rewrite EL2; exact Sm]).
  assert (DIa : dinv G 6 dict (l_s (set_l_s L2 (d1_ty (l_s L2)))) (zf_tout (z_adl z2 1))).
  { cbn [l_s set_l_s zf_tout z_adl]. rewrite EL2, ZT2. exact DI. }
  assert (AOa : zf_ao (z_adl z2 1) <= 2 ^ 31 - 1) by (cbn [zf_ao z_adl]; rewrite ZO2; lia).
  assert (HLs : 6 + Zlength inp <= Zlength (dc_src G)) by (change (dc_src G) with src; lia).
  destruct (DC G 6 dict _ _ inp Z_FINISH res2 GOK DIa LVa ZFa AOa ltac:(lia) HLs Einp RUN2)
    as [MEM | (RET & SNX & SOW & AOUT & PFX & DINV & HWIN & FIN & NFIN & HDT)].
  { left. exact MEM. }
  cbn [zf_ao z_adl] in AOUT, NFIN. rewrite ZO2 in AOUT, NFIN.
  assert (Efull : full G = dict ++ D).
  { unfold full, G, zd_ctx. cbn [dc_hist dc_bs]. rewrite rtzk_expand_data, Hdata. reflexivity. }
  assert (REnd : r_ret res2 = Z_STREAM_END).
  { destruct (Z.eq_dec (r_ret res2) Z_STREAM_END) as [E|E]; [exact E|].
    exfalso. destruct (NFIN E) as [(A & B) | [(A & B) | B]].
    - rewrite Hslen in B. lia.
    - rewrite Efull, !Zlength_app in B. lia.
    - unfold Z_FINISH, Z_BLOCK, Z_TREES in B. lia. }
  destruct (FIN REnd) as (F1 & F2).
  rewrite Efull in F1. apply app_inv_head in F1.
  right. split; [exact REnd|]. split; [rewrite Hslen in F2; lia|].
  split; [exact F1|]. split; [rewrite SOW, F1; reflexivity|]. exact AOUT.
Qed.

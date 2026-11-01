(* Law inflate_dict: the theory, an invariant with the facts of ITFacts.v (over Model2.run2). *)
Require Import Zlib.proof.harness.inflate_dict.ITFacts.
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Require Import Zlib.proof.harness.inflate_dict.ITWin Zlib.proof.harness.inflate_dict.ITCtx
  Zlib.proof.harness.inflate_dict.ITFrame Zlib.proof.harness.inflate_dict.ITDict
  Zlib.proof.harness.inflate_dict.ITD1 Zlib.proof.harness.inflate_dict.ITPre
  Zlib.proof.harness.inflate_dict.ITPost.
Require Zlib.proof.harness.inflate_dict.ITDecV4.
Import ListNotations.
Local Open Scope Z_scope.

(* the decode theory (rfc1951/Decode.v) under DecodeDefs v4: ITDecV4.v *)
Lemma it_decode_call : decode_call_stmt.
Proof. exact Zlib.proof.harness.inflate_dict.ITDecV4.it_decode_call_v4. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Small facts                                                                                    *)

Lemma it_I_ok G pos opos dset nd z L : it_I G pos opos dset nd z L -> it_ok G.
Proof. intros (A & _). exact A. Qed.

Lemma it_src_bytes G : it_ok G -> bytes_ok (it_src G).
Proof.
  intros H. pose proof (itc_ok G H) as (_ & _ & _ & _ & _ & _ & B & _). exact B.
Qed.

Lemma it_src_len G : it_ok G -> Zlength (it_src G) <= 2 ^ 19.
Proof. intros (_ & _ & _ & _ & A & _). exact A. Qed.

Lemma bytes_ok_sublist l i j : bytes_ok l -> bytes_ok (sublist i j l).
Proof. intros H. unfold bytes_ok in *. apply Forall_sublist. exact H. Qed.

Lemma d1_ty_head s : i_head (d1_ty s) = i_head s.
Proof. reflexivity. Qed.

Lemma d1_ty_whave s : i_whave (d1_ty s) = i_whave s.
Proof. reflexivity. Qed.

Lemma d1_ty_dict_bytes s : dict_bytes (d1_ty s) = dict_bytes s.
Proof. reflexivity. Qed.

Lemma post_head G pos opos tout s : post_st G pos opos tout s -> i_head s = false.
Proof. intros (_ & (_ & (_ & H & _) & _) & _). exact H. Qed.

(* the window fact *)
Lemma win_it G opos L : it_ok G -> win_st G (l_s L) (it_out G opos) -> it_win G opos L.
Proof.
  intros OK W. destruct (itw_get G (l_s L) (it_out G opos) OK W) as [A B].
  unfold it_win. unfold it_out in A, B. split; [exact A | exact B].
Qed.

Lemma zf_ok_adl z a : zf_ok z -> 0 <= a <= Int64.max_unsigned -> zf_ok (z_adl z a).
Proof. unfold zf_ok, z_adl; simpl. tauto. Qed.

(* it_post from the call's numbers: snx bytes consumed, sow bytes produced *)
Lemma mk_post (I: it_inv) G pos opos dset ain aout r (z': zfields) L' ow snx sow :
  zf_ai z' = ain - snx -> zf_ao z' = aout - sow -> 0 <= snx <= ain -> 0 <= sow <= aout ->
  Zlength ow = sow -> bytes_ok ow ->
  ((r = Z_NEED_DICT /\ g_zlib G = true /\ dset = false /\ sow = 0 /\ opos = 0 /\
    zf_adler z' = it_dictid G /\ I G (pos + snx) 0 false true z' L') \/
   ((r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END) /\
    sow <= Zlength (it_data G) - opos /\ ow = sublist opos (opos + sow) (it_data G) /\
    (r = Z_STREAM_END -> opos + sow = Zlength (it_data G) /\ pos + snx = Zlength (it_src G) /\
                         (dset = true -> g_zlib G = false -> it_win G (opos + sow) L')) /\
    (r <> Z_STREAM_END -> I G (pos + snx) (opos + sow) dset false z' L'))) ->
  it_post I G pos opos dset ain aout r z' L' ow.
Proof.
  intros A B C D E F H. unfold it_post.
  replace (ain - zf_ai z') with snx by lia. replace (aout - zf_ao z') with sow by lia.
  split; [lia|]. split; [lia|]. split; [exact E|]. split; [exact F|].
  destruct H as [H|H]; [left; tauto | right; tauto].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts                                                                                      *)

Lemma f_head G pos opos dset nd z L : it_I G pos opos dset nd z L -> i_head (l_s L) = false.
Proof.
  intros (_ & _ & _ & _ & H).
  destruct dset, nd; [contradiction | | |].
  - destruct H as [P | (_ & _ & (_ & _ & _ & P))].
    + eapply post_head; exact P.
    + rewrite <- d1_ty_head. eapply post_head; exact P.
  - destruct H as (_ & _ & _ & _ & ((_ & Hh & _) & _)). exact Hh.
  - destruct H as (_ & _ & _ & ((_ & Hh & _) & _)). exact Hh.
Qed.

Lemma f_window G pos opos nd z L : it_I G pos opos true nd z L -> it_win G opos L.
Proof.
  intros (OK & _ & _ & _ & H). destruct nd; [contradiction|].
  destruct H as [(_ & _ & W) | (_ & -> & (_ & _ & _ & (_ & _ & W)))].
  - apply win_it; auto.
  - destruct (itw_get G _ _ OK W) as [A B]. unfold it_win, it_out in *.
    rewrite d1_ty_whave, d1_ty_dict_bytes in *. split; [exact A | exact B].
Qed.

Lemma f_bad G pos z L alloc_ok winp :
  it_I G pos 0 false true z L -> setdict_f (it_bad G) alloc_ok winp z L = (Z_DATA_ERROR, z, L).
Proof.
  intros (OK & _ & _ & _ & (Zl & _ & _ & _ & ND)).
  destruct itd_facts as (_ & _ & B & _).
  unfold setdict_f. rewrite (B G (l_s L) OK Zl ND). reflexivity.
Qed.

Lemma f_good G pos z L alloc_ok winp :
  it_I G pos 0 false true z L -> live_ok L -> zf_ok z ->
  let '(r, z', L') := setdict_f (g_dict G) alloc_ok winp z L in
  (r = Z_OK \/ r = Z_MEM_ERROR) /\ (r = Z_OK -> it_I G pos 0 true false z' L').
Proof.
  intros (OK & WB & R1 & R2 & (Zl & _ & Hpos & Ht & ND)) _ _.
  destruct itd_facts as (_ & _ & _ & Gd). destruct (Gd G (l_s L) OK Zl WB ND) as [C D1].
  assert (Wf: i_win (l_s L) = false) by (destruct ND as ((_ & _ & _ & _ & _ & _ & _ & _ & W & _) & _); exact W).
  unfold setdict_f. rewrite C, Wf.
  destruct alloc_ok.
  - split; [left; reflexivity|]. intros _.
    split; [exact OK|]. split; [exact WB|]. split; [exact R1|]. split; [exact R2|].
    right. split; [exact Hpos|]. split; [reflexivity|]. rewrite Ht. exact D1.
  - split; [right; reflexivity|]. intros E. discriminate.
Qed.

(* the stream fields of the call *)
Lemma zc_ok z ni ai no ao : zf_ok z -> 0 <= ai <= 2 ^ 19 -> 0 <= ao <= 2 ^ 20 -> zf_ok (it_set_zf_call z ni ai no ao).
Proof. unfold zf_ok, it_set_zf_call; simpl. intros. rep_lia. Qed.

Lemma f_inflate G pos opos dset z L strmp flush lim ib inp o aout r z' st' ow :
  it_I G pos opos dset false z L -> live_ok L -> zf_ok z -> strmp <> nullval ->
  pos <= lim <= Zlength (it_src G) -> 0 <= aout <= 2 ^ 20 -> Int.min_signed <= flush <= Int.max_signed ->
  ib <> InNull -> inp = sublist pos lim (it_src G) ->
  inflate_rel flush strmp (it_set_zf_call z (in_ptr ib 0) (lim - pos) (out_ptr o 0) aout) (Some L) ib inp
    (Some o) r z' st' ow ->
  exists L', st' = Some L' /\ (r <> Z_MEM_ERROR -> it_post it_I G pos opos dset (lim - pos) aout r z' L' ow).
Proof.
  intros HI LV ZK SP Hlim Hao Hfl Hib Hinp REL.
  pose proof HI as (OK & WB & R1 & R2 & HC).
  pose proof (it_src_len G OK) as SL. pose proof (it_src_bytes G OK) as SB.
  set (zc := it_set_zf_call z (in_ptr ib 0) (lim - pos) (out_ptr o 0) aout) in REL.
  assert (ZC: zf_ok zc) by (apply zc_ok; auto; lia).
  assert (LI: Zlength inp = lim - pos) by (subst inp; rewrite Zlength_sublist; lia).
  assert (BI: bytes_ok inp) by (subst inp; apply bytes_ok_sublist; exact SB).
  assert (EI: inp = sublist pos (pos + Zlength inp) (it_src G)) by (rewrite LI; replace (pos + (lim - pos)) with lim by lia; exact Hinp).
  destruct REL as [(BAD & _) | (NB & L0 & o0 & res & winp & EL & EO & RUN & SNX & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad, is_live in BAD. destruct (eq_dec strmp nullval) as [E|_]; [contradiction|].
    destruct BAD as [B|[B|[B _]]]; [discriminate | discriminate | contradiction]. }
  injection EL as <-. injection EO as <-.
  eexists; split; [exact Est|]. intros Hmem. subst r z' ow.
  set (L' := Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  assert (EL': l_s L' = m_s (r_m res)) by reflexivity.
  destruct (itf_frame flush zc L inp res LV ZC ltac:(unfold zc, it_set_zf_call; simpl; rep_lia)
              ltac:(rep_lia) BI RUN) as (Fi & Fa & _ & Fs).
  assert (Zai: zf_ai (z_after zc ib o res) = (lim - pos) - m_snx (r_m res))
    by (unfold z_after; simpl; rewrite Fi, LI; reflexivity).
  assert (Zao: zf_ao (z_after zc ib o res) = aout - m_sow (r_m res))
    by (unfold z_after; simpl; rewrite Fa; reflexivity).
  assert (Zto: zf_tout (z_after zc ib o res) = m_tout (r_m res)) by reflexivity.
  destruct (Fs Hmem) as (_ & SW). rewrite Fa in SW. simpl in SW.
  destruct dset.
  - destruct HC as [P | (Hp & Ho & D1)].
    + (* the dictionary set, between calls *)
      destruct (itp_call it_decode_call itf_frame G pos opos zc L flush inp res OK (itc_ok G OK) LV ZC
                  ltac:(simpl; lia) P ltac:(lia) ltac:(lia) EI RUN Hmem)
        as (_ & Q1 & Q2 & _ & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
      apply (mk_post _ _ _ _ _ _ _ _ _ _ _ (m_snx (r_m res)) (Zlength (m_ow (r_m res))) Zai);
        [rewrite <- Q2; exact Zao | lia | lia | reflexivity | exact Q3 |].
      right. split; [exact Q4|]. split; [lia|]. split; [exact Q6|]. split.
      * intros E. destruct (Q7 E) as (A & B & C). split; [lia|]. split; [lia|].
        intros _ Zr. apply win_it; [exact OK|]. rewrite EL'. exact (C Zr).
      * intros E. split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
        left. rewrite Zto. exact (Q8 E).
    + (* zlib, the first call after the dictionary *)
      subst pos opos.
      pose proof D1 as D1'. destruct D1 as (Zl & Md & Hd & P1).
      destruct itd1_facts as (LV1 & C1).
      destruct (C1 G zc L flush inp res OK LV ZC D1' RUN) as [RUN1 | (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8)].
      * set (L1 := set_l_s L (d1_ty (l_s L))) in RUN1.
        assert (LV1': live_ok L1) by (apply LV1; [exact LV | exact Md]).
        assert (ZC1: zf_ok (z_adl zc 1)) by (apply zf_ok_adl; [exact ZC | rep_lia]).
        destruct (itp_call it_decode_call itf_frame G 6 0 (z_adl zc 1) L1 flush inp res OK (itc_ok G OK) LV1' ZC1
                    ltac:(simpl; lia) P1 ltac:(lia) ltac:(lia) EI RUN1 Hmem)
          as (_ & Q1 & Q2 & _ & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        apply (mk_post _ _ _ _ _ _ _ _ _ _ _ (m_snx (r_m res)) (Zlength (m_ow (r_m res))) Zai);
          [rewrite <- Q2; exact Zao | lia | lia | reflexivity | exact Q3 |].
        right. split; [exact Q4|]. split; [lia|]. split; [exact Q6|]. split.
        -- intros E. destruct (Q7 E) as (A & B & C). split; [lia|]. split; [lia|].
           intros _ Zr. rewrite Zl in Zr. discriminate.
        -- intros E. split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
           left. rewrite Zto. exact (Q8 E).
      * apply (mk_post _ _ _ _ _ _ _ _ _ _ _ 0 0);
          [rewrite Zai, T3; lia | rewrite Zao, T5; lia | lia | lia | rewrite T4; reflexivity |
           rewrite T4; constructor |].
        right. rewrite T1. split; [right; left; reflexivity|]. split; [lia|].
        split; [rewrite T4; reflexivity|]. split; [intros E; discriminate|].
        intros _. split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
        left. rewrite Zto, T7, EL'. exact T8.
  - (* zlib before the dictionary *)
    destruct HC as (Zl & Ho & Ht & HPre). subst opos.
    destruct (itpre_call G pos zc L flush inp res OK Zl WB LV ZC Ht HPre ltac:(lia) EI RUN)
      as (_ & P1 & P2 & P3 & _ & P4 & P5).
    apply (mk_post _ _ _ _ _ _ _ _ _ _ _ (m_snx (r_m res)) 0 Zai);
      [rewrite Zao, P3; lia | lia | lia | rewrite P2; reflexivity | rewrite P2; constructor |].
    destruct P5 as [(N1 & N2 & N3 & N4) | (N1 & N2)].
    + left. split; [exact N1|]. split; [exact Zl|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [exact N3|].
      split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
      split; [exact Zl|]. split; [reflexivity|]. split; [exact N2|]. split; [rewrite Zto; exact P4|].
      rewrite EL'. exact N4.
    + right. split; [tauto|]. split; [lia|]. split; [rewrite P2; reflexivity|].
      split; [intros E; destruct N1 as [N1|N1]; rewrite N1 in E; discriminate|].
      intros _. split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
      split; [exact Zl|]. split; [reflexivity|]. split; [rewrite Zto; exact P4|].
      rewrite EL'. replace (0 + 0) with 0 by lia. exact N2.
Qed.

(* inflateInit2_ (zlib) and the raw inflateSetDictionary right after it (total_out is 0 then) *)
Lemma f_init : forall G z sp,
    it_ok G -> g_zlib G = true -> wbits_ok (g_iw G) = true -> isptr sp -> zf_ok z -> zf_msg z = None ->
    zf_tout z = 0 -> live_ok (init_live sp (g_iw G)) ->
    it_I G 0 0 false false z (init_live sp (g_iw G)).
Proof.
  intros G z sp OK Zl WB _ _ _ Ht _.
  destruct itd_facts as (I1 & _).
  pose proof (Zlength_nonneg (it_src G)). pose proof (Zlength_nonneg (it_data G)).
  split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
  split; [exact Zl|]. split; [reflexivity|]. split; [exact Ht|]. exact (I1 G sp OK Zl WB).
Qed.

Lemma f_raw : forall G z sp alloc_ok winp,
    it_ok G -> g_zlib G = false -> wbits_ok (g_iw G) = true -> isptr sp -> zf_ok z -> zf_msg z = None ->
    zf_tout z = 0 -> live_ok (init_live sp (g_iw G)) ->
    let '(r, z', L') := setdict_f (g_dict G) alloc_ok winp z (init_live sp (g_iw G)) in
    (r = Z_OK \/ r = Z_MEM_ERROR) /\ (r = Z_OK -> it_I G 0 0 true false z' L').
Proof.
  intros G z sp alloc_ok winp OK Zl WB _ _ _ Ht _.
  destruct itd_facts as (_ & I2 & _).
  destruct (I2 G sp OK Zl WB) as (C & Wf & P).
  pose proof (Zlength_nonneg (it_src G)). pose proof (Zlength_nonneg (it_data G)).
  unfold setdict_f. rewrite C, Wf.
  destruct alloc_ok.
  - split; [left; reflexivity|]. intros _.
    split; [exact OK|]. split; [exact WB|]. split; [lia|]. split; [lia|].
    left. rewrite Ht. exact P.
  - split; [right; reflexivity|]. intros E. discriminate.
Qed.

Lemma it_facts_I : it_facts it_I.
Proof.
  constructor.
  - exact f_init.
  - exact f_raw.
  - exact f_head.
  - intros G pos opos dset nd z L (OK & _ & R1 & R2 & _). auto.
  - intros G pos opos nd z L H. exact (f_window G pos opos nd z L H).
  - intros G pos z L alloc_ok winp H. exact (f_bad G pos z L alloc_ok winp H).
  - intros G pos z L alloc_ok winp H LV ZK. exact (f_good G pos z L alloc_ok winp H LV ZK).
  - intros G pos opos dset z L strmp flush lim ib inp o aout r z' st' ow H LV ZK SP Hl Ha Hf Hib Hi REL.
    exact (f_inflate G pos opos dset z L strmp flush lim ib inp o aout r z' st' ow H LV ZK SP Hl Ha Hf Hib Hi REL).
Qed.

Lemma it_theory : it_theory_stmt.
Proof.
  exists it_I. exact it_facts_I.
Qed.

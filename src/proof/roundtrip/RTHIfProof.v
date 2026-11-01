(* RT-H: RTHIfDefs.ifacts6 from the decode theory (RTITheory.rt_ifacts for the old facts; RTIGzPass
   (rti_gz_pass: the header passes in two steps to mode TYPE) for hpass and the header fields). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTHIfDefs.
Require Zlib.proof.rfc1951.Decode.
Require Zlib.proof.roundtrip.RTITheory.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Zlib.proof.roundtrip.RTHIfGz.
From Coq Require Import ZArith List Lia Bool.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rthi_fz_nz (l0: list Z) : Forall (fun b => 0 < b < 256) l0 -> fz (l0 ++ [0]) = Zlength l0.
Proof.
  induction l0 as [|b t IH]; intros G; [reflexivity|].
  inversion G as [|b' t' Hb Ht]; subst. cbn [app fz].
  rewrite (proj2 (Z.eqb_neq b 0)) by lia. rewrite (IH Ht), Zlength_cons. lia.
Qed.

(* a name or comment of deflateSetHeader's header: its non-zero bytes, then the zero byte *)
Lemma rthi_fz_cstr (o: option (list Z)) (l: list Z) : RF.rcstr_ok o -> o = Some l -> Zlength l <= fz l + 1.
Proof.
  intros R E. destruct (R l E) as (l0 & -> & _ & F).
  rewrite (rthi_fz_nz l0 F), Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

(* the header after the passes is complete *)
Lemma rthi_hfull gh xfl x nm cm s h :
  RF.rhdr_ok gh -> DS.gz_extra gh = Some x -> DS.gz_name gh = Some nm -> DS.gz_comment gh = Some cm ->
  head_bufs gh x nm cm h -> i_flags s = gp_F (Some gh) xfl ->
  hfull s (gh_at xfl h 8 gh x nm cm).
Proof.
  intros HOK Ex En Ec B F.
  destruct B as (_ & _ & _ & X1 & X2 & _ & N1 & N2 & _ & C1 & C2 & _).
  destruct HOK as (_ & _ & _ & _ & _ & HX & HN & HC).
  destruct (HX x Ex) as (LX & _).
  unfold hfull, gh_at. cbn.
  split; [reflexivity|].
  split.
  { unfold fextra. rewrite F. unfold gp_F, gp_H, RF.fhdr_of, gz_flg. cbn [gz_text gz_hcrc gz_extra gz_name gz_comment].
    rewrite Ex, En, Ec. cbn [option_map].
    destruct (negb (DS.gz_text gh =? 0)), (negb (DS.gz_hcrc gh =? 0)); reflexivity. }
  split; [exact X1|]. split; [exact N1|]. split; [exact C1|].
  split; [rewrite X2, LX; lia|].
  split; [rewrite N2; exact (rthi_fz_cstr _ _ HN En)|].
  rewrite C2; exact (rthi_fz_cstr _ _ HC Ec).
Qed.

Lemma rt_ifacts6_proof : Zlib.proof.rfc1951.Decode.decode_parts -> ifacts6.
Proof.
  intros DP. constructor.
  - exact (Zlib.proof.roundtrip.RTITheory.rt_ifacts DP).
  - intros wb gh x nm cm D O sp z h headp hsh xb nb cb DF HOK Ex En Ec LD LO
      X1 X2 X3 N1 N2 N3 C1 C2 C3 LV ZC.
    destruct (Zlib.proof.roundtrip.RTITheory.rti_dfinal_gz [] 2 wb (Some gh) D O ltac:(lia) ltac:(lia) DF)
      as (W & _ & bs & xfl & Wf & Dd & X & EO).
    set (L := head_live (init_live sp 32) h headp hsh xb nb cb) in *.
    assert (HL: l_s L = set_i_head (init_s 7 0) true /\ h_done (l_h L) = 0 /\
                exists g x0 nm0 cm0, Some gh = Some g /\ head_bufs g x0 nm0 cm0 (l_h L)).
    { split; [reflexivity|]. split; [reflexivity|]. exists gh, x, nm, cm.
      split; [reflexivity|]. unfold head_bufs. cbn. repeat split; assumption. }
    destruct (Zlib.proof.roundtrip.RTHIfGz.rthi_gz_pass (Some gh) xfl wb bs D O L z
                W Wf Dd X EO ltac:(intros g E; injection E as <-; exact HOK) LD LO LV ZC (or_intror HL))
      as (_ & m1 & m2 & S1 & L1 & M1 & S2 & L2 & _ & M2 & _ & _ & F2 & HH).
    change Z_FINISH with 4 in S1, S2.
    exists 3%nat. cbn [hpass].
    replace (hdr_mode (m_mode (m_init z L O))) with true by reflexivity.
    rewrite S1. split; [exact L1|].
    rewrite M1. replace (hdr_mode FLAGS) with true by reflexivity.
    rewrite S2. split; [exact L2|].
    rewrite M2. replace (hdr_mode Zlib.proof.inflate.Model.TYPE) with false by reflexivity.
    destruct (HH eq_refl) as (g & x' & nm' & cm' & Eg & B & Hm).
    injection Eg as <-.
    pose proof B as (Ex' & En' & Ec' & _).
    rewrite Ex in Ex'. injection Ex' as <-. rewrite En in En'. injection En' as <-.
    rewrite Ec in Ec'. injection Ec' as <-.
    rewrite Hm. exact (rthi_hfull gh xfl x nm cm (m_s m2) (l_h L) HOK Ex En Ec B F2).
  - intros wb gh x nm cm D O sp z res h headp hsh xb nb cb DF HOK Ex En Ec LD LO
      X1 X2 X3 N1 N2 N3 C1 C2 C3 LV ZC RUN _.
    destruct (Zlib.proof.roundtrip.RTITheory.rti_dfinal_gz [] 2 wb (Some gh) D O ltac:(lia) ltac:(lia) DF)
      as (W & _ & bs & xfl & Wf & Dd & X & EO).
    set (L := head_live (init_live sp 32) h headp hsh xb nb cb) in *.
    assert (HL: l_s L = set_i_head (init_s 7 0) true /\ h_done (l_h L) = 0 /\
                exists g x0 nm0 cm0, Some gh = Some g /\ head_bufs g x0 nm0 cm0 (l_h L)).
    { split; [reflexivity|]. split; [reflexivity|]. exists gh, x, nm, cm.
      split; [reflexivity|]. unfold head_bufs. cbn. repeat split; assumption. }
    destruct (Zlib.proof.roundtrip.RTHIfGz.rthi_gz_run DP (Some gh) xfl wb bs D O L z res
                W Wf Dd X EO ltac:(intros g E; injection E as <-; exact HOK) LD LO LV ZC (or_intror HL) RUN)
      as (MD & HH).
    destruct (HH eq_refl) as (g & x' & nm' & cm' & _ & B & Hm).
    rewrite Hm. unfold gh_at. cbn.
    split; [exact X1|]. split; [exact N1|]. split; [exact C1|].
    unfold hdr_mode. apply andb_false_iff. right. apply Z.leb_gt.
    unfold m_mode, Zlib.proof.inflate.Model.TYPE, DONE, MEM in MD.
    change IM.HCRC with 16188. unfold m_mode. lia.
Qed.

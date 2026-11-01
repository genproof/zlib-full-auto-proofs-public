(* RT-H: the partial header hd6 after NAME (into COMMENT) and after COMMENT (into HCRC). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHNC6Kit.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.CaseCOMMENT5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma bufok6_0: forall l max cont, Zlength l = max -> 0 <= max -> bufok6 l max 0 cont.
Proof. intros. unfold bufok6. split; [auto | ]. split; [lia | ]. rewrite !sublist_nil. reflexivity. Qed.

Lemma bufok6_pre: forall (l: list val) max c ln cont,
  Zlength l = max -> 0 <= c <= ln -> ln <= max -> sublist 0 ln l = byte_vals (sublist 0 ln cont) ->
  Zlength cont = max -> bufok6 l max c cont.
Proof.
  intros l max c ln cont L C LN S LC. unfold bufok6. split; [auto | ]. split; [lia | ].
  assert (E: sublist 0 c (sublist 0 ln l) = sublist 0 c (byte_vals (sublist 0 ln cont))) by (rewrite S; reflexivity).
  rewrite sublist_sublist00 in E by lia. rewrite E. unfold byte_vals.
  rewrite sublist_map. rewrite sublist_sublist00 by lia. reflexivity.
Qed.

Ltac md_tac := unfold IM.HEAD, IM.EXTRA, IM.NAME, IM.COMMENT, IM.HCRC, IM.TIME, IM.OS, IM.EXLEN in *.

(* NAME, with FNAME: after the do-while (length ln, buffer bf), `length = 0; mode = COMMENT` *)
Lemma hd6_name_fin: forall F m c ln bf vt vtm vxf vos vxl vhc lx ln0 ln1 lc,
  m_mode m = IM.NAME -> hwf (m_h m) -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc ->
  Zlength ln1 = h_name_max (m_h m) -> Zlength bf = h_name_max (m_h m) ->
  (h_np (m_h m) = true -> sublist 0 ln ln1 = byte_vals (sublist 0 ln bf) /\
                           Z.min (fz bf + 1) (h_name_max (m_h m)) <= ln <= h_name_max (m_h m)) ->
  hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln1 lc |-- hd6 F (fin_n (nm_name m c ln bf)).
Proof.
  intros F m c ln bf vt vtm vxf vos vxl vhc lx ln0 ln1 lc HM HW I P L1 LB NP.
  rewrite nm_name_eq. unfold fin_n, nm3.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln1 lc)] end;
    [ apply derives_refl | | ].
  - destruct I as (I1 & I2 & I3 & I4 & I5). unfold m_mode in HM.
    unfold hinv6. cbn. rewrite HM in I2. md_tac.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; [intros; lia | ].
    intros _. pose proof (hw_comm_max _ HW). split; [lia | ]. split; [auto | ]. constructor.
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). unfold m_mode in HM.
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HM in *. md_tac. cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split.
    + destruct (h_np (m_h m)) eqn:E.
      * destruct (NP eq_refl) as (S & C).
        apply (bufok6_pre ln1 _ _ ln); unfold set_h_nbuf; cbn [h_name_max h_nbuf]; auto; try lia. pose proof (fz_nonneg bf). pose proof (hw_name_max _ HW). lia.
      * apply bufok6_0; auto. apply (hw_name_max _ HW).
    + apply bufok6_0; [apply P8 | apply (hw_comm_max _ HW)].
Qed.

(* NAME, without FNAME: `head->name = Z_NULL; length = 0; mode = COMMENT` *)
Lemma hd6_name_none: forall F m vt vtm vxf vos vxl vhc lx ln0 lc,
  m_mode m = IM.NAME -> hwf (m_h m) -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc ->
  hopen6 F (set_h_np (m_h m) false) vt vtm vxf vos vxl vhc lx ln0 lc |--
  hd6 F (fin_n (upd_h m (fun h => set_h_np h false))).
Proof.
  intros F m vt vtm vxf vos vxl vhc lx ln0 lc HM HW I P.
  unfold fin_n.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln0 lc)] end;
    [ apply derives_refl | | ].
  - destruct I as (I1 & I2 & I3 & I4 & I5). unfold m_mode in HM.
    unfold hinv6. cbn. rewrite HM in I2. md_tac.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; [intros; lia | ].
    intros _. pose proof (hw_comm_max _ HW). split; [lia | ]. split; [auto | ]. constructor.
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). unfold m_mode in HM.
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HM in *. md_tac. cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split.
    + apply bufok6_0; [apply P7 | apply (hw_name_max _ HW)].
    + apply bufok6_0; [apply P8 | apply (hw_comm_max _ HW)].
Qed.

(* COMMENT, with FCOMMENT: after the do-while (length ln, buffer bf), `mode = HCRC` *)
Lemma hd6_comm_fin: forall F m c ln bf vt vtm vxf vos vxl vhc lx ln0 lc0 lc1,
  m_mode m = IM.COMMENT -> hwf (m_h m) -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc0 ->
  Zlength lc1 = h_comm_max (m_h m) -> Zlength bf = h_comm_max (m_h m) ->
  (h_cp (m_h m) = true -> sublist 0 ln lc1 = byte_vals (sublist 0 ln bf) /\
                           Z.min (fz bf + 1) (h_comm_max (m_h m)) <= ln <= h_comm_max (m_h m)) ->
  hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc1 |-- hd6 F (fin_c (nm_comment m c ln bf)).
Proof.
  intros F m c ln bf vt vtm vxf vos vxl vhc lx ln0 lc0 lc1 HM HW I P L1 LB NP.
  rewrite cm_comment_eq. unfold fin_c, cm3.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln0 lc1)] end;
    [ apply derives_refl | | ].
  - destruct I as (I1 & I2 & I3 & I4 & I5). unfold m_mode in HM.
    unfold hinv6. cbn. rewrite HM in I2. md_tac.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; intros; lia.
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). unfold m_mode in HM.
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HM in *. md_tac. cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split; [exact P7 | ].
    destruct (h_cp (m_h m)) eqn:E.
    + destruct (NP eq_refl) as (S & C).
      apply (bufok6_pre lc1 _ _ ln); unfold set_h_cbuf; cbn [h_comm_max h_cbuf]; auto; try lia.
      pose proof (fz_nonneg bf). pose proof (hw_comm_max _ HW). lia.
    + apply bufok6_0; auto. apply (hw_comm_max _ HW).
Qed.

(* COMMENT, without FCOMMENT: `head->comment = Z_NULL; mode = HCRC` *)
Lemma hd6_comm_none: forall F m vt vtm vxf vos vxl vhc lx ln0 lc0,
  m_mode m = IM.COMMENT -> hwf (m_h m) -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc0 ->
  hopen6 F (set_h_cp (m_h m) false) vt vtm vxf vos vxl vhc lx ln0 lc0 |--
  hd6 F (fin_c (upd_h m (fun h => set_h_cp h false))).
Proof.
  intros F m vt vtm vxf vos vxl vhc lx ln0 lc0 HM HW I P.
  unfold fin_c.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln0 lc0)] end;
    [ apply derives_refl | | ].
  - destruct I as (I1 & I2 & I3 & I4 & I5). unfold m_mode in HM.
    unfold hinv6. cbn. rewrite HM in I2. md_tac.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; intros; lia.
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). unfold m_mode in HM.
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HM in *. md_tac. cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split; [exact P7 | ].
    apply bufok6_0; [apply P8 | apply (hw_comm_max _ HW)].
Qed.

(* The leave branches of the header cases NAME and COMMENT of inflate() (RTH9WKit.case_ok9v): `if (have == 0)
   goto inf_leave;` before the do-while, and `if (len) goto inf_leave;` after a do-while that read all the input
   without meeting the string's zero byte.  Both return in the same header mode with the partial header
   RTHCase.hd6: before the loop the header is unchanged; after it the name (comment) holds the bytes stored so
   far, all of them nonzero, which is what RTHSpec.hinv6 asks of a partial string. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.roundtrip.RTHNC6Kit.
Require Import Zlib.proof.roundtrip.RTHNC6Facts.
Require Import Zlib.proof.inflate.CaseNAME5.
Require Import Zlib.proof.inflate.CaseCOMMENT5.
Require Import Zlib.proof.roundtrip.RTH9HDefs.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the do-while that stops on a nonzero byte stored only nonzero bytes                            *)

Lemma Forall_nz_upd_last: forall (buf: list Z) L x,
  0 <= L < Zlength buf -> x <> 0 -> Forall (fun y => y <> 0) (sublist 0 L buf) ->
  Forall (fun y => y <> 0) (sublist 0 (L + 1) (upd_Znth L buf x)).
Proof.
  intros buf L x LB X F.
  rewrite (sublist_split 0 L (L + 1)) by (rewrite ?upd_Znth_Zlength; lia).
  rewrite sublist_upd_Znth_l by lia.
  rewrite sublist_len_1 by (rewrite upd_Znth_Zlength; lia).
  rewrite upd_Znth_same by lia.
  apply Forall_app. split; [exact F | constructor; [exact X | constructor]].
Qed.

Lemma zstr_f_leave: forall k bytes have L max wr buf j c b ln bf,
  Z.of_nat k = have - j -> 0 <= j < have -> 0 <= L <= max -> Zlength buf = max ->
  Forall (fun y => y <> 0) (sublist 0 L buf) ->
  zstr_f k bytes have L max wr buf j = (c, b, ln, bf) -> b <> 0 ->
  L <= ln <= max /\ Zlength bf = max /\ Forall (fun y => y <> 0) (sublist 0 ln bf).
Proof.
  induction k; intros bytes have L max wr buf j c b ln bf K J LM LB NZ Z B.
  - cbn [Z.of_nat] in K. lia.
  - cbn [zstr_f] in Z.
    set (x := Znth j bytes) in *.
    destruct (andb wr (L <? max)) eqn:WR.
    + apply andb_prop in WR. destruct WR as [_ WR]. apply Z.ltb_lt in WR.
      assert (ZL: Zlength (upd_Znth L buf x) = max) by (rewrite upd_Znth_Zlength; lia).
      destruct (negb (x =? 0) && (j + 1 <? have))%bool eqn:NX.
      * apply andb_prop in NX. destruct NX as [N1 N2]. apply Z.ltb_lt in N2.
        apply negb_true_iff, Z.eqb_neq in N1.
        destruct (IHk bytes have (L + 1) max wr _ (j + 1) c b ln bf ltac:(rewrite Nat2Z.inj_succ in K; lia)
                    ltac:(lia) ltac:(lia) ZL (Forall_nz_upd_last buf L x ltac:(lia) N1 NZ) Z B) as (A1 & A2 & A3).
        split; [lia | split; assumption].
      * inversion Z; subst c b ln bf. split; [lia | ]. split; [exact ZL | ].
        apply Forall_nz_upd_last; [lia | exact B | exact NZ].
    + destruct (negb (x =? 0) && (j + 1 <? have))%bool eqn:NX.
      * apply andb_prop in NX. destruct NX as [N1 N2]. apply Z.ltb_lt in N2.
        destruct (IHk bytes have L max wr buf (j + 1) c b ln bf ltac:(rewrite Nat2Z.inj_succ in K; lia)
                    ltac:(lia) LM LB NZ Z B) as (A1 & A2 & A3).
        split; [lia | split; assumption].
      * inversion Z; subst c b ln bf. split; [lia | ]. split; [exact LB | exact NZ].
Qed.

(* the string's state after a do-while that ended on a nonzero byte: the bytes stored (none without a buffer) *)
Lemma zstr_f_leave0: forall bytes have L max wr buf c b ln bf,
  0 < have -> 0 <= L <= max -> Zlength buf = max ->
  (wr = false -> L = 0) -> Forall (fun y => y <> 0) (sublist 0 L buf) ->
  zstr_f (Z.to_nat have) bytes have L max wr buf 0 = (c, b, ln, bf) -> b <> 0 ->
  0 <= ln <= max /\ (wr = false -> ln = 0) /\ Zlength bf = max /\ Forall (fun y => y <> 0) (sublist 0 ln bf).
Proof.
  intros bytes have L max wr buf c b ln bf H LM LB W0 NZ Z B.
  destruct (zstr_f_leave (Z.to_nat have) bytes have L max wr buf 0 c b ln bf ltac:(rewrite Z2Nat.id; lia)
              ltac:(lia) LM LB NZ Z B) as (A1 & A2 & A3).
  split; [lia | ]. split; [ | split; assumption].
  intros WF. subst wr. destruct (zstr_f_nowr _ _ _ _ _ _ _ _ _ _ _ Z) as [E _]. rewrite E. exact (W0 eq_refl).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the partial header after the leave that follows the do-while                                   *)

Ltac md_tac9 := unfold IM.HEAD, IM.EXTRA, IM.NAME, IM.COMMENT, IM.HCRC, IM.TIME, IM.OS, IM.EXLEN in *.

Lemma hd6_name_leave: forall F m c b ln bf vt vtm vxf vos vxl vhc lx ln0 ln1 lc,
  m_mode m = IM.NAME -> i_head (m_s m) = true -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc ->
  Zlength (h_nbuf (m_h m)) = h_name_max (m_h m) -> 0 < m_have m ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_name_max (m_h m))
    (andb (i_head (m_s m)) (h_np (m_h m))) (h_nbuf (m_h m)) 0 = (c, b, ln, bf) -> b <> 0 ->
  Zlength ln1 = h_name_max (m_h m) -> sublist 0 ln ln1 = byte_vals (sublist 0 ln bf) ->
  hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln1 lc |-- hd6 F (set_leave (nm_name m c ln bf)).
Proof.
  intros F m c b ln bf vt vtm vxf vos vxl vhc lx ln0 ln1 lc HM HH I P NB HV ZS B L1 S1.
  rewrite HH in ZS. cbn [andb] in ZS.
  assert (HMs: i_mode (m_s m) = IM.NAME) by exact HM.
  destruct I as (I1 & I2 & I3 & I4 & I5).
  destruct (I4 HMs) as (L0R & NP0 & NZ0).
  destruct (zstr_f_leave0 _ _ _ _ _ _ _ _ _ _ HV L0R NB NP0 NZ0 ZS B) as (A1 & A2 & A3 & A4).
  rewrite nm_name_eq. unfold nm3.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln1 lc)] end;
    [ apply derives_refl | | ].
  - unfold hinv6. cbn. rewrite HMs in I2 |- *. md_tac9.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; [ | intros; lia].
    intros _. split; [lia | ]. split; [exact A2 | exact A4].
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HMs in *. md_tac9.
    cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split; [ | exact P8].
    unfold bufok6. cbn [h_name_max h_nbuf h_comm_max h_cbuf set_h_nbuf set_h_cbuf].
    split; [exact L1 | ]. split; [lia | exact S1].
Qed.

Lemma hd6_comm_leave: forall F m c b ln bf vt vtm vxf vos vxl vhc lx ln0 lc0 lc1,
  m_mode m = IM.COMMENT -> i_head (m_s m) = true -> hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
    (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc0 ->
  Zlength (h_cbuf (m_h m)) = h_comm_max (m_h m) -> 0 < m_have m ->
  zstr_f (Z.to_nat (m_have m)) (name_bytes m) (m_have m) (i_length (m_s m)) (h_comm_max (m_h m))
    (andb (i_head (m_s m)) (h_cp (m_h m))) (h_cbuf (m_h m)) 0 = (c, b, ln, bf) -> b <> 0 ->
  Zlength lc1 = h_comm_max (m_h m) -> sublist 0 ln lc1 = byte_vals (sublist 0 ln bf) ->
  hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln0 lc1 |-- hd6 F (set_leave (nm_comment m c ln bf)).
Proof.
  intros F m c b ln bf vt vtm vxf vos vxl vhc lx ln0 lc0 lc1 HM HH I P NB HV ZS B L1 S1.
  rewrite HH in ZS. cbn [andb] in ZS.
  assert (HMs: i_mode (m_s m) = IM.COMMENT) by exact HM.
  destruct I as (I1 & I2 & I3 & I4 & I5).
  destruct (I5 HMs) as (L0R & NP0 & NZ0).
  destruct (zstr_f_leave0 _ _ _ _ _ _ _ _ _ _ HV L0R NB NP0 NZ0 ZS B) as (A1 & A2 & A3 & A4).
  rewrite cm_comment_eq. unfold cm3.
  match goal with |- _ |-- hd6 F ?M =>
    eapply derives_trans; [ | apply (hd6_close F M vt vtm vxf vos vxl vhc lx ln0 lc1)] end;
    [ apply derives_refl | | ].
  - unfold hinv6. cbn. rewrite HMs in I2 |- *. md_tac9.
    split; [exact I1 | ]. split; [exact I2 | ]. split; [intros; lia | ]. split; [intros; lia | ].
    intros _. split; [lia | ]. split; [exact A2 | exact A4].
  - destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    unfold hph, cx6, cn6, cc6, fextra in *. cbn. rewrite HMs in *. md_tac9.
    cbn in P1, P2, P3, P4, P5, P6, P7, P8 |- *.
    split; [exact P1 | ]. split; [exact P2 | ]. split; [exact P3 | ]. split; [exact P4 | ].
    split; [exact P5 | ]. split; [exact P6 | ]. split; [exact P7 | ].
    unfold bufok6. cbn [h_name_max h_nbuf h_comm_max h_cbuf set_h_nbuf set_h_cbuf].
    split; [exact L1 | ]. split; [lia | exact S1].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the post of a header case that leaves in a header mode                                         *)

(* `goto inf_leave` (the break of the switch) into the header mode of m': the model breaks with m', the header
   stays partial (RTH9HDefs.hd9 is hd6 in a header mode) *)
Lemma brk9_hdr: forall F m m' P,
  stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m' ->
  hdr_mode (m_mode m') = true -> hdr_tok F m' = hdr_tok F m ->
  P |-- PROPx (PP F m') (LOCALx (LL F m') (SEPx (SL6 F m' (hd6 F m')))) ->
  P |-- RA_break (frame_ret_assert (switch_ret_assert (case_post9 F m)) (lift0 (hdr_tok F m))).
Proof.
  intros F m m' P E HM T D.
  change (RA_break (frame_ret_assert (switch_ret_assert (case_post9 F m)) (lift0 (hdr_tok F m))))
    with (RA_normal (case_post9 F m) * lift0 (hdr_tok F m)).
  unfold case_post9. cbn [RA_normal]. rewrite exp_sepcon1. apply (exp_right m').
  rewrite sepcon_andp_prop'. apply andp_right; [apply prop_right; exact E | ].
  eapply derives_trans; [exact D | ].
  rewrite <- ls6_split. unfold post9, hd9. rewrite HM. rewrite T.
  intros rho. simpl. cancel.
Qed.

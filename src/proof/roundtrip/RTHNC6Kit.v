(* RT-H: kit of the cases NAME (6) and COMMENT (7) with the partial header hd6 (RTHCase.v):
   - the view of the headless loop state (RTHLoop.loop_stateH) with the six state fields these cases touch apart,
     the header tokens and the header as the last SEP item (SL6);
   - the header opened (hopen6: the struct with any values in the fields not yet written, the three buffers);
   - pure facts on zstr_f (where the string ends in the buffer). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Export Zlib.proof.inflate.NCKit5.
Require Export Zlib.proof.inflate.NCLoop5.
Require Export Zlib.proof.inflate.NCCrc5.
Require Export Zlib.proof.inflate.NCMach5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the view                                                                                       *)

Definition SL6 (F: frame) (m: mst) (Hd: mpred) : list mpred :=
  [field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F);
   field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F);
   field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F);
   in_rep (f_ib F); crc_table_at (f_tsh F) (f_gv F); mem_rep_nc F m;
   locals_rep F; hdr_tok F m; Hd].

Lemma mem_repH_nc: forall F m,
  mem_repH F m =
  field_at Ews t_state (DOT _mode) (zv (i_mode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _flags) (zv (i_flags (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _check) (lv (i_check (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _head) (if i_head (m_s m) then f_headp F else nullval) (f_sp F) *
  field_at Ews t_state (DOT _length) (zv (i_length (m_s m))) (f_sp F) *
  in_rep (f_ib F) * crc_table_at (f_tsh F) (f_gv F) * mem_rep_nc F m.
Proof.
  intros. unfold mem_repH, mem_rep_nc, head_partH, hnoneH. rewrite state_rep_nc_split.
  destruct (i_head (m_s m)); apply pred_ext; cancel.
Qed.

Lemma ls6_split: forall F m Hd,
  loop_stateH F m * (fun _ => hdr_tok F m * Hd) = PROPx (PP F m) (LOCALx (LL F m) (SEPx (SL6 F m Hd))).
Proof.
  intros. unfold loop_stateH. rewrite sepcon_comm.
  etransitivity; [apply (insert_SEP (hdr_tok F m * Hd)) | ].
  unfold PP, LL, SL6. f_equal. f_equal. unfold SEPx. extensionality rho. simpl.
  rewrite mem_repH_nc. apply pred_ext; cancel.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header opened                                                                              *)

Definition hstr6 (F: frame) (h: hstate) (vt vtm vxf vos vxl vhc: val) : mpred :=
  data_at (f_hsh F) t_head
     (vt, (vtm, (vxf, (vos,
      ((if h_xp h then f_xb F else nullval), (vxl, (zv (h_extra_max h),
      ((if h_np h then f_nb F else nullval), (zv (h_name_max h),
      ((if h_cp h then f_cb F else nullval), (zv (h_comm_max h), (vhc, zv (h_done h)))))))))))))
     (f_headp F).

Definition hopen6 (F: frame) (h: hstate) (vt vtm vxf vos vxl vhc: val) (lx ln lc: list val) : mpred :=
  hstr6 F h vt vtm vxf vos vxl vhc * hbuf6 (f_xb F) (h_extra_max h) lx * hbuf6 (f_nb F) (h_name_max h) ln *
  hbuf6 (f_cb F) (h_comm_max h) lc.

Definition hprops6 (p: Z) (fx: bool) (cx cn cc: Z) (h: hstate) (vt vtm vxf vos vxl vhc: val)
    (lx ln lc: list val) : Prop :=
  (1 <= p -> vt = zv (h_text h)) /\ (2 <= p -> vtm = lv (h_time h)) /\
  (3 <= p -> vxf = zv (h_xflags h) /\ vos = zv (h_os h)) /\
  (4 <= p -> fx = true -> vxl = zv (h_extra_len h)) /\ (5 <= p -> vhc = zv (h_hcrc h)) /\
  bufok6 lx (h_extra_max h) cx (h_xbuf h) /\ bufok6 ln (h_name_max h) cn (h_nbuf h) /\
  bufok6 lc (h_comm_max h) cc (h_cbuf h).

Lemma hd6_open: forall F m,
  hd6 F m = !! hinv6 (m_s m) (m_h m) &&
    EX vt: val, EX vtm: val, EX vxf: val, EX vos: val, EX vxl: val, EX vhc: val,
    EX lx: list val, EX ln: list val, EX lc: list val,
    !! hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
          (m_h m) vt vtm vxf vos vxl vhc lx ln lc &&
    hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln lc.
Proof. reflexivity. Qed.

Lemma hd6_close: forall F m vt vtm vxf vos vxl vhc lx ln lc,
  hinv6 (m_s m) (m_h m) ->
  hprops6 (hph (m_s m)) (fextra (m_s m)) (cx6 (m_s m) (m_h m)) (cn6 (m_s m) (m_h m)) (cc6 (m_s m) (m_h m))
          (m_h m) vt vtm vxf vos vxl vhc lx ln lc ->
  hopen6 F (m_h m) vt vtm vxf vos vxl vhc lx ln lc |-- hd6 F m.
Proof.
  intros F m vt vtm vxf vos vxl vhc lx ln lc I P. rewrite hd6_open.
  apply andp_right; [apply prop_right; exact I | ].
  Exists vt vtm vxf vos vxl vhc lx ln lc. apply andp_right; [apply prop_right; exact P | apply derives_refl].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* hpass: a header pass never leaves                                                               *)

Lemma hpass_noleave: forall flush n m m',
  hpass flush (S n) m -> hdr_mode (m_mode m) = true ->
  stepf2 flush lenfix_list distfix_list m = IBrk m' -> m_leave m' = 0.
Proof.
  intros flush n m m' P H E. cbn [hpass] in P. rewrite H, E in P. apply P.
Qed.

Lemma hpass_noleave_set: forall flush n m m',
  hpass flush (S n) m -> hdr_mode (m_mode m) = true ->
  stepf2 flush lenfix_list distfix_list m = IBrk (set_leave m') -> False.
Proof.
  intros flush n m m' P H E. pose proof (hpass_noleave _ _ _ _ P H E) as L. cbn in L. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* where the string ends                                                                          *)

Lemma fz_le: forall l i, 0 <= i < Zlength l -> Znth i l = 0 -> fz l <= i.
Proof.
  induction l as [ | x t IH]; intros i I Z.
  - rewrite Zlength_nil in I. lia.
  - cbn [fz]. destruct (Z.eqb_spec x 0); [lia | ].
    rewrite Zlength_cons in I. destruct (zeq i 0).
    + subst i. rewrite Znth_0_cons in Z. contradiction.
    + rewrite Znth_pos_cons in Z by lia. specialize (IH (i - 1) ltac:(lia) Z). lia.
Qed.

Lemma fz_nonneg: forall l, 0 <= fz l.
Proof. induction l as [ | x t IH]; cbn [fz]; [lia | destruct (x =? 0); lia]. Qed.

(* with b = 0 the string's zero byte was stored at ln - 1, or the buffer is full *)
Lemma zstr_f_end: forall k bytes have L max buf j c b ln bf,
  Z.of_nat k = have - j -> 0 <= j < have -> 0 <= L <= max -> Zlength buf = max ->
  zstr_f k bytes have L max true buf j = (c, b, ln, bf) ->
  L <= ln <= max /\ Zlength bf = max /\ (b = 0 -> ln = max \/ (0 < ln /\ Znth (ln - 1) bf = 0)).
Proof.
  induction k; intros bytes have L max buf j c b ln bf K J LM LB Z.
  - cbn [Z.of_nat] in K. lia.
  - cbn [zstr_f] in Z. cbn [andb] in Z.
    destruct (Z.ltb_spec L max) as [LT | GE].
    + assert (ZL: Zlength (upd_Znth L buf (Znth j bytes)) = max) by (rewrite upd_Znth_Zlength; lia).
      destruct (negb (Znth j bytes =? 0) && (j + 1 <? have))%bool eqn:NX.
      * apply andb_prop in NX. destruct NX as [N1 N2]. apply Z.ltb_lt in N2.
        destruct (IHk bytes have (L + 1) max _ (j + 1) c b ln bf ltac:(rewrite Nat2Z.inj_succ in K; lia) ltac:(lia) ltac:(lia) ZL Z) as (A & B & C). lia.
      * inversion Z; subst. split; [lia | ]. split; [auto | ]. intros B0. right. split; [lia | ].
        replace (L + 1 - 1) with L by lia. rewrite upd_Znth_same by lia. exact B0.
    + destruct (negb (Znth j bytes =? 0) && (j + 1 <? have))%bool eqn:NX.
      * apply andb_prop in NX. destruct NX as [N1 N2]. apply Z.ltb_lt in N2.
        destruct (IHk bytes have L max buf (j + 1) c b ln bf ltac:(rewrite Nat2Z.inj_succ in K; lia) ltac:(lia) ltac:(lia) LB Z) as (A & B & C). lia.
      * inversion Z; subst. split; [lia | ]. split; [reflexivity | ]. intros _. left. lia.
Qed.

Lemma zstr_f_cn: forall bytes have L max buf c ln bf,
  0 < have -> 0 <= L <= max -> Zlength buf = max ->
  zstr_f (Z.to_nat have) bytes have L max true buf 0 = (c, 0, ln, bf) ->
  L <= ln <= max /\ Zlength bf = max /\ 0 <= Z.min (fz bf + 1) max <= ln.
Proof.
  intros bytes have L max buf c ln bf H LM LB Z.
  destruct (zstr_f_end (Z.to_nat have) bytes have L max buf 0 c 0 ln bf ltac:(rewrite Z2Nat.id; lia) ltac:(lia) LM LB Z) as (A & B & C).
  split; [exact A | ]. split; [exact B | ]. pose proof (fz_nonneg bf).
  destruct (C eq_refl) as [E | [P E]]; [lia | ].
  pose proof (fz_le bf (ln - 1) ltac:(lia) E). lia.
Qed.

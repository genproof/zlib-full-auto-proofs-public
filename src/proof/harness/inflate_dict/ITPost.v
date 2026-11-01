(* Law inflate_dict, theory part: an inflate() call once the dictionary is set, from the
   decode theory (decode_call_stmt, rfc1951/Decode.v) and the call frame. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The data: the history is a prefix of the expansion, the data are bytes                         *)

Lemma itp_fold_ext {A: Type} (f: list Z -> A -> list Z) :
  (forall out a, exists d, f out a = out ++ d) ->
  forall l out, exists d, fold_left f l out = out ++ d.
Proof.
  intros F l; induction l as [|a l IH]; intros out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (F out a) as [d1 E1]; rewrite E1. destruct (IH (out ++ d1)) as [d2 E2].
    exists (d1 ++ d2); rewrite E2, app_assoc; auto.
Qed.

Lemma itp_lz_ext : forall n dist out, exists d, lz_copy n dist out = out ++ d.
Proof.
  induction n as [|n IH]; intros dist out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (IH dist (out ++ [Znth (Zlength out - dist) out])) as [d E]; rewrite E.
    exists ([Znth (Zlength out - dist) out] ++ d); rewrite app_assoc; auto.
Qed.

Lemma itp_block_ext : forall out b, exists d, block_data out b = out ++ d.
Proof.
  assert (S: forall out syms, exists d, syms_data out syms = out ++ d).
  { intros out syms; unfold syms_data; apply itp_fold_ext.
    intros o [b|len dist]; simpl; [exists [b]; auto | apply itp_lz_ext]. }
  intros out [bytes|syms|nlen ndist cl toks syms]; simpl; [exists bytes; auto|apply S|apply S].
Qed.

Lemma itp_expand_data : forall hist bs, expand hist bs = hist ++ data hist bs.
Proof.
  intros hist bs. unfold data. destruct (itp_fold_ext block_data itp_block_ext bs hist) as [d E].
  unfold expand; rewrite E. f_equal. rewrite Zlength_app. rewrite sublist_app2 by list_solve.
  rewrite Z.sub_diag. replace (Zlength hist + Zlength d - Zlength hist) with (Zlength d) by lia.
  rewrite sublist_same by lia; auto.
Qed.

Lemma itp_bytes_Znth : forall out i, Forall byte_ok out -> byte_ok (Znth i out).
Proof.
  intros out i F. destruct (zlt i 0); [rewrite Znth_underflow by lia; unfold byte_ok, default, Inhabitant_Z; lia|].
  destruct (zlt i (Zlength out)); [|rewrite Znth_overflow by lia; unfold byte_ok, default, Inhabitant_Z; lia].
  apply Forall_Znth; auto; lia.
Qed.

Lemma itp_lz_bytes : forall n dist out, Forall byte_ok out -> Forall byte_ok (lz_copy n dist out).
Proof.
  induction n as [|n IH]; intros dist out F; simpl; auto.
  apply IH. apply Forall_app; split; auto. constructor; auto. apply itp_bytes_Znth; auto.
Qed.

Lemma itp_syms_bytes : forall wmax ll dl syms out,
  Forall byte_ok out -> syms_ok wmax ll dl out syms -> Forall byte_ok (syms_data out syms).
Proof.
  intros wmax ll dl syms; induction syms as [|[b|len dist] syms IH]; intros out F OK; simpl in *; auto.
  - destruct OK as [[B _] R]. apply IH; auto. apply Forall_app; split; auto.
  - destruct OK as [_ R]. apply IH; auto. apply itp_lz_bytes; auto.
Qed.

Lemma itp_expand_bytes : forall wmax bs hist,
  Forall byte_ok hist -> blocks_ok wmax hist bs -> Forall byte_ok (expand hist bs).
Proof.
  intros wmax bs; induction bs as [|b bs IH]; intros hist F OK; simpl in *; auto.
  destruct OK as [B R]. apply IH; auto.
  destruct b as [bytes|syms|nlen ndist cl toks syms]; simpl in *.
  - destruct B as [_ B]. apply Forall_app; auto.
  - eapply itp_syms_bytes; eauto.
  - destruct B as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B). eapply itp_syms_bytes; eauto.
Qed.

Lemma itp_data_bytes : forall G, it_ok G -> bytes_ok (it_data G).
Proof.
  intros G (_ & _ & _ & _ & _ & _ & (_ & _ & _ & (_ & Fh & Bo)) & _).
  pose proof (itp_expand_bytes _ _ _ Fh Bo) as F.
  rewrite itp_expand_data in F. apply Forall_app in F as [_ F].
  unfold it_data, bytes_ok. eapply Forall_impl; [|exact F]. unfold byte_ok; simpl; intros; rep_lia.
Qed.

Lemma itp_full : forall G, full (itd G) = g_dict G ++ it_data G.
Proof. intros G. unfold full, itd, it_data; simpl. apply itp_expand_data. Qed.

(* the output after the call *)
Lemma itp_split : forall (D ow rest: list Z) opos,
  0 <= opos <= Zlength D -> D = sublist 0 opos D ++ ow ++ rest ->
  opos + Zlength ow <= Zlength D /\ ow = sublist opos (opos + Zlength ow) D /\
  sublist 0 opos D ++ ow = sublist 0 (opos + Zlength ow) D.
Proof.
  intros D ow rest opos R E. remember (sublist 0 opos D) as P eqn:HP.
  assert (LP: Zlength P = opos) by (subst P; list_solve).
  clear HP. subst D. split; [list_solve|]. split; list_solve.
Qed.

(* a state of post_st is not at a wrapped HEAD *)
Lemma itp_not_whead : forall G pos opos tout s,
  it_ok G -> post_st G pos opos tout s -> i_mode s <> HEAD \/ i_wrap s = 0.
Proof.
  intros G pos opos tout s HG (_ & (Hat & ((wb0 & Hr & _) & _) & _) & _).
  destruct (g_zlib G) eqn:Z.
  - left. intros Hm. unfold at_mode in Hat; cbv zeta in Hat. destruct Hat as [_ [[_ Hh]|Hrest]].
    + destruct Hh as (_ & _ & _ & _ & _ & _ & F). eapply F.
      unfold itd, it_wrapper; simpl; rewrite Z; reflexivity.
    + repeat (destruct Hrest as [Hrest|Hrest]);
      destruct Hrest as [Hx _]; rewrite Hm in Hx; cbv in Hx; repeat (destruct Hx as [Hx|Hx]); discriminate.
  - right. destruct HG as (Hwb & _ & _ & _ & _ & _ & _ & Hiw). rewrite Z in Hiw.
    unfold itd in Hr; simpl in Hr. rewrite Hiw in Hr.
    destruct (init_wrap_wb_bits _ _ _ Hr) as (wrap & R & _ & _ & _ & Z0). apply Z0. unfold reset2_wb in R.
    destruct (Z.ltb_spec (- g_wb G) 0); [|lia]. destruct (Z.ltb_spec (- g_wb G) (-15)); [lia|].
    destruct (andb (8 <=? - - g_wb G) (- - g_wb G <=? 15)); inversion R; auto.
Qed.


Lemma itp_call : decode_call_stmt -> frame_stmt ->
  forall G pos opos z L flush inp res,
  it_ok G -> dctx_ok (itd G) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 20 ->
  post_st G pos opos (zf_tout z) (l_s L) ->
  0 <= pos -> pos + Zlength inp <= Zlength (it_src G) -> inp = sublist pos (pos + Zlength inp) (it_src G) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res -> r_ret res <> Z_MEM_ERROR ->
  let m := r_m res in let ow := m_ow m in
  m_inp m = inp /\ 0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength ow /\ m_aout m = zf_ao z /\ bytes_ok ow /\
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
  opos + Zlength ow <= Zlength (it_data G) /\ ow = sublist opos (opos + Zlength ow) (it_data G) /\
  (r_ret res = Z_STREAM_END ->
     opos + Zlength ow = Zlength (it_data G) /\ pos + m_snx m = Zlength (it_src G) /\
     (g_zlib G = false -> win_st G (m_s m) (it_out G (opos + Zlength ow)))) /\
  (r_ret res <> Z_STREAM_END -> post_st G (pos + m_snx m) (opos + Zlength ow) (m_tout m) (m_s m)).
Proof.
  intros DC FR G pos opos z L flush inp res HG Hd HL Hz Hao Hpost Hpos Hlen Hinp Hrun Hmem. cbv zeta.
  pose proof (itp_not_whead _ _ _ _ _ HG Hpost) as NH.
  pose proof Hpost as (Hopos & Hdinv & (Hwb & Hws & Hwi & Hwstr & Hwok)).
  pose proof HG as (Hg8 & _ & _ & Hdl & Hsl & _).
  assert (Hsrc: Zlength (it_src G) = slen (itd G)) by reflexivity.
  assert (Hbin: bytes_ok inp).
  { rewrite Hinp. unfold bytes_ok. apply Forall_sublist.
    destruct Hd as (_ & _ & _ & _ & _ & _ & B & _). exact B. }
  destruct (FR flush z L inp res HL Hz ltac:(rep_lia) ltac:(rep_lia) Hbin Hrun) as (Fi & Fa & Fw & Fs).
  specialize (Fs Hmem) as [Fsw Fsow].
  destruct (DC (itd G) pos (it_out G opos) L z inp flush res Hd Hdinv HL Hz ltac:(rep_lia) Hpos Hlen Hinp Hrun)
    as [Hm|(Hr & Hsnx & Hsow & Haout & (rest & Hfull) & Hdinv' & HW & Hend & _ & _)]; [contradiction|].
  rewrite itp_full in Hfull. unfold it_out in Hfull. rewrite <- app_assoc in Hfull. apply app_inv_head in Hfull.
  destruct (itp_split _ _ _ _ Hopos Hfull) as (Hle & How & Hpre).
  assert (Hout: it_out G opos ++ m_ow (r_m res) = it_out G (opos + Zlength (m_ow (r_m res)))).
  { unfold it_out. rewrite <- app_assoc, Hpre. auto. }
  assert (Hwb': i_wbits (m_s (r_m res)) = g_wb G) by (rewrite Fw by auto; auto).
  assert (Hwin': (r_ret res <> Z_STREAM_END \/ g_zlib G = false) ->
                 win_st G (m_s (r_m res)) (it_out G (opos + Zlength (m_ow (r_m res))))).
  { intros C. destruct HW as [W0 Wok].
    - intros h; unfold itd, it_wrapper; simpl; destruct (g_zlib G); discriminate.
    - rewrite Hws. assert (0 < 2 ^ g_wb G) by (apply Z.pow_pos_nonneg; lia). lia.
    - exact Hwok.
    - destruct C as [C|C]; [left; auto|right; unfold wrapped, itd, it_wrapper; simpl; rewrite C; auto].
    - rewrite <- Hout. unfold win_st. split; [exact Hwb'|].
      destruct (sw_wsize _ Fsw) as [W1|[Wi Ws]]; [contradiction|].
      assert (0 < 2 ^ g_wb G) by (apply Z.pow_pos_nonneg; lia).
      split; [rewrite Ws, Hwb'; auto|]. split; [auto|]. split; [|exact Wok].
      pose proof (sw_whave _ Fsw). pose proof (sw_wnext _ Fsw). pose proof (sw_wvalid _ Fsw).
      pose proof (sw_wdata _ Fsw). unfold wstruct. rewrite Ws, Hwb' in *. intuition lia. }
  split; [auto|]. split; [lia|]. split; [auto|]. split; [auto|]. split.
  { rewrite How. unfold bytes_ok; apply Forall_sublist; apply itp_data_bytes; auto. }
  split; [auto|]. split; [lia|]. split; [auto|]. split.
  - intros He. destruct (Hend He) as [Ho Hp].
    rewrite itp_full in Ho. unfold it_out in Ho. rewrite <- app_assoc in Ho; apply app_inv_head in Ho.
    split; [|split].
    + apply (f_equal (@Zlength Z)) in Ho. rewrite Zlength_app, Zlength_sublist in Ho by lia. lia.
    + rewrite Hsrc; exact Hp.
    + intros Hz0. apply Hwin'. right; auto.
  - intros Hne. unfold post_st. split; [lia|]. split.
    + rewrite <- Hout. exact Hdinv'.
    + apply Hwin'. left; auto.
Qed.

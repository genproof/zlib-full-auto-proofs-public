(* Kit of DecTab: the pass from TABLE / LENLENS / CODELENS as a flush-independent part (as
   inflate_codes' TheoryTab.v), the frame of a pass, the bit buffer along a pass, the layout of a dynamic
   block header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The pass up to LEN_ (flush is read only at CODELENS's end)                                      *)

Inductive ttab_res := TTDone (o: iout) | TTLen (m: mst).

Definition ttab_run (flush: Z) (p: ttab_res) : iout :=
  match p with
  | TTDone o => o
  | TTLen m => if flush =? Z_TREES then IBrk (set_leave m)
               else c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m
  end.

Definition ttab_clpost (m: mst) : ttab_res :=
  let s := m_s m in
  if Znth 256 (i_lens s) =? 0 then TTDone (IBrk (set_bad m M_eob)) else
  let s := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9 in
  let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_ll_set)) else
  let s := set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6 in
  let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
  let s := set_i_distbits (set_i_next (set_i_codes s codes) nxt) db in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_d_set)) else
  TTLen (set_mode m LEN_).

Definition ttab_cl (m: mst) : ttab_res :=
  match codelens_loop lenfix_list distfix_list 320 m with
  | CLleave m => TTDone (IBrk m)
  | CLbad m => TTDone (IBrk m)
  | CLnext m => ttab_clpost m
  end.

Definition ttab_llpost (m: mst) : ttab_res :=
  let s := lenlens_zero 19 (m_s m) in
  let s := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next s 0) (TCodes 0)) (TCodes 0)) 7 in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_cl_set)) else
  ttab_cl (set_mode (upd_s m (fun s => set_i_have s 0)) CODELENS).

Definition ttab_ll (m: mst) : ttab_res :=
  let m := lenlens_loop 19 m in
  if m_leave m =? 1 then TTDone (IBrk m) else ttab_llpost m.

Definition ttab_tab (m: mst) : ttab_res :=
  let m := needbits 14 m in
  if m_leave m =? 1 then TTDone (IBrk m) else
  let nlen := bitsn m 5 + 257 in let m := dropbits 5 m in
  let ndist := bitsn m 5 + 1 in let m := dropbits 5 m in
  let ncode := bitsn m 4 + 4 in let m := dropbits 4 m in
  let m := upd_s m (fun s => set_i_ncode (set_i_ndist (set_i_nlen s nlen) ndist) ncode) in
  if orb (286 <? nlen) (30 <? ndist) then TTDone (IBrk (set_bad m M_toomany)) else
  ttab_ll (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS).

Lemma ttab_cl_eq flush m :
  c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_cl m).
Proof.
  unfold c_CODELENS, ttab_cl. destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1];
    try reflexivity.
  unfold ttab_clpost. cbv zeta.
  destruct (Znth 256 (i_lens (m_s m1)) =? 0); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r2 c2] n2] b2].
  destruct (negb (r2 =? 0)); reflexivity.
Qed.

Lemma ttab_ll_eq flush m :
  c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_ll m).
Proof.
  unfold c_LENLENS, ttab_ll. cbv zeta.
  destruct (m_leave (lenlens_loop 19 m) =? 1); [reflexivity|].
  unfold ttab_llpost. cbv zeta.
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|]. apply ttab_cl_eq.
Qed.

Lemma ttab_tab_eq flush m :
  c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_tab m).
Proof.
  unfold c_TABLE, ttab_tab. cbv zeta.
  destruct (m_leave (needbits 14 m) =? 1); [reflexivity|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [reflexivity|].
  apply ttab_ll_eq.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The frame: what a pass of the group does not change                                            *)

Record tfr (m0 m: mst) : Prop := {
  tf_inp : m_inp m = m_inp m0;
  tf_ow : m_ow m = m_ow m0;
  tf_aout : m_aout m = m_aout m0;
  tf_out : m_out m = m_out m0;
  tf_tout : m_tout m = m_tout m0;
  tf_last : i_last (m_s m) = i_last (m_s m0);
  tf_wrap : i_wrap (m_s m) = i_wrap (m_s m0);
  tf_flags : i_flags (m_s m) = i_flags (m_s m0);
  tf_check : i_check (m_s m) = i_check (m_s m0);
  tf_total : i_total (m_s m) = i_total (m_s m0);
  tf_head : i_head (m_s m) = i_head (m_s m0);
  tf_wbits : i_wbits (m_s m) = i_wbits (m_s m0);
  tf_wsize : i_wsize (m_s m) = i_wsize (m_s m0);
  tf_whave : i_whave (m_s m) = i_whave (m_s m0);
  tf_wnext : i_wnext (m_s m) = i_wnext (m_s m0);
  tf_wdata : i_wdata (m_s m) = i_wdata (m_s m0) }.

Lemma tfr_refl m : tfr m m.
Proof. constructor; reflexivity. Qed.

Lemma tfr_trans m0 m1 m2 : tfr m0 m1 -> tfr m1 m2 -> tfr m0 m2.
Proof. intros [] []. constructor; congruence. Qed.

(* the modes of the pass *)
Definition md_tabl (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS \/ md = LEN_.

Lemma md_tab_tabl md : md_tab md -> md_tabl md.
Proof. unfold md_tab, md_tabl. tauto. Qed.

(* Kd at the end of (a part of) the pass *)
Lemma kd_tfr G pos inp ob m0 m :
  Kd G pos inp ob m0 -> md_tab (m_mode m0) -> tfr m0 m -> md_tabl (m_mode m) -> m_ret m = Z_OK ->
  at_mode G (m_s m) (pos + m_nx m) (m_hold m) (m_bits m) (ob ++ m_ow m) ->
  Kd G pos inp ob m.
Proof.
  intros K M0 F M R A. destruct K, F.
  assert (N0: m_mode m0 <> HEAD /\ m_mode m0 <> FLAGS /\ m_mode m0 <> TIME /\ m_mode m0 <> OS /\
              m_mode m0 < CHECK /\ m_mode m0 <> LENGTH /\ m_mode m0 <> DONE).
  { unfold md_tab in M0. unfold TABLE, LENLENS, CODELENS, HEAD, FLAGS, TIME, OS, CHECK, LENGTH, DONE in *.
    lia. }
  assert (N: m_mode m <> HEAD /\ m_mode m <> FLAGS /\ m_mode m <> TIME /\ m_mode m <> OS /\
              m_mode m < CHECK /\ m_mode m <> LENGTH /\ m_mode m <> DONE).
  { unfold md_tabl in M. unfold TABLE, LENLENS, CODELENS, LEN_, HEAD, FLAGS, TIME, OS, CHECK, LENGTH, DONE in *.
    lia. }
  unfold m_mode in N0, N.
  destruct N0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7). destruct N as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (AC: forall md, md <> LENGTH -> md <> DONE -> after_check G md = false).
  { intros md H1 H2. unfold after_check. apply Z.eqb_neq in H1. apply Z.eqb_neq in H2.
    rewrite H1, H2. destruct (wrapped G); reflexivity. }
  unfold m_mode in *. rewrite (AC _ A6 A7) in kd_tout, kd_out.
  constructor.
  - congruence.
  - exact A.
  - destruct kd_glob as ((wb0 & E1 & E2) & H & W & FL). split; [|split; [|split]].
    + exists wb0. rewrite tf_wrap0. split; [exact E1|]. intros; tauto.
    + congruence.
    + intros _. rewrite tf_wbits0. apply W. tauto.
    + intros WR _ _. rewrite tf_flags0. apply FL; tauto.
  - intros _. assert (WO := kd_win A5).
    unfold win_ok, win_at in *. rewrite tf_wsize0, tf_wbits0, tf_whave0, tf_wnext0, tf_wdata0. exact WO.
  - intros WR _ _ _ _. assert (C := kd_chk WR A1 A2 A3 A4).
    cbv zeta in C |- *. rewrite tf_check0, tf_total0, tf_ow0.
    replace ((i_mode (m_s m) =? LENGTH) || (i_mode (m_s m) =? DONE)) with false
      by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; tauto).
    replace ((i_mode (m_s m0) =? LENGTH) || (i_mode (m_s m0) =? DONE)) with false in C
      by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; tauto).
    exact C.
  - unfold m_mode. rewrite (AC _ B6 B7). congruence.
  - unfold m_mode. rewrite (AC _ B6 B7). congruence.
  - unfold m_mode. replace (i_mode (m_s m) =? DONE) with false by (symmetry; apply Z.eqb_neq; tauto). exact R.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Bits                                                                                           *)

Lemma bval_app a b : bval (a ++ b) = bval a + 2 ^ Zlength a * bval b.
Proof.
  induction a as [|x a IH]; cbn [app bval].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). lia.
Qed.

Lemma bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|x l IH]; cbn [bval].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). destruct x; simpl Z.b2z; lia.
Qed.

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma bits_le_succ v n : 0 <= n ->
  bits_le v (n + 1) = bits_le v n ++ [Z.testbit v n].
Proof.
  intros Hn. unfold bits_le. rewrite Z2Nat.inj_add by lia. simpl (Z.to_nat 1).
  rewrite seq_app, map_app. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bval_bits_le v n : 0 <= n -> bval (bits_le v n) = v mod 2 ^ n.
Proof.
  intros Hn. pattern n. apply natlike_ind; [| |exact Hn].
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - intros x Hx IH. rewrite <- Z.add_1_r, bits_le_succ by lia. rewrite bval_app, IH, Zlength_bits_le by lia.
    cbn [bval]. rewrite Z.add_0_r.
    rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by lia.
    replace (v / 2 ^ x mod 2 ^ 1) with (Z.b2z (Z.testbit v x)); [lia|].
    rewrite Z.testbit_spec' by lia. change (2 ^ 1) with 2.
    pose proof (Z.mod_pos_bound (v / 2 ^ x) 2 ltac:(lia)).
    destruct (Z.eq_dec (v / 2 ^ x mod 2) 0) as [E|E];
      [rewrite E; reflexivity | replace (v / 2 ^ x mod 2) with 1 by lia; reflexivity].
Qed.

Lemma bits_le_testbit v n i : 0 <= i < n -> nth (Z.to_nat i) (bits_le v n) false = Z.testbit v i.
Proof.
  intros Hi. unfold bits_le.
  rewrite nth_indep with (d' := (fun i0 : nat => Z.testbit v (Z.of_nat i0)) O)
    by (rewrite map_length, seq_length; lia).
  rewrite (map_nth (fun i0 : nat => Z.testbit v (Z.of_nat i0))).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* the testbits of bval *)
Lemma bval_testbit : forall l i, 0 <= i -> Z.testbit (bval l) i = nth (Z.to_nat i) l false.
Proof.
  induction l as [|x l IH]; intros i Hi; cbn [bval].
  - rewrite Z.testbit_0_l. destruct (Z.to_nat i); reflexivity.
  - destruct (Z.eq_dec i 0) as [->|Ne].
    + simpl nth. destruct x; simpl Z.b2z.
      * rewrite Z.add_comm; apply Z.testbit_odd_0.
      * rewrite Z.add_0_l; apply Z.testbit_even_0.
    + replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. cbn [nth].
      rewrite <- IH by lia.
      replace i with (Z.succ (i - 1)) at 1 by lia.
      destruct x; simpl Z.b2z.
      * rewrite Z.add_comm, Z.testbit_odd_succ by lia. reflexivity.
      * rewrite Z.add_0_l, Z.testbit_even_succ by lia. reflexivity.
Qed.

Lemma reverse_loop_testbit : forall k i r c j, 0 <= i -> 0 <= j ->
  Z.testbit (ref.reverse_loop k i r c) j =
  if j <? Z.of_nat k then Z.testbit c (i + Z.of_nat k - 1 - j) else Z.testbit r (j - Z.of_nat k).
Proof.
  induction k as [|k IH]; intros i r c j Hi Hj; cbn [ref.reverse_loop].
  - simpl. replace (j - 0) with j by lia. destruct (j <? 0) eqn:E; [lia|reflexivity].
  - rewrite IH by lia.
    destruct (Z.ltb_spec j (Z.of_nat k)).
    + replace (j <? Z.of_nat (S k)) with true by (symmetry; apply Z.ltb_lt; lia).
      f_equal. lia.
    + rewrite Z.lor_spec, Z.land_spec.
      destruct (Z.ltb_spec j (Z.of_nat (S k))).
      * replace (j - Z.of_nat k) with 0 by lia.
        rewrite Z.shiftl_spec_low by lia. simpl.
        rewrite andb_true_r, <- Z.bit0_odd, Z.shiftr_spec by lia. f_equal. lia.
      * rewrite Z.shiftl_spec by lia.
        replace (Z.testbit 1 (j - Z.of_nat k)) with false.
        -- rewrite andb_false_r, orb_false_r. f_equal. lia.
        -- symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma bval_bits_msb c n : 0 <= n -> bval (bits_msb c n) = ref.reverse_bits c n.
Proof.
  intros Hn. apply Z.bits_inj'. intros j Hj.
  rewrite bval_testbit by lia. unfold ref.reverse_bits. rewrite reverse_loop_testbit by lia.
  rewrite Z2Nat.id by lia. unfold bits_msb.
  destruct (Z.ltb_spec j n).
  - rewrite rev_nth.
    2:{ unfold bits_le. rewrite map_length, seq_length. lia. }
    unfold bits_le at 1. rewrite map_length, seq_length.
    replace (Z.to_nat n - S (Z.to_nat j))%nat with (Z.to_nat (0 + n - 1 - j)) by lia.
    apply bits_le_testbit. lia.
  - rewrite Z.testbit_0_l. apply nth_overflow. rewrite rev_length. unfold bits_le.
    rewrite map_length, seq_length. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The bit buffer along a pass                                                                    *)

(* the call's input: the next bytes of src *)
Definition ictx (G: dctx) (pos: Z) (inp: list Z) : Prop :=
  dctx_ok G /\ 0 <= pos /\ pos + Zlength inp <= Zlength (dc_src G) /\
  inp = sublist pos (pos + Zlength inp) (dc_src G).

(* the machine's bit buffer holds the bits [q, 8 c) of src, c = pos + nx *)
Definition hb (G: dctx) (pos: Z) (inp: list Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= m_nx m <= Zlength inp /\ m_bits m <= 64 /\
  hold_ok G (pos + m_nx m) (m_hold m) (m_bits m).
Definition qp (pos: Z) (m: mst) : Z := 8 * (pos + m_nx m) - m_bits m.

(* the machine operations on the bit buffer only *)
Definition bop (m m': mst) : Prop :=
  m_s m' = m_s m /\ m_ret m' = m_ret m /\ m_leave m' = m_leave m /\ tfr m m'.

Lemma bop_refl m : bop m m.
Proof. split; [|split; [|split]]; auto using tfr_refl. Qed.

Lemma bop_trans m0 m1 m2 : bop m0 m1 -> bop m1 m2 -> bop m0 m2.
Proof. intros (A & B & C & D) (E & F & H & I). split; [|split; [|split]]; try congruence. eapply tfr_trans; eauto. Qed.

Lemma bop_pull m : bop m (pull m).
Proof. split; [|split; [|split]]; try reflexivity. constructor; reflexivity. Qed.

Lemma bop_drop n m : bop m (dropbits n m).
Proof. split; [|split; [|split]]; try reflexivity. constructor; reflexivity. Qed.

Lemma tfr_leave m : tfr m (set_leave m).
Proof. constructor; reflexivity. Qed.

Section Buf.
Variables (K: dkit_stmt) (G: dctx) (pos: Z) (inp: list Z).
Hypothesis (C: ictx G pos inp).

Lemma ictx_bytes : bytes_ok (dc_src G).
Proof. destruct C as ((_ & _ & _ & _ & _ & _ & B & _) & _). exact B. Qed.

Lemma hb_pull m : hb G pos inp m -> m_have m <> 0 -> m_bits m + 8 <= 64 ->
  hb G pos inp (pull m) /\ qp pos (pull m) = qp pos m /\ m_bits (pull m) = m_bits m + 8.
Proof.
  intros (I & N & _ & H) Hv Hb. unfold m_have in Hv. rewrite I in Hv.
  destruct C as (OK & P0 & PL & E).
  pose proof (proj1 H) as Hb0.
  assert (Hc: pos + m_nx m < Zlength (dc_src G)) by lia.
  pose proof (dk_pull K G _ _ _ H Hc Hb ictx_bytes) as H'.
  assert (B8: u32 (m_bits m + 8) = m_bits m + 8) by (unfold u32; rewrite Z.mod_small; lia).
  assert (Ez: Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src G)).
  { rewrite I, E at 1. rewrite Znth_sublist by lia. f_equal. lia. }
  unfold pull, qp, hb. cbn [m_inp m_nx m_hold m_bits set_m_bits set_m_hold set_m_nx]. rewrite B8, Ez.
  split; [split; [exact I | split; [lia|split; [lia|]]]|split; [lia|reflexivity]].
  replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia. exact H'.
Qed.

Lemma hb_drop m n : hb G pos inp m -> 0 <= n <= m_bits m ->
  hb G pos inp (dropbits n m) /\ qp pos (dropbits n m) = qp pos m + n /\ m_bits (dropbits n m) = m_bits m - n.
Proof.
  intros (I & N & B64 & H) Hn. pose proof (dk_drop K G _ _ _ n H Hn) as H'.
  assert (B: u32 (m_bits m - n) = m_bits m - n) by (unfold u32; rewrite Z.mod_small; lia).
  unfold dropbits, qp, hb. cbn [m_inp m_nx m_hold m_bits set_m_bits set_m_hold]. rewrite B.
  split; [split; [exact I | split; [exact N | split; [lia | exact H']]]|split; lia].
Qed.

Lemma hb_bitsn m n : hb G pos inp m -> 0 <= n <= m_bits m ->
  bitsn m n = bval (sublist (qp pos m) (qp pos m + n) (sbits G)).
Proof. intros (I & N & _ & H) Hn. unfold bitsn, qp. apply (dk_bitsn K G _ _ _ n H Hn). Qed.

Lemma hb_bits_le m : hb G pos inp m -> 0 <= m_bits m <= 8 * (pos + m_nx m).
Proof. intros (_ & _ & _ & H & _). exact H. Qed.

(* NEEDBITS(n) *)
Lemma hb_needbits : forall k n m, hb G pos inp m -> 0 <= n <= 56 -> n <= m_bits m + 8 * Z.of_nat k ->
  let m' := needbits_f k n m in
  hb G pos inp m' /\ qp pos m' = qp pos m /\ m_s m' = m_s m /\ m_ret m' = m_ret m /\ tfr m m' /\
  m_bits m' <= Z.max (m_bits m) (n + 7) /\
  ((m_leave m' = 1 /\ m_nx m' = Zlength inp /\ m_bits m' < n) \/
   (m_leave m' = m_leave m /\ n <= m_bits m')).
Proof.
  induction k; intros n m H Hn Hk; cbn [needbits_f].
  - split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply tfr_refl|]. split; [lia|]. right. split; [reflexivity|]. simpl in Hk. lia.
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [exact H|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply tfr_leave|]. split; [cbn; lia|]. left. destruct H as (A & B & _ & D).
        unfold m_have in e. rewrite A in e. cbn. split; [reflexivity|]. split; lia.
      * pose proof (hb_bits_le m H) as BL.
        destruct (hb_pull m H n0 ltac:(lia)) as (H1 & Q1 & B1).
        destruct (IHk n (pull m) H1 Hn ltac:(rewrite B1; lia)) as (A & Q & S & R & T & Bb & O).
        split; [exact A|]. split; [congruence|]. split; [exact S|]. split; [exact R|].
        split; [eapply tfr_trans; [apply bop_pull | exact T]|]. split; [rewrite B1 in Bb; lia|].
        exact O.
    + split; [exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [apply tfr_refl|]. split; [lia|]. right. split; [reflexivity|]. lia.
Qed.

End Buf.

(* ---------------------------------------------------------------------------------------------- *)
(* Lists                                                                                          *)

Lemma firstn_S_nth {A} (d: A) : forall n (l: list A), (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n; intros [|x l] H; simpl in *; try lia; [reflexivity|].
  f_equal. apply IHn. lia.
Qed.

Lemma flat_map_firstn_S {A B} (f: A -> list B) (d: A) n l : (n < length l)%nat ->
  flat_map f (firstn (S n) l) = flat_map f (firstn n l) ++ f (nth n l d).
Proof. intros H. rewrite (firstn_S_nth d) by exact H. rewrite flat_map_app. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma flat_map_split {A B} (f: A -> list B) n l :
  flat_map f l = flat_map f (firstn n l) ++ flat_map f (skipn n l).
Proof. rewrite <- flat_map_app, firstn_skipn. reflexivity. Qed.

(* the piece of element n in flat_map *)
Lemma flat_map_piece {A B} (f: A -> list B) (d: A) n l : (n < length l)%nat ->
  let o := Zlength (flat_map f (firstn n l)) in
  sublist o (o + Zlength (f (nth n l d))) (flat_map f l) = f (nth n l d).
Proof.
  intros H o. rewrite (flat_map_split f (S n) l), (flat_map_firstn_S f d n l H).
  rewrite <- app_assoc. unfold o. rewrite sublist_app2 by (pose proof (Zlength_nonneg (flat_map f (firstn n l))); lia).
  rewrite Z.sub_diag. replace (_ + _ - _) with (Zlength (f (nth n l d))) by lia.
  rewrite sublist_app1 by (pose proof (Zlength_nonneg (f (nth n l d))); lia).
  apply sublist_same; reflexivity.
Qed.

(* the length of flat_map of a constant-size function *)
Lemma Zlength_flat_map_const {A B} (f: A -> list B) c l : (forall x, Zlength (f x) = c) ->
  Zlength (flat_map f l) = c * Zlength l.
Proof.
  intros H. induction l as [|x l IH]; simpl flat_map.
  - rewrite !Zlength_nil. lia.
  - rewrite Zlength_app, IH, H, Zlength_cons. lia.
Qed.

Lemma firstn_Zlength_le {A} n (l: list A) : Zlength (firstn n l) <= Zlength l.
Proof. rewrite !Zlength_correct, firstn_length. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The layout of a block                                                                          *)

Lemma epos_ge : forall k p bs, p <= epos p bs k.
Proof.
  induction k; intros p [|b bs]; simpl; try lia.
  specialize (IHk (p + Zlength (enc_block p false b)) bs). pose proof (Zlength_nonneg (enc_block p false b)). lia.
Qed.

Lemma D0_nonneg G : 0 <= D0 G.
Proof. unfold D0. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). lia. Qed.

Lemma bpos_ge_D0 G k : D0 G <= bpos G k.
Proof. unfold bpos. pose proof (epos_ge (Z.to_nat k) 0 (dc_bs G)). lia. Qed.

Definition blk_enc (G: dctx) (k: Z) : list bool := enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k).

Lemma blk_sub (K: dkit_stmt) G k a b : dctx_ok G -> 0 <= k < nblk G -> 0 <= a <= b -> b <= Zlength (blk_enc G k) ->
  sublist (bpos G k + a) (bpos G k + b) (sbits G) = sublist a b (blk_enc G k).
Proof.
  intros OK Hk Ha Hb. destruct (dk_blk K G k OK Hk) as [E1 E2]. unfold blk_enc. rewrite <- E2.
  pose proof (bpos_ge_D0 G k). pose proof (D0_nonneg G).
  rewrite sublist_sublist by (unfold blk_enc in Hb; lia). f_equal; lia.
Qed.

Lemma bpos_succ (K: dkit_stmt) G k : dctx_ok G -> 0 <= k < nblk G -> bpos G (k + 1) = bpos G k + Zlength (blk_enc G k).
Proof. intros OK Hk. apply (dk_blk K G k OK Hk). Qed.

Lemma bpos_mono_n (K: dkit_stmt) G : dctx_ok G -> forall n k, 0 <= k -> k + Z.of_nat n <= nblk G ->
  bpos G k <= bpos G (k + Z.of_nat n).
Proof.
  intros OK n. induction n; intros k Hk Hn.
  - rewrite Z.add_0_r. lia.
  - specialize (IHn k Hk ltac:(lia)).
    pose proof (bpos_succ K G (k + Z.of_nat n) OK ltac:(lia)).
    replace (k + Z.of_nat (S n)) with (k + Z.of_nat n + 1) by lia.
    pose proof (Zlength_nonneg (blk_enc G (k + Z.of_nat n))). lia.
Qed.

Lemma bpos_mono (K: dkit_stmt) G k j : dctx_ok G -> 0 <= k <= j -> j <= nblk G -> bpos G k <= bpos G j.
Proof.
  intros OK Hk Hj. pose proof (bpos_mono_n K G OK (Z.to_nat (j - k)) k ltac:(lia) ltac:(lia)).
  replace (k + Z.of_nat (Z.to_nat (j - k))) with j in H by lia. exact H.
Qed.

Lemma bpos_endpos (K: dkit_stmt) G k : dctx_ok G -> 0 <= k <= nblk G -> bpos G k <= endpos G.
Proof.
  intros OK Hk. pose proof (bpos_mono K G k (nblk G) OK ltac:(lia) ltac:(lia)).
  destruct (dk_end K G OK) as [E _]. unfold pad8 in E.
  pose proof (Z.mod_pos_bound (8 - bpos G (nblk G) mod 8) 8 ltac:(lia)). lia.
Qed.

(* a dynamic block *)
Definition dyn_hdr14 (nlen ndist: Z) (cls: list Z) : list bool :=
  bits_le (nlen - 257) 5 ++ bits_le (ndist - 1) 5 ++ bits_le (Zlength cls - 4) 4.
Definition dyn_clb (cls: list Z) : list bool := flat_map (fun c => bits_le c 3) cls.
Definition dyn_tkb (cls: list Z) (toks: list cltok) : list bool := flat_map (send_tok (cl_lens cls)) toks.

Lemma Zlength_hdr14 nlen ndist cls : Zlength (dyn_hdr14 nlen ndist cls) = 14.
Proof. unfold dyn_hdr14. rewrite !Zlength_app, !Zlength_bits_le by lia. reflexivity. Qed.

Lemma Zlength_clb cls : Zlength (dyn_clb cls) = 3 * Zlength cls.
Proof. unfold dyn_clb. apply Zlength_flat_map_const. intros. apply Zlength_bits_le. lia. Qed.

Lemma dyn_enc G k nlen ndist cls toks syms : blk G k = Dynamic nlen ndist cls toks syms ->
  blk_enc G k = [lastflag G k =? 1; false; true] ++ dyn_hdr14 nlen ndist cls ++ dyn_clb cls ++
                dyn_tkb cls toks ++ send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms.
Proof. intros E. unfold blk_enc. rewrite E. unfold enc_block, dyn_hdr14, dyn_clb, dyn_tkb. simpl. rewrite !app_assoc. reflexivity. Qed.

Section Dyn.
Variables (K: dkit_stmt) (G: dctx) (k nlen ndist: Z) (cls: list Z) (toks: list cltok) (syms: list sym).
Hypotheses (OK: dctx_ok G) (Hk: 0 <= k < nblk G) (B: blk G k = Dynamic nlen ndist cls toks syms).

Let P := bpos G k.

Lemma dyn_len : Zlength (blk_enc G k) =
  17 + 3 * Zlength cls + Zlength (dyn_tkb cls toks) +
  Zlength (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms).
Proof.
  rewrite (dyn_enc G k _ _ _ _ _ B). rewrite !Zlength_app, Zlength_hdr14, Zlength_clb. 
  change (Zlength [lastflag G k =? 1; false; true]) with 3. lia.
Qed.

Lemma dyn_sub_hdr : sublist (P + 3) (P + 17) (sbits G) = dyn_hdr14 nlen ndist cls.
Proof.
  pose proof dyn_len. pose proof (Zlength_nonneg cls). pose proof (Zlength_nonneg (dyn_tkb cls toks)).
  pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)).
  unfold P. rewrite blk_sub by (auto; lia). rewrite (dyn_enc G k _ _ _ _ _ B).
  rewrite sublist_app2 by (rewrite !Zlength_cons, Zlength_nil; lia). rewrite !Zlength_cons, Zlength_nil. simpl Z.succ.
  rewrite sublist_app1 by (rewrite ?Zlength_hdr14; lia).
  apply sublist_same; [lia | rewrite ?Zlength_hdr14; lia].
Qed.

Lemma dyn_sub_cl i : 0 <= i < Zlength cls ->
  sublist (P + 17 + 3 * i) (P + 17 + 3 * i + 3) (sbits G) = bits_le (Znth i cls) 3.
Proof.
  intros Hi. pose proof dyn_len. pose proof (Zlength_nonneg (dyn_tkb cls toks)).
  pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)).
  unfold P. rewrite <- !Z.add_assoc. rewrite blk_sub by (auto; lia). rewrite (dyn_enc G k _ _ _ _ _ B).
  rewrite sublist_app2 by (rewrite !Zlength_cons, Zlength_nil; lia). rewrite !Zlength_cons, Zlength_nil. simpl Z.succ.
  rewrite sublist_app2 by (rewrite ?Zlength_hdr14; lia). rewrite Zlength_hdr14.
  rewrite sublist_app1 by (rewrite ?Zlength_clb; lia).
  pose proof (flat_map_piece (fun c => bits_le c 3) 0 (Z.to_nat i) cls ltac:(rewrite Zlength_correct in Hi; lia)) as F.
  cbv zeta in F. rewrite Zlength_flat_map_const with (c := 3) in F by (intros; apply Zlength_bits_le; lia).
  rewrite Zlength_bits_le in F by lia. rewrite Zlength_firstn in F.
  replace (Z.min (Z.max 0 i) (Zlength cls)) with i in F by lia.
  unfold dyn_clb. replace (Znth i cls) with (nth (Z.to_nat i) cls 0)
    by (unfold Znth; destruct (Z_lt_dec i 0); [lia | reflexivity]).
  replace (17 + 3 * i - 3 - 14) with (3 * i) by lia.
  replace (17 + (3 * i + 3) - 3 - 14) with (3 * i + 3) by lia. exact F.
Qed.
Lemma tok_off_succ t : 0 <= t < Zlength toks ->
  tok_off (cl_lens cls) toks (t + 1) = tok_off (cl_lens cls) toks t + Zlength (send_tok (cl_lens cls) (tok_at toks t)).
Proof.
  intros Ht. unfold tok_off, tok_at. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite (flat_map_firstn_S _ (CLen 0)) by (rewrite Zlength_correct in Ht; lia). rewrite Zlength_app. reflexivity.
Qed.

Lemma tok_off_range t : 0 <= t <= Zlength toks ->
  0 <= tok_off (cl_lens cls) toks t <= Zlength (dyn_tkb cls toks).
Proof.
  intros Ht. unfold tok_off, dyn_tkb. split; [apply Zlength_nonneg|].
  rewrite (flat_map_split _ (Z.to_nat t) toks). rewrite Zlength_app.
  pose proof (Zlength_nonneg (flat_map (send_tok (cl_lens cls)) (skipn (Z.to_nat t) toks))). lia.
Qed.

Lemma tok_off_all : tok_off (cl_lens cls) toks (Zlength toks) = Zlength (dyn_tkb cls toks).
Proof. unfold tok_off, dyn_tkb. rewrite firstn_all2 by (rewrite Zlength_correct; lia). reflexivity. Qed.

Lemma dyn_sub_tok t : 0 <= t < Zlength toks ->
  let q := P + 17 + 3 * Zlength cls + tok_off (cl_lens cls) toks t in
  sublist q (q + Zlength (send_tok (cl_lens cls) (tok_at toks t))) (sbits G) = send_tok (cl_lens cls) (tok_at toks t).
Proof.
  intros Ht q. pose proof dyn_len. pose proof (Zlength_nonneg cls).
  pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)).
  pose proof (tok_off_range (t + 1) ltac:(lia)) as R1. rewrite tok_off_succ in R1 by lia.
  pose proof (tok_off_range t ltac:(lia)) as R0.
  pose proof (Zlength_nonneg (send_tok (cl_lens cls) (tok_at toks t))).
  unfold q, P. rewrite <- !Z.add_assoc. rewrite blk_sub by (auto; lia). rewrite (dyn_enc G k _ _ _ _ _ B).
  rewrite sublist_app2 by (rewrite !Zlength_cons, Zlength_nil; lia). rewrite !Zlength_cons, Zlength_nil. simpl Z.succ.
  rewrite sublist_app2 by (rewrite ?Zlength_hdr14; lia). rewrite Zlength_hdr14.
  rewrite sublist_app2 by (rewrite ?Zlength_clb; lia). rewrite Zlength_clb.
  rewrite sublist_app1 by lia.
  pose proof (flat_map_piece (send_tok (cl_lens cls)) (CLen 0) (Z.to_nat t) toks
                ltac:(rewrite Zlength_correct in Ht; lia)) as F.
  cbv zeta in F. unfold tok_off, tok_at, dyn_tkb in *.
  match goal with |- sublist ?a ?b _ = _ => match type of F with sublist ?a' ?b' _ = _ =>
    replace a with a' by lia; replace b with b' by lia end end. exact F.
Qed.

Lemma dyn_toks_end : P + 17 + 3 * Zlength cls + Zlength (dyn_tkb cls toks) <= bpos G (k + 1).
Proof.
  pose proof dyn_len. pose proof (Zlength_nonneg (send_syms (dyn_ll nlen toks) (dyn_dl nlen ndist toks) syms)).
  rewrite (bpos_succ K G k OK Hk). unfold P. lia.
Qed.

End Dyn.

(* ---------------------------------------------------------------------------------------------- *)
(* What a pass gives, and the parts                                                               *)

(* the end of the deflate stream is within the stream *)
Definition slen_ok (G: dctx) : Prop := endpos G <= 8 * slen G.

(* leaving for want of input inside the deflate stream *)
Lemma leave_slen G pos (inp: list Z) m n :
  slen_ok G -> m_nx m = Zlength inp -> m_bits m < n -> qp pos m + n <= endpos G -> pos + Zlength inp < slen G.
Proof. unfold slen_ok, qp. intros S N B Q. rewrite N in Q. lia. Qed.

(* the facts of the state the pass needs besides Kd *)
Definition tabs_ok (s: istate) : Prop :=
  Zlength (i_lens s) = 320 /\ Zlength (i_codes s) = ENOUGH_CODES /\ Forall entry_ok (i_codes s).

(* a state of the pass at a loop head (or between its parts) *)
Definition tin (G: dctx) (pos: Z) (inp ob: list Z) (m: mst) : Prop :=
  Kd G pos inp ob m /\ m_leave m = 0 /\ 0 <= m_nx m <= Zlength inp /\ tabs_ok (m_s m).

(* the result of the pass: it leaves for want of input, or it reaches LEN_ (Z_TREES / LEN's pass) *)
Definition tt_ok (G: dctx) (pos: Z) (inp ob ow0: list Z) (p: ttab_res) : Prop :=
  match p with
  | TTDone (IBrk m') => Kd G pos inp ob m' /\ m_ow m' = ow0 /\ m_leave m' = 1 /\
                        m_nx m' = Zlength inp /\ pos + Zlength inp < slen G
  | TTDone (IRet _ _) => False
  | TTLen m' => Kd G pos inp ob m' /\ m_ow m' = ow0 /\ m_leave m' = 0 /\ m_mode m' = LEN_
  end.

(* the parts *)
Definition part_tab_stmt : Prop :=
  forall G pos inp ob m, dkit_stmt -> ictx G pos inp -> slen_ok G -> tin G pos inp ob m -> m_mode m = TABLE ->
  (forall m', tin G pos inp ob m' -> m_mode m' = LENLENS -> m_ow m' = m_ow m ->
     tt_ok G pos inp ob (m_ow m) (ttab_ll m')) ->
  tt_ok G pos inp ob (m_ow m) (ttab_tab m).

Definition part_ll_stmt : Prop :=
  forall G pos inp ob m, dkit_stmt -> tabdec_stmt -> ictx G pos inp -> slen_ok G -> tin G pos inp ob m ->
  m_mode m = LENLENS ->
  (forall m', tin G pos inp ob m' -> m_mode m' = CODELENS -> m_ow m' = m_ow m ->
     tt_ok G pos inp ob (m_ow m) (ttab_cl m')) ->
  tt_ok G pos inp ob (m_ow m) (ttab_ll m).

(* one token of CODELENS *)
Definition part_iter_stmt : Prop :=
  forall G pos inp ob m, dkit_stmt -> ictx G pos inp -> slen_ok G -> tin G pos inp ob m ->
  m_mode m = CODELENS -> i_have (m_s m) < i_nlen (m_s m) + i_ndist (m_s m) ->
  match codelens_iter lenfix_list distfix_list m with
  | CLnext m' => tin G pos inp ob m' /\ m_mode m' = CODELENS /\ m_ow m' = m_ow m /\
                 i_have (m_s m) < i_have (m_s m')
  | CLleave m' => tt_ok G pos inp ob (m_ow m) (TTDone (IBrk m'))
  | CLbad _ => False
  end.

(* CODELENS: the loop and the tables *)
Definition part_cl_stmt : Prop :=
  forall G pos inp ob m, dkit_stmt -> tabdec_stmt -> ictx G pos inp -> slen_ok G -> tin G pos inp ob m ->
  m_mode m = CODELENS -> part_iter_stmt ->
  tt_ok G pos inp ob (m_ow m) (ttab_cl m).

(* Part of DecDec.group_dec: decoding one code (lookup1/lookup2/DROPBITS) of c_LEN / c_DIST.  Statement: DecDecDefs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.DecDecDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Lengths, prefixes, bit arithmetic                                                              *)

Lemma dl_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros H. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma dl_send_sym_len lens s : 0 <= Znth s lens -> Zlength (send_sym lens s) = Znth s lens.
Proof. intros H. unfold send_sym, bits_msb. rewrite Zlength_rev. apply dl_bits_le_len; auto. Qed.

Lemma dl_bytes_bits_len l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, dl_bits_le_len, IH, Zlength_cons by lia. lia.
Qed.

Lemma dl_prefix (S: list bool) q a b :
  0 <= q -> 0 <= a -> 0 <= b -> q + a <= Zlength S -> q + b <= Zlength S ->
  (exists R, sublist q (q + a) S ++ R = sublist q (q + b) S) \/
  (exists R, sublist q (q + a) S = sublist q (q + b) S ++ R).
Proof.
  intros. destruct (Z.le_ge_cases a b).
  - left. exists (sublist (q + a) (q + b) S). rewrite (sublist_split q (q + a) (q + b)) by lia. reflexivity.
  - right. exists (sublist (q + b) (q + a) S). rewrite (sublist_split q (q + b) (q + a)) by lia. reflexivity.
Qed.

Lemma dl_shiftr_mod h a o : 0 <= a -> 0 <= o ->
  Z.shiftr (h mod 2 ^ (a + o)) a = Z.shiftr h a mod 2 ^ o.
Proof.
  intros Ha Ho. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i o).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma dl_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small. exact H. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Links                                                                                          *)

Lemma dl_islink_of kind op : ref.is_link op = true -> islink kind op = true.
Proof.
  unfold ref.is_link, islink. intros H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite H1, H2. destruct (kind =? DISTS); reflexivity.
Qed.

Lemma dl_not_is_link kind op : islink kind op = false -> ref.is_link op = false.
Proof.
  intros H. destruct (ref.is_link op) eqn:E; [|reflexivity].
  rewrite (dl_islink_of kind op E) in H. discriminate.
Qed.

Lemma dl_is_link kind op : islink kind op = true -> 1 <= op -> ref.is_link op = true.
Proof.
  unfold ref.is_link, islink. intros H Hop. apply andb_prop in H. destruct H as [_ H2].
  rewrite H2. destruct (Z.eqb_spec op 0); [lia|reflexivity].
Qed.

Section Walk.
Variables (kind: Z) (s: istate) (t: tref) (rb sz: Z).
Variable TV: tvalid_b kind lenfix_list distfix_list s t rb sz.

Lemma dl_root_ok h : 
  let e := tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb) in
  entry_ok e /\
  (if islink kind (e_op e) then sub_ok kind (tab_entry lenfix_list distfix_list s t) rb sz e
   else e_bits e <= rb /\ final_ok kind e).
Proof.
  destruct TV as [R _ T]. apply T. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma dl_twalk_final h :
  islink kind (e_op (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb))) = false ->
  let e := tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb) in
  twalk s t rb h = Some (e_op e, e_val e, e_bits e).
Proof.
  intros H. unfold twalk. cbv zeta. rewrite (dl_not_is_link kind _ H). reflexivity.
Qed.

Lemma dl_twalk_link h :
  islink kind (e_op (tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb))) = true ->
  let e := tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb) in
  let e2 := tab_entry lenfix_list distfix_list s t
              (e_val e + Z.shiftr (h mod 2 ^ (e_bits e + e_op e)) (e_bits e)) in
  twalk s t rb h = Some (e_op e2, e_val e2, e_bits e + e_bits e2) /\ e_bits e = rb /\ 1 <= e_op e /\
  0 <= e_bits e2 /\ islink kind (e_op e2) = false.
Proof.
  intros H. cbv zeta. pose proof (dl_root_ok h) as RO. cbv zeta in RO. rewrite H in RO.
  destruct RO as [EO (S1 & S2 & S3 & S4)].
  set (e := tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb)) in *.
  assert (J: 0 <= Z.shiftr h (e_bits e) mod 2 ^ e_op e < 2 ^ e_op e)
    by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (S4 _ J) as (B1 & B2 & B3 & B4 & B5). cbv zeta in B1, B2, B3, B4, B5.
  pose proof EO as (_ & EO2 & _). rewrite dl_shiftr_mod by lia.
  unfold twalk. cbv zeta. fold e. rewrite (dl_is_link kind _ H S2).
  rewrite (dl_not_is_link kind _ B3).
  split; [reflexivity|]. split; [exact S1|]. split; [exact S2|]. split; [|exact B3].
  destruct B2 as (_ & B2 & _). lia.
Qed.

End Walk.

(* ---------------------------------------------------------------------------------------------- *)
(* The walk on the valid bits of the bit buffer                                                   *)

Lemma dl_walk_at (WK: walk_stmt) G c h b s t rb kind lens sy q :
  dctx_ok G -> hold_ok G c h b -> q = 8 * c - b ->
  tdec s t rb kind lens -> lens_ok lens -> (complete lens \/ single lens) -> used lens sy ->
  sublist q (q + Znth sy lens) (sbits G) = send_sym lens sy -> q + Znth sy lens <= 8 * slen G ->
  exists op val L, twalk s t rb h = Some (op, val, L) /\ (L <= b <-> Znth sy lens <= b) /\
    (L <= b -> L = Znth sy lens /\ ref.means_symbol kind sy op val = true).
Proof.
  intros Hok (Hb & Hc & Hh) Hq Htd Hlo Hcs Hus Hsb Hsl.
  destruct Hok as (_ & _ & _ & _ & Hsl' & _).
  destruct Hus as [Hsy Hnz].
  assert (HL: 0 <= Znth sy lens <= 15) by (apply (Forall_Znth _ _ _ Hsy Hlo)).
  pose proof (dl_bytes_bits_len (dc_src G)) as LS. fold (sbits G) in LS.
  assert (E8: 8 * c = q + b) by lia.
  rewrite E8 in Hh.
  assert (LV: Zlength (sublist q (q + b) (sbits G)) = b) by (rewrite Zlength_sublist; lia).
  assert (PF: (exists R, sublist q (q + b) (sbits G) ++ R = send_sym lens sy) \/
              (exists R, sublist q (q + b) (sbits G) = send_sym lens sy ++ R)).
  { rewrite <- Hsb. apply dl_prefix; lia. }
  assert (PF': sublist q (q + b) (sbits G) ++ sublist (q + b) (q + Znth sy lens) (sbits G) = send_sym lens sy \/
               sublist q (q + b) (sbits G) = send_sym lens sy ++ sublist (q + Znth sy lens) (q + b) (sbits G)).
  { rewrite <- Hsb. destruct (Z.le_ge_cases b (Znth sy lens)).
    - left. rewrite <- sublist_split by lia. reflexivity.
    - right. rewrite <- sublist_split by lia. reflexivity. }
  clear PF. replace (q + b - b) with q in Hh by lia.
  assert (WW: exists op val L, twalk s t rb (bval (sublist q (q + b) (sbits G))) = Some (op, val, L) /\
      (L <= Zlength (sublist q (q + b) (sbits G)) <-> Znth sy lens <= Zlength (sublist q (q + b) (sbits G))) /\
      (L <= Zlength (sublist q (q + b) (sbits G)) -> L = Znth sy lens /\ ref.means_symbol kind sy op val = true)).
  { destruct PF' as [P|P].
    - exact (WK s t rb kind lens sy _ _ Htd Hlo Hcs (conj Hsy Hnz) (or_introl P)).
    - exact (WK s t rb kind lens sy _ _ Htd Hlo Hcs (conj Hsy Hnz) (or_intror P)). }
  destruct WW as (op & val & L & W1 & W2 & W3).
  rewrite LV in W2, W3. rewrite <- Hh in W1.
  exists op, val, L. auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at its place in the input                                                          *)

Definition dl_cfg (G: dctx) (pos: Z) (inp: list Z) (q: Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= m_nx m <= Zlength inp /\ hold_ok G (pos + m_nx m) (m_hold m) (m_bits m) /\
  8 * (pos + m_nx m) - m_bits m = q.

Lemma dl_pull (K: dkit_stmt) G pos inp q m :
  in_ctx G pos inp -> dl_cfg G pos inp q m -> m_have m <> 0 -> m_bits m + 8 <= 64 ->
  dl_cfg G pos inp q (pull m) /\ m_bits (pull m) = m_bits m + 8 /\ m_s (pull m) = m_s m /\
  m_leave (pull m) = m_leave m /\ m_nx (pull m) = m_nx m + 1 /\
  pull m = set_m_bits (set_m_hold (set_m_nx m (m_nx m + 1)) (m_hold (pull m))) (m_bits (pull m)).
Proof.
  intros (Hok & Hpos & Hlen & Hinp) (Hi & Hnx & Hh & Hq) Hhave Hb.
  unfold m_have in Hhave. rewrite Hi in Hhave.
  pose proof Hh as (Hb0 & _ & _).
  assert (Hc: pos + m_nx m < Zlength (dc_src G)) by lia.
  assert (BO: bytes_ok (dc_src G)) by (destruct Hok as (_ & _ & _ & _ & _ & _ & BO & _); exact BO).
  pose proof (dk_pull K G _ _ _ Hh Hc Hb BO) as P.
  assert (ZB: Znth (m_nx m) (m_inp m) = Znth (pos + m_nx m) (dc_src G)).
  { rewrite Hi, Hinp. rewrite Znth_sublist by lia. f_equal. lia. }
  unfold pull. cbn [m_inp m_nx m_hold m_bits m_s m_leave set_m_nx set_m_hold set_m_bits].
  rewrite ZB. rewrite dl_u32 by lia. unfold u64.
  split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity|reflexivity]]]]].
  unfold dl_cfg. cbn [m_inp m_nx m_hold m_bits set_m_nx set_m_hold set_m_bits].
  split; [exact Hi|]. split; [lia|]. split.
  - replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia. exact P.
  - lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The two lookup loops                                                                           *)

Section Loops.
Variables (K: dkit_stmt) (WK: walk_stmt) (G: dctx) (pos: Z) (inp: list Z) (q: Z).
Variables (kind: Z) (s: istate) (t: tref) (rb sz: Z) (lens: list Z) (sy: Z).
Variables (Hctx: in_ctx G pos inp) (TV: tvalid_b kind lenfix_list distfix_list s t rb sz)
  (Htd: tdec s t rb kind lens) (Hlo: lens_ok lens) (Hcs: complete lens \/ single lens) (Hus: used lens sy)
  (Hsb: sublist q (q + Znth sy lens) (sbits G) = send_sym lens sy) (Hsl: q + Znth sy lens <= 8 * slen G).

Let L := Znth sy lens.

Lemma dl_L : 0 <= L <= 15.
Proof. destruct Hus as [Hsy _]. apply (Forall_Znth _ _ _ Hsy Hlo). Qed.

Lemma dl_walk m : dl_cfg G pos inp q m ->
  exists op val L', twalk s t rb (m_hold m) = Some (op, val, L') /\ (L' <= m_bits m <-> L <= m_bits m) /\
    (L' <= m_bits m -> L' = L /\ ref.means_symbol kind sy op val = true).
Proof.
  intros (_ & _ & Hh & Hq). destruct Hctx as (Hok & _).
  exact (dl_walk_at WK G _ _ _ s t rb kind lens sy q Hok Hh (eq_sym Hq) Htd Hlo Hcs Hus Hsb Hsl).
Qed.

Lemma dl_out m : dl_cfg G pos inp q m -> m_nx m = Zlength inp -> m_bits m < L -> pos + Zlength inp < slen G.
Proof. intros (_ & _ & _ & Hq) E Hb. lia. Qed.

Lemma dl_lk1 : forall k m, dl_cfg G pos inp q m -> m_s m = s -> 1 <= Z.of_nat k ->
  L <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup1_f k lenfix_list distfix_list t rb m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_nx m <= nx <= Zlength inp /\ hold_ok G (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
    (b = m_bits m \/ b < L + 8) /\
    (ok = true -> lv = m_leave m /\ here = tab_entry lenfix_list distfix_list s t (h mod 2 ^ rb) /\
                  e_bits here <= b) /\
    (ok = false -> lv = 1 /\ nx = Zlength inp /\ b < L).
Proof.
  pose proof dl_L as HL.
  induction k as [|k IH]; intros m Hcfg Hs Hk Hfu; [cbn in Hk; lia|].
  cbn [lookup1_f]. unfold bitsn. rewrite Hs.
  pose proof Hcfg as (Hi & Hnx & Hh & Hq).
  destruct (Z.leb_spec (e_bits (tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb))) (m_bits m))
    as [Hst|Hst].
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [exact Hh|]. split; [exact Hq|]. split; [left; reflexivity|].
    split; [|discriminate]. intros _. auto.
  - (* not stopping: the code is longer than the bits *)
    assert (HLb: m_bits m < L).
    { destruct (dl_walk m Hcfg) as (op & val & L' & W1 & W2 & _).
      destruct (islink kind (e_op (tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)))) eqn:LK.
      - destruct (dl_twalk_link kind s t rb sz TV (m_hold m) LK) as (T1 & T2 & _ & T4 & _).
        rewrite T1 in W1. injection W1 as <- <- <-.
        destruct (Z.lt_ge_cases (m_bits m) L); [lia|]. apply W2 in H. lia.
      - rewrite (dl_twalk_final kind s t rb (m_hold m) LK) in W1. injection W1 as <- <- <-.
        destruct (Z.lt_ge_cases (m_bits m) L); [lia|]. apply W2 in H. lia. }
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
      split; [lia|]. split; [exact Hh|]. split; [exact Hq|]. split; [left; reflexivity|].
      split; [discriminate|]. intros _. unfold m_have in H0. rewrite Hi in H0. split; [reflexivity|]. lia.
    + destruct (dl_pull K G pos inp q m Hctx Hcfg H0 ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
      specialize (IH (pull m) C1 ltac:(rewrite C3; exact Hs)).
      assert (Hk': 1 <= Z.of_nat k) by (destruct k; cbn in Hfu |- *; lia).
      specialize (IH Hk' ltac:(rewrite C2; lia)).
      destruct (lookup1_f k lenfix_list distfix_list t rb (pull m)) as [[here m'] ok].
      destruct IH as (nx & h & b & lv & E & R1 & R2 & R3 & R4 & R5 & R6).
      exists nx, h, b, lv. split.
      { rewrite E, C6. destruct m; reflexivity. }
      rewrite C5, C2, C4 in *. split; [lia|]. split; [exact R2|]. split; [exact R3|].
      split; [lia|]. split; [exact R5|exact R6].
Qed.

Lemma dl_lk2 : forall k m last, dl_cfg G pos inp q m -> m_s m = s -> rb <= m_bits m ->
  last = tab_entry lenfix_list distfix_list s t (bval (sublist q (q + rb) (sbits G))) ->
  islink kind (e_op last) = true -> 1 <= Z.of_nat k -> L <= m_bits m + 8 * (Z.of_nat k - 1) ->
  let '(here, m', ok) := lookup2_f k lenfix_list distfix_list t last m in
  exists nx h b lv, m' = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv /\
    m_nx m <= nx <= Zlength inp /\ hold_ok G (pos + nx) h b /\ 8 * (pos + nx) - b = q /\
    (b = m_bits m \/ b < L + 8) /\
    (ok = true -> lv = m_leave m /\ e_bits last = rb /\ 0 <= e_bits here /\ L = e_bits last + e_bits here /\
                  L <= b /\ ref.means_symbol kind sy (e_op here) (e_val here) = true) /\
    (ok = false -> lv = 1 /\ nx = Zlength inp /\ b < L).
Proof.
  pose proof dl_L as HL.
  induction k as [|k IH]; intros m last Hcfg Hs Hrb Hlast Hlk Hk Hfu; [cbn in Hk; lia|].
  pose proof Hcfg as (Hi & Hnx & Hh & Hq).
  (* the root entry of the current hold is last *)
  assert (Hroot: last = tab_entry lenfix_list distfix_list s t (m_hold m mod 2 ^ rb)).
  { rewrite Hlast. f_equal. rewrite (dk_bitsn K G _ _ _ rb Hh) by (pose proof (tv_rb _ _ _ _ TV); lia).
    rewrite Hq. reflexivity. }
  rewrite Hroot in Hlk.
  destruct (dl_twalk_link kind s t rb sz TV (m_hold m) Hlk) as (T1 & T2 & T3 & T4 & T5).
  rewrite <- Hroot in T1, T2, T3, T4, T5.
  destruct (dl_walk m Hcfg) as (op & val & L' & W1 & W2 & W3).
  rewrite T1 in W1. injection W1 as Eop Eval EL. subst op val L'.
  cbn [lookup2_f]. unfold bitsn. rewrite Hs.
  set (e2 := tab_entry lenfix_list distfix_list s t
               (e_val last + Z.shiftr (m_hold m mod 2 ^ (e_bits last + e_op last)) (e_bits last))) in *.
  destruct (Z.leb_spec (e_bits last + e_bits e2) (m_bits m)) as [Hst|Hst].
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. split; [exact Hh|]. split; [exact Hq|]. split; [left; reflexivity|].
    split; [|discriminate]. intros _. destruct (W3 Hst) as [W4 W5].
    split; [reflexivity|]. split; [exact T2|]. split; [exact T4|]. split; [lia|]. split; [lia|exact W5].
  - assert (HLb: m_bits m < L).
    { destruct (Z.lt_ge_cases (m_bits m) L); [lia|]. apply W2 in H. lia. }
    destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
      split; [lia|]. split; [exact Hh|]. split; [exact Hq|]. split; [left; reflexivity|].
      split; [discriminate|]. intros _. unfold m_have in H0. rewrite Hi in H0. split; [reflexivity|]. lia.
    + destruct (dl_pull K G pos inp q m Hctx Hcfg H0 ltac:(lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
      assert (Hk': 1 <= Z.of_nat k) by (destruct k; cbn in Hfu |- *; lia).
      specialize (IH (pull m) last C1 ltac:(rewrite C3; exact Hs) ltac:(lia) Hlast
                    ltac:(rewrite Hroot; exact Hlk) Hk' ltac:(rewrite C2; lia)).
      destruct (lookup2_f k lenfix_list distfix_list t last (pull m)) as [[here m'] ok].
      destruct IH as (nx & h & b & lv & E & R1 & R2 & R3 & R4 & R5 & R6).
      exists nx, h, b, lv. split.
      { rewrite E, C6. destruct m; reflexivity. }
      rewrite C5, C2, C4 in *. split; [lia|]. split; [exact R2|]. split; [exact R3|].
      split; [lia|]. split; [exact R5|exact R6].
Qed.

End Loops.

(* ---------------------------------------------------------------------------------------------- *)
(* The shape of the machine                                                                        *)

Lemma dl_shape_upd m nx h b lv f :
  upd_s (set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx) h) b) lv) f =
  set_m_leave (set_m_bits (set_m_hold (set_m_nx (upd_s m f) nx) h) b) lv.
Proof. destruct m; reflexivity. Qed.

Lemma dl_shape_drop M nx h b lv n :
  dropbits n (set_m_leave (set_m_bits (set_m_hold (set_m_nx M nx) h) b) lv) =
  set_m_leave (set_m_bits (set_m_hold (set_m_nx M nx) (Z.shiftr h n)) (u32 (b - n))) lv.
Proof. destruct M; reflexivity. Qed.

Lemma dl_shape_twice M nx h b lv nx' h' b' lv' :
  set_m_leave (set_m_bits (set_m_hold (set_m_nx
    (set_m_leave (set_m_bits (set_m_hold (set_m_nx M nx) h) b) lv) nx') h') b') lv' =
  set_m_leave (set_m_bits (set_m_hold (set_m_nx M nx') h') b') lv'.
Proof. destruct M; reflexivity. Qed.

Lemma dl_upd_id m : upd_s m (fun s => set_i_back s (i_back (m_s m))) = m.
Proof.
  unfold upd_s. replace (set_i_back (m_s m) (i_back (m_s m))) with (m_s m) by (destruct (m_s m); reflexivity).
  destruct m; reflexivity.
Qed.

Lemma dl_upd_back2 m a b :
  upd_s (upd_s m (fun s => set_i_back s (i_back s + a))) (fun s => set_i_back s (i_back s + b)) =
  upd_s m (fun s => set_i_back s (i_back s + a + b)).
Proof. destruct m; reflexivity. Qed.

Lemma dcode_ok : dkit_stmt -> walk_stmt -> dcode_stmt.
Proof.
  intros K WK G pos inp m kind t rb lens sy q Hctx Hbuf Hq Hkind Htv Htd Hlo Hcs Hus Hsb Hsl Hb0.
  destruct Htv as (sz & _ & TV).
  pose proof (tv_rb _ _ _ _ TV) as Hrb.
  assert (HL: 0 <= Znth sy lens <= 15) by (destruct Hus as [Hsy _]; apply (Forall_Znth _ _ _ Hsy Hlo)).
  pose proof Hctx as (Hok & Hpos & Hlen & Hinp).
  destruct Hbuf as (Hi & Hnx & Hh).
  pose proof Hh as (Hbb & _).
  assert (Hcfg: dl_cfg G pos inp q m) by (split; [exact Hi|]; split; [lia|]; split; [exact Hh|lia]).
  pose proof (dl_lk1 K WK G pos inp q kind (m_s m) t rb sz lens sy Hctx TV Htd Hlo Hcs Hus Hsb Hsl 3 m Hcfg
                eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as LK1.
  unfold dcode, lookup1.
  destruct (lookup1_f 3 lenfix_list distfix_list t rb m) as [[here m1] ok1].
  destruct LK1 as (nx1 & h1 & b1 & lv1 & E1 & N1 & H1 & Q1 & B1 & S1 & F1).
  destruct ok1; cbn [negb].
  2: { destruct (F1 eq_refl) as (Lv & Nx & Bl). subst m1.
       exists nx1, h1, b1, (i_back (m_s m)), lv1. rewrite dl_upd_id.
       split; [reflexivity|]. split; [lia|]. split; [exact H1|]. split; [discriminate|].
       intros _. split; [exact Lv|]. split; [exact Nx|]. split; [exact Q1|]. split; [exact Bl|]. lia. }
  destruct (S1 eq_refl) as (Lv1 & Here1 & Hst1).
  pose proof H1 as (Hb1 & _).
  assert (Hcfg1: dl_cfg G pos inp q m1).
  { subst m1. unfold dl_cfg. cbn [m_inp m_nx m_hold m_bits set_m_leave set_m_bits set_m_hold set_m_nx].
    split; [exact Hi|]. split; [lia|]. split; [exact H1|lia]. }
  destruct (islink kind (e_op here)) eqn:LKh.
  - (* a link: the second level *)
    pose proof (dl_twalk_link kind (m_s m) t rb sz TV h1) as TL. rewrite <- Here1 in TL.
    destruct (TL LKh) as (_ & Erb & _).
    assert (Hlast: here = tab_entry lenfix_list distfix_list (m_s m) t (bval (sublist q (q + rb) (sbits G)))).
    { rewrite Here1. f_equal. rewrite (dk_bitsn K G _ _ _ rb H1) by lia. rewrite Q1. reflexivity. }
    assert (Ms1: m_s m1 = m_s m) by (subst m1; reflexivity).
    assert (Mb1: m_bits m1 = b1) by (subst m1; reflexivity).
    assert (Mn1: m_nx m1 = nx1) by (subst m1; reflexivity).
    assert (Ml1: m_leave m1 = lv1) by (subst m1; reflexivity).
    pose proof (dl_lk2 K WK G pos inp q kind (m_s m) t rb sz lens sy Hctx TV Htd Hlo Hcs Hus Hsb Hsl 3 m1 here
                  Hcfg1 Ms1 ltac:(lia) Hlast LKh ltac:(cbn; lia) ltac:(cbn; lia)) as LK2.
    unfold lookup2.
    destruct (lookup2_f 3 lenfix_list distfix_list t here m1) as [[here2 m2] ok2].
    destruct LK2 as (nx2 & hh2 & b2 & lv2 & E2 & N2 & H2 & Q2 & B2 & S2 & F2).
    rewrite Mb1, Mn1, Ml1 in *.
    subst m1. rewrite dl_shape_twice in E2. subst m2.
    destruct ok2; cbn [negb].
    + destruct (S2 eq_refl) as (Lv2 & Eb & Eh2 & EL & HLb & Hmean).
      repeat (rewrite dl_shape_upd || rewrite dl_shape_drop).
      rewrite (dl_u32 (b2 - e_bits here)) by lia.
      rewrite (dl_u32 (b2 - e_bits here - e_bits here2)) by lia.
      rewrite dl_upd_back2.
      exists nx2, (Z.shiftr (Z.shiftr hh2 (e_bits here)) (e_bits here2)), (b2 - e_bits here - e_bits here2),
        (i_back (m_s m) + e_bits here + e_bits here2), lv2.
      split; [reflexivity|]. split; [lia|]. split.
      { apply (dk_drop K). - apply (dk_drop K); [exact H2|lia]. - lia. }
      split; [|discriminate].
      intros _. split; [congruence|]. split; [exact Hmean|]. split; lia.
    + destruct (F2 eq_refl) as (Lv & Nx & Bl).
      exists nx2, hh2, b2, (i_back (m_s m)), lv2. rewrite dl_upd_id.
      split; [reflexivity|]. split; [lia|]. split; [exact H2|]. split; [discriminate|].
      intros _. split; [exact Lv|]. split; [exact Nx|]. split; [exact Q2|]. split; [exact Bl|]. lia.
  - (* a final root entry *)
    cbn [negb].
    pose proof (dl_twalk_final kind (m_s m) t rb h1) as TF. rewrite <- Here1 in TF. specialize (TF LKh).
    destruct (dl_walk_at WK G (pos + nx1) h1 b1 (m_s m) t rb kind lens sy q Hok H1 (eq_sym Q1) Htd Hlo Hcs Hus
                Hsb Hsl) as (op & val & L' & W1 & W2 & W3).
    rewrite TF in W1. injection W1 as <- <- <-.
    destruct (W3 Hst1) as [EL Hmean].
    subst m1. repeat (rewrite dl_shape_upd || rewrite dl_shape_drop).
    rewrite (dl_u32 (b1 - e_bits here)) by lia.
    exists nx1, (Z.shiftr h1 (e_bits here)), (b1 - e_bits here), (i_back (m_s m) + e_bits here), lv1.
    split; [reflexivity|]. split; [lia|]. split.
    { apply (dk_drop K); [exact H1|lia]. }
    split; [|discriminate].
    intros _. split; [exact Lv1|]. split; [exact Hmean|]. split; lia.
Qed.

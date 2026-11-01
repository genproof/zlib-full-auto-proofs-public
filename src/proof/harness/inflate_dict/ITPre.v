(* Law inflate_dict, theory part: the inflate() calls on a zlib stream before the dictionary:
   HEAD (the 2 header bytes, FDICT), DICTID (the 4 bytes of the id), DICT: Z_NEED_DICT after exactly 6 bytes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Require Zlib.proof.harness.inflate_codes.TheoryHead Zlib.proof.harness.inflate_codes.TheoryDict.
Import ListNotations.
Local Open Scope Z_scope.


Module TD := Zlib.proof.harness.inflate_codes.TheoryDefs.
Module TH := Zlib.proof.harness.inflate_codes.TheoryHead.
Module TDi := Zlib.proof.harness.inflate_codes.TheoryDict.

(* ---------------------------------------------------------------------------------------------- *)
(* Facts on the stream                                                                            *)

Lemma itp_le l : it_le l = TD.le_val l.
Proof. induction l as [|b l IH]; cbn [it_le TD.le_val]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma itp_bval l : 0 <= bval l < 2 ^ Z.of_nat (length l).
Proof.
  induction l as [|b l IH]; cbn [bval length]; [cbn; lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma itp_pack bs : bytes_ok (pack bs).
Proof.
  unfold bytes_ok, pack. rewrite Forall_map, Forall_forall. intros k _.
  pose proof (itp_bval (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) as B.
  assert (Lk : (length (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs) <= 8)%nat).
  { unfold sublist. rewrite skipn_length, firstn_length. lia. }
  assert (2 ^ Z.of_nat (length (sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs)) <= 2 ^ 8)
    by (apply Z.pow_le_mono_r; lia).
  change Byte.max_unsigned with 255. change (2 ^ 8) with 256 in *. unfold Basics.compose. lia.
Qed.

Lemma itp_be_bytes v n : bytes_ok (be_bytes v n).
Proof.
  unfold bytes_ok, be_bytes, le_bytes. apply Forall_rev. rewrite Forall_map, Forall_forall. intros i _.
  change Byte.max_unsigned with 255. pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256). unfold Basics.compose. lia.
Qed.

Definition itp_hv (wb f: Z) : Z := TD.le_val (zlib_hdr wb f true).

Definition itp_hdr_okb (wb f: Z) : bool :=
  let h := zlib_hdr wb f true in let hv := itp_hv wb f in
  (0 <=? Znth 0 h) && (Znth 0 h <=? 255) && (0 <=? Znth 1 h) && (Znth 1 h <=? 255) &&
  negb (hv =? 35615) && (((hv mod 256) * 256 + Z.shiftr hv 8) mod 31 =? 0) && (hv mod 16 =? 8) &&
  (Z.shiftr hv 4 mod 16 + 8 =? wb) && negb (Z.land (Z.shiftr hv 4) 512 =? 0).

Lemma itp_hdr_all wb f : 8 <= wb <= 15 -> 0 <= f <= 3 -> itp_hdr_okb wb f = true.
Proof.
  intros Hw Hf.
  assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) as Ew by lia.
  assert (f = 0 \/ f = 1 \/ f = 2 \/ f = 3) as Ef by lia.
  destruct Ew as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
  destruct Ef as [->|[->|[->| ->]]]; vm_compute; reflexivity.
Qed.

Lemma itp_hdr wb f : 8 <= wb <= 15 -> 0 <= f <= 3 ->
  bytes_ok (zlib_hdr wb f true) /\
  (itp_hv wb f =? 35615) = false /\ (((itp_hv wb f mod 256) * 256 + Z.shiftr (itp_hv wb f) 8) mod 31 =? 0) = true /\
  (itp_hv wb f mod 16 =? 8) = true /\ Z.shiftr (itp_hv wb f) 4 mod 16 + 8 = wb /\
  (Z.land (Z.shiftr (itp_hv wb f) 4) 512 =? 0) = false.
Proof.
  intros Hw Hf. pose proof (itp_hdr_all wb f Hw Hf) as T. unfold itp_hdr_okb in T. cbv zeta in T.
  repeat rewrite andb_true_iff in T.
  destruct T as [[[[[[[[A0 A1] A2] A3] B1] B2] B3] B4] B5].
  rewrite negb_true_iff in B1, B5. rewrite Z.leb_le in A0, A1, A2, A3. apply Z.eqb_eq in B4.
  split; [|repeat split; auto].
  unfold zlib_hdr in *. cbv zeta in *. unfold bytes_ok. change Byte.max_unsigned with 255.
  repeat constructor; cbn in *; lia.
Qed.

Lemma itp_dictid_range G : 0 <= it_dictid G < 2 ^ 32.
Proof.
  unfold it_dictid. assert (V : adler_valid 1) by (vm_compute; repeat split; congruence).
  destruct (ref_adler32_valid 1 (g_dict G) V) as [R _]. exact R.
Qed.

Lemma itp_be32 v : 0 <= v < 2 ^ 32 -> be32 (be_bytes v 4) = v.
Proof.
  intros Hv.
  assert (E : be_bytes v 4 = [Z.shiftr v (8 * 3) mod 256; Z.shiftr v (8 * 2) mod 256; Z.shiftr v (8 * 1) mod 256;
                              Z.shiftr v (8 * 0) mod 256]) by reflexivity.
  assert (B : forall a b c d, be32 [a; b; c; d] = a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d) by reflexivity.
  rewrite E, B. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 3)) with 16777216.
  change (2 ^ 24) with 16777216. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
  assert (v / 16777216 < 256) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Z.mod_small (v / 16777216)) by (split; [apply Z.div_pos|]; lia).
  pose proof (Z.div_mod v 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 256) 256 ltac:(lia)).
  pose proof (Z.div_mod (v / 65536) 256 ltac:(lia)).
  assert (D1 : v / 256 / 256 = v / 65536) by (rewrite Z.div_div by lia; reflexivity).
  assert (D2 : v / 65536 / 256 = v / 16777216) by (rewrite Z.div_div by lia; reflexivity).
  rewrite D1 in *. rewrite D2 in *. lia.
Qed.

Lemma itp_src G : it_ok G -> g_zlib G = true ->
  it_src G = zlib_hdr (g_wb G) (Z.land (g_flevel G) 3) true ++ be_bytes (it_dictid G) 4 ++
             deflate_bytes (g_bs G) ++ be_bytes (ref_adler32 1 (it_data G)) 4.
Proof. intros _ Hz. unfold it_src, it_wrapper. rewrite Hz. reflexivity. Qed.

Lemma itp_flevel G : it_ok G -> 0 <= Z.land (g_flevel G) 3 <= 3.
Proof.
  intros _. assert (E : Z.land (g_flevel G) (Z.ones 2) = g_flevel G mod 2 ^ 2) by (apply Z.land_ones; lia).
  change (Z.ones 2) with 3 in E. change (2 ^ 2) with 4 in E. rewrite E. pose proof (Z.mod_pos_bound (g_flevel G) 4). lia.
Qed.

Lemma itp_len_hdr wb f : Zlength (zlib_hdr wb f true) = 2.
Proof. unfold zlib_hdr. cbv zeta. rewrite !Zlength_cons, Zlength_nil. reflexivity. Qed.

Lemma itp_len_be v : Zlength (be_bytes v 4) = 4.
Proof. unfold be_bytes, le_bytes. rewrite Zlength_rev, Zlength_map. reflexivity. Qed.

Lemma itp_src_facts G : it_ok G -> g_zlib G = true ->
  bytes_ok (it_src G) /\ 6 <= Zlength (it_src G) /\
  sublist 0 2 (it_src G) = zlib_hdr (g_wb G) (Z.land (g_flevel G) 3) true /\
  sublist 2 6 (it_src G) = be_bytes (it_dictid G) 4.
Proof.
  intros OK Hz. pose proof (itp_flevel G OK) as Hf. pose proof OK as (Hw & _).
  destruct (itp_hdr _ _ Hw Hf) as (Hb & _).
  rewrite (itp_src G OK Hz).
  set (h := zlib_hdr (g_wb G) (Z.land (g_flevel G) 3) true) in *.
  set (d := be_bytes (it_dictid G) 4).
  set (t := deflate_bytes (g_bs G) ++ be_bytes (ref_adler32 1 (it_data G)) 4).
  assert (L2 : Zlength h = 2) by apply itp_len_hdr.
  assert (L4 : Zlength d = 4) by apply itp_len_be.
  assert (Bt : bytes_ok t) by (apply Forall_app; split; [apply itp_pack | apply itp_be_bytes]).
  assert (Bd : bytes_ok d) by apply itp_be_bytes.
  pose proof (Zlength_nonneg t).
  split; [|split; [|split]].
  - apply Forall_app; split; [exact Hb|]. apply Forall_app; split; [exact Bd | exact Bt].
  - rewrite !Zlength_app, L2, L4. lia.
  - rewrite sublist0_app1 by lia. rewrite <- L2. apply sublist_same; lia.
  - rewrite sublist_app2 by lia. rewrite L2. rewrite sublist0_app1 by lia.
    replace (6 - 2) with (Zlength d) by lia. apply sublist_same; lia.
Qed.

Lemma itp_wrap G : it_ok G -> g_zlib G = true ->
  (it_wrap G =? 0) = false /\ (Z.land (it_wrap G) 1 =? 0) = false /\
  (if it_wb0 G =? 0 then g_wb G else it_wb0 G) = g_wb G /\ (it_wb0 G = g_wb G \/ it_wb0 G = 0).
Proof.
  intros (Hw & _ & _ & _ & _ & _ & _ & Hiw) Hz. rewrite Hz in Hiw. unfold it_wrap, it_wb0.
  assert (g_wb G = 8 \/ g_wb G = 9 \/ g_wb G = 10 \/ g_wb G = 11 \/ g_wb G = 12 \/ g_wb G = 13 \/
          g_wb G = 14 \/ g_wb G = 15) as Ew by lia.
  destruct Hiw as [E|[E|E]]; rewrite E;
  destruct Ew as [W|[W|[W|[W|[W|[W|[W|W]]]]]]]; rewrite W; vm_compute;
  (split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]); first [left; reflexivity | right; reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine during the call                                                                    *)

(* what stays as in m_init (no output, Z_OK, total_out 0) *)
Definition mfr (z: zfields) (inp: list Z) (m: mst) : Prop :=
  m_inp m = inp /\ m_aout m = zf_ao z /\ m_ow m = [] /\ m_in m = Zlength inp /\ m_out m = zf_ao z /\
  m_ret m = Z_OK /\ m_tout m = 0.

(* pre_st over the machine's registers (pos + nx bytes read) *)
Definition mpre (G: it_ghost) (pos: Z) (m: mst) : Prop :=
  pre_common G (m_s m) /\ 0 <= m_nx m <= Zlength (m_inp m) /\
  ((m_mode m = HEAD /\ i_wbits (m_s m) = it_wb0 G /\ 0 <= pos + m_nx m <= 1 /\ m_bits m = 8 * (pos + m_nx m) /\
    m_hold m = TD.le_val (sublist 0 (pos + m_nx m) (it_src G))) \/
   (m_mode m = DICTID /\ i_wbits (m_s m) = g_wb G /\ i_flags (m_s m) = 0 /\ 2 <= pos + m_nx m <= 5 /\
    m_bits m = 8 * (pos + m_nx m - 2) /\ m_hold m = TD.le_val (sublist 2 (pos + m_nx m) (it_src G)))).

Ltac itp_red :=
  cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler m_ow m_in m_tout m_tin m_snx m_sow m_h
       set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler
       set_leave set_m_leave initbits dropbits
       i_mode i_wrap i_head i_last i_havedict i_total i_wsize i_whave i_wnext i_win i_wdata i_wbits i_flags i_check
       set_i_mode set_i_check set_i_wbits set_i_flags set_i_dmax
       set_m_tin set_m_snx set_m_sow set_m_tout set_i_bits set_i_hold set_i_total i_hold i_bits] in *.

(* THE case HEAD (everything that unfolds c_HEAD2 is here): the zlib FDICT header *)
Lemma itp_head fl fx dx G pos z inp m :
  it_ok G -> g_zlib G = true -> TD.ctx_ok (it_src G) pos inp -> mfr z inp m -> mpre G pos m -> m_mode m = HEAD ->
  m_leave m = 0 ->
  exists m', stepf2 fl fx dx m = IBrk m' /\ mfr z inp m' /\ mpre G pos m' /\
    (m_leave m' = 1 \/ (m_leave m' = 0 /\ m_mode m' = DICTID)).
Proof.
  intros OK Hz Hc F P Hmd Hl.
  destruct P as (Pc & Pn & [(_ & Hwb & Hp & Hb & Hh) | (Hm & _)]);
    [| rewrite Hmd in Hm; unfold HEAD, DICTID in Hm; lia].
  pose proof F as (Fi & Fa & Fo & Fin & Fout & Fr & Ft).
  pose proof Pc as (Pw & Ph & _).
  destruct (itp_wrap G OK Hz) as (W0 & W1 & Wb & _).
  assert (S : stepf2 fl fx dx m = c_HEAD2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
  rewrite S. unfold c_HEAD2. rewrite Pw, W0. cbv beta iota zeta.
  assert (Hc' : TD.ctx_ok (it_src G) pos (m_inp m)) by (rewrite Fi; exact Hc).
  destruct (TH.thh_nb m (it_src G) pos Hc' Pn) as (nx' & Hn' & [[E Hp']|[E Hp']]);
    [unfold TD.hd_head; auto| |]; rewrite E.
  - rewrite TH.thh_lv1. cbv iota. eexists; split; [reflexivity|].
    unfold mfr, mpre in *. itp_red. split; [tauto|]. split; [|left; reflexivity].
    split; [exact Pc|]. split; [lia|]. left. repeat split; auto; lia.
  - destruct (itp_src_facts G OK Hz) as (Sb & Sl & S02 & S26).
    pose proof (itp_flevel G OK) as Hf. pose proof OK as (Hw8 & _).
    destruct (itp_hdr _ _ Hw8 Hf) as (_ & H1 & H2 & H3 & H4 & H5).
    rewrite S02.
    change (TD.le_val (zlib_hdr (g_wb G) (Z.land (g_flevel G) 3) true)) with (itp_hv (g_wb G) (Z.land (g_flevel G) 3)).
    set (hv := itp_hv (g_wb G) (Z.land (g_flevel G) 3)) in *.
    cbn [m_nx m_bits m_hold m_msg m_s m_inp m_aout m_out m_ret m_leave m_adler m_ow m_in m_tout m_tin m_snx m_sow m_h
         set_mode upd_s set_m_s set_m_h upd_h set_m_nx set_m_hold set_m_bits set_m_msg set_m_adler
         set_leave set_m_leave initbits dropbits set_bad].
    rewrite Hl, Pw, Ph, H1, W1. rewrite andb_false_r. cbv iota.
    change (m_hold (set_m_bits (set_m_hold (set_m_nx m nx') hv) 16)) with hv.
    change (m_s (set_m_bits (set_m_hold (set_m_nx m nx') hv) 16)) with (m_s m).
    rewrite H2, H3, H4, Hwb. cbn [negb].
    replace (15 <? g_wb G) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (negb (it_wb0 G =? 0) && (it_wb0 G <? g_wb G))%bool with false
      by (destruct (it_wb0 G =? 0); [reflexivity|]; rewrite Wb, Z.ltb_irrefl; reflexivity).
    cbn [orb]. rewrite H5. eexists; split; [reflexivity|].
    unfold mfr, mpre, pre_common, m_mode in *. itp_red.
    rewrite Hwb, Wb. rewrite Hp', sublist_nil. split; [tauto|]. split; [|right; split; [exact Hl|reflexivity]].
    split; [tauto|]. split; [lia|]. right. repeat split; try reflexivity; lia.
Qed.

(* the call's end at Z_NEED_DICT *)
Definition ndfin (G: it_ghost) (z: zfields) (inp: list Z) (pos: Z) (m: mst) : Prop :=
  m_inp m = inp /\ 0 <= m_snx m <= Zlength inp /\ m_ow m = [] /\ m_sow m = 0 /\ m_aout m = zf_ao z /\
  m_tout m = 0 /\ pos + m_snx m = 6 /\ m_adler m = it_dictid G /\ nd_st G (m_s m).

Lemma itp_id G : it_ok G -> g_zlib G = true -> swap32 (TD.le_val (sublist 2 6 (it_src G))) = it_dictid G.
Proof.
  intros OK Hz. destruct (itp_src_facts G OK Hz) as (Sb & Sl & _ & S26).
  rewrite TDi.td_dict_id by auto. unfold TD.dict_id. rewrite S26. apply itp_be32, itp_dictid_range.
Qed.

(* the cases DICTID and DICT (havedict 0) *)
Lemma itp_dictid fl fx dx G pos z inp m :
  it_ok G -> g_zlib G = true -> TD.ctx_ok (it_src G) pos inp -> mfr z inp m -> mpre G pos m -> m_mode m = DICTID ->
  m_leave m = 0 ->
  (exists m', stepf2 fl fx dx m = IBrk m' /\ m_leave m' = 1 /\ mfr z inp m' /\ mpre G pos m') \/
  (exists m', stepf2 fl fx dx m = IRet Z_NEED_DICT m' /\ ndfin G z inp pos m').
Proof.
  intros OK Hz Hc F P Hmd Hl.
  destruct P as (Pc & Pn & [(Hm & _) | (_ & Hwb & Hfl & Hp & Hb & Hh)]);
    [rewrite Hmd in Hm; unfold HEAD, DICTID in Hm; lia|].
  pose proof F as (Fi & Fa & Fo & Fin & Fout & Fr & Ft).
  rewrite (TDi.td_step_DICTID fl fx dx m Hmd). unfold c_DICTID, needbits.
  assert (Hc' : TD.ctx_ok (it_src G) pos (m_inp m)) by (rewrite Fi; exact Hc).
  destruct (TDi.td_nbk (it_src G) pos 4 m Hc' Pn) as (nx' & Hn' & [[E Hp']|[E Hp']]);
    try (cbn [Z.of_nat Pos.of_succ_nat]; lia); try assumption; rewrite E.
  - rewrite TDi.td_lv1. cbv iota. left. eexists; split; [reflexivity|].
    unfold TDi.td_sh, mfr, mpre in *. itp_red. split; [reflexivity|]. split; [tauto|].
    split; [exact Pc|]. split; [lia|]. right. repeat split; auto; lia.
  - change (m_leave (TDi.td_sh (it_src G) pos m nx')) with (m_leave m). rewrite Hl. cbv iota beta zeta.
    unfold c_DICT. unfold TDi.td_sh. itp_red. pose proof Pc as (Pw & Ph & Pl & Pd & Pt & _). rewrite Pd.
    cbv iota beta zeta.
    right. eexists; split; [reflexivity|].
    unfold ndfin, restore, nd_st, pre_common in *. itp_red. clear E.
    rewrite Hp', (itp_id G OK Hz), Fo, Zlength_nil. rewrite Fi in Hn', Pn.
    repeat split; first [assumption | reflexivity | tauto | lia].
Qed.

Lemma itp_mode G pos m : mpre G pos m -> m_mode m = HEAD \/ m_mode m = DICTID.
Proof. intros (_ & _ & [(A & _)|(A & _)]); auto. Qed.

(* the loop: HEAD -> DICTID -> DICT (Z_NEED_DICT), or a leave for want of input *)
Lemma itp_loop fl fx dx G pos z inp : forall m o, loop2 fl fx dx m o ->
  it_ok G -> g_zlib G = true -> TD.ctx_ok (it_src G) pos inp -> mfr z inp m -> mpre G pos m -> m_leave m = 0 ->
  match o with
  | IRet r m' => r = Z_NEED_DICT /\ ndfin G z inp pos m'
  | IBrk m' => m_leave m' = 1 /\ mfr z inp m' /\ mpre G pos m'
  end.
Proof.
  intros m o HL. induction HL as [m r m' Hs | m m' Hs Hl' | m m' o Hs Hl' HL IH]; intros OK Hz Hc F P Hl;
    destruct (itp_mode G pos m P) as [Hmd|Hmd].
  - destruct (itp_head fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as (m2 & E & _). congruence.
  - destruct (itp_dictid fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as [(m2 & E & _)|(m2 & E & N)];
      rewrite E in Hs; [discriminate|]. injection Hs as <- <-. auto.
  - destruct (itp_head fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as (m2 & E & F2 & P2 & _).
    rewrite E in Hs. injection Hs as <-. auto.
  - destruct (itp_dictid fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as [(m2 & E & L2 & F2 & P2)|(m2 & E & N)];
      rewrite E in Hs; [|discriminate]. injection Hs as <-. auto.
  - destruct (itp_head fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as (m2 & E & F2 & P2 & L2).
    rewrite E in Hs. injection Hs as <-. apply IH; auto. destruct L2 as [L2|[L2 _]]; [contradiction|exact L2].
  - destruct (itp_dictid fl fx dx G pos z inp m OK Hz Hc F P Hmd Hl) as [(m2 & E & L2 & F2 & P2)|(m2 & E & N)];
      rewrite E in Hs; [|discriminate]. injection Hs as <-. contradiction.
Qed.

(* inf_leave without output: no window, the counters + 0, Z_OK or Z_BUF_ERROR *)
Lemma itp_leave fl G pos z inp m res :
  Zlength inp < 2 ^ 32 -> mfr z inp m -> mpre G pos m -> inf_leave fl m res ->
  let m' := r_m res in
  m_inp m' = inp /\ 0 <= m_snx m' <= Zlength inp /\ m_ow m' = [] /\ m_sow m' = 0 /\ m_aout m' = zf_ao z /\
  m_tout m' = 0 /\ (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ pre_st G (pos + m_snx m') (m_s m').
Proof.
  intros Hli F P IL. pose proof F as (Fi & Fa & Fo & Fin & Fout & Fr & Ft).
  pose proof P as (Pc & Pn & Pm). pose proof Pc as (Pw & Ph & Pl & Pd & Pt & Ps & _).
  assert (LO : leave_ok fl m = false).
  { unfold leave_ok, m_left. rewrite Ps, Fout, Fa, Fo, Zlength_nil, Z.sub_0_r, !Z.eqb_refl. reflexivity. }
  destruct IL as [Hok _ | ]; [rewrite LO in Hok; discriminate|].
  unfold leave_fin. rewrite LO. cbv beta iota zeta.
  set (m1 := restore m).
  assert (I1 : u32 (m_in m1 - m_have m1) = m_nx m).
  { change (m_in m1) with (m_in m). unfold m_have. change (m_inp m1) with (m_inp m). change (m_nx m1) with (m_nx m).
    rewrite Fin, Fi. rewrite Fi in Pn. replace (Zlength inp - (Zlength inp - m_nx m)) with (m_nx m) by lia.
    apply TDi.td_u32. lia. }
  assert (O1 : u32 (m_out m1 - m_left m1) = 0).
  { change (m_out m1) with (m_out m). unfold m_left. change (m_aout m1) with (m_aout m). change (m_ow m1) with (m_ow m).
    rewrite Fout, Fa, Fo, Zlength_nil, Z.sub_0_r, Z.sub_diag. reflexivity. }
  rewrite I1, O1. rewrite Z.eqb_refl. cbn [negb]. rewrite andb_false_r. cbv iota beta zeta.
  cbn [r_m r_ret]. clear I1 O1. unfold m1, restore. itp_red.
  rewrite Fo, Fi, Fa, Ft, Pt, Fr, Zlength_nil. change (u64 (0 + 0)) with 0.
  rewrite Fi in Pn. split; [reflexivity|]. split; [lia|]. do 4 (split; [reflexivity|]). split.
  { destruct (_ && _)%bool; [right|left]; reflexivity. }
  unfold pre_st, pre_common, mpre, m_mode in *. itp_red. rewrite !itp_le.
  split; [tauto|]. destruct Pm as [(A1 & A2 & A3 & A4 & A5)|(A1 & A2 & A3 & A4 & A5 & A6)]; [left|right];
    repeat split; first [assumption | lia].
Qed.



Lemma itpre_call : forall G pos z L flush inp res,
  it_ok G -> g_zlib G = true -> wbits_ok (g_iw G) = true -> live_ok L -> zf_ok z -> zf_tout z = 0 ->
  pre_st G pos (l_s L) -> pos + Zlength inp <= Zlength (it_src G) -> inp = sublist pos (pos + Zlength inp) (it_src G) ->
  run2 flush lenfix_list distfix_list (m_init z L inp) res ->
  let m := r_m res in
  m_inp m = inp /\ 0 <= m_snx m <= Zlength inp /\ m_ow m = [] /\ m_sow m = 0 /\ m_aout m = zf_ao z /\
  m_tout m = 0 /\
  ((r_ret res = Z_NEED_DICT /\ pos + m_snx m = 6 /\ m_adler m = it_dictid G /\ nd_st G (m_s m)) \/
   ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR) /\ pre_st G (pos + m_snx m) (m_s m))).
Proof.
  intros G pos z L flush inp res OK Hz _ _ _ Ht Pre Hlen Hinp (o & HL & Ho).
  destruct (itp_src_facts G OK Hz) as (Sb & _ & _ & _).
  pose proof Pre as (Pc & Pm).
  assert (Hc : TD.ctx_ok (it_src G) pos inp).
  { unfold TD.ctx_ok. split; [destruct Pm as [(_ & _ & A & _)|(_ & _ & _ & A & _)]; lia|].
    split; [exact Hlen|]. split; [exact Sb|].
    intros k Hk. rewrite Hinp at 1. rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hs : (if i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE then set_i_mode (l_s L) TYPEDO else l_s L) = l_s L).
  { replace (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE) with false; [reflexivity|].
    symmetry; apply Z.eqb_neq.
    destruct Pm as [(A & _)|(A & _)]; rewrite A; unfold HEAD, DICTID, Zlib.proof.inflate.Model.TYPE; lia. }
  assert (F : mfr z inp (m_init z L inp)) by (unfold mfr, m_init; cbn [m_inp m_aout m_ow m_in m_out m_ret m_tout]; repeat split; auto).
  assert (P : mpre G pos (m_init z L inp)).
  { unfold mpre, m_init, m_mode. cbn [m_s m_nx m_bits m_hold m_inp]. rewrite Hs. rewrite Z.add_0_r.
    split; [exact Pc|]. split; [pose proof (Zlength_nonneg inp); lia|].
    rewrite <- !itp_le. exact Pm. }
  pose proof (itp_loop flush lenfix_list distfix_list G pos z inp _ _ HL OK Hz Hc F P eq_refl) as R.
  destruct o as [m'|r m'].
  - destruct R as (_ & F' & P').
    assert (Hli : Zlength inp < 2 ^ 32).
    { pose proof OK as (_ & _ & _ & _ & Ls & _). destruct Pm as [(_ & _ & A & _)|(_ & _ & _ & A & _)]; lia. }
    destruct (itp_leave flush G pos z inp m' res Hli F' P' Ho) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (or_intror (conj A7 A8)))))))).
  - destruct R as (Er & N). rewrite Ho. cbn [r_m r_ret]. rewrite Er.
    destruct N as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (or_introl (conj eq_refl (conj N7 (conj N8 N9)))))))))).
Qed.

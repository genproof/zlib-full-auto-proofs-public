(* Law inflate_check, theory part: the gzip header cases FLAGS .. HCRC keep Kx. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_check.IKTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The FLG byte                                                                                   *)

Lemma ikh_land7 x k : 0 <= k -> Z.land x (Z.shiftl 7 k) = Z.shiftl ((x / 2 ^ k) mod 8) k.
Proof.
  intros Hk.
  replace ((x / 2 ^ k) mod 8) with (Z.land (Z.shiftr x k) 7).
  2: { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite Z.shiftl_land. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.ltb_spec i k).
  - rewrite (Z.shiftl_spec_low 7 k i) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.shiftl_spec_high (Z.shiftr x k) k i) by lia. rewrite Z.shiftr_spec by lia.
    replace (i - k + k) with i by lia. reflexivity.
Qed.

Lemma ikh_flags h a b : 0 <= a < 256 -> 0 <= b < 256 -> h mod 65536 = a + 256 * b ->
  Z.land (s32 h) 255 = a /\ (Z.land (s32 h) 57344 = 0 <-> Z.land b 224 = 0).
Proof.
  intros Ha Hb E.
  assert (S : s32 h mod 65536 = a + 256 * b).
  { unfold s32. change (2 ^ 32) with 4294967296. change (2 ^ 31) with 2147483648.
    assert (M : (h mod 4294967296) mod 65536 = h mod 65536).
    { rewrite (Zmod_div_mod 65536 4294967296 h) by (try lia; exists 65536; lia). reflexivity. }
    destruct (_ <? _).
    - rewrite M; exact E.
    - replace (h mod 4294967296 - 4294967296) with (h mod 4294967296 + (-65536) * 65536) by lia.
      rewrite Z.mod_add by lia. rewrite M; exact E. }
  clear E. set (y := s32 h) in *. clearbody y.
  split.
  - change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    rewrite (Zmod_div_mod 256 65536 y) by (try lia; exists 256; lia). rewrite S.
    rewrite (Z.mul_comm 256 b), Z.mod_add by lia. apply Z.mod_small; lia.
  - change 57344 with (Z.shiftl 7 13). change 224 with (Z.shiftl 7 5).
    rewrite !ikh_land7 by lia. rewrite !Z.shiftl_mul_pow2 by lia.
    change (2 ^ 13) with 8192. change (2 ^ 5) with 32.
    assert (Q : (y / 8192) mod 8 = b / 32).
    { pose proof (Z.rem_mul_r y 8192 8 ltac:(lia) ltac:(lia)) as M. change (8192 * 8) with 65536 in M.
      rewrite S in M.
      pose proof (Z.mod_pos_bound y 8192 ltac:(lia)). pose proof (Z.mod_pos_bound (y / 8192) 8 ltac:(lia)).
      assert (D : (a + 256 * b) / 8192 = b / 32).
      { change 8192 with (256 * 32). rewrite <- Z.div_div by lia.
        rewrite (Z.mul_comm 256 b), Z.div_add by lia. rewrite (Z.div_small a 256) by lia. reflexivity. }
      rewrite <- D, M. rewrite (Z.mul_comm 8192), Z.div_add by lia. rewrite (Z.div_small (y mod 8192)) by lia. lia. }
    rewrite Q. pose proof (Z.div_pos b 32 ltac:(lia) ltac:(lia)).
    assert (b / 32 < 8) by (apply Z.div_lt_upper_bound; lia).
    rewrite (Z.mod_small (b / 32) 8) by lia. lia.
Qed.

Lemma ikh_bytes_rng src i : bytes_ok src -> 0 <= i < Zlength src -> 0 <= Znth i src < 256.
Proof.
  intros B Hi. pose proof (proj1 (Forall_Znth _ _) B i Hi) as R. cbv beta in R. rep_lia.
Qed.

(* FLAGS: after NEEDBITS(16) with 16 bits consumed before, the low 16 bits of hold are bytes 2, 3 *)
Lemma ikh_hold16 (KK: ik_kit) src P h bits :
  bytes_ok src -> 4 <= P <= Zlength src -> ik_bitbuf src P h bits -> 8 * P - bits = 16 ->
  h mod 65536 = Znth 2 src + 256 * Znth 3 src.
Proof.
  intros B HP [_ Hh] E. rewrite E in Hh. subst h.
  assert (Bs : forall lo hi, bytes_ok (sublist lo hi src)) by (intros; apply Forall_sublist; exact B).
  rewrite <- (sublist_rejoin 0 2 P) by lia. rewrite (kk_le_app KK).
  replace (8 * Zlength (sublist 0 2 src)) with 16 by (rewrite Zlength_sublist; lia).
  rewrite <- (sublist_rejoin 2 4 P) by lia. rewrite (kk_le_app KK).
  replace (8 * Zlength (sublist 2 4 src)) with 16 by (rewrite Zlength_sublist; lia).
  pose proof (kk_le_range KK (sublist 0 2 src) (Bs _ _)) as R1.
  pose proof (kk_le_range KK (sublist 2 4 src) (Bs _ _)) as R2.
  rewrite Zlength_sublist in R1, R2 by lia.
  replace (sublist 2 4 src) with [Znth 2 src; Znth 3 src].
  2: { rewrite (sublist_split 2 3 4) by lia. rewrite !sublist_len_1 by lia. reflexivity. }
  replace (sublist 2 4 src) with [Znth 2 src; Znth 3 src] in R2.
  2: { rewrite (sublist_split 2 3 4) by lia. rewrite !sublist_len_1 by lia. reflexivity. }
  cbn [le_val] in *. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 16) with 65536 in *. change (8 * (2 - 0)) with 16 in R1. change (8 * (4 - 2)) with 16 in R2.
  change (2 ^ 16) with 65536 in *.
  set (A := le_val (sublist 0 2 src)) in *. set (C := le_val (sublist 4 P src)) in *.
  clearbody A C.
  pose proof (ikh_bytes_rng src 2 B ltac:(lia)). pose proof (ikh_bytes_rng src 3 B ltac:(lia)).
  set (D := Znth 2 src + 256 * (Znth 3 src + 256 * 0)) in *.
  rewrite (Z.mul_comm 65536 (D + _)), Z.div_add by lia. rewrite (Z.div_small A) by lia.
  rewrite Z.add_0_l. rewrite (Z.mul_comm 65536 C), Z.mod_add by lia. rewrite Z.mod_small by lia.
  subst D. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kx of the states the header cases produce                                                      *)

Ltac ikh_num :=
  unfold ik_pre_mode, ik_post_mode, ik_gzhdr_mode, md_hdr, decode_mode in *;
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
    Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *; lia.

(* a state in a gzip header mode *)
Lemma ikh_gz wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> wrap <> 0 -> ik_gzhdr_mode (m_mode m) ->
  m_out m' = m_out m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_tout m' = m_tout m ->
  i_total (m_s m') = i_total (m_s m) ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  ik_gzhdr_mode (m_mode m') ->
  ((m_mode m' = EXTRA \/ m_mode m' = NAME \/ m_mode m' = COMMENT) -> m_bits m' = 0) ->
  (m_mode m' = EXLEN -> Z.land (i_flags (m_s m')) 1024 = 0 -> m_bits m' = 0) ->
  ik_gzhdr_ok wrap src (pos + m_nx m') (m_bits m') (m_mode m') (i_flags (m_s m')) ->
  Kx wrap src pos out a0 m'.
Proof.
  intros K W G Eo Ea Eow Eto Etot Bb G' B0 B1 Gz.
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ K).
  - exact Bb.
  - split; [|exact B1]. intros D. apply B0.
    destruct D as [D|[D|[D|[D|D]]]]; auto; exfalso; rewrite D in G'; ikh_num.
  - unfold m_left; rewrite Eo, Ea, Eow. exact (kx_out _ _ _ _ _ _ K).
  - rewrite Etot, Eo, Ea. exact (kx_total _ _ _ _ _ _ K).
  - rewrite Eto, Eo, Ea. exact (kx_tout _ _ _ _ _ _ K).
  - intros; contradiction.
  - intros _ _. destruct (kx_pre _ _ _ _ _ _ K W) as (X1 & X2 & X3); [unfold ik_pre_mode; tauto|].
    unfold ik_pre. rewrite Eow, Eo, Ea. auto.
  - intros _ _. exact Gz.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _. unfold ik_trail. cbv zeta. split; [|split]; intros D; exfalso; ikh_num.
Qed.

(* BAD from a gzip header mode *)
Lemma ikh_bad wrap src pos out a0 m m' :
  Kx wrap src pos out a0 m -> wrap <> 0 -> ik_gzhdr_mode (m_mode m) ->
  m_out m' = m_out m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_tout m' = m_tout m ->
  i_total (m_s m') = i_total (m_s m) ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  m_mode m' = BAD ->
  Kx wrap src pos out a0 m'.
Proof.
  intros K W G Eo Ea Eow Eto Etot Bb Hb.
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ K).
  - exact Bb.
  - split; [intros D|intros D _]; exfalso; ikh_num.
  - unfold m_left; rewrite Eo, Ea, Eow. exact (kx_out _ _ _ _ _ _ K).
  - rewrite Etot, Eo, Ea. exact (kx_total _ _ _ _ _ _ K).
  - rewrite Eto, Eo, Ea. exact (kx_tout _ _ _ _ _ _ K).
  - intros; contradiction.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ _. left. destruct (kx_pre _ _ _ _ _ _ K W) as (X1 & X2 & X3); [unfold ik_pre_mode; tauto|].
    unfold ik_pre. rewrite Eow, Eo, Ea. auto.
  - intros _. unfold ik_trail. cbv zeta. split; [|split]; intros D; exfalso; ikh_num.
Qed.

(* TYPE from HCRC: the header is complete, check = adler = 0 = the CRC-32 of nothing *)
Lemma ikh_type wrap src pos out a0 m m' :
  ref_crc32 0 [] = 0 ->
  Kx wrap src pos out a0 m -> wrap <> 0 -> m_mode m = HCRC ->
  m_out m' = m_out m -> m_aout m' = m_aout m -> m_ow m' = m_ow m -> m_tout m' = m_tout m ->
  i_total (m_s m') = i_total (m_s m) ->
  ik_bitbuf src (pos + m_nx m') (m_hold m') (m_bits m') ->
  m_mode m' = Zlib.proof.inflate.Model.TYPE -> i_flags (m_s m') = i_flags (m_s m) ->
  i_check (m_s m') = 0 -> m_adler m' = 0 ->
  8 * (pos + m_nx m) - m_bits m <= 8 * (pos + m_nx m') - m_bits m' ->
  Kx wrap src pos out a0 m'.
Proof.
  intros Cn K W Hm Eo Ea Eow Eto Etot Bb Ht Ef Ec Ead Hc.
  assert (G : ik_gzhdr_mode (m_mode m)) by (rewrite Hm; unfold ik_gzhdr_mode; tauto).
  destruct (kx_pre _ _ _ _ _ _ K W) as (X1 & X2 & X3); [unfold ik_pre_mode; tauto|].
  pose proof (kx_gzh _ _ _ _ _ _ K W G) as (Gw & Gzw & Gl & G0 & G1 & GF & GN & GO & GL).
  destruct (GN ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  specialize (GL ltac:(rewrite Hm; tauto)).
  constructor.
  - exact (kx_wrap _ _ _ _ _ _ K).
  - exact Bb.
  - split; [intros D|intros D _]; exfalso; ikh_num.
  - unfold m_left; rewrite Eo, Ea, Eow. exact (kx_out _ _ _ _ _ _ K).
  - rewrite Etot, Eo, Ea. exact (kx_total _ _ _ _ _ _ K).
  - rewrite Eto, Eo, Ea. exact (kx_tout _ _ _ _ _ _ K).
  - intros; contradiction.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ D. exfalso. ikh_num.
  - intros _ _. unfold ik_post. cbv zeta. rewrite Ef, Ec, Ead.
    assert (F0 : i_flags (m_s m) <> 0) by (intro F; rewrite F in G8; discriminate).
    split; [right; split; [exact G8|]; split; [exact Gh|]; split; [exact Gzw|]; lia|].
    apply Z.eqb_neq in F0. rewrite F0. cbn [negb ik_chk].
    rewrite Eow, Eo, Ea, X1, X2, X3, Z.sub_diag.
    replace (sublist 0 0 (@nil Z)) with (@nil Z) by reflexivity. rewrite app_nil_l.
    split; [rewrite Cn|]; reflexivity.
  - intros _ D. exfalso. ikh_num.
  - intros _. unfold ik_trail. cbv zeta. split; [|split]; intros D; exfalso; ikh_num.
Qed.

Lemma ikh_gzok_mono wrap src P bits P' bits' md fl :
  ik_gzhdr_ok wrap src P bits md fl -> (md = FLAGS -> 8 * P' - bits' = 8 * P - bits) ->
  8 * P - bits <= 8 * P' - bits' -> ik_gzhdr_ok wrap src P' bits' md fl.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) E Le.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [intros H; rewrite (E H); auto|].
  split; [intros H; destruct (A7 H) as (X & Y & Z); split; [exact X|split; [exact Y|lia]]|].
  split; intros H; [specialize (A8 H)|specialize (A9 H)]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases, from a loop head or a fallthrough                                                   *)

Record xH (wrap: Z) (src: list Z) (pos: Z) (out: list Z) (a0: Z) (m: mst) : Prop := {
  xh_kx : Kx wrap src pos out a0 m;
  xh_ctx : ctx_ok src pos (m_inp m);
  xh_w : wrap <> 0;
  xh_lv : m_leave m = 0;
  xh_nx : 0 <= m_nx m <= Zlength (m_inp m);
  xh_len : 0 <= i_length (m_s m);
  xh_bits : 0 <= m_bits m <= 31;
  xh_hd : i_head (m_s m) = false;
  xh_md : ik_gzhdr_mode (m_mode m) }.

Lemma ikh_P src pos m : ctx_ok src pos (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) ->
  0 <= pos + m_nx m <= Zlength src.
Proof. intros (A & B & _). lia. Qed.

Lemma ikh_nb (KK: ik_kit) wrap src pos out a0 m n :
  xH wrap src pos out a0 m -> 0 <= n <= 32 ->
  ik_bitbuf src (pos + m_nx (needbits n m)) (m_hold (needbits n m)) (m_bits (needbits n m)) /\
  ik_same_but_buf m (needbits n m) /\ m_nx m <= m_nx (needbits n m) <= Zlength (m_inp m) /\
  8 * (pos + m_nx (needbits n m)) - m_bits (needbits n m) = 8 * (pos + m_nx m) - m_bits m /\
  ((m_leave (needbits n m) = 1 /\ m_bits (needbits n m) < n) \/
   (m_leave (needbits n m) = 0 /\ n <= m_bits (needbits n m) < 40)).
Proof.
  intros [K Hc W Hl Hnx Hlen Hb Hhd Hg] Hn.
  pose proof (kk_needbits KK src pos (m_inp m) n m Hc eq_refl Hnx Hn ltac:(lia) (kx_buf _ _ _ _ _ _ K)) as X.
  cbv zeta in X. destruct X as (Bb & S & R & D & Lt & Eq & C).
  split; [exact Bb|]. split; [exact S|]. split; [exact R|]. split; [lia|].
  destruct C as [(C1 & C2 & C3)|(C1 & C2)]; [left; split; auto|right; rewrite C1, Hl; split; auto].
  destruct (Z.lt_ge_cases (m_bits m) n) as [L|L]; [specialize (Lt L); lia|].
  rewrite (Eq L). lia.
Qed.

Lemma ikh_crc m d : exists c, crc_if m d = upd_s m (fun s => set_i_check s c).
Proof.
  unfold crc_if. destruct (andb _ _).
  - eexists; reflexivity.
  - exists (i_check (m_s m)). destruct m as [s]; destruct s; reflexivity.
Qed.

Lemma ikh_zstr k bytes have : forall length max wr buf copy cp b ln buf',
  zstr_f k bytes have length max wr buf copy = (cp, b, ln, buf') -> 0 <= copy < have ->
  copy <= cp <= have /\ length <= ln.
Proof.
  induction k as [|k IH]; intros length max wr buf copy cp b ln buf' E C.
  - cbn in E. inversion E; subst. lia.
  - cbn [zstr_f] in E.
    match type of E with context [if ?c then _ else _] =>
      destruct c eqn:G; [|]
    end.
    + match type of E with context [if ?c then _ else _] => destruct c eqn:G2 end.
      * apply andb_true_iff in G2. destruct G2 as [_ G2]. apply Z.ltb_lt in G2.
        apply IH in E; [|lia]. lia.
      * inversion E; subst. lia.
    + match type of E with context [if ?c then _ else _] => destruct c eqn:G2 end.
      * apply andb_true_iff in G2. destruct G2 as [_ G2]. apply Z.ltb_lt in G2.
        apply IH in E; [|lia]. lia.
      * inversion E; subst. lia.
Qed.

Ltac ikh_red :=
  unfold m_mode, m_have in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       upd_s upd_h set_mode set_leave set_bad initbits andb negb
       i_mode i_wrap i_head i_length i_flags i_check i_total
       set_i_mode set_i_check set_i_length set_i_flags] in *.

Ltac ikh_eqs :=
  repeat match goal with
  | E: m_s ?a = m_s ?b |- context [m_s ?a] => rewrite E
  | E: m_out ?a = m_out ?b |- context [m_out ?a] => rewrite E
  | E: m_aout ?a = m_aout ?b |- context [m_aout ?a] => rewrite E
  | E: m_ow ?a = m_ow ?b |- context [m_ow ?a] => rewrite E
  | E: m_tout ?a = m_tout ?b |- context [m_tout ?a] => rewrite E
  | E: m_inp ?a = m_inp ?b |- context [m_inp ?a] => rewrite E
  end.

Ltac ikh_same S :=
  let Es := fresh "Es" in let Eh := fresh "Eh" in let Ei := fresh "Ei" in let Ea := fresh "Ea" in
  let Eow := fresh "Eow" in let Ein := fresh "Ein" in let Eo := fresh "Eo" in let Er := fresh "Er" in
  let Ead := fresh "Ead" in let Emsg := fresh "Emsg" in let Etin := fresh "Etin" in
  let Eto := fresh "Eto" in let Esnx := fresh "Esnx" in let Esow := fresh "Esow" in
  destruct S as (Es & Eh & Ei & Ea & Eow & Ein & Eo & Er & Ead & Emsg & Etin & Eto & Esnx & Esow).

Lemma ikh_01 : (0 =? 1) = false.
Proof. reflexivity. Qed.

Ltac ikh_fin KK :=
  first [ apply (kk_crc_nil KK) | lia
        | (apply (kk_bb_init KK); [assumption | lia]) ].

Lemma x_hcrc (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = HCRC -> stepx_post wrap src pos out a0 (c_HCRC m).
Proof.
  intros Hh Hm. pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  unfold c_HCRC. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 512 =? 0)).
  - destruct (ikh_nb KK _ _ _ _ _ m 16 Hh ltac:(lia)) as (Bb & S & R & D & C).
    set (m1 := needbits 16 m) in *. clearbody m1. ikh_same S.
    destruct C as [[L1 C]|[L1 C]]; rewrite L1; [rewrite Z.eqb_refl | rewrite ikh_01]; cbv beta iota.
    + cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m m1); auto; ikh_red; ikh_eqs; auto.
      * intros. exfalso. ikh_num.
      * intros. exfalso. ikh_num.
      * apply (ikh_gzok_mono _ _ _ _ _ _ _ _ (kx_gzh _ _ _ _ _ _ K W Hg)); intros; lia.
    + destruct (andb _ _); cbv beta iota; cbn [stepx_post].
      * apply (ikh_bad wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto.
      * ikh_red. rewrite Es, Hhd. cbv beta iota.
        apply (ikh_type wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto; ikh_fin KK.
  - rewrite Hhd. cbn [stepx_post].
    apply (ikh_type wrap src pos out a0 m); auto; ikh_red; auto; try ikh_fin KK.
    exact (kx_buf _ _ _ _ _ _ K).
Qed.

Lemma ikh_gzok_mk wrap src P bits md fl0 fl P' bits' md' :
  ik_gzhdr_ok wrap src P bits md fl0 -> md' <> FLAGS -> ik_ghdr src -> Z.land fl 255 = 8 ->
  32 <= 8 * P' - bits' -> (md' = OS -> 64 <= 8 * P' - bits') ->
  (md' = EXLEN \/ md' = EXTRA \/ md' = NAME \/ md' = COMMENT \/ md' = HCRC -> 80 <= 8 * P' - bits') ->
  ik_gzhdr_ok wrap src P' bits' md' fl.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & _) N Gh G8 L32 L64 L80.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [intros; contradiction|]. split; [intros _; split; [exact Gh|split; [exact G8|lia]]|].
  split; [exact L64|exact L80].
Qed.

(* the facts of a gzip header mode other than FLAGS *)
Lemma ikh_gzN wrap src P bits md fl :
  ik_gzhdr_ok wrap src P bits md fl -> md <> FLAGS ->
  ik_ghdr src /\ Z.land fl 255 = 8 /\ 32 <= 8 * P - bits.
Proof. intros (_ & _ & _ & _ & _ & _ & A7 & _) N. exact (A7 N). Qed.

Lemma ikh_gzL wrap src P bits md fl :
  ik_gzhdr_ok wrap src P bits md fl ->
  (md = EXLEN \/ md = EXTRA \/ md = NAME \/ md = COMMENT \/ md = HCRC) -> 80 <= 8 * P - bits.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & A9) N. exact (A9 N). Qed.

Ltac ikh_fin2 KK :=
  first [ apply (kk_crc_nil KK) | lia
        | (apply (kk_bb_init KK); [assumption | lia])
        | (unfold ik_gzhdr_mode; ikh_num)
        | (intros; exfalso; ikh_num) ].

(* the bit buffer is empty in EXTRA, NAME, COMMENT *)
Lemma ikh_empty (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> (m_mode m = EXTRA \/ m_mode m = NAME \/ m_mode m = COMMENT) ->
  m_bits m = 0 /\ m_hold m = 0.
Proof.
  intros [K Hc W Hl Hnx Hlen Hb Hhd Hg] Hm.
  assert (B0 : m_bits m = 0) by (apply (proj1 (kx_bits0 _ _ _ _ _ _ K)); tauto).
  split; [exact B0|].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kk_bb_range KK src (pos + m_nx m) (m_hold m) (m_bits m) Hsrc ltac:(lia)
                (kx_buf _ _ _ _ _ _ K)) as R.
  rewrite B0 in R. change (2 ^ 0) with 1 in R. lia.
Qed.

Ltac ikh_close KK K Gz :=
  first [ exact (kx_buf _ _ _ _ _ _ K)
        | ikh_fin2 KK
        | (intros; lia)
        | (apply (ikh_gzok_mono _ _ _ _ _ _ _ _ Gz); intros; first [lia | exfalso; ikh_num])
        | (apply (ikh_gzok_mk _ _ _ _ _ _ _ _ _ _ Gz); auto; ikh_fin2 KK) ].

Lemma x_comment (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = COMMENT -> stepx_post wrap src pos out a0 (c_COMMENT2 m).
Proof.
  intros Hh Hm. destruct (ikh_empty KK _ _ _ _ _ _ Hh ltac:(tauto)) as [B0 H0].
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  pose proof (ikh_gzL _ _ _ _ _ _ Gz ltac:(rewrite Hm; tauto)) as G80.
  unfold c_COMMENT2. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 4096 =? 0)).
  - destruct (Z.eqb_spec (m_have m) 0) as [E0|E0]; cbv beta iota.
    + cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
    + unfold m_have in E0.
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[cp b] ln] buf] eqn:Ez.
      apply ikh_zstr in Ez; [|unfold m_have; lia].
      destruct (ikh_crc m (inbytes m cp)) as [c ->].
      destruct (negb (b =? 0)); cbv beta iota.
      * cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
      * apply (x_hcrc KK); [|ikh_red; reflexivity].
        constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
        apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
  - rewrite Hhd. apply (x_hcrc KK); [|ikh_red; reflexivity].
    constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
Qed.

Lemma x_name (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = NAME -> stepx_post wrap src pos out a0 (c_NAME2 m).
Proof.
  intros Hh Hm. destruct (ikh_empty KK _ _ _ _ _ _ Hh ltac:(tauto)) as [B0 H0].
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  pose proof (ikh_gzL _ _ _ _ _ _ Gz ltac:(rewrite Hm; tauto)) as G80.
  unfold c_NAME2. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 2048 =? 0)).
  - destruct (Z.eqb_spec (m_have m) 0) as [E0|E0]; cbv beta iota.
    + cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
    + unfold m_have in E0.
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[cp b] ln] buf] eqn:Ez.
      apply ikh_zstr in Ez; [|unfold m_have; lia].
      destruct (ikh_crc m (inbytes m cp)) as [c ->].
      destruct (negb (b =? 0)); cbv beta iota.
      * cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
      * apply (x_comment KK); [|ikh_red; reflexivity].
        constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
        apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
  - rewrite Hhd. apply (x_comment KK); [|ikh_red; reflexivity].
    constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
Qed.

Lemma x_extra (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = EXTRA -> stepx_post wrap src pos out a0 (c_EXTRA2 m).
Proof.
  intros Hh Hm. destruct (ikh_empty KK _ _ _ _ _ _ Hh ltac:(tauto)) as [B0 H0].
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  pose proof (ikh_gzL _ _ _ _ _ _ Gz ltac:(rewrite Hm; tauto)) as G80.
  unfold c_EXTRA2. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)).
  - destruct (negb (Z.min (i_length (m_s m)) (m_have m) =? 0)).
    + rewrite Hhd. cbn [andb]. cbv beta iota.
      destruct (ikh_crc m (inbytes m (Z.min (i_length (m_s m)) (m_have m)))) as [c ->].
      pose proof (Z.le_min_l (i_length (m_s m)) (m_have m)).
      pose proof (Z.le_min_r (i_length (m_s m)) (m_have m)).
      pose proof (Z.min_glb (i_length (m_s m)) (m_have m) 0 ltac:(lia) ltac:(unfold m_have; lia)).
      unfold m_have in *.
      ikh_red. destruct (negb _); cbv beta iota.
      * cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
      * apply (x_name KK); [|ikh_red; reflexivity].
        constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
        apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
    + cbv beta iota. destruct (negb _); cbv beta iota.
      * cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
      * apply (x_name KK); [|ikh_red; reflexivity].
        constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
        apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
  - apply (x_name KK); [|ikh_red; reflexivity].
    constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; rewrite ?H0, ?B0; ikh_close KK K Gz.
Qed.

Ltac ikh_crcs :=
  repeat match goal with |- context [crc_if ?x ?d] => destruct (ikh_crc x d) as [? ->] end.

Ltac ikh_nbcase KK m n Hh :=
  let Bb := fresh "Bb" in let S := fresh "S" in let R := fresh "R" in let D := fresh "D" in
  let C := fresh "C" in let m1 := fresh "m1" in let L1 := fresh "L1" in
  destruct (ikh_nb KK _ _ _ _ _ m n Hh ltac:(lia)) as (Bb & S & R & D & C);
  set (m1 := needbits n m) in *; clearbody m1; ikh_same S;
  destruct C as [[L1 C]|[L1 C]]; rewrite L1; [rewrite Z.eqb_refl | rewrite ikh_01]; cbv beta iota.

Lemma x_exlen (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = EXLEN -> stepx_post wrap src pos out a0 (c_EXLEN2 m).
Proof.
  intros Hh Hm.
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  pose proof (ikh_gzL _ _ _ _ _ _ Gz ltac:(rewrite Hm; tauto)) as G80.
  unfold c_EXLEN2. cbv beta zeta.
  destruct (Z.eqb_spec (Z.land (i_flags (m_s m)) 1024) 0) as [F|F]; cbn [negb]; cbv beta iota.
  - assert (B0 : m_bits m = 0) by (apply (proj2 (kx_bits0 _ _ _ _ _ _ K)); auto).
    rewrite Hhd. apply (x_extra KK); [|ikh_red; reflexivity].
    constructor; ikh_red; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; auto; ikh_close KK K Gz.
  - ikh_nbcase KK m 16 Hh.
    + cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m m1); auto; ikh_red; ikh_eqs; auto;
        ikh_close KK K Gz.
    + ikh_red. rewrite Es, Hhd. cbv beta iota. ikh_crcs. ikh_red.
      apply (x_extra KK); [|ikh_red; reflexivity].
      constructor; ikh_red; ikh_eqs; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
      * apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto; ikh_close KK K Gz.
      * unfold u32. apply Z.mod_pos_bound. vm_compute. reflexivity.
Qed.

Lemma x_os (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = OS -> stepx_post wrap src pos out a0 (c_OS2 m).
Proof.
  intros Hh Hm.
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  pose proof Gz as (_ & _ & _ & _ & _ & _ & _ & GO & _). specialize (GO Hm).
  unfold c_OS2. cbv beta zeta.
  ikh_nbcase KK m 16 Hh.
  - cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m m1); auto; ikh_red; ikh_eqs; auto;
      ikh_close KK K Gz.
  - ikh_red. rewrite Es, Hhd. cbv beta iota. ikh_crcs. ikh_red.
    apply (x_exlen KK); [|ikh_red; reflexivity].
    constructor; ikh_red; ikh_eqs; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto; ikh_close KK K Gz.
Qed.

Lemma x_time (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = TIME -> stepx_post wrap src pos out a0 (c_TIME2 m).
Proof.
  intros Hh Hm.
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  destruct (ikh_gzN _ _ _ _ _ _ Gz ltac:(rewrite Hm; ikh_num)) as (Gh & G8 & G32).
  unfold c_TIME2. cbv beta zeta.
  ikh_nbcase KK m 32 Hh.
  - cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m m1); auto; ikh_red; ikh_eqs; auto;
      ikh_close KK K Gz.
  - ikh_red. rewrite Es, Hhd. cbv beta iota. ikh_crcs. ikh_red.
    apply (x_os KK); [|ikh_red; reflexivity].
    constructor; ikh_red; ikh_eqs; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto; ikh_close KK K Gz.
Qed.

Lemma x_flags (KK: ik_kit) wrap src pos out a0 m :
  xH wrap src pos out a0 m -> m_mode m = FLAGS -> stepx_post wrap src pos out a0 (c_FLAGS2 m).
Proof.
  intros Hh Hm.
  pose proof Hh as [K Hc W Hl Hnx Hlen Hb Hhd Hg].
  pose proof Hc as (Hc1 & Hc2 & Hsrc & _).
  pose proof (kx_gzh _ _ _ _ _ _ K W Hg) as Gz.
  pose proof Gz as (_ & _ & _ & G0 & G1 & GF & _). specialize (GF Hm).
  unfold c_FLAGS2. cbv beta zeta.
  ikh_nbcase KK m 16 Hh.
  - cbn [stepx_post]. apply (ikh_gz wrap src pos out a0 m m1); auto; ikh_red; ikh_eqs; auto;
      ikh_close KK K Gz.
  - assert (H16 : m_hold m1 mod 65536 = Znth 2 src + 256 * Znth 3 src).
    { apply (ikh_hold16 KK src (pos + m_nx m1) (m_hold m1) (m_bits m1) Hsrc); auto; lia. }
    assert (R2 : 0 <= Znth 2 src < 256) by (apply ikh_bytes_rng; auto; lia).
    assert (R3 : 0 <= Znth 3 src < 256) by (apply ikh_bytes_rng; auto; lia).
    destruct (ikh_flags (m_hold m1) (Znth 2 src) (Znth 3 src) R2 R3 H16) as [Fa Fb].
    destruct (Z.eqb_spec (Z.land (s32 (m_hold m1)) 255) 8) as [E8|E8]; cbn [negb]; cbv beta iota.
    2: { cbn [stepx_post]. apply (ikh_bad wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto. }
    destruct (Z.eqb_spec (Z.land (s32 (m_hold m1)) 57344) 0) as [E0|E0]; cbn [negb]; cbv beta iota.
    2: { cbn [stepx_post]. apply (ikh_bad wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto. }
    assert (Gh : ik_ghdr src) by (split; [lia|]; split; [auto|]; split; [auto|]; split; [lia|]; apply Fb; auto).
    ikh_red. rewrite Es, Hhd. cbv beta iota. ikh_crcs. ikh_red.
    apply (x_time KK); [|ikh_red; reflexivity].
    constructor; ikh_red; ikh_eqs; auto; try lia; try (unfold ik_gzhdr_mode; ikh_num).
    apply (ikh_gz wrap src pos out a0 m); auto; ikh_red; ikh_eqs; auto; ikh_close KK K Gz.
Qed.

Lemma ikx_hdr : hdrx_stmt.
Proof.
  intros KK wrap src pos out a0 inp aout flush m Hc K Kx0 Hw Hl Hmd.
  assert (G : ik_gzhdr_mode (m_mode m)) by exact Hmd.
  assert (Hh : xH wrap src pos out a0 m).
  { assert (W : wrap <> 0).
    { intro E. destruct (kx_raw _ _ _ _ _ _ Kx0 E) as (_ & N & _). contradiction. }
    constructor; auto.
    - rewrite (kc_inp _ _ _ _ _ _ K). exact Hc.
    - apply (Inv.mw_nx _ (proj1 Hw)).
    - pose proof (Inv.sw_length _ (Inv.mw_s _ (proj1 Hw))) as U. unfold Inv.urange in U. lia.
    - apply (kc_bits _ _ _ _ _ _ K); intro E; rewrite E in G; ikh_num.
    - apply (kc_head _ _ _ _ _ _ K). }
  unfold md_hdr in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 _ _ _ m) with (c_FLAGS2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_flags KK); auto.
  - replace (stepf2 _ _ _ m) with (c_TIME2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_time KK); auto.
  - replace (stepf2 _ _ _ m) with (c_OS2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_os KK); auto.
  - replace (stepf2 _ _ _ m) with (c_EXLEN2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_exlen KK); auto.
  - replace (stepf2 _ _ _ m) with (c_EXTRA2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_extra KK); auto.
  - replace (stepf2 _ _ _ m) with (c_NAME2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_name KK); auto.
  - replace (stepf2 _ _ _ m) with (c_COMMENT2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_comment KK); auto.
  - replace (stepf2 _ _ _ m) with (c_HCRC m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply (x_hcrc KK); auto.
Qed.

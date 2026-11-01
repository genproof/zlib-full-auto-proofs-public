(* RT-I: copy of rfc1951/DecType.v over the generalized definitions RTIGDefs.v. *)
(* Part of the decode theory: the passes from TYPE, TYPEDO, STORED, COPY_, COPY.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Pure facts about the bit format                                                                 *)

Lemma dt_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros H. unfold bits_le. rewrite Zlength_map, Zlength_correct, length_seq. lia. Qed.

Lemma dt_zeros_len n : 0 <= n -> Zlength (zeros n) = n.
Proof. intros H. unfold zeros. rewrite Zlength_correct, repeat_length. lia. Qed.

Lemma dt_bval_app x y : bval (x ++ y) = bval x + 2 ^ Zlength x * bval y.
Proof.
  induction x as [|a x IH]; cbn [app bval].
  - rewrite Zlength_nil. cbn. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg x); lia). ring.
Qed.

Lemma dt_bval_seq v s n : 0 <= v ->
  bval (map (fun i => Z.testbit v (Z.of_nat i)) (seq s n)) = (v / 2 ^ Z.of_nat s) mod 2 ^ Z.of_nat n.
Proof.
  intros Hv. revert s. induction n as [|n IH]; intros s.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [seq map bval]. rewrite IH.
    rewrite Z.testbit_spec' by lia.
    replace (Z.of_nat (S s)) with (Z.of_nat s + 1) by lia.
    replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
    set (w := v / 2 ^ Z.of_nat s).
    assert (0 <= w) by (apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]).
    rewrite Z.pow_add_r, Z.pow_1_r by lia.
    rewrite Z.rem_mul_r by (try apply Z.pow_pos_nonneg; lia). reflexivity.
Qed.

Lemma dt_bval_le v n : 0 <= n -> 0 <= v < 2 ^ n -> bval (bits_le v n) = v.
Proof.
  intros Hn Hv. unfold bits_le. rewrite dt_bval_seq by lia. cbn [Z.of_nat]. rewrite Z.pow_0_r, Z.div_1_r.
  rewrite Z2Nat.id by lia. apply Z.mod_small. lia.
Qed.

Lemma dt_bytes_bits_len l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, dt_bits_le_len, Zlength_cons by lia. lia.
Qed.

Lemma dt_bytes_bits_app x y : bytes_bits (x ++ y) = bytes_bits x ++ bytes_bits y.
Proof. apply List.flat_map_app. Qed.

Lemma dt_bytes_bits_sub l a b : 0 <= a <= b -> b <= Zlength l ->
  sublist (8 * a) (8 * b) (bytes_bits l) = bytes_bits (sublist a b l).
Proof.
  intros Ha Hb.
  assert (E : l = sublist 0 a l ++ sublist a b l ++ sublist b (Zlength l) l)
    by (rewrite !sublist_rejoin, sublist_same by lia; reflexivity).
  rewrite E at 1. rewrite !dt_bytes_bits_app.
  assert (L0 : Zlength (bytes_bits (sublist 0 a l)) = 8 * a)
    by (rewrite dt_bytes_bits_len, Zlength_sublist by lia; lia).
  assert (L1 : Zlength (bytes_bits (sublist a b l)) = 8 * (b - a))
    by (rewrite dt_bytes_bits_len, Zlength_sublist by lia; lia).
  rewrite sublist_app2 by lia. rewrite L0.
  rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

(* bytes_bits is injective on bytes *)
Lemma dt_bytes_bits_inj l l' : bytes_ok l -> bytes_ok l' -> bytes_bits l = bytes_bits l' -> l = l'.
Proof.
  revert l'. induction l as [|a l IH]; intros l' Bl Bl' E; destruct l' as [|b l'].
  - reflexivity.
  - apply (f_equal (@Zlength bool)) in E. rewrite !dt_bytes_bits_len, Zlength_nil, Zlength_cons in E.
    pose proof (Zlength_nonneg l'). lia.
  - apply (f_equal (@Zlength bool)) in E. rewrite !dt_bytes_bits_len, Zlength_nil, Zlength_cons in E.
    pose proof (Zlength_nonneg l). lia.
  - unfold bytes_bits in E. cbn [flat_map] in E. fold bytes_bits in E.
    apply app_eq_len_eq in E as [E1 E2];
      [|unfold bits_le; rewrite !length_map; reflexivity].
    inversion Bl as [|x y Ba Bl0]; subst. inversion Bl' as [|x y Bb Bl0']; subst.
    f_equal; [|apply IH; auto].
    change compcert.lib.Integers.Byte.max_unsigned with 255 in Ba, Bb.
    apply (f_equal bval) in E1. rewrite !dt_bval_le in E1 by (change (2 ^ 8) with 256; lia). exact E1.
Qed.

Fixpoint dt_lxor_chk (k: nat) (i: Z) : bool :=
  match k with O => true | S k' => (Z.lxor (65535 - i) 65535 =? i) && dt_lxor_chk k' (i + 1) end.

Lemma dt_lxor_chk_ok k i n : dt_lxor_chk k i = true -> i <= n < i + Z.of_nat k -> Z.lxor (65535 - n) 65535 = n.
Proof.
  revert i. induction k as [|k IH]; intros i C Hn; [lia|].
  cbn [dt_lxor_chk] in C. apply andb_true_iff in C as [C1 C2].
  destruct (Z.eq_dec n i) as [->|Ne]; [apply Z.eqb_eq; exact C1|].
  apply (IH (i + 1) C2). lia.
Qed.

Lemma dt_lxor16_check : dt_lxor_chk (Z.to_nat 65536) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dt_lxor16 n : 0 <= n <= 65535 -> Z.lxor (65535 - n) 65535 = n.
Proof.
  intros Hn. apply (dt_lxor_chk_ok _ _ _ dt_lxor16_check). rewrite Z2Nat.id by lia. lia.
Qed.

(* the deflate stream ends within the stream bytes *)
Lemma dt_endpos_pack x : 0 <= Zlength x -> Zlength (pack x) = (Zlength x + 7) / 8.
Proof.
  intros _. unfold pack. rewrite Zlength_map, Zlength_correct, length_seq.
  apply Z2Nat.id. apply Z.div_pos; [pose proof (Zlength_nonneg x)|]; lia.
Qed.

Lemma dt_endpos_bits bs : Zlength (deflate_bits bs) = 8 * Zlength (deflate_bytes bs).
Proof.
  unfold deflate_bytes. rewrite dt_endpos_pack by apply Zlength_nonneg.
  unfold deflate_bits. set (e := enc_blocks 0 bs).
  pose proof (Zlength_nonneg e).
  assert (P : 0 <= pad8 (Zlength e) < 8) by (unfold pad8; apply Z.mod_pos_bound; lia).
  rewrite Zlength_app, dt_zeros_len by lia.
  unfold pad8 in *. Z.to_euclidean_division_equations. lia.
Qed.

Lemma dt_endpos_slen G : endpos G <= 8 * slen G.
Proof.
  unfold endpos, slen, D0. rewrite dt_endpos_bits.
  unfold stream_bytes, hdr_bytes. destruct (dc_w G) as [|wb fl [did|]|h]; rewrite ?Zlength_app, ?Zlength_nil;
    repeat match goal with |- context [Zlength ?x] =>
      lazymatch goal with H: 0 <= Zlength x |- _ => fail | _ => pose proof (Zlength_nonneg x) end end; lia.
Qed.

Lemma dt_stored_len p f bytes :
  Zlength (enc_block p f (Stored bytes)) = 3 + pad8 (p + 3) + 32 + 8 * Zlength bytes.
Proof.
  assert (P : 0 <= pad8 (p + 3)) by (unfold pad8; apply Z.mod_pos_bound; lia).
  unfold enc_block. rewrite Zlength_cons.
  rewrite !Zlength_app, dt_zeros_len, !dt_bits_le_len, dt_bytes_bits_len by lia.
  cbn [Zlength Zlength_aux]. lia.
Qed.


Lemma dt_sub_in {A} (l e: list A) a b x y : sublist a b l = e -> 0 <= a <= x -> x <= y <= b ->
  sublist x y l = sublist (x - a) (y - a) e.
Proof.
  intros E Ha Hy. subst e. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Modes                                                                                          *)

Notation MTYPE := Zlib.proof.inflate.Model.TYPE.

Ltac dt_md := unfold HEAD, FLAGS, TIME, OS, MTYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS,
  LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *; lia.

Ltac dt_at_get :=
  let Hh := fresh "Hh" in let D := fresh "D" in let M := fresh "M" in
  intros [Hh D] M; split; [exact Hh|];
  repeat match type of D with
         | (_ /\ _) \/ _ =>
             let Dm := fresh "Dm" in let DA := fresh "DA" in
             destruct D as [[Dm DA]|D]; [first [exfalso; dt_md | exact DA] |]
         end;
  let Dm := fresh "Dm" in destruct D as [Dm _]; exfalso; dt_md.

Lemma dt_at_type G s c h b out : at_mode G s c h b out -> (i_mode s = MTYPE \/ i_mode s = TYPEDO) ->
  hold_ok G c h b /\ at_type G s (8 * c - b) b out.
Proof. unfold at_mode; cbv zeta. dt_at_get. Qed.

Lemma dt_at_stored G s c h b out : at_mode G s c h b out -> i_mode s = STORED ->
  hold_ok G c h b /\ at_stored G s (8 * c - b) b out.
Proof. unfold at_mode; cbv zeta. dt_at_get. Qed.

Lemma dt_at_copy G s c h b out : at_mode G s c h b out -> (i_mode s = COPY_ \/ i_mode s = COPY) ->
  hold_ok G c h b /\ at_copy G s (8 * c - b) b out.
Proof. unfold at_mode; cbv zeta. dt_at_get. Qed.

Lemma dt_mk_type G s c h b out : hold_ok G c h b -> (i_mode s = MTYPE \/ i_mode s = TYPEDO) ->
  at_type G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 2 right; left. auto. Qed.

Lemma dt_mk_stored G s c h b out : hold_ok G c h b -> i_mode s = STORED ->
  at_stored G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 3 right; left. auto. Qed.

Lemma dt_mk_copy G s c h b out : hold_ok G c h b -> (i_mode s = COPY_ \/ i_mode s = COPY) ->
  at_copy G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 4 right; left. auto. Qed.

Lemma dt_mk_table G s c h b out : hold_ok G c h b -> i_mode s = TABLE ->
  at_table G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 5 right; left. auto. Qed.

Lemma dt_mk_len G s c h b out : hold_ok G c h b -> i_mode s = LEN_ ->
  at_len G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 8 right; left. auto. Qed.

Lemma dt_mk_check G s c h b out : hold_ok G c h b -> i_mode s = CHECK ->
  at_check G s (8 * c - b) b out -> at_mode G s c h b out.
Proof. intros H M A. unfold at_mode; cbv zeta. split; [exact H|]. do 14 right; left. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Kd after a pass that only moves in the stream                                                  *)

Definition dt_okmd (x: Z) : Prop := md_type x \/ x = TABLE \/ x = LEN_ \/ x = CHECK.

Definition s_same (s s': istate) : Prop :=
  i_wrap s' = i_wrap s /\ i_head s' = i_head s /\ i_wbits s' = i_wbits s /\ i_flags s' = i_flags s /\
  i_wsize s' = i_wsize s /\ i_whave s' = i_whave s /\ i_wnext s' = i_wnext s /\ i_wdata s' = i_wdata s /\
  i_check s' = i_check s /\ i_total s' = i_total s.

Lemma dt_kd G pos inp ob m m' :
  Kd G pos inp ob m -> md_type (m_mode m) -> dt_okmd (m_mode m') ->
  m_inp m' = m_inp m -> m_out m' = m_out m -> m_aout m' = m_aout m -> m_ret m' = m_ret m ->
  m_tout m' = m_tout m -> s_same (m_s m) (m_s m') ->
  at_mode G (m_s m') (pos + m_nx m') (m_hold m') (m_bits m') (ob ++ m_ow m') ->
  Kd G pos inp ob m'.
Proof.
  intros K M M' Ei Eo Ea Er Et (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) A.
  destruct K as [Ki _ Kg Kw Kc Kt Ko Kr].
  unfold md_type, dt_okmd, md_type, m_mode in *.
  assert (N : forall x, (x = MTYPE \/ x = TYPEDO \/ x = STORED \/ x = COPY_ \/ x = COPY) \/ x = TABLE \/
            x = LEN_ \/ x = CHECK ->
            x <> HEAD /\ x <> FLAGS /\ x <> TIME /\ x <> OS /\ (x =? LENGTH) = false /\ (x =? DONE) = false)
    by (intros x Hx; repeat split; try (apply Z.eqb_neq); dt_md).
  destruct (N _ M') as (N1 & N2 & N3 & N4 & N5 & N6).
  destruct (N _ (or_introl M)) as (O1 & O2 & O3 & O4 & O5 & O6).
  constructor.
  - rewrite Ei; exact Ki.
  - exact A.
  - unfold glob_ok in *. destruct Kg as ((wb0 & E & _) & G2 & G3 & G4).
    rewrite S1, S2, S3, S4. split; [exists wb0; split; [exact E|intros; contradiction]|].
    split; [exact G2|]. split; [intros; apply G3; exact O1|]. intros; apply G4; auto.
  - intros _. unfold win_ok, win_at in *. rewrite S3, S5, S6, S7, S8.
    apply Kw. dt_md.
  - unfold chk_ok in *. intros W _ _ _ _. rewrite N5, N6, S9, S10. cbn [orb].
    specialize (Kc W O1 O2 O3 O4). rewrite O5, O6 in Kc. exact Kc.
  - unfold after_check in *. unfold m_mode. rewrite N5, N6, Et. rewrite O5, O6 in Kt.
    rewrite andb_false_r in *. exact Kt.
  - unfold after_check in *. unfold m_mode. rewrite N5, N6, Eo, Ea. rewrite O5, O6 in Ko.
    rewrite andb_false_r in *. exact Ko.
  - unfold m_mode. rewrite N6, Er. rewrite O6 in Kr. exact Kr.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS                                                                                       *)

Lemma dt_nbf (DK: dkit_stmt) G pos (inp: list Z) n k m :
  bytes_ok (dc_src G) ->
  m_inp m = sublist pos (pos + Zlength inp) (dc_src G) -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  0 <= m_nx m <= Zlength (m_inp m) -> hold_ok G (pos + m_nx m) (m_hold m) (m_bits m) ->
  0 < n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  exists nx' h' b' lv',
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv' /\
    hold_ok G (pos + nx') h' b' /\ m_nx m <= nx' <= Zlength (m_inp m) /\ b' - m_bits m = 8 * (nx' - m_nx m) /\
    ((lv' = 1 /\ nx' = Zlength (m_inp m) /\ b' < n) \/
     (lv' = m_leave m /\ n <= b' /\ (m_bits m < n -> b' < n + 8) /\ (n <= m_bits m -> b' = m_bits m))).
Proof.
  intros Hb Hi Hp Hl. pose proof (Zlength_nonneg inp).
  assert (Li : Zlength (m_inp m) = Zlength inp) by (rewrite Hi, Zlength_sublist; lia).
  revert m Hi Li. induction k as [|k IH]; intros m Hi Li Hx Hh Hn Hk.
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [exact Hh|]. split; [lia|]. split; [lia|]. right. lia.
  - cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        unfold m_have in H0. split; [exact Hh|]. split; [lia|]. split; [lia|]. left. lia.
      * unfold m_have in H0. destruct Hh as (Hh1 & Hh2 & Hh3) eqn:Hh0.
        assert (Hp' : hold_ok G (pos + m_nx (pull m)) (m_hold (pull m)) (m_bits (pull m))).
        { cbn [pull m_nx m_hold m_bits set_m_bits set_m_hold set_m_nx].
          unfold u32, u64. rewrite (Z.mod_small (m_bits m + 8)) by lia.
          replace (pos + (m_nx m + 1)) with (pos + m_nx m + 1) by lia.
          rewrite Hi, Znth_sublist by lia. rewrite Z.add_comm with (n := m_nx m).
          apply (dk_pull DK); auto; lia. }
        destruct (IH (pull m) Hi Li ltac:(cbn [pull m_nx m_inp set_m_bits set_m_hold set_m_nx]; lia) Hp' Hn
                    ltac:(cbn [pull m_bits set_m_bits]; unfold u32; rewrite Z.mod_small by lia; lia))
          as (nx' & h' & b' & lv' & E & R1 & R2 & R3 & C).
        cbn [pull m_nx m_inp m_bits m_leave set_m_bits set_m_hold set_m_nx] in R2, R3, C.
        unfold u32 in R3, C. rewrite (Z.mod_small (m_bits m + 8)) in R3, C by lia.
        exists nx', h', b', lv'. split; [rewrite E; destruct m; reflexivity|].
        split; [exact R1|]. split; [lia|]. split; [lia|].
        destruct C as [C|C]; [left; exact C|right]. lia.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [exact Hh|]. split; [lia|]. split; [lia|]. right. lia.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* Positions                                                                                      *)

Lemma dt_src_ok G : dctx_ok G -> bytes_ok (dc_src G).
Proof. intros (_ & _ & _ & _ & _ & _ & B & _). exact B. Qed.

Lemma dt_nblk G : dctx_ok G -> 1 <= nblk G.
Proof.
  intros ((_ & _ & _ & (NE & _)) & _). unfold nblk.
  destruct (dc_bs G) as [|b r]; [congruence|]. rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma dt_sbits_len G : Zlength (sbits G) = 8 * Zlength (dc_src G).
Proof. apply dt_bytes_bits_len. Qed.

Lemma dt_enc_len3 p f b : 3 <= Zlength (enc_block p f b).
Proof.
  unfold enc_block. rewrite Zlength_cons.
  destruct b; rewrite Zlength_app; cbn [Zlength Zlength_aux];
    match goal with |- context [Zlength ?x] => pose proof (Zlength_nonneg x) end; lia.
Qed.

Lemma dt_bpos_mono (DK: dkit_stmt) G k k' : dctx_ok G -> 0 <= k <= k' -> k' <= nblk G -> bpos G k <= bpos G k'.
Proof.
  intros Gok Hk Hk'.
  assert (A : forall i, 0 <= i -> k + i <= nblk G -> bpos G k <= bpos G (k + i)).
  { intros i Hi. pattern i. apply natlike_ind; [|intros j Hj IH Hn|exact Hi].
    - intros _. rewrite Z.add_0_r. lia.
    - unfold Z.succ in *. destruct (dk_blk DK G (k + j) Gok ltac:(lia)) as [E _].
      replace (k + (j + 1)) with (k + j + 1) by lia. rewrite E.
      pose proof (dt_enc_len3 (bpos G (k + j) - D0 G) (lastflag G (k + j) =? 1) (blk G (k + j))).
      specialize (IH ltac:(lia)). lia. }
  replace k' with (k + (k' - k)) by lia. apply A; lia.
Qed.

Lemma dt_bpos_nonneg (DK: dkit_stmt) G k : dctx_ok G -> 0 <= k <= nblk G -> 0 <= bpos G k.
Proof.
  intros Gok Hk. pose proof (dt_bpos_mono DK G 0 k Gok ltac:(lia) ltac:(lia)). rewrite (dk_bpos0 DK) in H.
  unfold D0 in H. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). lia.
Qed.

(* the end of block k is within the stream *)
Lemma dt_blk_end (DK: dkit_stmt) G k : dctx_ok G -> 0 <= k < nblk G -> bpos G (k + 1) <= 8 * slen G.
Proof.
  intros Gok Hk. pose proof (dt_bpos_mono DK G (k + 1) (nblk G) Gok ltac:(lia) ltac:(lia)).
  destruct (dk_end DK G Gok) as [E _]. pose proof (dt_endpos_slen G).
  assert (0 <= pad8 (bpos G (nblk G))) by (unfold pad8; apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma dt_b2z_last G k : Z.b2z (lastflag G k =? 1) = lastflag G k.
Proof. unfold lastflag. destruct (k =? nblk G - 1); reflexivity. Qed.

(* the pad to the byte boundary of a position 8c - b, b < 8 *)
Lemma dt_pad8_q c b : 0 <= b < 8 -> pad8 (8 * c - b) = b.
Proof. intros H. unfold pad8. Z.to_euclidean_division_equations. lia. Qed.

Ltac dt_red :=
  unfold m_mode, m_have, m_left in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_ow
       upd_s set_mode set_leave dropbits bytebits initbits bitsn
       i_mode i_last i_wrap i_head i_wbits i_flags i_wsize i_whave i_wnext i_wdata i_check i_total i_length
       i_lencode i_lenbits i_distcode i_distbits
       set_i_mode set_i_last set_i_length set_i_lencode set_i_lenbits set_i_distcode set_i_distbits] in *.

Lemma dt_drop (DK: dkit_stmt) G c h b n b' : hold_ok G c h b -> 0 <= n <= b -> b' = b - n ->
  hold_ok G c (Z.shiftr h n) b'.
Proof. intros H Hn ->. apply (dk_drop DK); auto. Qed.

Lemma dt_bfinal p f b : bval (sublist 0 1 (enc_block p f b)) = Z.b2z f.
Proof. destruct f, b; reflexivity. Qed.

Lemma dt_btype p f b : bval (sublist 1 3 (enc_block p f b)) =
  match b with Stored _ => 0 | Fixed _ => 1 | Dynamic _ _ _ _ _ => 2 end.
Proof. destruct f, b; reflexivity. Qed.

Lemma dt_u32 x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

Lemma dt_kd_leave G pos inp ob m : Kd G pos inp ob m -> m_mode m <> DONE -> Kd G pos inp ob (set_leave m).
Proof.
  intros K N. destruct K as [K1 K2 K3 K4 K5 K6 K7 K8]. constructor; auto.
  unfold m_mode, set_leave in *. cbn [m_s m_ret m_leave set_m_leave] in *.
  rewrite K8. apply Z.eqb_neq in N. rewrite N. reflexivity.
Qed.

Lemma dt_ow_leave x : m_ow (set_leave x) = m_ow x.
Proof. reflexivity. Qed.

Lemma dt_mode_leave x : m_mode (set_leave x) = m_mode x.
Proof. reflexivity. Qed.

Lemma dt_post G pos inp ob flush m m' :
  Kd G pos inp ob m' -> (exists d, m_ow m' = m_ow m ++ d) -> (m_leave m' = 1 -> leave_why G pos inp ob flush m') ->
  dstep_post G pos inp ob flush m (IBrk m').
Proof. intros. cbn [dstep_post]. auto. Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* TYPEDO                                                                                         *)

Definition dt_pre G pos (inp: list Z) ob m : Prop :=
  dctx_ok G /\ 0 <= pos /\ pos + Zlength inp <= Zlength (dc_src G) /\
  inp = sublist pos (pos + Zlength inp) (dc_src G) /\ Kd G pos inp ob m /\ mwf3 m /\ m_leave m = 0.

Lemma dt_typedo (DK: dkit_stmt) (TD: tabdec_stmt) G pos inp ob flush m :
  dt_pre G pos inp ob m -> (m_mode m = MTYPE \/ m_mode m = TYPEDO) ->
  dstep_post G pos inp ob flush m (c_TYPEDO flush m).
Proof.
  intros (Gok & Hp & Hl & Hinp & K & W & L0) M.
  pose proof (kd_at _ _ _ _ _ K) as A. pose proof (kd_inp _ _ _ _ _ K) as Ki.
  destruct (dt_at_type _ _ _ _ _ _ A M) as [Hh (k & Hk & Hq & Ho & Hb & Hlast)].
  pose proof (dt_src_ok G Gok) as Bs. pose proof (dt_nblk G Gok) as Nb.
  pose proof (mw_nx _ (mwf3_mwf _ W)) as Hx.
  pose proof (Zlength_nonneg inp).
  unfold c_TYPEDO.
  destruct (Z.eqb_spec (i_last (m_s m)) 0) as [Lz|Lnz]; cbn [negb].
  - assert (Hk1 : k < nblk G).
    { destruct (Z.eqb_spec k (nblk G)) as [E|E]; [|lia]. exfalso. rewrite Hlast in Lz.
      destruct (Z.eqb_spec k 0); [lia|]. unfold lastflag in Lz. rewrite E, Z.eqb_refl in Lz. discriminate. }
    rewrite Ki in Hx.
    destruct (dt_nbf DK G pos inp 3 4 m Bs ltac:(rewrite Ki; exact Hinp) Hp Hl ltac:(rewrite Ki; exact Hx) Hh
                ltac:(lia) ltac:(cbn; destruct Hh; lia))
      as (nx' & h' & b' & lv' & E & R1 & R2 & R3 & C).
    unfold needbits. rewrite E. rewrite Ki in R2, C.
    destruct (dk_blk DK G k Gok ltac:(lia)) as [Eb Sb].
    destruct C as [(-> & Enx & Cb)|(Cl & Cb1 & Cb2 & Cb3)].
    + (* out of input *)
      rewrite Z.eqb_refl.
      apply dt_post; [| exists []; dt_red; rewrite app_nil_r; reflexivity |intros _].
      * apply (dt_kd G pos inp ob m); auto; dt_red; auto.
        { unfold md_type; tauto. }
        { unfold dt_okmd, md_type; tauto. }
        { unfold s_same; dt_red; tauto. }
        apply dt_mk_type; auto. exists k. repeat split; auto; lia.
      * right; left. dt_red. split; [lia|].
        pose proof (dt_blk_end DK G k Gok ltac:(lia)).
        pose proof (dt_enc_len3 (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)). lia.
    + rewrite Cl, L0.
      set (m1 := set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') 0).
      assert (Q1 : 8 * (pos + nx') - b' = bpos G k) by lia.
      pose proof (dt_enc_len3 (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) as L3.
      pose proof (dt_bpos_nonneg DK G k Gok ltac:(lia)) as Bp0.
      assert (F1 : bitsn m1 1 = lastflag G k).
      { unfold bitsn; subst m1; dt_red. rewrite (dk_bitsn DK G _ _ _ 1 R1) by lia. rewrite Q1.
        rewrite (dt_sub_in _ _ _ _ _ _ Sb) by lia. rewrite Z.sub_diag, Z.add_simpl_l, dt_bfinal.
        apply dt_b2z_last. }
      assert (Lm1 : m_leave m1 = 0) by reflexivity.
      rewrite Lm1, F1. change (0 =? 1) with false. cbv iota.
      set (m2 := dropbits 1 (upd_s m1 (fun s => set_i_last s (lastflag G k)))).
      assert (H2 : hold_ok G (pos + nx') (Z.shiftr h' 1) (b' - 1)) by (apply (dt_drop DK _ _ _ b'); auto; lia).
      assert (F2 : bitsn m2 2 = match blk G k with Stored _ => 0 | Fixed _ => 1 | Dynamic _ _ _ _ _ => 2 end).
      { unfold bitsn; subst m2 m1; dt_red. rewrite (dk_bitsn DK G _ _ _ 2 H2) by lia.
        replace (8 * (pos + nx') - (b' - 1)) with (bpos G k + 1) by lia.
        rewrite (dt_sub_in _ _ _ _ _ _ Sb) by lia.
        replace (bpos G k + 1 - bpos G k) with 1 by lia. replace (bpos G k + 1 + 2 - bpos G k) with 3 by lia.
        apply dt_btype. }
      rewrite F2.
      assert (Bb : b' < 11) by lia.
      destruct (blk G k) as [bytes|syms|nlen ndist clsent toks syms] eqn:Ebk; cbn [Z.eqb Pos.eqb].
      * (* stored *)
        apply dt_post; [| exists []; subst m2 m1; dt_red; rewrite app_nil_r; reflexivity
                        | subst m2 m1; dt_red; lia].
        apply (dt_kd G pos inp ob m); subst m2 m1; auto; dt_red; auto.
        { unfold md_type; tauto. }
        { unfold dt_okmd, md_type; tauto. }
        { unfold s_same; dt_red; tauto. }
        rewrite (dt_u32 (b' - 1)) by lia. rewrite dt_u32 by lia.
        apply dt_mk_stored; dt_red; auto.
        { apply (dt_drop DK _ _ _ (b' - 1)); auto; lia. }
        exists k, bytes. split; [split; [lia|reflexivity]|]. split; [exact Ebk|]. split; [exact Ho|].
        cbv zeta. left. split; lia.
      * (* fixed *)
        assert (KK : forall mm, mm = dropbits 2 (set_mode (upd_s m2 (fun s =>
               set_i_distbits (set_i_distcode (set_i_lenbits (set_i_lencode s TLenfix) 9) TDistfix) 5)) LEN_) ->
               Kd G pos inp ob mm /\ m_ow mm = m_ow m ++ [] /\ m_leave mm = 0).
        { intros mm ->. split; [|split; [subst m2 m1; dt_red; rewrite app_nil_r; reflexivity
                                       | subst m2 m1; dt_red; lia]].
          apply (dt_kd G pos inp ob m); subst m2 m1; auto; dt_red; auto.
          { unfold md_type; tauto. }
          { unfold dt_okmd, md_type; tauto. }
          { unfold s_same; dt_red; tauto. }
          rewrite (dt_u32 (b' - 1)) by lia. rewrite dt_u32 by lia.
          apply dt_mk_len; dt_red; auto.
          { apply (dt_drop DK _ _ _ (b' - 1)); auto; lia. }
          exists k, 0, fixed_ll, fixed_dl, syms, (bpos G k + 3).
          split; [|split; [rewrite Ho; unfold outj; cbn [Z.to_nat firstn syms_data fold_left]; reflexivity
                           |split; [lia|left; lia]]].
          split; [split; [lia|reflexivity]|].
          split; [left; auto|].
          split; [pose proof (Zlength_nonneg syms); lia|].
          split; [apply (proj1 (td_fixed TD _))|]. split; [apply (proj2 (td_fixed TD _))|].
          rewrite Ebk. unfold sym_off. cbn [hb_hdr Z.to_nat firstn flat_map]. rewrite Zlength_nil. lia. }
        destruct (Z.eqb_spec flush Z_TREES) as [Ft|Ft].
        -- destruct (KK _ eq_refl) as (K1 & K2 & K3).
           apply dt_post; [| exists []; rewrite dt_ow_leave; exact K2 | intros _; do 3 right; auto].
           apply dt_kd_leave; [exact K1|]. subst m2 m1. dt_red. dt_md.
        -- destruct (KK _ eq_refl) as (K1 & K2 & K3).
           apply dt_post; [exact K1| exists []; exact K2 | intros E'; lia].
      * (* dynamic *)
        apply dt_post; [| exists []; subst m2 m1; dt_red; rewrite app_nil_r; reflexivity
                        | subst m2 m1; dt_red; lia].
        apply (dt_kd G pos inp ob m); subst m2 m1; auto; dt_red; auto.
        { unfold md_type; tauto. }
        { unfold dt_okmd, md_type; tauto. }
        { unfold s_same; dt_red; tauto. }
        rewrite (dt_u32 (b' - 1)) by lia. rewrite dt_u32 by lia.
        apply dt_mk_table; dt_red; auto.
        { apply (dt_drop DK _ _ _ (b' - 1)); auto; lia. }
        exists k, nlen, ndist, clsent, toks, syms. split; [split; [lia|reflexivity]|].
        split; [exact Ebk|]. split; [exact Ho|]. split; lia.
  - assert (Ek : k = nblk G).
    { destruct (Z.eqb_spec k 0) as [E0|E0]; [contradiction|]. unfold lastflag in Hlast.
      destruct (Z.eqb_spec (k - 1) (nblk G - 1)); [lia|contradiction]. }
    assert (L1 : i_last (m_s m) = 1).
    { rewrite Hlast. subst k. destruct (Z.eqb_spec (nblk G) 0); [lia|]. unfold lastflag.
      rewrite Z.eqb_refl. reflexivity. }
    apply dt_post; [| exists []; dt_red; rewrite app_nil_r; reflexivity | dt_red; lia].
    apply (dt_kd G pos inp ob m); auto; dt_red; auto.
    { unfold md_type; tauto. }
    { unfold dt_okmd; auto. }
    { unfold s_same; dt_red; tauto. }
    assert (Bm : m_bits m mod 8 = m_bits m) by (apply Z.mod_small; destruct Hh; lia).
    rewrite Bm, Z.sub_diag.
    apply dt_mk_check; dt_red; auto.
    { apply (dt_drop DK _ _ _ (m_bits m)); auto; destruct Hh; lia. }
    unfold at_check. rewrite Z.sub_0_r. split; [rewrite Ho, Ek; apply (dk_full DK)|].
    split; [exact L1|]. split; [|split; [reflexivity|lia]].
    destruct (dk_end DK G Gok) as [E _]. rewrite E, <- Ek, <- Hq, dt_pad8_q by (destruct Hh; lia). lia.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* COPY_ / COPY                                                                                   *)

Lemma dt_blocks_nth wmax out bs k b : blocks_ok wmax out bs -> (k < length bs)%nat ->
  nth k bs (Stored []) = Stored b -> Zlength b <= 65535 /\ Forall byte_ok b.
Proof.
  revert out k. induction bs as [|a r IH]; intros out k Hb Hk E; [cbn in Hk; lia|].
  destruct Hb as [Ha Hr]. destruct k as [|k].
  - cbn in E. subst a. exact Ha.
  - cbn in E, Hk. apply (IH _ k Hr); auto. lia.
Qed.

Lemma dt_blk_bytes G k bytes : dctx_ok G -> 0 <= k < nblk G -> blk G k = Stored bytes -> bytes_ok bytes.
Proof.
  intros ((_ & _ & _ & (_ & _ & Hb)) & _) Hk E.
  assert (F : Forall byte_ok bytes).
  { apply (dt_blocks_nth _ _ _ (Z.to_nat k) _ Hb); [|exact E]. unfold nblk in Hk. rewrite Zlength_correct in Hk. lia. }
  unfold bytes_ok. eapply Forall_impl; [|exact F]. intros a Ha. unfold byte_ok in Ha.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma dt_pad8_shift x d : d mod 8 = 0 -> pad8 (x - d) = pad8 x.
Proof. intros H. unfold pad8. Z.to_euclidean_division_equations. lia. Qed.

Lemma dt_stored_hdr p f bytes : exists H, enc_block p f (Stored bytes) = H ++ bytes_bits bytes /\
  Zlength H = 3 + pad8 (p + 3) + 32.
Proof.
  set (n := Zlength bytes).
  exists (f :: [false; false] ++ zeros (pad8 (p + 3)) ++ bits_le n 16 ++ bits_le (65535 - n) 16). split.
  - unfold enc_block. cbn [app]. f_equal. f_equal. f_equal. rewrite <- !app_assoc. reflexivity.
  - assert (P : 0 <= pad8 (p + 3)) by (unfold pad8; apply Z.mod_pos_bound; lia).
    rewrite Zlength_cons, !Zlength_app, dt_zeros_len, !dt_bits_le_len by lia. cbn [Zlength Zlength_aux]. lia.
Qed.

Lemma dt_blk_len G k bytes : dctx_ok G -> 0 <= k < nblk G -> blk G k = Stored bytes -> Zlength bytes <= 65535.
Proof.
  intros ((_ & _ & _ & (_ & _ & Hb)) & _) Hk E.
  apply (dt_blocks_nth _ _ _ (Z.to_nat k) _ Hb); [|exact E]. unfold nblk in Hk. rewrite Zlength_correct in Hk. lia.
Qed.

Lemma dt_stored_lenbits p f bytes :
  sublist (3 + pad8 (p + 3)) (3 + pad8 (p + 3) + 32) (enc_block p f (Stored bytes)) =
  bits_le (Zlength bytes) 16 ++ bits_le (65535 - Zlength bytes) 16.
Proof.
  set (n := Zlength bytes).
  assert (P : 0 <= pad8 (p + 3)) by (unfold pad8; apply Z.mod_pos_bound; lia).
  assert (E : enc_block p f (Stored bytes) =
    (f :: [false; false] ++ zeros (pad8 (p + 3))) ++ (bits_le n 16 ++ bits_le (65535 - n) 16) ++ bytes_bits bytes).
  { unfold enc_block. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  assert (L1 : Zlength (f :: [false; false] ++ zeros (pad8 (p + 3))) = 3 + pad8 (p + 3)).
  { rewrite Zlength_cons, Zlength_app, dt_zeros_len by lia. cbn [Zlength Zlength_aux]. lia. }
  assert (L2 : Zlength (bits_le n 16 ++ bits_le (65535 - n) 16) = 32).
  { rewrite Zlength_app, !dt_bits_le_len by lia. lia. }
  rewrite E, sublist_app2 by lia. rewrite L1.
  replace (3 + pad8 (p + 3) - (3 + pad8 (p + 3))) with 0 by lia.
  replace (3 + pad8 (p + 3) + 32 - (3 + pad8 (p + 3))) with 32 by lia.
  rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

Lemma dt_kd_copy G pos inp ob m : Kd G pos inp ob m -> m_mode m = COPY_ -> Kd G pos inp ob (set_mode m COPY).
Proof.
  intros K M. apply (dt_kd G pos inp ob m); auto; try reflexivity.
  { unfold md_type; tauto. }
  { unfold dt_okmd, md_type; dt_red; tauto. }
  { unfold s_same; dt_red; tauto. }
  pose proof (kd_at _ _ _ _ _ K) as A. destruct (dt_at_copy _ _ _ _ _ _ A (or_introl M)) as [Hh Ac].
  apply dt_mk_copy; dt_red; auto.
Qed.

Lemma dt_post_ow G pos inp ob flush m m1 o : dstep_post G pos inp ob flush m1 o -> m_ow m1 = m_ow m ->
  dstep_post G pos inp ob flush m o.
Proof.
  destruct o as [mo|r mo]; cbn [dstep_post]; [|tauto]. intros (K & (d & E) & L) Eo.
  split; [exact K|]. split; [exists d; rewrite E, Eo; reflexivity|exact L].
Qed.

Lemma dt_copy (DK: dkit_stmt) G pos inp ob flush m :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) -> Kd G pos inp ob m ->
  0 <= m_nx m <= Zlength (m_inp m) -> Zlength (m_ow m) <= m_aout m -> m_leave m = 0 ->
  (m_mode m = COPY_ \/ m_mode m = COPY) ->
  dstep_post G pos inp ob flush m (c_COPY m).
Proof.
  intros Gok Hp Hl Hinp K Hx Hw L0 M. unfold c_COPY. cbv zeta.
  pose proof (kd_at _ _ _ _ _ K) as A. pose proof (kd_inp _ _ _ _ _ K) as Ki.
  destruct (dt_at_copy _ _ _ _ _ _ A M) as [Hh (k & bytes & (Hk & Hlast) & Ebk & Hr & Hb0 & Hq & Ho)].
  pose proof (dt_src_ok G Gok) as Bs. pose proof (Zlength_nonneg inp).
  rewrite Ki in Hx.
  destruct (dk_blk DK G k Gok ltac:(lia)) as [Eb Sb]. rewrite Ebk in Eb, Sb.
  rewrite dt_stored_len in Eb. replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in Eb by lia.
  rewrite dt_pad8_shift in Eb by (apply (dk_D0 DK)).
  set (p := bpos G k + 3) in *. set (r := i_length (m_s m)) in *.
  pose proof (dt_bpos_nonneg DK G k Gok ltac:(lia)) as Bp0.
  assert (P8 : 0 <= pad8 p) by (unfold pad8; apply Z.mod_pos_bound; lia).
  assert (QE : 8 * (pos + m_nx m) - m_bits m + 8 * r = bpos G (k + 1)) by (unfold p in *; lia).
  pose proof (dt_blk_end DK G k Gok ltac:(lia)) as BE.
  destruct (Z.eqb_spec r 0) as [R0|R0]; cbn [negb].
  - (* the block is copied: next block *)
    apply dt_post; [| exists []; dt_red; rewrite app_nil_r; reflexivity | dt_red; lia].
    apply (dt_kd G pos inp ob m); auto; dt_red; auto.
    { unfold md_type; tauto. }
    { unfold dt_okmd, md_type; tauto. }
    { unfold s_same; dt_red; tauto. }
    apply dt_mk_type; dt_red; auto.
    exists (k + 1). split; [lia|]. split; [lia|]. split.
    { rewrite Ho, R0, Z.sub_0_r, sublist_same by lia. rewrite (dk_outk DK G k ltac:(lia)), Ebk. reflexivity. }
    split; [lia|]. replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.add_simpl_r. exact Hlast.
  - set (cp := Z.min (Z.min r (m_have m)) (m_left m)).
    assert (Cp : 0 <= cp <= r /\ cp <= m_have m /\ cp <= m_left m /\ (cp = 0 -> m_have m = 0 \/ m_left m = 0))
      by (unfold cp, m_have, m_left in *; rewrite Ki; lia).
    destruct (Z.eqb_spec cp 0) as [C0|C0].
    + apply dt_post; [apply dt_kd_leave; [exact K| unfold m_mode in *; dt_md]
                     | exists []; rewrite dt_ow_leave, app_nil_r; reflexivity | intros _].
      destruct Cp as (_ & _ & _ & Cz). destruct (Cz C0) as [Hv|Hv]; unfold leave_why.
      * right; left. unfold m_have in Hv. unfold set_leave; cbn [m_nx set_m_leave]. rewrite Ki in Hv. subst r. lia.
      * right; right; left. unfold m_left in *. unfold set_leave; cbn [m_ow m_aout set_m_leave]. split; [lia|].
        rewrite Ho. destruct (dk_full_len DK G (k + 1) ltac:(lia)) as [_ (rest & Er)].
        rewrite Er, (dk_outk DK G k ltac:(lia)), Ebk. cbn [block_data].
        rewrite !Zlength_app, Zlength_sublist by lia. pose proof (Zlength_nonneg rest). lia.
    + destruct Cp as (Cp1 & Cp2 & Cp3 & _). unfold m_have, m_left in Cp2, Cp3. rewrite Ki in Cp2.
      set (n := Zlength bytes) in *.
      pose proof (dt_blk_bytes G k bytes Gok Hk Ebk) as Bb.
      destruct (dt_stored_hdr (bpos G k - D0 G) (lastflag G k =? 1) bytes) as (Hd & Ed & Ld).
      replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in Ld by lia.
      rewrite dt_pad8_shift in Ld by (apply (dk_D0 DK)). fold p in Ld.
      assert (IB : inbytes m cp = sublist (n - r) (n - r + cp) bytes).
      { unfold inbytes. rewrite Ki, Hinp at 1. rewrite sublist_sublist by lia.
        apply dt_bytes_bits_inj; [apply Forall_sublist; exact Bs|apply Forall_sublist; exact Bb|].
        rewrite <- (dt_bytes_bits_sub (dc_src G)) by lia.
        rewrite <- (dt_bytes_bits_sub bytes) by lia.
        fold (sbits G). rewrite (dt_sub_in _ _ _ _ _ _ Sb) by lia. rewrite Ed.
        rewrite sublist_app2 by lia. f_equal; lia. }
      apply dt_post; [| exists (inbytes m cp); dt_red; reflexivity | dt_red; lia].
      apply (dt_kd G pos inp ob m); auto; dt_red; auto.
      { unfold md_type, m_mode in *; tauto. }
      { unfold dt_okmd, md_type, m_mode in *; tauto. }
      { unfold s_same; dt_red; tauto. }
      assert (H0 : m_hold m = 0).
      { destruct Hh as (_ & _ & Hh). rewrite Hh, Hb0, Z.sub_0_r, sublist_nil. reflexivity. }
      apply dt_mk_copy; dt_red.
      { rewrite H0, Hb0. split; [lia|]. split; [lia|]. rewrite Z.sub_0_r, sublist_nil. reflexivity. }
      { unfold m_mode in M; exact M. }
      rewrite Hb0. exists k, bytes. split; [split; [exact Hk|exact Hlast]|]. split; [exact Ebk|].
      cbv zeta. cbn [i_length set_i_length]. fold n. fold p.
      split; [lia|]. split; [reflexivity|]. split; [lia|].
      rewrite app_assoc, Ho, IB, <- app_assoc, sublist_rejoin by lia. f_equal. f_equal. lia.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* STORED                                                                                         *)

Lemma dt_stored (DK: dkit_stmt) G pos inp ob flush m :
  dt_pre G pos inp ob m -> m_mode m = STORED -> dstep_post G pos inp ob flush m (c_STORED flush m).
Proof.
  intros (Gok & Hp & Hl & Hinp & K & W & L0) M.
  pose proof (kd_at _ _ _ _ _ K) as A. pose proof (kd_inp _ _ _ _ _ K) as Ki.
  destruct (dt_at_stored _ _ _ _ _ _ A M) as [Hh (k & bytes & (Hk & Hlast) & Ebk & Ho & Hpos)].
  cbv zeta in Hpos.
  pose proof (dt_src_ok G Gok) as Bs. pose proof (Zlength_nonneg inp).
  pose proof (mw_nx _ (mwf3_mwf _ W)) as Hx. pose proof (mw_ow _ (mwf3_mwf _ W)) as [Hw _].
  pose proof (mw_bits _ (mwf3_mwf _ W)) as Hb.
  rewrite Ki in Hx.
  destruct (dk_blk DK G k Gok ltac:(lia)) as [Eb Sb]. rewrite Ebk in Eb, Sb.
  pose proof (dt_stored_lenbits (bpos G k - D0 G) (lastflag G k =? 1) bytes) as SL.
  rewrite dt_stored_len in Eb.
  replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in Eb, SL by lia.
  rewrite dt_pad8_shift in Eb, SL by (apply (dk_D0 DK)).
  set (p := bpos G k + 3) in *. set (n := Zlength bytes) in *.
  pose proof (dt_bpos_nonneg DK G k Gok ltac:(lia)) as Bp0.
  assert (P8 : 0 <= pad8 p) by (unfold pad8; apply Z.mod_pos_bound; lia).
  pose proof (dt_blk_end DK G k Gok ltac:(lia)) as BE.
  pose proof (dt_blk_len G k bytes Gok Hk Ebk) as Nl. fold n in Nl.
  assert (N0 : 0 <= n) by apply Zlength_nonneg.
  unfold c_STORED, needbits.
  set (mb := bytebits m).
  assert (Hmb : hold_ok G (pos + m_nx mb) (m_hold mb) (m_bits mb) /\
                8 * (pos + m_nx mb) - m_bits mb = p + pad8 p /\ m_bits mb mod 8 = 0 /\ 0 <= m_bits mb < 32).
  { subst mb. unfold bytebits. cbn [m_nx m_hold m_bits set_m_bits set_m_hold].
    destruct Hh as (Hh1 & Hh2 & Hh3).
    split; [apply (dt_drop DK _ _ _ (m_bits m)); [split; [|split]; auto|
              pose proof (Z.mod_pos_bound (m_bits m) 8); pose proof (Z.mod_le (m_bits m) 8); lia|lia]|].
    destruct Hpos as [(Q & B8)|(Q & B0 & B32)].
    - rewrite Z.mod_small by lia. rewrite Z.sub_diag, Z.mod_0_l by lia. split; [|lia].
      rewrite <- Q, dt_pad8_q by lia. lia.
    - rewrite B0, Z.sub_0_r. split; [lia|]. split; [exact B0|lia]. }
  destruct Hmb as (Hmb & Qb & Mb8 & Bb32).
  assert (Imb : m_inp mb = m_inp m) by reflexivity. assert (Xmb : m_nx mb = m_nx m) by reflexivity.
  destruct (dt_nbf DK G pos inp 32 4 mb Bs ltac:(rewrite Imb, Ki; exact Hinp) Hp Hl
              ltac:(rewrite Imb, Xmb, Ki; lia) Hmb ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
    as (nx' & h' & b' & lv' & E & R1 & R2 & R3 & C).
  rewrite E.
  destruct C as [(-> & Enx & Cb)|(Cl & Cb1 & Cb2 & Cb3)].
  - (* out of input *)
    rewrite Z.eqb_refl.
    apply dt_post; [| exists []; subst mb; dt_red; rewrite app_nil_r; reflexivity |intros _].
    + apply (dt_kd G pos inp ob m); subst mb; auto; dt_red; auto.
      { unfold md_type; tauto. }
      { unfold dt_okmd, md_type; tauto. }
      { unfold s_same; dt_red; tauto. }
      apply dt_mk_stored; auto. exists k, bytes. split; [split; [exact Hk|exact Hlast]|].
      split; [exact Ebk|]. split; [exact Ho|]. cbv zeta. right. fold p.
      cbn [m_nx m_bits bytebits set_m_bits set_m_hold] in *. split; [lia|]. split; [|lia].
      replace b' with (m_bits m - m_bits m mod 8 + 8 * (nx' - m_nx m)) by lia.
      rewrite (Z.mul_comm 8), Z_mod_plus_full. exact Mb8.
    + right; left. dt_red. rewrite Imb, Ki in Enx. rewrite Xmb in Qb, R3. unfold p in *. lia.
  - assert (Lv : m_leave mb = 0) by exact L0. rewrite Cl, Lv in *. clear Cl.
    rewrite Xmb in Qb, R3, R2. rewrite Imb, Ki in R2.
    assert (B32 : b' = 32) by (clear -Mb8 Bb32 Cb1 Cb2 R3; Z.to_euclidean_division_equations; lia). subst b'.
    set (m2 := set_m_leave (set_m_bits (set_m_hold (set_m_nx mb nx') h') 32) 0).
    assert (H2 : m_hold m2 = h') by reflexivity. assert (L2 : m_leave m2 = 0) by reflexivity.
    rewrite L2, H2. change (0 =? 1) with false. cbv iota.
    pose proof (dk_hold_lt DK _ _ _ _ R1 Bs) as HL.
    pose proof (dk_bitsn DK _ _ _ _ 32 R1 ltac:(lia)) as HB.
    rewrite Z.mod_small in HB by lia.
    replace (8 * (pos + nx') - 32) with (bpos G k + (3 + pad8 p)) in HB by (unfold p in *; lia).
    replace (bpos G k + (3 + pad8 p) + 32) with (bpos G k + (3 + pad8 p + 32)) in HB by lia.
    rewrite (dt_sub_in _ _ _ _ _ _ Sb) in HB by (unfold p in *; lia).
    replace (bpos G k + (3 + pad8 p) - bpos G k) with (3 + pad8 p) in HB by lia.
    replace (bpos G k + (3 + pad8 p + 32) - bpos G k) with (3 + pad8 p + 32) in HB by lia.
    rewrite SL, dt_bval_app, !dt_bval_le, dt_bits_le_len in HB by (try change (2 ^ 16) with 65536; lia).
    change (2 ^ 16) with 65536 in HB.
    assert (CH1 : Z.land h' 65535 = n).
    { change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536. rewrite HB.
      Z.to_euclidean_division_equations. lia. }
    assert (CH2 : Z.shiftr h' 16 = 65535 - n).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. rewrite HB.
      Z.to_euclidean_division_equations. lia. }
    assert (HM : h' mod 65536 = n) by (rewrite HB; Z.to_euclidean_division_equations; lia).
    rewrite CH1, CH2, dt_lxor16, Z.eqb_refl by lia. cbn [negb]. rewrite HM.
    set (m3 := set_mode (initbits (upd_s m2 (fun s => set_i_length s n))) COPY_).
    assert (KK : Kd G pos inp ob m3).
    { apply (dt_kd G pos inp ob m); subst m3 m2 mb; auto; dt_red; auto.
      { unfold md_type; tauto. }
      { unfold dt_okmd, md_type; tauto. }
      { unfold s_same; dt_red; tauto. }
      destruct R1 as (_ & R1b & _).
      apply dt_mk_copy; dt_red; auto.
      { split; [lia|]. split; [lia|]. rewrite Z.sub_0_r, sublist_nil. reflexivity. }
      exists k, bytes. split; [split; [exact Hk|exact Hlast]|]. split; [exact Ebk|].
      cbv zeta. fold n. fold p. cbn [i_length set_i_mode set_i_length].
      split; [lia|]. split; [reflexivity|]. split; [unfold p in *; lia|].
      rewrite Z.sub_diag, sublist_nil, app_nil_r. exact Ho. }
    destruct (Z.eqb_spec flush Z_TREES) as [Ft|Ft].
    + apply dt_post; [apply dt_kd_leave; [exact KK|subst m3; dt_red; dt_md]
                     | exists []; rewrite dt_ow_leave; subst m3 m2 mb; dt_red; rewrite app_nil_r; reflexivity
                     | intros _; do 3 right; right; exact Ft].
    + unfold c_COPY_. apply (dt_post_ow _ _ _ _ _ _ (set_mode m3 COPY)); [|subst m3 m2 mb; dt_red; reflexivity].
      apply (dt_copy DK); auto.
      * apply dt_kd_copy; [exact KK|subst m3; dt_red; reflexivity].
      * subst m3 m2 mb; dt_red. rewrite Ki. lia.
Qed.

Lemma group_type : dkit_stmt -> tabdec_stmt -> group_ok md_type.
Proof.
  intros DK TD G pos inp ob flush m Gok Hp Hl Hinp K W L0 P.
  assert (Pre : dt_pre G pos inp ob m) by (unfold dt_pre; tauto).
  pose proof (mw_nx _ (mwf3_mwf _ W)) as Hx. pose proof (mw_ow _ (mwf3_mwf _ W)) as [Hw _].
  unfold stepf2. unfold md_type in P. destruct P as [E|[E|[E|[E|E]]]].
  - replace (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with (c_TYPE flush m)
      by (unfold step2; rewrite E; reflexivity).
    unfold c_TYPE. destruct ((flush =? Z_BLOCK) || (flush =? Z_TREES)) eqn:F.
    + apply dt_post; [apply dt_kd_leave; [exact K|rewrite E; dt_md]
                     | exists []; rewrite dt_ow_leave, app_nil_r; reflexivity | intros _].
      do 3 right. apply orb_true_iff in F. destruct F as [F|F]; apply Z.eqb_eq in F; auto.
    + apply (dt_typedo DK TD); auto.
  - replace (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with (c_TYPEDO flush m)
      by (unfold step2; rewrite E; reflexivity).
    apply (dt_typedo DK TD); auto.
  - replace (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with (c_STORED flush m)
      by (unfold step2; rewrite E; reflexivity).
    apply (dt_stored DK); auto.
  - replace (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with (c_COPY_ m)
      by (unfold step2; rewrite E; reflexivity).
    unfold c_COPY_. apply (dt_post_ow _ _ _ _ _ _ (set_mode m COPY)); [|reflexivity].
    apply (dt_copy DK); auto.
    apply dt_kd_copy; auto.
  - replace (step2 flush lenfix_list distfix_list (fast lenfix_list distfix_list) m) with (c_COPY m)
      by (unfold step2; rewrite E; reflexivity).
    apply (dt_copy DK); auto.
Qed.

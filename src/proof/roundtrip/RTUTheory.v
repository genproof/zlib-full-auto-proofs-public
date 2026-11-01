(* Round-trip laws, part RT-U: uncompress on compress2's zlib stream (RTIIface.ufacts), from the
   decode theory (rfc1951/Decode.v; its parts are proved by the inflate area). *)
Require Import Zlib.proof.roundtrip.RTIIface.
Require Zlib.proof.rfc1951.Decode.
Require Zlib.proof.harness.uncompress_any.UALive.
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope Z_scope.

Module DD := Zlib.proof.rfc1951.Decode.
Module FM := Zlib.proof.rfc1951.Format.

(* ---------------------------------------------------------------------------------------------- *)
(* The zlib header of compress2's stream: Format.zlib_hdr 15 (flg / 64) false                      *)

Definition rtu_hdr_okb (f: Z) : bool :=
  implb ((((RF.zcmf 15 * 256 + f) mod 31) =? 0) && negb (Z.testbit f 5))
    (Z.eqb (nth 1 (FM.zlib_hdr 15 (f / 64) false) 0) f).

Lemma rtu_hdr_all : forallb rtu_hdr_okb (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rtu_hdr (flg: Z) : RF.zflg_ok 15 false flg ->
  FM.zlib_hdr 15 (flg / 64) false = [RF.zcmf 15; flg] /\ 0 <= flg / 64 <= 3.
Proof.
  intros (R & M & T).
  assert (B: rtu_hdr_okb flg = true).
  { pose proof rtu_hdr_all as A. rewrite forallb_forall in A. apply A.
    replace flg with (Z.of_nat (Z.to_nat flg)) by lia. apply in_map. apply in_seq. lia. }
  unfold rtu_hdr_okb in B. rewrite M, T, Z.eqb_refl in B. cbn [andb negb implb] in B. apply Z.eqb_eq in B.
  split; [|split; [apply Z.div_pos; lia | assert (flg / 64 < 4) by (apply Z.div_lt_upper_bound; lia); lia]].
  unfold FM.zlib_hdr in *. cbv zeta in *. cbn [nth] in B. rewrite B. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Lengths of the encodings                                                                       *)

Import DD.

Lemma rtu_len_bits_le (v n: Z) : Zlength (bits_le v n) = Z.max 0 n.
Proof.
  unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length.
  destruct (Z_le_gt_dec 0 n); [rewrite Z2Nat.id by lia; lia | rewrite Z_to_nat_neg by lia; lia].
Qed.

Lemma rtu_len_bits_msb (c n: Z) : Zlength (bits_msb c n) = Z.max 0 n.
Proof. unfold bits_msb. rewrite Zlength_rev. apply rtu_len_bits_le. Qed.

Lemma rtu_len_send_sym (l: list Z) (s: Z) : Zlength (send_sym l s) = Z.max 0 (Znth s l).
Proof. unfold send_sym. apply rtu_len_bits_msb. Qed.

Lemma rtu_len_zeros (n: Z) : Zlength (zeros n) = Z.max 0 n.
Proof.
  unfold zeros. rewrite Zlength_correct, repeat_length.
  destruct (Z_le_gt_dec 0 n); [rewrite Z2Nat.id by lia; lia | rewrite Z_to_nat_neg by lia; lia].
Qed.

Lemma rtu_len_flat_const {A B: Type} (f: A -> list B) (n: Z) (l: list A) :
  (forall x, Zlength (f x) = n) -> Zlength (flat_map f l) = n * Zlength l.
Proof.
  intros F. induction l as [|x r IH]; [cbn [flat_map]; rewrite !Zlength_nil; lia|].
  cbn [flat_map]. rewrite Zlength_app, IH, F, Zlength_cons. lia.
Qed.

Lemma rtu_len_bytes_bits (l: list Z) : Zlength (bytes_bits l) = 8 * Zlength l.
Proof. unfold bytes_bits. apply rtu_len_flat_const. intros x. rewrite rtu_len_bits_le. lia. Qed.

Lemma rtu_flat_split {A B: Type} (f: A -> list B) (l: list A) (t: nat) :
  Zlength (flat_map f (firstn t l)) + Zlength (flat_map f (skipn t l)) = Zlength (flat_map f l).
Proof. rewrite <- Zlength_app, flat_map_app, firstn_skipn. reflexivity. Qed.

Lemma rtu_flat_nth {A B: Type} (f: A -> list B) (d: A) : forall (l: list A) (t: nat), (t < length l)%nat ->
  Zlength (f (nth t l d)) <= Zlength (flat_map f (skipn t l)).
Proof.
  induction l as [|x r IH]; intros t H; [cbn in H; lia|].
  destruct t as [|t]; cbn [nth skipn].
  - cbn [flat_map]. rewrite Zlength_app. pose proof (Zlength_nonneg (flat_map f r)). lia.
  - apply IH. cbn in H. lia.
Qed.

Lemma rtu_nat_lt {A: Type} (l: list A) (t: Z) : 0 <= t < Zlength l -> (Z.to_nat t < length l)%nat.
Proof. intros H. rewrite Zlength_correct in H. lia. Qed.

Lemma rtu_enc_stored (p: Z) (f: bool) (bytes: list Z) :
  Zlength (enc_block p f (Stored bytes)) = 3 + pad8 (p + 3) + 32 + 8 * Zlength bytes.
Proof.
  unfold enc_block. rewrite Zlength_cons, !Zlength_app, rtu_len_zeros, !rtu_len_bits_le, rtu_len_bytes_bits.
  change (Zlength [false; false]) with 2.
  assert (0 <= pad8 (p + 3)) by (unfold pad8; apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma rtu_enc_fixed (p: Z) (f: bool) (syms: list sym) :
  Zlength (enc_block p f (Fixed syms)) =
  3 + Zlength (flat_map (send_one fixed_ll fixed_dl) syms) + Zlength (send_sym fixed_ll 256).
Proof.
  unfold enc_block, send_syms. rewrite Zlength_cons, !Zlength_app. change (Zlength [true; false]) with 2. lia.
Qed.

Lemma rtu_enc_dyn (p: Z) (f: bool) nlen ndist clsent toks syms :
  Zlength (enc_block p f (Dynamic nlen ndist clsent toks syms)) =
  17 + 3 * Zlength clsent + Zlength (flat_map (send_tok (cl_lens clsent)) toks) +
  Zlength (flat_map (send_one (dyn_ll nlen toks) (dyn_dl nlen ndist toks)) syms) +
  Zlength (send_sym (dyn_ll nlen toks) 256).
Proof.
  unfold enc_block, send_syms. rewrite Zlength_cons, !Zlength_app, !rtu_len_bits_le.
  rewrite (rtu_len_flat_const (fun c => bits_le c 3) 3) by (intros; rewrite rtu_len_bits_le; lia).
  change (Zlength [false; true]) with 2. lia.
Qed.

Lemma rtu_len_send_ref (ll dl: list Z) (len dist: Z) :
  Zlength (send_one ll dl (Ref len dist)) =
  Z.max 0 (Znth (257 + len_code len) ll) + Z.max 0 (Znth (len_code len) len_extra) +
  Z.max 0 (Znth (dist_code dist) dl) + Z.max 0 (Znth (dist_code dist) dist_extra).
Proof.
  unfold send_one. cbv zeta. rewrite !Zlength_app, !rtu_len_send_sym, !rtu_len_bits_le. lia.
Qed.

Lemma rtu_znth_le (l: list Z) (b i: Z) : Forall (fun x => 0 <= x <= b) l -> 0 <= b -> 0 <= Znth i l <= b.
Proof.
  intros F B. destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - eapply Forall_Znth in F; [exact F | lia].
  - rewrite Znth_outofbounds by lia. unfold Inhabitant_Z. lia.
  - rewrite Znth_outofbounds by lia. unfold Inhabitant_Z. lia.
Qed.

Lemma rtu_len_extra (i: Z) : 0 <= Znth i len_extra <= 5.
Proof. apply rtu_znth_le; [repeat constructor; lia | lia]. Qed.

Lemma rtu_dist_extra (i: Z) : 0 <= Znth i dist_extra <= 13.
Proof. apply rtu_znth_le; [repeat constructor; lia | lia]. Qed.

Lemma rtu_pad8_nonneg (p: Z) : 0 <= pad8 p.
Proof. unfold pad8. apply Z.mod_pos_bound. lia. Qed.

Lemma rtu_pad8_sub (p d: Z) : d mod 8 = 0 -> pad8 (p - d) = pad8 p.
Proof.
  intros H. unfold pad8. f_equal. f_equal. rewrite Zminus_mod, H, Z.sub_0_r, Z.mod_mod by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Positions: every block ends before the end of the deflate stream                               *)

Section Pos.
Variable K : dkit_stmt.

Lemma rtu_bpos_le (G: dctx) : dctx_ok G -> forall k, 0 <= k <= nblk G -> bpos G k <= bpos G (nblk G).
Proof.
  intros C.
  assert (A: forall n k, k = nblk G - Z.of_nat n -> 0 <= k -> bpos G k <= bpos G (nblk G)).
  { induction n as [|n IH]; intros k E H0; [subst k; replace (nblk G - Z.of_nat 0) with (nblk G) by lia; lia|].
    destruct (dk_blk K G k C ltac:(lia)) as [B _].
    specialize (IH (k + 1) ltac:(lia) ltac:(lia)). pose proof (Zlength_nonneg (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k))). lia. }
  intros k Hk. apply (A (Z.to_nat (nblk G - k))); [rewrite Z2Nat.id by lia|]; lia.
Qed.

Lemma rtu_bpos_end (G: dctx) : dctx_ok G -> forall k, 0 <= k <= nblk G -> bpos G k <= endpos G.
Proof.
  intros C k Hk. pose proof (rtu_bpos_le G C k Hk). destruct (dk_end K G C) as [E _].
  pose proof (rtu_pad8_nonneg (bpos G (nblk G))). lia.
Qed.

Lemma rtu_blk_end (G: dctx) (k: Z) : dctx_ok G -> 0 <= k < nblk G ->
  bpos G k + Zlength (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) <= endpos G.
Proof.
  intros C Hk. destruct (dk_blk K G k C Hk) as [B _]. rewrite <- B. apply rtu_bpos_end; [exact C | lia].
Qed.

Lemma rtu_endpos_nonneg (G: dctx) : 0 <= endpos G.
Proof.
  unfold endpos, D0. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). pose proof (Zlength_nonneg (deflate_bits (dc_bs G))). lia.
Qed.

(* a Huffman block: the symbols from j on and the end-of-block code end before endpos *)
Lemma rtu_huff_end (G: dctx) (s: istate) k j ll dl syms p0 : dctx_ok G -> in_huff G s k j ll dl syms p0 ->
  p0 + Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)) + Zlength (send_sym ll 256) <= endpos G.
Proof.
  intros C (IB & BK & J & _ & _ & P0). destruct IB as [Hk _].
  pose proof (rtu_blk_end G k C Hk) as E.
  pose proof (rtu_flat_split (send_one ll dl) syms (Z.to_nat j)) as S. unfold sym_off in P0.
  destruct BK as [(B & -> & ->) | (nlen & ndist & clsent & toks & B & -> & ->)]; rewrite B in E, P0.
  - rewrite rtu_enc_fixed in E. cbn [hb_hdr] in P0. lia.
  - rewrite rtu_enc_dyn in E. cbn [hb_hdr] in P0. lia.
Qed.

Lemma rtu_first_len ll dl syms j : 0 <= j <= Zlength syms ->
  sym_first_len ll syms j <= Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)) + Zlength (send_sym ll 256).
Proof.
  intros J. unfold sym_first_len.
  pose proof (Zlength_nonneg (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms))).
  rewrite (rtu_len_send_sym ll 256).
  destruct (Z.ltb_spec j (Zlength syms)) as [L|L]; [|lia].
  pose proof (rtu_flat_nth (send_one ll dl) (Lit 0) syms (Z.to_nat j) (rtu_nat_lt syms j ltac:(lia))) as N.
  unfold sym_at. destruct (nth (Z.to_nat j) syms (Lit 0)) as [b|len dist].
  - cbn [send_one] in N. rewrite rtu_len_send_sym in N. lia.
  - rewrite rtu_len_send_ref in N. lia.
Qed.

Lemma rtu_sym_le ll dl syms j : 0 <= j < Zlength syms ->
  Zlength (send_one ll dl (sym_at syms j)) <= Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)).
Proof. intros J. apply rtu_flat_nth. apply rtu_nat_lt. exact J. Qed.

End Pos.

Ltac rtu_zl :=
  repeat match goal with
  | H: context [Zlength ?l] |- _ =>
      lazymatch goal with
      | _: 0 <= Zlength l |- _ => fail
      | _ => pose proof (Zlength_nonneg l)
      end
  end.

(* a decoder that has not produced all the data has not consumed the whole zlib stream (the trailer at least
   is left) *)
Lemma rtu_pos (K: dkit_stmt) (G: dctx) (s: istate) (c hold bits: Z) (out: list Z) (fl: Z) :
  dctx_ok G -> dc_w G = WZlib 15 fl None -> at_mode G s c hold bits out -> Zlength out < Zlength (full G) ->
  c < slen G.
Proof.
  intros C W A LT.
  pose proof (dk_slen K G C) as SL. rewrite W in SL. cbn [trl_len] in SL.
  pose proof (rtu_endpos_nonneg G) as E0.
  unfold at_mode in A. cbv zeta in A.
  destruct A as [HO A]. destruct HO as (B0 & _ & _).
  enough (8 * c < endpos G + 32) by lia.
  unfold at_head, at_gzhdr, at_type, at_stored, at_copy, at_table, at_lenlens, at_codelens, at_len, at_lenext,
    at_dist, at_distext, at_match, at_lit, at_check, at_length, at_done in A.
  destruct A as [(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|
                 [(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|(M & H)]]]]]]]]]]]]]]]].
  - (* HEAD *) destruct H as (_ & Q & Bt & _). lia.
  - (* FLAGS, TIME, OS *) destruct H as (h & Wh & _). congruence.
  - (* TYPE *) destruct H as (k & Hk & Q & _ & Bt & _). pose proof (rtu_bpos_end K G C k Hk). lia.
  - (* STORED *) destruct H as (k & bytes & IB & BK & _ & P). destruct IB as [Hk _].
    pose proof (rtu_blk_end K G k C Hk) as E. rewrite BK, rtu_enc_stored in E.
    replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in E by lia.
    rewrite rtu_pad8_sub in E by apply (dk_D0 K).
    pose proof (rtu_pad8_nonneg (bpos G k + 3)). rtu_zl.
    destruct P as [(Q & Bt)|(Q & _ & Bt)]; lia.
  - (* COPY_, COPY *) destruct H as (k & bytes & IB & BK & P). destruct IB as [Hk _].
    pose proof (rtu_blk_end K G k C Hk) as E. rewrite BK, rtu_enc_stored in E.
    replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in E by lia.
    rewrite rtu_pad8_sub in E by apply (dk_D0 K).
    pose proof (rtu_pad8_nonneg (bpos G k + 3)). rtu_zl.
    destruct P as (R & Bt & Q & _). lia.
  - (* TABLE *) destruct H as (k & nlen & ndist & clsent & toks & syms & IB & BK & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (rtu_bpos_end K G C k ltac:(lia)). lia.
  - (* LENLENS *) destruct H as (k & nlen & ndist & clsent & toks & syms & IB & BK & _ & _ & _ & NC & HV & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (rtu_blk_end K G k C Hk) as E. rewrite BK, rtu_enc_dyn in E. rtu_zl. lia.
  - (* CODELENS *) destruct H as (k & nlen & ndist & clsent & toks & syms & t & IB & BK & _ & _ & _ & Ht & _ & _ & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (rtu_blk_end K G k C Hk) as E. rewrite BK, rtu_enc_dyn in E.
    pose proof (rtu_flat_split (send_tok (cl_lens clsent)) toks (Z.to_nat t)) as S. unfold tok_off in Q.
    rtu_zl. destruct Bt as [Bt|(Lt & Bt)]; [lia|].
    pose proof (rtu_flat_nth (send_tok (cl_lens clsent)) (CLen 0) toks (Z.to_nat t) (rtu_nat_lt toks t ltac:(lia))).
    unfold tok_at in Bt. lia.
  - (* LEN_, LEN *) destruct H as (k & j & ll & dl & syms & p0 & IH & _ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_first_len ll dl syms j J). rtu_zl. lia.
  - (* LENEXT *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & _ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, rtu_len_send_ref in SJ.
    rewrite rtu_len_send_sym in Q. pose proof (rtu_len_extra (len_code len)). rtu_zl. lia.
  - (* DIST *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, rtu_len_send_ref in SJ.
    rewrite rtu_len_send_sym in Q. pose proof (rtu_len_extra (len_code len)).
    pose proof (rtu_dist_extra (dist_code dist)). rtu_zl. lia.
  - (* DISTEXT *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & _ & _ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, rtu_len_send_ref in SJ.
    rewrite rtu_len_send_sym in Q. pose proof (rtu_len_extra (len_code len)).
    pose proof (rtu_dist_extra (dist_code dist)). rtu_zl. lia.
  - (* MATCH *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & _ & _ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj in SJ. rtu_zl. lia.
  - (* LIT *) destruct H as (k & j & ll & dl & syms & p0 & b & IH & Jl & Sj & _ & _ & Q & Bt).
    pose proof (rtu_huff_end K G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (rtu_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj in SJ. cbn [send_one] in SJ. rtu_zl. lia.
  - (* CHECK *) destruct H as (_ & _ & Q & _ & Bt & _). lia.
  - (* LENGTH *) destruct H as (_ & _ & _ & _ & _ & (h & Wh)). congruence.
  - (* DONE *) destruct H as (Ho & _). rewrite Ho in LT. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* compress2's stream as a decode context                                                         *)

Lemma rtu_bval_range (l: list bool) : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; [cbn; lia|].
  cbn [bval]. rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma rtu_len_sublist {A: Type} (lo hi: Z) (l: list A) : 0 <= lo <= hi -> Zlength (sublist lo hi l) <= hi - lo.
Proof.
  intros H. unfold sublist. rewrite Zlength_correct, skipn_length, firstn_length. lia.
Qed.

Lemma rtu_bytes_pack (bs: list bool) : bytes_ok (pack bs).
Proof.
  unfold pack, bytes_ok. apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & _).
  set (l := sublist _ _ bs). assert (Zlength l <= 8) by (unfold l; pose proof (rtu_len_sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs ltac:(lia)); lia).
  pose proof (rtu_bval_range l). pose proof (Z.pow_le_mono_r 2 (Zlength l) 8 ltac:(lia) ltac:(lia)).
  change (2 ^ 8) with 256 in *. rep_lia.
Qed.

Lemma rtu_bytes_be (v n: Z) : bytes_ok (be_bytes v n).
Proof.
  unfold be_bytes, le_bytes, bytes_ok. apply Forall_rev. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as (i & <- & _). pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). rep_lia.
Qed.

Definition rtu_G (fl: Z) (bs: list block) (src: list Z) : dctx := DCtx (WZlib 15 fl None) 15 [] bs 15 src.

Lemma rtu_setup (D O: list Z) : RF.dfinal [] 1 15 None D O -> Zlength O <= 2097152 ->
  exists fl bs, dctx_ok (rtu_G fl bs O) /\ full (rtu_G fl bs O) = D /\ slen (rtu_G fl bs O) = Zlength O.
Proof.
  intros (_ & bs & WF & DA & Hw) LO. cbn iota in Hw. destruct Hw as (_ & flg & FO & EO).
  cbn [negb] in FO. destruct (rtu_hdr flg FO) as (HD & FL).
  assert (ES: O = stream_bytes (WZlib 15 (flg / 64) None) [] bs).
  { rewrite EO. unfold stream_bytes. rewrite HD, DA. reflexivity. }
  assert (FD: full (rtu_G (flg / 64) bs O) = D).
  { rewrite <- DA. unfold full, data. cbn [dc_hist dc_bs rtu_G]. rewrite Zlength_nil. rewrite sublist_same; reflexivity. }
  assert (BO: bytes_ok O).
  { rewrite EO. unfold bytes_ok. destruct FO as (F1 & _).
    apply (proj2 (Forall_app _ _ _)); split; [repeat constructor; unfold RF.zcmf; rep_lia|].
    apply (proj2 (Forall_app _ _ _)); split; [constructor|].
    apply (proj2 (Forall_app _ _ _)); split; [apply rtu_bytes_pack | apply rtu_bytes_be]. }
  assert (SL: slen (rtu_G (flg / 64) bs O) = Zlength O) by (unfold slen; cbn [dc_w dc_hist dc_bs rtu_G]; rewrite <- ES; reflexivity).
  exists (flg / 64), bs. split; [|split; [exact FD | exact SL]].
  unfold dctx_ok. cbn [dc_w dc_wb dc_hist dc_bs dc_iw dc_src rtu_G].
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - unfold stream_ok, wrapper_ok. refine (conj _ (conj _ (conj eq_refl WF))); [lia | repeat split; lia].
  - unfold accepts. cbn. left; reflexivity.
  - intros h E; discriminate.
  - intros wb' fl' did E. inversion E. left; reflexivity.
  - rewrite SL. lia.
  - lia.
  - exact BO.
  - rewrite SL, <- ES. apply sublist_same; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* uncompress2_z's loop of inflate() calls, call by call by decode_call_stmt                       *)

(* the stream between two calls: Spec5's (z, L) for the machine m, live, the decoder's invariant *)
Definition rtu_RI (G: dctx) (cap used: Z) (out: list Z) (m: mst) : Prop :=
  exists z L, l_s L = m_s m /\ l_h L = m_h m /\ zf_adler z = m_adler m /\ zf_msg z = m_msg m /\
    zf_tin z = m_tin m /\ zf_tout z = m_tout m /\ live_ok L /\ zf_ok z /\
    dinv G used out (m_s m) (m_tout m) /\ 0 <= used /\ Zlength out <= cap.

Definition rtu_zc (z: zfields) (ai ao: Z) : zfields :=
  ZF nullval ai (zf_tin z) nullval ao (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).

Lemma rtu_next_eq (m: mst) (z: zfields) (L: live) (inp: list Z) (aout: Z) :
  l_s L = m_s m -> l_h L = m_h m -> zf_adler z = m_adler m -> zf_msg z = m_msg m -> zf_tin z = m_tin m ->
  zf_tout z = m_tout m ->
  m_next m inp aout = m_init (rtu_zc z (Zlength inp) aout) L inp.
Proof.
  intros E1 E2 E3 E4 E5 E6. unfold m_next, m_init, rtu_zc. cbn [zf_ao zf_adler zf_msg zf_tin zf_tout].
  rewrite E1, E2, E3, E4, E5, E6. reflexivity.
Qed.

(* the outcome of one call *)
Definition rtu_call_ok (G: dctx) (n cap used: Z) (out: list Z) (res: result) : Prop :=
  r_ret res = Z_MEM_ERROR \/
  ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
   0 <= m_snx (r_m res) <= n - used /\
   (r_ret res <> Z_MEM_ERROR -> rtu_RI G cap (used + m_snx (r_m res)) (out ++ m_ow (r_m res)) (r_m res)) /\
   (r_ret res = Z_STREAM_END -> out ++ m_ow (r_m res) = full G /\ used + m_snx (r_m res) = slen G) /\
   (r_ret res <> Z_STREAM_END ->
      (used + m_snx (r_m res) = n /\ n < slen G) \/
      (Zlength (out ++ m_ow (r_m res)) = cap /\ Zlength (out ++ m_ow (r_m res)) < Zlength (full G)))).

Lemma rtu_step (DC: decode_call_stmt) (G: dctx) (n cap used: Z) (out: list Z) (m: mst) (res: result) :
  dctx_ok G -> 0 <= n <= Zlength (dc_src G) -> 0 <= cap <= 2 ^ 20 -> used <= n ->
  rtu_RI G cap used out m ->
  Zlib.proof.inflate.Model2.run2 0 lenfix_list distfix_list
    (m_next m (sublist used (Zlength (sublist 0 n (dc_src G))) (sublist 0 n (dc_src G))) (cap - Zlength out)) res ->
  rtu_call_ok G n cap used out res.
Proof.
  intros C N CAP UN (z & L & ES & EH & EA & EM & ETI & ETO & LV & ZF & DI & U0 & OC) RUN.
  pose proof C as (_ & _ & _ & _ & _ & CSRC & CB & _).
  rewrite Zlength_sublist in RUN by lia. rewrite Z.sub_0_r in RUN.
  rewrite sublist_sublist in RUN by lia. rewrite !Z.add_0_r in RUN.
  set (inp := sublist used n (dc_src G)) in *.
  assert (LI: Zlength inp = n - used) by (unfold inp; rewrite Zlength_sublist; lia).
  set (aout := cap - Zlength out) in *.
  set (zc := rtu_zc z (Zlength inp) aout).
  rewrite (rtu_next_eq m z L inp aout ES EH EA EM ETI ETO) in RUN. fold zc in RUN.
  assert (ZFc: zf_ok zc).
  { destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zc, rtu_zc, zf_ok. cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
    pose proof (Zlength_nonneg out). repeat split; rep_lia. }
  assert (DI': dinv G used out (l_s L) (zf_tout zc)) by (rewrite ES; unfold zc, rtu_zc; cbn [zf_tout]; rewrite ETO; exact DI).
  assert (IE: inp = sublist used (used + Zlength inp) (dc_src G)) by (rewrite LI; unfold inp; f_equal; lia).
  pose proof (Zlength_nonneg out).
  pose proof (DC G used out L zc inp 0 res C DI' LV ZFc ltac:(unfold zc, rtu_zc; cbn; rep_lia)
                U0 ltac:(lia) IE RUN) as P.
  cbv zeta in P.
  destruct P as [P|(R & SNX & SOW & AOUT & _ & DI2 & _ & SE & NSE & _)]; [left; exact P|right].
  (* the live part and the stream fields after the call (inflate()'s body: UALive.ua_live) *)
  set (ib := InBuf Ews nullval 0 (Zlength inp) []).
  set (o := OutBuf Ews nullval 0 aout []).
  set (strmp := Vptr xH Ptrofs.zero).
  set (L' := Live (l_sp L) (l_winp L) (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
  set (z' := z_after zc ib o res).
  assert (REL: inflate_rel 0 strmp zc (Some L) ib inp (Some o) (r_ret res) z' (Some L') (m_ow (r_m res))).
  { right. split.
    - unfold inflate_bad, is_live. destruct (eq_dec strmp nullval) as [E|_]; [discriminate|].
      intros [B|[B|(B & _)]]; discriminate.
    - exists L, o, res, (l_winp L). split; [reflexivity|]. split; [reflexivity|].
      split; [exact RUN|]. split; [exact SNX|].
      repeat split; auto. }
  assert (BI: bytes_ok inp) by (unfold inp; apply Forall_sublist; exact CB).
  assert (LIVE: r_ret res <> Z_MEM_ERROR -> live_ok L' /\ zf_ok z').
  { intros NM.
    destruct (Zlib.proof.harness.uncompress_any.UALive.ua_live 0 strmp zc L ib inp o (r_ret res) z' (Some L')
                (m_ow (r_m res)) LV ZFc ltac:(discriminate) ltac:(discriminate) ltac:(reflexivity) ltac:(rep_lia) BI
                ltac:(unfold zc, rtu_zc; cbn; rep_lia) REL NM) as (L4 & EL4 & LV' & ZF').
    inversion EL4; subst L4. split; assumption. }
  assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [E|[E|E]]; rewrite E; discriminate).
  destruct (LIVE NM) as (LV' & ZF').
  assert (OW: Zlength (m_ow (r_m res)) <= aout).
  { destruct ZF' as (_ & (Z2 & _) & _). unfold z', z_after in Z2. cbn [zf_ao] in Z2.
    rewrite AOUT in Z2. unfold zc, rtu_zc in Z2. cbn [zf_ao] in Z2. lia. }
  split; [exact R|]. split; [lia|]. split.
  { intros _. exists z', L'. unfold z', z_after, L'. cbn [l_s l_h zf_adler zf_msg zf_tin zf_tout].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact LV'|]. split; [exact ZF'|]. split; [exact DI2|]. split; [lia|].
    rewrite Zlength_app. unfold aout in OW. lia. }
  split; [exact SE|].
  intros NE. destruct (NSE NE) as [(A & B)|[(A & B)|[F|F]]].
  - left. split; lia.
  - right. split; [|exact B]. rewrite Zlength_app, A. unfold zc, rtu_zc. cbn [zf_ao]. unfold aout. lia.
  - discriminate.
  - discriminate.
Qed.

Lemma rtu_loop (DC: decode_call_stmt) (K: dkit_stmt) (G: dctx) (fl n cap: Z) :
  dctx_ok G -> dc_w G = WZlib 15 fl None -> 0 <= n <= Zlength (dc_src G) -> 0 <= cap <= 2 ^ 20 ->
  forall m used out err used' out',
  unc_loop (sublist 0 n (dc_src G)) cap m used out err used' out' -> used <= n -> rtu_RI G cap used out m ->
  err = Z_MEM_ERROR \/
  ((err = Z_BUF_ERROR \/ err = Z_STREAM_END) /\ 0 <= used' <= n /\ Zlength out' <= cap /\
   (err = Z_STREAM_END -> out' = full G /\ used' = slen G) /\
   (err = Z_BUF_ERROR -> (used' = n /\ n < slen G) \/
                         (Zlength out' = cap /\ Zlength out' < Zlength (full G) /\ used' < slen G))).
Proof.
  intros C W N CAP m used out err used' out' U.
  induction U as [m used out res RUN NOK | m used out res err used' out' RUN OK U IH]; intros UN RI.
  - destruct (rtu_step DC G n cap used out m res C N CAP UN RI RUN) as [M|(R & SNX & RI' & SE & NSE)];
      [left; exact M|right].
    assert (NM: r_ret res <> Z_MEM_ERROR) by (destruct R as [E|[E|E]]; rewrite E; discriminate).
    destruct (RI' NM) as (z' & L' & _ & _ & _ & _ & _ & _ & _ & _ & DI & U0 & OC).
    split; [destruct R as [E|[E|E]]; [contradiction | left | right]; exact E|].
    split; [lia|]. split; [exact OC|]. split; [exact SE|].
    intros EB. assert (NE: r_ret res <> Z_STREAM_END) by (rewrite EB; discriminate).
    destruct (NSE NE) as [A|(A & B)]; [left; exact A|right].
    split; [exact A|]. split; [exact B|].
    exact (rtu_pos K G _ _ _ _ _ fl C W (proj1 DI) B).
  - destruct (rtu_step DC G n cap used out m res C N CAP UN RI RUN) as [M|(R & SNX & RI' & SE & NSE)].
    + rewrite OK in M. discriminate.
    + apply IH; [lia|]. apply RI'. rewrite OK. discriminate.
Qed.

(* the stream after inflateInit_ (as UATheory.ua_init_live_ok) *)
Lemma rtu_init_live_ok (sp: val) : isptr sp -> live_ok (init_live sp 15).
Proof.
  intros Hsp.
  unfold live_ok, init_live. simpl l_sp; simpl l_s; simpl l_h; simpl l_hsh.
  assert (Hl: Forall (fun x => 0 <= x <= 65535) (Zrepeat 0 320)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  assert (Hc: Forall entry_ok (Zrepeat (mkE 0 0 0) ENOUGH_CODES)).
  { apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. cbv; repeat split; congruence. }
  (* windowBits 15: reset2_wrap leaves the wrap as it is (bit 3 only for windowBits 0), and inflateReset's
     extra step of patch F8 does nothing *)
  unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap, reset_s, reset_keep_s, zero_s. simpl.
  split; [exact Hsp | ]. split; [ | split; [ | split; [ | split; [ | split]]]].
  - constructor; simpl; unfold urange, srange, lrange, tref_ok, ENOUGH_CODES, HEAD, SYNC in *; try rep_lia.
    all: try (split; [reflexivity | auto]).
    all: try (left; reflexivity).
    all: try lia.
    all: try (intros; lia).
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
  - constructor; simpl; unfold urange, srange, lrange; try rep_lia; try (split; [reflexivity | constructor]).
  - constructor; simpl; intros; try discriminate; unfold decode_mode in *; unfold HEAD, LENLENS, CODELENS,
      LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; try lia; auto.
  - apply writable_Ews.
  - simpl. split; [intros H0; discriminate | ].
    split; [discriminate | ].
    intros; discriminate.
Qed.

Lemma rtu_RI_first (DI: decode_init_stmt) (fl: Z) (bs: list block) (src: list Z) (cap: Z) :
  dctx_ok (rtu_G fl bs src) -> 0 <= cap -> rtu_RI (rtu_G fl bs src) cap 0 [] m_first.
Proof.
  intros C CAP.
  set (sp := Vptr xH Ptrofs.zero).
  pose proof (DI (rtu_G fl bs src) sp C eq_refl ltac:(intros wb' fl' did E; inversion E; reflexivity)) as D0.
  exists (ZF nullval 0 0 nullval 0 0 None 0 1 nullval), (init_live sp 15).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [apply rtu_init_live_ok; exact I|].
  split; [unfold zf_ok; cbn; rep_lia|].
  split; [exact D0|]. split; [lia|]. rewrite Zlength_nil. lia.
Qed.

Lemma rtu_unc_mem (rest: Z) : unc_ret Z_MEM_ERROR rest = Z_MEM_ERROR.
Proof. reflexivity. Qed.

Lemma rtu_unc_end (rest: Z) : unc_ret Z_STREAM_END rest = Z_OK.
Proof. reflexivity. Qed.

Lemma rtu_unc_buf (rest: Z) : rest <> 0 -> unc_ret Z_BUF_ERROR rest = Z_BUF_ERROR.
Proof. intros H. unfold unc_ret. rewrite (proj2 (Z.eqb_neq rest 0) H). reflexivity. Qed.

Lemma rtu_unc_buf' (rest: Z) : unc_ret Z_BUF_ERROR rest = Z_DATA_ERROR \/ unc_ret Z_BUF_ERROR rest = Z_BUF_ERROR.
Proof. unfold unc_ret. destruct (rest =? 0); cbn; auto. Qed.

(* the loop on a prefix of length n of compress2's stream O, with cap bytes of space *)
Lemma rtu_run (P: decode_parts) (D O: list Z) (n cap slen0: Z) (err: Z) (out: list Z) :
  RF.dfinal [] 1 15 None D O -> Zlength O <= 2097152 -> 0 <= n <= Zlength O -> 0 <= cap <= 2 ^ 20 ->
  unc_loop (sublist 0 n O) cap m_first 0 [] err slen0 out ->
  err = Z_MEM_ERROR \/
  ((err = Z_BUF_ERROR \/ err = Z_STREAM_END) /\ 0 <= slen0 <= n /\ Zlength out <= cap /\
   (err = Z_STREAM_END -> out = D /\ slen0 = Zlength O) /\
   (err = Z_BUF_ERROR -> (slen0 = n /\ n < Zlength O) \/
                         (Zlength out = cap /\ Zlength out < Zlength D /\ slen0 < Zlength O))).
Proof.
  intros F LO N CAP UL.
  destruct (decode_of_parts P) as (DI & DC). pose proof (proj1 P) as K.
  destruct (rtu_setup D O F LO) as (fl & bs & C & FD & SL).
  rewrite <- FD, <- SL.
  exact (rtu_loop DC K (rtu_G fl bs O) fl n cap C eq_refl ltac:(cbn [dc_src rtu_G]; lia) CAP _ _ _ _ _ _ UL
           ltac:(lia) (rtu_RI_first DI fl bs O cap C ltac:(lia))).
Qed.

Theorem rt_ufacts : Zlib.proof.rfc1951.Decode.decode_parts -> ufacts.
Proof.
  intros P. constructor.
  - (* uf_full *)
    intros D O r slen0 dlen out F LD LO REL.
    destruct REL as [(-> & _)|(err & UL & -> & ->)]; [left; reflexivity|].
    rewrite <- (sublist_same 0 (Zlength O) O) in UL by reflexivity.
    destruct (rtu_run P D O (Zlength O) (Zlength D) slen0 err out F LO ltac:(pose proof (Zlength_nonneg O); lia)
                ltac:(pose proof (Zlength_nonneg D); lia) UL) as [->|(E & U1 & OC & SE & BE)];
      [left; apply rtu_unc_mem|].
    destruct E as [E|E].
    + exfalso. destruct (BE E) as [(A & B)|(A & B & _)]; lia.
    + right. destruct (SE E) as (A & B). subst err out slen0.
      split; [apply rtu_unc_end|]. auto.
  - (* uf_short *)
    intros D O r slen0 dlen out F LD LO REL.
    destruct REL as [(-> & _)|(err & UL & -> & ->)]; [left; reflexivity|].
    rewrite <- (sublist_same 0 (Zlength O) O) in UL by reflexivity.
    destruct (rtu_run P D O (Zlength O) (Zlength D - 1) slen0 err out F LO ltac:(pose proof (Zlength_nonneg O); lia)
                ltac:(lia) UL) as [->|(E & U1 & OC & SE & BE)];
      [left; apply rtu_unc_mem|].
    destruct E as [E|E].
    + right. subst err. split; [|lia].
      destruct (BE eq_refl) as [(A & B)|(A & B & C)]; [lia|].
      apply rtu_unc_buf. lia.
    + exfalso. destruct (SE E) as (A & B). subst out. lia.
  - (* uf_prefix *)
    intros D O k r slen0 dlen out F LD LO K REL.
    destruct REL as [(-> & _)|(err & UL & -> & ->)]; [left; reflexivity|].
    destruct (rtu_run P D O k (Zlength D) slen0 err out F LO ltac:(lia)
                ltac:(pose proof (Zlength_nonneg D); lia) UL) as [->|(E & U1 & OC & SE & BE)];
      [left; apply rtu_unc_mem|].
    destruct E as [E|E].
    + subst err. right. apply rtu_unc_buf'.
    + exfalso. destruct (SE E) as (A & B). lia.
Qed.

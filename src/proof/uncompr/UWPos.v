(* A decoder of a zlib stream that has not produced all of the data has not consumed the whole stream: the
   Adler-32 trailer at least is left.  Round 1's RTUTheory.rtu_pos for inputs of any length (Decode7.dctx_ok7;
   the stream's layout from the wide port's kit, wide/rfc1951/DecKit.v dkit_wide).  uncompress2's model uses it
   to show that a call that stops with the output space full leaves input unread. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Zlib.proof.roundtrip.RTUTheory.
Require Import Zlib.proof.wide.rfc1951.DecodeDefs.
Require Import Zlib.proof.wide.rfc1951.DecKit.
Require Import Zlib.proof.wide.Decode7.
Import ListNotations.
Local Open Scope Z_scope.

Module RT := Zlib.proof.roundtrip.RTUTheory.

(* Positions in the stream (RTUTheory's Section Pos over the wide kit): every block, and every symbol of a
   Huffman block with its end-of-block code, ends before the end of the deflate data (endpos). *)

Lemma uwp_bpos_le (G: dctx) : dctx_ok_wide G -> forall k, 0 <= k <= nblk G -> bpos G k <= bpos G (nblk G).
Proof.
  intros C.
  assert (A: forall n k, k = nblk G - Z.of_nat n -> 0 <= k -> bpos G k <= bpos G (nblk G)).
  { induction n as [|n IH]; intros k E H0; [subst k; replace (nblk G - Z.of_nat 0) with (nblk G) by lia; lia|].
    destruct (dk_blk_wide dkit_wide G k C ltac:(lia)) as [B _].
    specialize (IH (k + 1) ltac:(lia) ltac:(lia)). pose proof (Zlength_nonneg (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k))). lia. }
  intros k Hk. apply (A (Z.to_nat (nblk G - k))); [rewrite Z2Nat.id by lia|]; lia.
Qed.

Lemma uwp_bpos_end (G: dctx) : dctx_ok_wide G -> forall k, 0 <= k <= nblk G -> bpos G k <= endpos G.
Proof.
  intros C k Hk. pose proof (uwp_bpos_le G C k Hk). destruct (dk_end_wide dkit_wide G C) as [E _].
  pose proof (RT.rtu_pad8_nonneg (bpos G (nblk G))). lia.
Qed.

Lemma uwp_blk_end (G: dctx) (k: Z) : dctx_ok_wide G -> 0 <= k < nblk G ->
  bpos G k + Zlength (enc_block (bpos G k - D0 G) (lastflag G k =? 1) (blk G k)) <= endpos G.
Proof.
  intros C Hk. destruct (dk_blk_wide dkit_wide G k C Hk) as [B _]. rewrite <- B. apply uwp_bpos_end; [exact C | lia].
Qed.

Lemma uwp_endpos_nonneg (G: dctx) : 0 <= endpos G.
Proof.
  unfold endpos, D0. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). pose proof (Zlength_nonneg (deflate_bits (dc_bs G))). lia.
Qed.

(* a Huffman block: the symbols from j on and the end-of-block code end before endpos *)
Lemma uwp_huff_end (G: dctx) (s: istate) k j ll dl syms p0 : dctx_ok_wide G -> in_huff G s k j ll dl syms p0 ->
  p0 + Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)) + Zlength (send_sym ll 256) <= endpos G.
Proof.
  intros C (IB & BK & J & _ & _ & P0). destruct IB as [Hk _].
  pose proof (uwp_blk_end G k C Hk) as E.
  pose proof (RT.rtu_flat_split (send_one ll dl) syms (Z.to_nat j)) as S. unfold sym_off in P0.
  destruct BK as [(B & -> & ->) | (nlen & ndist & clsent & toks & B & -> & ->)]; rewrite B in E, P0.
  - rewrite RT.rtu_enc_fixed in E. cbn [hb_hdr] in P0. lia.
  - rewrite RT.rtu_enc_dyn in E. cbn [hb_hdr] in P0. lia.
Qed.

Lemma uwp_first_len ll dl syms j : 0 <= j <= Zlength syms ->
  sym_first_len ll syms j <= Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)) + Zlength (send_sym ll 256).
Proof.
  intros J. unfold sym_first_len.
  pose proof (Zlength_nonneg (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms))).
  rewrite (RT.rtu_len_send_sym ll 256).
  destruct (Z.ltb_spec j (Zlength syms)) as [L|L]; [|lia].
  pose proof (RT.rtu_flat_nth (send_one ll dl) (Lit 0) syms (Z.to_nat j) (RT.rtu_nat_lt syms j ltac:(lia))) as N.
  unfold sym_at. destruct (nth (Z.to_nat j) syms (Lit 0)) as [b|len dist].
  - cbn [send_one] in N. rewrite RT.rtu_len_send_sym in N. lia.
  - rewrite RT.rtu_len_send_ref in N. lia.
Qed.

Lemma uwp_sym_le ll dl syms j : 0 <= j < Zlength syms ->
  Zlength (send_one ll dl (sym_at syms j)) <= Zlength (flat_map (send_one ll dl) (skipn (Z.to_nat j) syms)).
Proof. intros J. apply RT.rtu_flat_nth. apply RT.rtu_nat_lt. exact J. Qed.


Ltac uwp_zl :=
  repeat match goal with
  | H: context [Zlength ?l] |- _ =>
      lazymatch goal with
      | _: 0 <= Zlength l |- _ => fail
      | _ => pose proof (Zlength_nonneg l)
      end
  end.

Lemma uw_pos (G: dctx) (s: istate) (c hold bits: Z) (out: list Z) (wb fl: Z) (did: option Z) :
  dctx_ok7 G -> dc_w G = WZlib wb fl did -> at_mode G s c hold bits out -> Zlength out < Zlength (full G) ->
  c < slen G.
Proof.
  intros C7 W A LT. pose proof (dctx_ok7_wide G C7) as C. clear C7.
  pose proof (dk_slen_wide dkit_wide G C) as SL. rewrite W in SL. cbn [trl_len] in SL.
  pose proof (uwp_endpos_nonneg G) as E0.
  unfold at_mode in A. cbv zeta in A.
  destruct A as [HO A]. destruct HO as (B0 & _ & _).
  enough (8 * c < endpos G + 32) by lia.
  unfold at_head, at_gzhdr, at_type, at_stored, at_copy, at_table, at_lenlens, at_codelens, at_len, at_lenext,
    at_dist, at_distext, at_match, at_lit, at_check, at_length, at_done in A.
  destruct A as [(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|
                 [(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|[(M & H)|(M & H)]]]]]]]]]]]]]]]].
  - (* HEAD *) destruct H as (_ & Q & Bt & _). lia.
  - (* FLAGS, TIME, OS *) destruct H as (h & Wh & _). congruence.
  - (* TYPE *) destruct H as (k & Hk & Q & _ & Bt & _). pose proof (uwp_bpos_end G C k Hk). lia.
  - (* STORED *) destruct H as (k & bytes & IB & BK & _ & P). destruct IB as [Hk _].
    pose proof (uwp_blk_end G k C Hk) as E. rewrite BK, RT.rtu_enc_stored in E.
    replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in E by lia.
    rewrite RT.rtu_pad8_sub in E by apply (dk_D0_wide dkit_wide).
    pose proof (RT.rtu_pad8_nonneg (bpos G k + 3)). uwp_zl.
    destruct P as [(Q & Bt)|(Q & _ & Bt)]; lia.
  - (* COPY_, COPY *) destruct H as (k & bytes & IB & BK & P). destruct IB as [Hk _].
    pose proof (uwp_blk_end G k C Hk) as E. rewrite BK, RT.rtu_enc_stored in E.
    replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in E by lia.
    rewrite RT.rtu_pad8_sub in E by apply (dk_D0_wide dkit_wide).
    pose proof (RT.rtu_pad8_nonneg (bpos G k + 3)). uwp_zl.
    destruct P as (R & Bt & Q & _). lia.
  - (* TABLE *) destruct H as (k & nlen & ndist & clsent & toks & syms & IB & BK & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (uwp_bpos_end G C k ltac:(lia)). lia.
  - (* LENLENS *) destruct H as (k & nlen & ndist & clsent & toks & syms & IB & BK & _ & _ & _ & NC & HV & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (uwp_blk_end G k C Hk) as E. rewrite BK, RT.rtu_enc_dyn in E. uwp_zl. lia.
  - (* CODELENS *) destruct H as (k & nlen & ndist & clsent & toks & syms & t & IB & BK & _ & _ & _ & Ht & _ & _ & _ & Q & Bt).
    destruct IB as [Hk _]. pose proof (uwp_blk_end G k C Hk) as E. rewrite BK, RT.rtu_enc_dyn in E.
    pose proof (RT.rtu_flat_split (send_tok (cl_lens clsent)) toks (Z.to_nat t)) as S. unfold tok_off in Q.
    uwp_zl. destruct Bt as [Bt|(Lt & Bt)]; [lia|].
    pose proof (RT.rtu_flat_nth (send_tok (cl_lens clsent)) (CLen 0) toks (Z.to_nat t) (RT.rtu_nat_lt toks t ltac:(lia))).
    unfold tok_at in Bt. lia.
  - (* LEN_, LEN *) destruct H as (k & j & ll & dl & syms & p0 & IH & _ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_first_len ll dl syms j J). uwp_zl. lia.
  - (* LENEXT *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & _ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, RT.rtu_len_send_ref in SJ.
    rewrite RT.rtu_len_send_sym in Q. pose proof (RT.rtu_len_extra (len_code len)). uwp_zl. lia.
  - (* DIST *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, RT.rtu_len_send_ref in SJ.
    rewrite RT.rtu_len_send_sym in Q. pose proof (RT.rtu_len_extra (len_code len)).
    pose proof (RT.rtu_dist_extra (dist_code dist)). uwp_zl. lia.
  - (* DISTEXT *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & H). cbv zeta in H.
    destruct H as (_ & _ & _ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj, RT.rtu_len_send_ref in SJ.
    rewrite RT.rtu_len_send_sym in Q. pose proof (RT.rtu_len_extra (len_code len)).
    pose proof (RT.rtu_dist_extra (dist_code dist)). uwp_zl. lia.
  - (* MATCH *) destruct H as (k & j & ll & dl & syms & p0 & len & dist & IH & Jl & Sj & _ & _ & _ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj in SJ. uwp_zl. lia.
  - (* LIT *) destruct H as (k & j & ll & dl & syms & p0 & b & IH & Jl & Sj & _ & _ & Q & Bt).
    pose proof (uwp_huff_end G s k j ll dl syms p0 C IH) as E.
    destruct IH as (_ & _ & J & _).
    pose proof (uwp_sym_le ll dl syms j ltac:(lia)) as SJ. rewrite Sj in SJ. cbn [send_one] in SJ. uwp_zl. lia.
  - (* CHECK *) destruct H as (_ & _ & Q & _ & Bt & _). lia.
  - (* LENGTH *) destruct H as (_ & _ & _ & _ & _ & (h & Wh)). congruence.
  - (* DONE *) destruct H as (Ho & _). rewrite Ho in LT. lia.
Qed.

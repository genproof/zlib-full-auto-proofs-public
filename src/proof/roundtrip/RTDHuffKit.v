(* RT-D part HUFF: kit for the functional proof of deflate_huff.
   The safety proof is RTDLTCHuff*.v (copied Qed theory); the functional proof follows its structure:
   - [hk3]: the functional facts of [kcore] at a huff state, without [wtrees] (a full sym_buf after the
     literal step breaks the L - 2 bound of [wtrees]) and without the trivial parts (kmatch: match_available
     is 0; khash: chain_hok, the insert part is for fast/slow only);
   - the parts: [hflit_stmt] (the literal step [hlit]), [hfflush_stmt] (FLUSH_BLOCK_ONLY on an [HS0] state),
     [hfrefill_stmt] (fill_window);
   - the assembly (loop, tail) is in RTDHuff.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix.
Require Export Zlib.proof.roundtrip.RTDLTCHuffKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The functional facts of a huff state *)
Definition hk3 (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s) H /\
  chain_hok s.

(** ** The part statements *)

(* the literal step: one more literal symbol, the byte at strstart *)
Definition hflit_stmt : Prop :=
  forall s syms dict D BS,
    W s -> huff_extra s -> outok s -> quiet s -> fn_of s = 3 -> 1 <= d_lookahead s ->
    wtrees s syms -> hk3 dict D BS syms s ->
    exists s3 bf c,
      hlit s = Some (s3, bf) /\ HS0 s3 (syms ++ [(0, c)]) /\
      bf = (Zlength (syms ++ [(0, c)]) =? d_L s3 - 1) /\ hfr s s3 /\
      d_lookahead s3 = d_lookahead s - 1 /\
      hk3 dict D BS (syms ++ [(0, c)]) s3 /\ bibits s3 = bibits s.

(* FLUSH_BLOCK_ONLY(s, last) at a huff state with the symbols syms: one more block, no symbols left *)
Definition hfflush_stmt : Prop :=
  forall s z syms last s' z' dict D BS p,
    HS0 s syms -> zall z -> 0 <= last <= 1 ->
    hk3 dict D BS syms s -> 0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_flush_block_only s z last = Some (s', z') ->
    exists x blk,
      zout_only z z' x /\ wtrees s' [] /\ hk3 dict D (BS ++ [blk]) [] s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p [blk] (last =? 1).

(* fill_window: the bytes read extend the history *)
Definition hfrefill_stmt : Prop :=
  forall s z s' z' syms dict D BS,
    W s -> fn_of s = 3 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    wtrees s syms -> hk3 dict D BS syms s -> c_fill_window s z = Some (s', z') ->
    exists k,
      zstep (d_wrap s) z z' k [] /\ wtrees s' syms /\
      hk3 dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) BS syms s' /\
      bibits s' = bibits s /\ pend s' = pend s.

(** ** Small lemmas *)

(* [W_HS0] for given symbols *)
Lemma W_HS0_syms s syms : W s -> wtrees s syms -> huff_extra s -> outok s -> quiet s -> fn_of s = 3 ->
  HS0 s syms /\ Zlength syms <= d_L s - 2.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & _) Ht He Ho Hq Hfn.
  assert (Hlev := fn_of_huff s Hp Hfn).
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  destruct Ht as (Ht & HL & Hf & Hz & Hb).
  split; [|exact HL].
  specialize (He Hfn). destruct Ht as (T1 & T2 & T3 & Trest). unfold d_sym_next in He. rewrite T3 in He.
  unfold HS0. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [exact (conj T1 (conj T2 (conj T3 Trest)))|].
  split; [lia|]. split; [exact Hf|].
  split; [rewrite Hb by lia; rewrite Ha; lia|]. split; [lia|]. split; [exact Ho|]. split; [exact Hq|].
  exact Hfn.
Qed.

(* [kcore] at a huff state is [wtrees] + [hk3] *)
Lemma kcore_hk3 dict D BS syms s : W s -> fn_of s = 3 ->
  (kcore dict D BS syms s <-> wtrees s syms /\ hk3 dict D BS syms s).
Proof.
  intros HW Hfn.
  pose proof HW as (Hp & _ & _ & _ & _ & Hm & _).
  destruct (fn_of_huff s Hp Hfn) as [Hlev _].
  assert (Ha : d_match_available s = 0).
  { destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia. }
  unfold kcore, kdata, khash, hk3. cbv zeta.
  rewrite (proj2 (Z.eqb_neq _ _) Hlev), Ha, Z.sub_0_r, Hfn.
  split.
  - intros ((A1 & A2 & A3 & A4 & A5 & A6 & A7) & B1 & B2).
    split; [exact A3|]. exact (conj A1 (conj A4 (conj A5 (conj A6 (conj A7 B1))))).
  - intros (A3 & A1 & A4 & A5 & A6 & A7 & B1).
    split; [|split; [exact B1|intros [E|E]; discriminate E]].
    split; [exact A1|]. split; [intros E; rewrite Ha in E; discriminate E|].
    exact (conj A3 (conj A4 (conj A5 (conj A6 A7)))).
Qed.

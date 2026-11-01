(** * RT-D part RLE: the kit of the functional proof of deflate_rle.

    The proof follows the safety proof of the deflate laws (RTDLTCRleKit.v / RTDLTCRleGlue.v, Qed): the same
    pieces (refill, scan, literal, run, bflush, tail), each with a functional statement [rf*_stmt] below (one
    file each), and the glue (RTDRle.v) composing them along the main loop.

    - [rkt dict D BS syms s]: [kcore] without the trees part (after a tally, sym_buf may be full: RTS of the
      safety kit), with match_available = 0 and the trivial parts dropped (kmatch; khash = chain_hok since
      deflate_rle never inserts).
    - the pieces only state the functional facts; the safety facts (RTS, FI, ...) come from the Qed safety
      parts by determinism (the model run is given). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix.
Require Export Zlib.proof.roundtrip.RTDLTCRleGlue.
Require Export Zlib.proof.roundtrip.RTDLTCRleRefill Zlib.proof.roundtrip.RTDLTCRleScan Zlib.proof.roundtrip.RTDLTCRleLit Zlib.proof.roundtrip.RTDLTCRleDist Zlib.proof.roundtrip.RTDLTCRleFbw Zlib.proof.roundtrip.RTDLTCRleBflush Zlib.proof.roundtrip.RTDLTCRleTail.
Require Export Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCFlushKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The functional invariant of an rle state (no trees part) *)
Definition rkt (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s) H /\
  chain_hok s.

(** the state and stream of a loop piece's result *)
Definition rst (r : (dstate * strm) + dexit) : dstate * strm :=
  match r with inl a => a | inr (s, z, _) => (s, z) end.

(** ** The part statements *)

(** The top of the loop: c_refill need_rle (fill_window when lookahead <= MAX_MATCH).  The bytes read extend
    the history; nothing is output; the trees part is untouched. *)
Definition rfrefill_stmt : Prop :=
  forall s z flush r dict D BS syms,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
    wtrees s syms -> rkt dict D BS syms s ->
    c_refill need_rle flush s z = Some r ->
    exists k,
      zstep (d_wrap s) z (snd (rst r)) k [] /\ wtrees (fst (rst r)) syms /\
      rkt dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) BS syms (fst (rst r)) /\
      pend (fst (rst r)) = pend s /\ bibits (fst (rst r)) = bibits s.

(** The run scan: a run (match_length >= MIN_MATCH) repeats the byte at strstart - 1. *)
Definition rfscan_stmt : Prop :=
  forall s s2,
    W s -> fn_of s = 4 -> rready s -> 1 <= d_lookahead s -> rscan s = Some s2 ->
    MIN_MATCH <= d_match_length s2 ->
    forall i, 0 <= i < d_match_length s2 ->
      Znth (d_strstart s + i) (mb_val (d_window s)) = Znth (d_strstart s - 1) (mb_val (d_window s)).

(** The literal branch: the literal window[strstart] is tallied. *)
Definition rflit_stmt : Prop :=
  forall s ml s3 bf dict D BS syms,
    W s -> outok s -> quiet s -> fn_of s = 4 -> rready s -> 1 <= d_lookahead s -> 0 <= ml < MIN_MATCH ->
    Forall F.byte_ok dict -> bytes D -> wtrees s syms -> rkt dict D BS syms s ->
    flit (set_d_match_length s ml) = Some (s3, bf) ->
    exists syms3, RTS s3 syms3 bf /\ rkt dict D BS syms3 s3 /\ bibits s3 = bibits s /\ pend s3 = pend s.

(** The run branch: the match of length ml at distance 1 is tallied. *)
Definition rfdist_stmt : Prop :=
  forall s ml s3 bf dict D BS syms,
    W s -> outok s -> quiet s -> fn_of s = 4 -> rready s ->
    MIN_MATCH <= ml <= MAX_MATCH -> ml <= d_lookahead s -> 1 <= d_strstart s ->
    (forall i, 0 <= i < ml ->
       Znth (d_strstart s + i) (mb_val (d_window s)) = Znth (d_strstart s - 1) (mb_val (d_window s))) ->
    Forall F.byte_ok dict -> bytes D -> wtrees s syms -> rkt dict D BS syms s ->
    rdist (set_d_match_length s ml) = Some (s3, bf) ->
    exists syms3, RTS s3 syms3 bf /\ rkt dict D BS syms3 s3 /\ bibits s3 = bibits s /\ pend s3 = pend s.

(** FLUSH_BLOCK_ONLY(s, last) at an rle state with the symbols syms: one more block, no symbols left. *)
Definition rffbo_stmt : Prop :=
  forall s z syms last s' z' dict D BS p,
    RTS0 s syms -> zall z -> 0 <= last <= 1 ->
    Forall F.byte_ok dict -> bytes D -> rkt dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_flush_block_only s z last = Some (s', z') ->
    exists x blk,
      zout_only z z' x /\ wtrees s' [] /\ rkt dict D (BS ++ [blk]) [] s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p [blk] (last =? 1).

(** [if (bflush) FLUSH_BLOCK(s, 0)]: at most one block, its bits appended. *)
Definition rfbflush_stmt : Prop :=
  forall s z flush syms bf r dict D BS p,
    RTS s syms bf -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 ->
    Forall F.byte_ok dict -> bytes D -> rkt dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_bflush s z bf = Some r ->
    exists x BS' syms',
      zstep (d_wrap s) z (snd (rst r)) 0 x /\
      wtrees (fst (rst r)) syms' /\ rkt dict D (BS ++ BS') syms' (fst (rst r)) /\
      F.bytes_bits (x ++ pend (fst (rst r))) ++ bibits (fst (rst r)) = bibits s ++ enc_from p BS' false.

(** deflate_tail after the loop: FLUSH_BLOCK(s, 1) on Z_FINISH (the final block), else the last symbols. *)
Definition rftail_stmt : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 ->
    0 <= flush <= 5 -> flush <> Z_NO_FLUSH ->
    d_lookahead s = 0 -> z_avail_in z = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
    Forall F.byte_ok dict -> bytes D -> wtrees s syms -> rkt dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_deflate_tail (set_d_insert s 0) z flush = Some (s', z', bs) ->
    exists x BS' syms',
      zstep (d_wrap s) z z' 0 x /\
      wtrees s' syms' /\ rkt dict D (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> []).

(** ** Helper lemmas (Qed) *)

(** the symbols in sym_buf determine the symbol list *)
Lemma rk_sym_bytes_inj : forall l1 l2, Zlength l1 = Zlength l2 -> sym_bytes l1 = sym_bytes l2 -> l1 = l2.
Proof.
  induction l1 as [|[a b] l1 IH]; intros [|[c d] l2] L E.
  - reflexivity.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg l2). lia.
  - rewrite Zlength_nil, Zlength_cons in L. pose proof (Zlength_nonneg l1). lia.
  - rewrite !sym_bytes_cons in E. cbn [fst snd] in E. injection E as E1 E2 E3 E4.
    rewrite !Zlength_cons in L.
    rewrite (IH l2) by (auto; lia).
    assert (a = c).
    { change (a / 256 = c / 256) in E2. rewrite (Z_div_mod_eq_full a 256), (Z_div_mod_eq_full c 256), E1, E2. reflexivity. }
    subst. reflexivity.
Qed.

Lemma rk_tree_ok_uniq t m s1 s2 : tree_ok t m s1 -> tree_ok t m s2 -> s1 = s2.
Proof.
  intros (_ & _ & N1 & _ & B1 & _) (_ & _ & N2 & _ & B2 & _).
  assert (L : Zlength s1 = Zlength s2) by lia.
  apply rk_sym_bytes_inj; [exact L|]. rewrite <- B1, <- B2, L. reflexivity.
Qed.

Lemma rk_wtrees_uniq s s1 s2 : wtrees s s1 -> wtrees s s2 -> s1 = s2.
Proof. intros (T1 & _) (T2 & _). exact (rk_tree_ok_uniq _ _ _ _ T1 T2). Qed.

Lemma rk_RTS_uniq s s1 s2 bf : RTS s s1 bf -> wtrees s s2 -> s1 = s2.
Proof. intros ((_ & _ & _ & _ & _ & _ & T1 & _) & _) (T2 & _). exact (rk_tree_ok_uniq _ _ _ _ T1 T2). Qed.

(** kcore = rkt + wtrees at an rle state *)
Lemma rk_kcore_rkt dict D BS syms s :
  W s -> fn_of s = 4 -> (kcore dict D BS syms s <-> rkt dict D BS syms s /\ wtrees s syms).
Proof.
  intros HW Hfn.
  pose proof HW as (Hp & _ & _ & _ & _ & Hm & _).
  destruct (fn_of_rle s Hp Hfn) as [Hlev _].
  pose proof (wmatch_avail0 s Hm Hfn) as Ha.
  unfold kcore, kdata, khash, rkt. cbv zeta.
  replace (d_level s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite Ha, Z.sub_0_r, Hfn.
  split.
  - intros ((A1 & A2 & A3 & A4 & A5 & A6 & A7) & B1 & B2).
    split; [|exact A3]. exact (conj A1 (conj A4 (conj A5 (conj A6 (conj A7 B1))))).
  - intros ((A1 & A4 & A5 & A6 & A7 & B1) & A3).
    split; [|split; [exact B1|intros [E|E]; discriminate E]].
    split; [exact A1|]. split; [intros E; rewrite Ha in E; discriminate E|].
    exact (conj A3 (conj A4 (conj A5 (conj A6 A7)))).
Qed.

(** ** Symbols *)
Lemma rk_syms_data_app out a b :
  F.syms_data out (map fsym (a ++ b)) = F.syms_data (F.syms_data out (map fsym a)) (map fsym b).
Proof. unfold F.syms_data. rewrite map_app, fold_left_app. reflexivity. Qed.

Lemma rk_syms_rok_app wmax : forall a out b,
  syms_rok wmax out (a ++ b) <-> syms_rok wmax out a /\ syms_rok wmax (F.syms_data out (map fsym a)) b.
Proof.
  induction a as [|x a IH]; intros out b.
  - cbn. tauto.
  - cbn [app syms_rok map]. rewrite IH. unfold F.syms_data. cbn [fold_left]. tauto.
Qed.

(** ** Bits *)
Lemma rk_enc_from_app_false p A B :
  enc_from p (A ++ B) false = enc_from p A false ++ enc_from (p + Zlength (enc_from p A false)) B false.
Proof.
  revert p. induction A as [|a A IH]; intros p.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app enc_from andb]. rewrite IH, <- app_assoc. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
Qed.

Lemma rk_enc_from_app p A B fin : B <> [] ->
  enc_from p (A ++ B) fin = enc_from p A false ++ enc_from (p + Zlength (enc_from p A false)) B fin.
Proof.
  intros HB. revert p. induction A as [|a A IH]; intros p.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app enc_from]. rewrite IH, <- app_assoc.
    assert (E : (fin && match A ++ B with [] => true | _ :: _ => false end) = false).
    { destruct (A ++ B) eqn:E; [apply app_eq_nil in E; destruct E; contradiction|]. apply andb_false_r. }
    rewrite E, andb_false_l. f_equal. f_equal. f_equal. rewrite Zlength_app. lia.
Qed.

Lemma rk_enc_out_app p A B fin : (fin = true -> B <> []) ->
  enc_out p (A ++ B) fin = enc_from p A false ++ enc_out (p + Zlength (enc_from p A false)) B fin.
Proof.
  intros HB. unfold enc_out. destruct fin.
  - rewrite (rk_enc_from_app p A B true (HB eq_refl)), <- app_assoc. f_equal. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
  - apply rk_enc_from_app_false.
Qed.

Lemma rk_Zlength_bits_le v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof.
  intros Hn. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma rk_Zlength_bytes_bits l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  unfold F.bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, rk_Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma rk_Zlength_bibits s : 0 <= d_bi_valid s -> Zlength (bibits s) = d_bi_valid s.
Proof. intros H. unfold bibits. apply rk_Zlength_bits_le. exact H. Qed.

Lemma rk_bytes_bits_app a b : F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma rk_quiet_pend s : quiet s -> pend s = [].
Proof. intros (Hp & Ho & _). unfold pend. rewrite Hp, Z.add_0_r. apply sublist_nil. Qed.

(** the bit position after a run of bits: whole bytes before the bit buffer *)
Lemma rk_bitpos_aligned (x : list Z) s s' (E : list bool) p :
  0 <= d_bi_valid s -> 0 <= d_bi_valid s' -> (p - d_bi_valid s) mod 8 = 0 ->
  F.bytes_bits x ++ bibits s' = bibits s ++ E ->
  (p + Zlength E - d_bi_valid s') mod 8 = 0.
Proof.
  intros H0 H1 Hp Eq. apply (f_equal (@Zlength bool)) in Eq.
  rewrite !Zlength_app, rk_Zlength_bytes_bits, !rk_Zlength_bibits in Eq by assumption.
  replace (p + Zlength E - d_bi_valid s') with ((p - d_bi_valid s) + 8 * Zlength x) by lia.
  rewrite Z.add_mod, Hp by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(** the history after two steps *)
Lemma rk_hist_app (D : list Z) (z0 : strm) (n k1 k2 : Z) :
  0 <= n -> 0 <= k1 -> 0 <= k2 -> n + k1 + k2 <= Zlength (z_in z0) ->
  (D ++ sublist n (n + k1) (z_in z0)) ++ sublist (n + k1) (n + k1 + k2) (z_in z0) =
  D ++ sublist n (n + (k1 + k2)) (z_in z0).
Proof.
  intros H0 H1 H2 Hl. rewrite <- app_assoc. f_equal.
  replace (n + (k1 + k2)) with (n + k1 + k2) by lia.
  rewrite <- sublist_split by lia. reflexivity.
Qed.

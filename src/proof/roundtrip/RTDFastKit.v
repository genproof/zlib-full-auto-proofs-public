(** * RT-D part FAST: the kit of the functional proof of deflate_fast.

    The proof follows the safety proof of the deflate laws (RTDLTCFastKit.v / RTDLTCFastGlue.v, Qed): the same
    pieces (refill, search, literal, match, bflush, tail), each with a functional statement [f*_stmt] below
    (one file each), and the glue (RTDFastGlue.v) composing them along the main loop.

    - [kt dict D BS syms s]: [kcore] without the trees part (after a tally, sym_buf may be full: TS of the safety
      kit) and with match_available = 0 (deflate_fast).
    - the pieces only state the functional facts; the safety facts (TS, SR, FI, ...) come from the Qed safety
      parts by determinism (the model run is given). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV2.
Require Export Zlib.proof.roundtrip.RTDLTCFastGlue.
Require Export Zlib.proof.roundtrip.RTDLTCFastRefill Zlib.proof.roundtrip.RTDLTCFastSearch Zlib.proof.roundtrip.RTDLTCFastLit2 Zlib.proof.roundtrip.RTDLTCFastMatch2 Zlib.proof.roundtrip.RTDLTCFastInsLoop Zlib.proof.roundtrip.RTDLTCFastFbw Zlib.proof.roundtrip.RTDLTCFastBflush Zlib.proof.roundtrip.RTDLTCFastTail.
Require Export Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCTrees2.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The functional invariant after a tally (no trees part) *)
Definition kt (dict D : list Z) (BS : list F.block) (syms : list (Z * Z)) (s : dstate) : Prop :=
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  kwin H s /\
  F.blocks_ok (2 ^ d_w_bits s) dict BS /\
  F.expand dict BS = sublist 0 (off + d_block_start s) H /\
  syms_rok (2 ^ d_w_bits s) (F.expand dict BS) syms /\
  F.syms_data (F.expand dict BS) (map fsym syms) = sublist 0 (off + d_strstart s) H /\
  khash s.

(** the state and stream of a loop piece's result *)
Definition rst (r : (dstate * strm) + dexit) : dstate * strm :=
  match r with inl a => a | inr (s, z, _) => (s, z) end.

(** ** The part statements *)

(** The top of the loop: c_refill (fill_window when lookahead < MIN_LOOKAHEAD).  The bytes read extend the
    history; nothing is output. *)
Definition frefill_stmt : Prop :=
  forall s z flush r dict D BS syms,
    fill_fspec ->
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 -> 0 <= flush <= 5 ->
    kcore dict D BS syms s ->
    c_refill need_min_lookahead flush s z = Some r ->
    exists k,
      zstep (d_wrap s) z (snd (rst r)) k [] /\
      kcore dict (D ++ sublist (z_next_in z) (z_next_in z + k) (z_in z)) BS syms (fst (rst r)) /\
      pend (fst (rst r)) = pend s /\ bibits (fst (rst r)) = bibits s.

(** INSERT_STRING at strstart and longest_match ([fsearch]): the chains stay hash-consistent, ins_h is primed
    for strstart + 1 after the insertion, and a match (match_length >= MIN_MATCH) is real.
    NOTE: lm_fspec assumes [chain_ok], false right after INSERT_STRING(strstart) (head holds strstart); apply it
    to [set_d_head s2 (d_head s)] (longest_match does not read head) and transfer the result. *)
Definition fsearch_stmt : Prop :=
  forall s s2,
    ins_fspec2 -> lm_fspec ->
    W s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s -> khash s ->
    fsearch s = Some s2 ->
    chain_hok s2 /\
    (MIN_MATCH <= d_lookahead s -> primed s2 (d_strstart s + 1)) /\
    (MIN_MATCH <= d_match_length s2 -> forall i, 0 <= i < d_match_length s2 ->
       Znth (d_match_start s2 + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s))).

(** The literal branch: the literal window[strstart] is tallied. *)
Definition flit_stmt : Prop :=
  forall s s2 s3 bf dict D BS syms,
    tally_spec2 ->
    W s -> outok s -> quiet s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s ->
    SR s s2 -> d_match_length s2 < MIN_MATCH ->
    Forall F.byte_ok dict -> bytes D -> kcore dict D BS syms s ->
    chain_hok s2 -> (MIN_MATCH <= d_lookahead s -> primed s2 (d_strstart s + 1)) ->
    flit s2 = Some (s3, bf) ->
    exists syms3, TS s3 syms3 bf /\ kt dict D BS syms3 s3 /\ bibits s3 = bibits s.

(** The match branch: the match (dist = strstart - match_start, length match_length) is tallied; then the
    insertion loop (short match, keeps ins_h primed) or the re-priming of ins_h (long match). *)
Definition fmatch_stmt : Prop :=
  forall s s2 s3 bf dict D BS syms,
    tally_spec2 -> ins_fspec2 ->
    W s -> outok s -> quiet s -> fn_of s = 1 -> ready s -> 1 <= d_lookahead s ->
    SR s s2 -> MIN_MATCH <= d_match_length s2 ->
    Forall F.byte_ok dict -> bytes D -> kcore dict D BS syms s ->
    chain_hok s2 -> (MIN_MATCH <= d_lookahead s -> primed s2 (d_strstart s + 1)) ->
    (forall i, 0 <= i < d_match_length s2 ->
       Znth (d_match_start s2 + i) (mb_val (d_window s)) = Znth (d_strstart s + i) (mb_val (d_window s))) ->
    fmatch s2 = Some (s3, bf) ->
    exists syms3, TS s3 syms3 bf /\ kt dict D BS syms3 s3 /\ bibits s3 = bibits s.

(** [if (bflush) FLUSH_BLOCK(s, 0)]: at most one block, its bits appended. *)
Definition fbflush_stmt : Prop :=
  forall s z flush syms bf r dict D BS p,
    fbo_fspec ->
    TS s syms bf -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 ->
    Forall F.byte_ok dict -> bytes D -> kt dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_bflush s z bf = Some r ->
    exists x BS' syms',
      zstep (d_wrap s) z (snd (rst r)) 0 x /\
      kcore dict D (BS ++ BS') syms' (fst (rst r)) /\
      F.bytes_bits (x ++ pend (fst (rst r))) ++ bibits (fst (rst r)) = bibits s ++ enc_from p BS' false.

(** deflate_tail after the loop: FLUSH_BLOCK(s, 1) on Z_FINISH (the final block), else the last symbols. *)
Definition ftail_stmt : Prop :=
  forall s z flush s' z' bs dict D BS syms p,
    fbo_fspec ->
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 1 ->
    0 <= flush <= 5 -> flush <> Z_NO_FLUSH ->
    d_lookahead s = 0 -> z_avail_in z = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
    Forall F.byte_ok dict -> bytes D -> kcore dict D BS syms s ->
    0 <= p -> (p - d_bi_valid s) mod 8 = 0 ->
    c_deflate_tail (set_insert_end s) z flush = Some (s', z', bs) ->
    exists x BS' syms',
      zstep (d_wrap s) z z' 0 x /\
      kcore dict D (BS ++ BS') syms' s' /\
      F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ enc_out p BS' (fin_bs bs) /\
      (fin_bs bs = true -> BS' <> []).

(** ** Helper lemmas (Qed) *)

(** the symbols in sym_buf determine the symbol list *)
Lemma sym_bytes_inj : forall l1 l2, Zlength l1 = Zlength l2 -> sym_bytes l1 = sym_bytes l2 -> l1 = l2.
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

Lemma tree_ok_uniq t m s1 s2 : tree_ok t m s1 -> tree_ok t m s2 -> s1 = s2.
Proof.
  intros (_ & _ & N1 & _ & B1 & _) (_ & _ & N2 & _ & B2 & _).
  assert (L : Zlength s1 = Zlength s2) by lia.
  apply sym_bytes_inj; [exact L|]. rewrite <- B1, <- B2, L. reflexivity.
Qed.

Lemma wtrees_uniq s s1 s2 : wtrees s s1 -> wtrees s s2 -> s1 = s2.
Proof. intros (T1 & _) (T2 & _). exact (tree_ok_uniq _ _ _ _ T1 T2). Qed.

(** kcore = kt + wtrees (deflate_fast: match_available = 0) *)
Lemma kcore_kt dict D BS syms s :
  d_match_available s = 0 -> kcore dict D BS syms s -> kt dict D BS syms s /\ wtrees s syms.
Proof.
  intros Ha ((K1 & _ & K3 & K4 & K5 & K6 & K7) & Kh). rewrite Ha, Z.sub_0_r in K7.
  split; [|exact K3]. unfold kt. auto 7.
Qed.

Lemma kt_kcore dict D BS syms s :
  d_match_available s = 0 -> kt dict D BS syms s -> wtrees s syms -> kcore dict D BS syms s.
Proof.
  intros Ha (K1 & K4 & K5 & K6 & K7 & Kh) Hw. split; [|exact Kh].
  unfold kdata. cbv zeta. rewrite Ha, Z.sub_0_r.
  split; [exact K1|]. split; [unfold kmatch; intros E; lia|]. auto 6.
Qed.

(** ** Bits *)
Lemma enc_from_app_false p A B :
  enc_from p (A ++ B) false = enc_from p A false ++ enc_from (p + Zlength (enc_from p A false)) B false.
Proof.
  revert p. induction A as [|a A IH]; intros p.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app enc_from andb]. rewrite IH, <- app_assoc. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
Qed.

Lemma enc_from_app p A B fin : B <> [] ->
  enc_from p (A ++ B) fin = enc_from p A false ++ enc_from (p + Zlength (enc_from p A false)) B fin.
Proof.
  intros HB. revert p. induction A as [|a A IH]; intros p.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [app enc_from]. rewrite IH, <- app_assoc.
    assert (E : (fin && match A ++ B with [] => true | _ :: _ => false end) = false).
    { destruct (A ++ B) eqn:E; [apply app_eq_nil in E; destruct E; contradiction|]. apply andb_false_r. }
    rewrite E, andb_false_l. f_equal. f_equal. f_equal. rewrite Zlength_app. lia.
Qed.

Lemma enc_out_app p A B fin : (fin = true -> B <> []) ->
  enc_out p (A ++ B) fin = enc_from p A false ++ enc_out (p + Zlength (enc_from p A false)) B fin.
Proof.
  intros HB. unfold enc_out. destruct fin.
  - rewrite (enc_from_app p A B true (HB eq_refl)), <- app_assoc. f_equal. f_equal. f_equal. f_equal.
    rewrite Zlength_app. lia.
  - apply enc_from_app_false.
Qed.

Lemma enc_out_false p BS : enc_out p BS false = enc_from p BS false.
Proof. reflexivity. Qed.

Lemma Zlength_bits_le v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof.
  intros Hn. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma Zlength_bytes_bits l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  unfold F.bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, IH, Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma Zlength_bibits s : 0 <= d_bi_valid s -> Zlength (bibits s) = d_bi_valid s.
Proof. intros H. unfold bibits. apply Zlength_bits_le. exact H. Qed.

Lemma bytes_bits_app a b : F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma quiet_pend s : quiet s -> pend s = [].
Proof. intros (Hp & Ho & _). unfold pend. rewrite Hp, Z.add_0_r. apply sublist_nil. Qed.

(** the bit position after a run of bits: whole bytes before the bit buffer *)
Lemma bitpos_aligned (x : list Z) s s' (E : list bool) p :
  0 <= d_bi_valid s -> 0 <= d_bi_valid s' -> (p - d_bi_valid s) mod 8 = 0 ->
  F.bytes_bits x ++ bibits s' = bibits s ++ E ->
  (p + Zlength E - d_bi_valid s') mod 8 = 0.
Proof.
  intros H0 H1 Hp Eq. apply (f_equal (@Zlength bool)) in Eq.
  rewrite !Zlength_app, Zlength_bytes_bits, !Zlength_bibits in Eq by assumption.
  replace (p + Zlength E - d_bi_valid s') with ((p - d_bi_valid s) + 8 * Zlength x) by lia.
  rewrite Z.add_mod, Hp by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(** the history after two steps *)
Lemma hist_app (D : list Z) (z0 : strm) (n k1 k2 : Z) :
  0 <= n -> 0 <= k1 -> 0 <= k2 -> n + k1 + k2 <= Zlength (z_in z0) ->
  (D ++ sublist n (n + k1) (z_in z0)) ++ sublist (n + k1) (n + k1 + k2) (z_in z0) =
  D ++ sublist n (n + (k1 + k2)) (z_in z0).
Proof.
  intros H0 H1 H2 Hl. rewrite <- app_assoc. f_equal.
  replace (n + (k1 + k2)) with (n + k1 + k2) by lia.
  rewrite <- sublist_split by lia. reflexivity.
Qed.

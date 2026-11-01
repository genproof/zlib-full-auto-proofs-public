(* RT-D part SLOW: the functional proof of deflate_slow, interface of the parts.
   Safety (Qed, RTDLTCSlow*.v): the loop invariant [SI], the split dsl_pre / dsl_match / dsl_lit / dsl_cand /
   dsl_end, [MID], [rdy].  Here the functional companion: [FI] (the call's functional invariant, kcore3 of
   RTDV3.v), [FQ] (comp_fspec3's conclusion), [FMID] (what dsl_pre adds), the part statements, and shared
   lemmas on the bits.  The parts are proved in RTDSlow<Part>.v, the assembly in RTDSlow3.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDV3.
Require Export Zlib.proof.roundtrip.RTDLTCSlowInv.
Require Zlib.proof.roundtrip.RTDLTCFill Zlib.proof.roundtrip.RTDLTCTrees2 Zlib.proof.roundtrip.RTDLTCLm Zlib.proof.roundtrip.RTDLTCFlushKit.
Import ListNotations.
Local Open Scope Z_scope.

(** ** The specs *)

(* the safety specs (all Qed in the deflate laws' theory, given lemma (i)) *)
Definition sspecs : Prop := fill_spec /\ ins_spec /\ lm_spec /\ tally_spec2 /\ fbo_spec /\ fpend_spec2.

Lemma sspecs_ok : Zlib.proof.huffman.Overlay.overlay_statement -> sspecs.
Proof.
  intros Hov. destruct (RTDLTCTrees2.trees_ok2 Hov) as (Htal & Htf & Hroom).
  destruct RTDLTCLm.lm_ok as [Hins Hlm].
  exact (conj RTDLTCFill.fill_ok (conj Hins (conj Hlm (conj Htal
           (conj (RTDLTCFlushKit.fbo_ok Htf Hroom) fpend2_ok))))).
Qed.

(* the functional specs of the functions deflate_slow calls (hypotheses here, discharged in RTDTheory.v) *)
Definition fspecs : Prop := fill_fspec /\ ins_fspec2 /\ lm_fspec /\ fpend_fspec2 /\ fbo_fspec.

(** ** The functional invariant of a call c_deflate_slow s0 z0 flush (dict, D, BS: comp_fspec3's history and
    blocks at the start; p: the bit position at the start) *)

Definition FG (dict D : list Z) (p : Z) (s0 : dstate) : Prop :=
  Forall F.byte_ok dict /\ bytes D /\ 0 <= p /\ (p - d_bi_valid s0) mod 8 = 0.

(* after consuming k input bytes and writing x: kcore3 with the blocks BS' emitted since the start, and the bits
   added are their encoding (none final) *)
Definition FI (dict D : list Z) (BS : list F.block) (p : Z) (s0 : dstate) (z0 : strm) (s : dstate) (z : strm) :
    Prop :=
  exists k x BS' syms,
    zstep (d_wrap s0) z0 z k x /\
    kcore3 dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS ++ BS') syms s /\
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' false.

(* the result (comp_fspec3's conclusion) *)
Definition FQ (dict D : list Z) (BS : list F.block) (p : Z) (s0 : dstate) (z0 : strm) (s : dstate) (z : strm)
    (bs : bstate) : Prop :=
  exists k x BS' syms,
    zstep (d_wrap s0) z0 z k x /\
    kcore3 dict (D ++ sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0)) (BS ++ BS') syms s /\
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' (fin_bs bs) /\
    (fin_bs bs = true -> BS' <> []).

(* the outcome of a part of an iteration: go on (FI), return bs (FQ), or break (FI) *)
Definition fstep_ok (dict D : list Z) (BS : list F.block) (p : Z) (s0 : dstate) (z0 : strm)
    (r : (dstate * strm) + dexit) : Prop :=
  match r with
  | inl (s', z') => FI dict D BS p s0 z0 s' z'
  | inr (s', z', Some bs) => FQ dict D BS p s0 z0 s' z' bs
  | inr (s', z', None) => FI dict D BS p s0 z0 s' z'
  end.

(** What dsl_pre adds (from s after the refill to s1): the chains stay hash-consistent, ins_h is primed for
    strstart + 1 after INSERT_STRING(strstart), and a candidate longer than prev_length is a match (at a
    position in [lim, strstart)). *)
Definition FMID (s s1 : dstate) : Prop :=
  chain_hok s1 /\
  (MIN_MATCH <= d_lookahead s -> primed s1 (d_strstart s + 1)) /\
  (MIN_MATCH <= d_match_length s1 -> d_prev_length s1 < d_match_length s1 ->
     lim s1 <= d_match_start s1 /\ 0 < d_match_start s1 < d_strstart s1 /\
     forall i, 0 <= i < d_match_length s1 ->
       Znth (d_match_start s1 + i) (mb_val (d_window s1)) = Znth (d_strstart s1 + i) (mb_val (d_window s1))).

(** ** The parts *)

(* the refill (fill_window, then need_more / break / go on) *)
Definition frefill_part : Prop :=
  forall dict D BS p s0 z0 flush s z evs r,
    sspecs -> fspecs -> SI s0 z0 flush s z evs -> FG dict D p s0 -> FI dict D BS p s0 z0 s z ->
    c_refill need_min_lookahead flush s z = Some r ->
    fstep_ok dict D BS p s0 z0 r.

(* INSERT_STRING, longest_match, the filter *)
Definition fpre_part : Prop :=
  forall s0 z0 flush s z evs s1 dict H BS syms,
    sspecs -> fspecs -> SI s0 z0 flush s z evs -> rdy s -> kcore3 dict H BS syms s ->
    dsl_pre s = Some s1 -> FMID s s1.

(* the match branch: Ref prev_length (strstart - 1 - prev_match), the insertions, FLUSH_BLOCK if bflush *)
Definition fmatch_part : Prop :=
  forall dict D BS p s0 z0 flush s z evs s1 r,
    sspecs -> fspecs -> SI s0 z0 flush s z evs -> rdy s -> MID s s1 -> FMID s s1 ->
    FG dict D p s0 -> FI dict D BS p s0 z0 s z ->
    MIN_MATCH <= d_prev_length s1 -> d_match_length s1 <= d_prev_length s1 ->
    dsl_match s1 z = Some r -> fstep_ok dict D BS p s0 z0 r.

(* the pending-literal branch: Lit window[strstart - 1], FLUSH_BLOCK_ONLY if bflush *)
Definition flit_part : Prop :=
  forall dict D BS p s0 z0 flush s z evs s1 r,
    sspecs -> fspecs -> SI s0 z0 flush s z evs -> rdy s -> MID s s1 -> FMID s s1 ->
    FG dict D p s0 -> FI dict D BS p s0 z0 s z ->
    ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 <> 0 ->
    dsl_lit s1 z = Some r -> fstep_ok dict D BS p s0 z0 r.

(* the new-candidate branch *)
Definition fcand_part : Prop :=
  forall dict D BS p s0 z0 flush s z evs s1 r,
    sspecs -> fspecs -> SI s0 z0 flush s z evs -> rdy s -> MID s s1 -> FMID s s1 ->
    FG dict D p s0 -> FI dict D BS p s0 z0 s z ->
    ~ (MIN_MATCH <= d_prev_length s1 /\ d_match_length s1 <= d_prev_length s1) -> d_match_available s1 = 0 ->
    dsl_cand s1 z = Some r -> fstep_ok dict D BS p s0 z0 r.

(* after the loop's break: the pending literal, then FLUSH_BLOCK(s, 1) / FLUSH_BLOCK(s, 0) / nothing *)
Definition fend_part : Prop :=
  forall dict D BS p s0 z0 flush s z evs s' z' bs,
    sspecs -> fspecs -> SI s0 z0 flush s z evs ->
    d_lookahead s = 0 -> z_avail_in z = 0 -> flush <> Z_NO_FLUSH ->
    d_strstart s + MIN_LOOKAHEAD <= d_window_size s ->
    FG dict D p s0 -> FI dict D BS p s0 z0 s z ->
    dsl_end s z flush = Some (s', z', bs) -> FQ dict D BS p s0 z0 s' z' bs.

(** ** Shared lemmas: the bits *)

Lemma sk_bytes_bits_app a b : F.bytes_bits (a ++ b) = F.bytes_bits a ++ F.bytes_bits b.
Proof. unfold F.bytes_bits. apply flat_map_app. Qed.

Lemma sk_Zlength_bits_le v n : 0 <= n -> Zlength (F.bits_le v n) = n.
Proof.
  intros Hn. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, seq_length. apply Z2Nat.id. exact Hn.
Qed.

Lemma sk_Zlength_bytes_bits l : Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH].
  - reflexivity.
  - change (F.bytes_bits (a :: l)) with (F.bits_le a 8 ++ F.bytes_bits l).
    rewrite Zlength_app, IH, sk_Zlength_bits_le by lia. rewrite Zlength_cons. lia.
Qed.

Lemma sk_Zlength_bibits s : 0 <= d_bi_valid s -> Zlength (bibits s) = d_bi_valid s.
Proof. intros H. unfold bibits. apply sk_Zlength_bits_le. exact H. Qed.

(* a run of blocks then one more *)
Lemma enc_from_snoc p l b fin :
  enc_from p (l ++ [b]) fin = enc_from p l false ++ enc_from (p + Zlength (enc_from p l false)) [b] fin.
Proof.
  revert p. induction l as [|a l IH]; intros p.
  - cbn [app enc_from]. rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - cbn [app enc_from]. 
    assert (E : match l ++ [b] with [] => true | _ => false end = false).
    { destruct l; reflexivity. }
    rewrite E, andb_false_r. cbn [andb].
    rewrite IH, <- app_assoc. f_equal. f_equal. rewrite Zlength_app, Z.add_assoc. reflexivity.
Qed.

Lemma enc_out_snoc p l b fin :
  enc_out p (l ++ [b]) fin = enc_out p l false ++ enc_out (p + Zlength (enc_out p l false)) [b] fin.
Proof.
  unfold enc_out. rewrite enc_from_snoc. cbv zeta. cbn [negb].
  destruct fin.
  - rewrite <- app_assoc. f_equal. f_equal. rewrite Zlength_app, Z.add_assoc. reflexivity.
  - reflexivity.
Qed.

(* the bits after a block writer that started on a quiet state *)
Lemma bits_step s0 s s' x0 x E0 E1 :
  F.bytes_bits (x0 ++ pend s) ++ bibits s = bibits s0 ++ E0 -> pend s = [] ->
  F.bytes_bits (x ++ pend s') ++ bibits s' = bibits s ++ E1 ->
  F.bytes_bits ((x0 ++ x) ++ pend s') ++ bibits s' = bibits s0 ++ E0 ++ E1.
Proof.
  intros H0 Hp H1. rewrite Hp, app_nil_r in H0.
  rewrite <- app_assoc, sk_bytes_bits_app, <- app_assoc, H1, app_assoc, H0, app_assoc.
  reflexivity.
Qed.

(* the bit position after the bits so far is aligned with the bit buffer *)
Lemma bits_align s0 s x0 E0 p :
  F.bytes_bits (x0 ++ pend s) ++ bibits s = bibits s0 ++ E0 ->
  0 <= d_bi_valid s -> 0 <= d_bi_valid s0 -> (p - d_bi_valid s0) mod 8 = 0 ->
  (p + Zlength E0 - d_bi_valid s) mod 8 = 0.
Proof.
  intros H Hv Hv0 Hp. apply (f_equal (@Zlength bool)) in H.
  rewrite !Zlength_app, sk_Zlength_bytes_bits, !sk_Zlength_bibits in H by lia.
  replace (p + Zlength E0 - d_bi_valid s) with ((p - d_bi_valid s0) + 8 * Zlength (x0 ++ pend s)) by lia.
  rewrite Z.add_mod, Hp by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(* pend of a quiet state *)
Lemma pend_quiet s : quiet s -> pend s = [].
Proof. intros (H1 & H2 & _). unfold pend. rewrite H1, H2. apply sublist_nil. Qed.

(** FLUSH_BLOCK_ONLY on the functional state: fbo_fspec with the bits of the run so far *)
Lemma fbo_bits_step s0 s z s' z' syms last dict D BS BS' p x0 :
  fbo_fspec ->
  fbo_pre s z syms last ->
  let H := dict ++ D in
  let off := Zlength H - (d_strstart s + d_lookahead s) in
  let wmax := 2 ^ d_w_bits s in
  kwin H s -> F.blocks_ok wmax dict (BS ++ BS') ->
  F.expand dict (BS ++ BS') = sublist 0 (off + d_block_start s) H ->
  syms_rok wmax (F.expand dict (BS ++ BS')) syms ->
  F.syms_data (F.expand dict (BS ++ BS')) (map fsym syms) = sublist 0 (off + d_strstart s) H ->
  0 <= p -> (p - d_bi_valid s0) mod 8 = 0 -> 0 <= d_bi_valid s0 ->
  F.bytes_bits (x0 ++ pend s) ++ bibits s = bibits s0 ++ enc_out p BS' false ->
  c_flush_block_only s z last = Some (s', z') ->
  exists x blk,
    zout_only z z' x /\
    F.blocks_ok wmax dict ((BS ++ BS') ++ [blk]) /\
    F.expand dict ((BS ++ BS') ++ [blk]) = sublist 0 (off + d_strstart s) H /\
    F.bytes_bits ((x0 ++ x) ++ pend s') ++ bibits s' = bibits s0 ++ enc_out p (BS' ++ [blk]) (last =? 1).
Proof.
  intros Hf Hpre H off wmax Hw Hb He Hr Hd Hp Hal Hv0 Hbits E.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & (Hbv & _) & _) & Hq & _).
  assert (Hv : 0 <= d_bi_valid s).
  { unfold d_bi_valid. lia. }
  set (q := p + Zlength (enc_out p BS' false)).
  assert (Hq0 : 0 <= q).
  { unfold q. pose proof (Zlength_nonneg (enc_out p BS' false)). lia. }
  assert (Hqa : (q - d_bi_valid s) mod 8 = 0).
  { unfold q. exact (bits_align s0 s x0 _ p Hbits Hv Hv0 Hal). }
  destruct (Hf s z s' z' syms last dict D (BS ++ BS') q Hpre Hw Hb He Hr Hd Hq0 Hqa E)
    as (x & blk & Hz & Hb' & He' & Hbits').
  exists x, blk. split; [exact Hz|]. split; [exact Hb'|]. split; [exact He'|].
  rewrite enc_out_snoc. fold q. exact (bits_step s0 s s' x0 x _ _ Hbits (pend_quiet s Hq) Hbits').
Qed.

(** ** The start *)
Lemma FI_init dict D BS p s0 z0 flush syms :
  compress_pre2 s0 z0 flush -> kcore3 dict D BS syms s0 -> FI dict D BS p s0 z0 s0 z0.
Proof.
  intros (HW & Ho & Hq & Hfl & Hz & Hw & Ha) Hk.
  exists 0, [], [], syms. split; [apply zstep_refl; [apply zin_ok_zall; exact Hz|exact Ha]|].
  rewrite Z.add_0_r, sublist_nil, !app_nil_r. split; [exact Hk|].
  rewrite (pend_quiet s0 Hq). reflexivity.
Qed.

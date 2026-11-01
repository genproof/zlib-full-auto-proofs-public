(** * Kit for LTCRle2.v: deflate_rle on the checked model.

    Reuses the definitions of LTCFastKit.v:
    [crel], [bpost], [FI], [fr], [flit], [cpost_of], [FI_refl], [blk_len_app], [blk_len_bound], the rewrite
    database [fproj].  The proof of [rle_ok2] is cut into parts (statements [r*_stmt] below, one file each):
    - [rrefill_stmt] (LTCRleRefill.v): the top of the loop, c_refill need_rle with fill_window;
    - [rscan_stmt] (LTCRleScan.v): the run scan ([rscan]): match_length of the run at strstart;
    - [rlit_stmt] (LTCRleLit.v): the literal branch ([flit] of LTCFastKit, identical to deflate_rle's);
    - [rdist_stmt] (LTCRleDist.v): the run branch ([rdist]: _tr_tally_dist with distance 1);
    - [rfbw_stmt] (LTCRleFbw.v): FLUSH_BLOCK_ONLY at a state with the symbols [syms] ([RTS0]);
    - [rbflush_stmt] (LTCRleBflush.v): [if (bflush) FLUSH_BLOCK(s, 0)] (c_bflush);
    - [rtail_stmt] (LTCRleTail.v): deflate_tail after the loop (insert = 0).
    The glue (step, loop, final assembly) is in LTCRle2.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Require Export Zlib.proof.deflate.LTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** After the refill of deflate_rle: more than MAX_MATCH bytes of lookahead, or a fill just happened
    (strstart low, high_water far enough).  Either way strstart + MAX_MATCH < window_size and the window is
    defined on [0, strstart + MAX_MATCH]. *)
Definition rready (s : dstate) : Prop :=
  MAX_MATCH < d_lookahead s \/
  (d_strstart s < d_w_size s + MAX_DIST s /\
   Z.min (d_window_size s) (d_strstart s + d_lookahead s + WIN_INIT) <= d_high_water s).

(** A state of deflate_rle with the symbols [syms] (at most L - 1: a full sym_buf is allowed), strstart inside
    the window: [W] minus the L - 2 bound, plus outok, quiet ([TS0] of LTCFastKit with fn_of = 4). *)
Definition RTS0 (s : dstate) (syms : list (Z * Z)) : Prop :=
  prm s /\ wstruct s /\ wpos s /\ wwin s /\ whash s /\ wmatch s /\
  tree_ok (d_tr s) (d_pbm s) syms /\ Zlength syms <= d_L s - 1 /\ Forall (sym_ok s) syms /\
  blk_len syms = d_strstart s - d_block_start s /\
  outok s /\ quiet s /\ fn_of s = 4 /\ d_strstart s < d_window_size s.

(** ... after a tally that returned [bf]. *)
Definition RTS (s : dstate) (syms : list (Z * Z)) (bf : bool) : Prop :=
  RTS0 s syms /\ bf = (Zlength syms =? d_L s - 1).

(** ** The pieces of rle_step *)

(** [s->match_length = 0; if (lookahead >= MIN_MATCH && strstart > 0) { the run scan }] *)
Definition rscan (s : dstate) : option dstate :=
  let s := set_d_match_length s 0 in
  if (d_lookahead s >=? MIN_MATCH) && (d_strstart s >? 0) then
    let scan := d_strstart s - 1 in
    let* prev := mb_rd (d_window s) scan in
    let* c1 := mb_rd (d_window s) (scan + 1) in
    if negb (prev =? c1) then Some s else
    let* c2 := mb_rd (d_window s) (scan + 2) in
    if negb (prev =? c2) then Some s else
    let* c3 := mb_rd (d_window s) (scan + 3) in
    if negb (prev =? c3) then Some s else
    let strend := d_strstart s + MAX_MATCH in
    let* scan := loop FUEL (rle_cmp_body s prev strend) (scan + 3, 0) in
    let s := set_d_match_length s (u32 (MAX_MATCH - u32 (strend - scan))) in
    Some (if d_match_length s >? d_lookahead s then set_d_match_length s (d_lookahead s) else s)
  else Some s.

(** The run branch: [_tr_tally_dist(s, 1, match_length - MIN_MATCH); lookahead -= match_length;
    strstart += match_length; match_length = 0]. *)
Definition rdist (s : dstate) : option (dstate * bool) :=
  let* (s, bflush) := c_dtally_dist s 1 (u32 (d_match_length s - MIN_MATCH)) in
  let s := set_d_lookahead s (u32 (d_lookahead s - d_match_length s)) in
  let s := set_d_strstart s (u32 (d_strstart s + d_match_length s)) in
  Some (set_d_match_length s 0, bflush).

Definition rbranch (s : dstate) : option (dstate * bool) :=
  if d_match_length s >=? MIN_MATCH then rdist s else flit s.

Lemma rle_step_eq s z :
  rle_step s z = let* s2 := rscan s in let* (s3, bf) := rbranch s2 in c_bflush s3 z bf.
Proof. reflexivity. Qed.

(** The result of the scan: only match_length set, to a length within the lookahead; a run (>= MIN_MATCH)
    only when strstart >= 1 (distance 1). *)
Definition RSC (s s2 : dstate) : Prop :=
  exists ml, s2 = set_d_match_length s ml /\ 0 <= ml <= MAX_MATCH /\ ml <= d_lookahead s /\
             (MIN_MATCH <= ml -> 1 <= d_strstart s).

(** ** The part statements *)

Definition rrefill_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 -> 0 <= flush <= 5 ->
    exists r, c_refill need_rle flush s z = Some r /\
    match r with
    | inl (s', z') =>
        FI s z flush s' z' [] /\ rready s' /\ 1 <= d_lookahead s' /\
        z_avail_in z' + d_lookahead s' = z_avail_in z + d_lookahead s
    | inr (s', z', Some bs) => bs = need_more /\ crel s z flush s' z' [] /\ bpost s z flush s' z' need_more []
    | inr (s', z', None) =>
        FI s z flush s' z' [] /\ d_lookahead s' = 0 /\ z_avail_in z' = 0 /\ flush <> Z_NO_FLUSH /\
        d_strstart s' < d_w_size s' + MAX_DIST s'
    end.

Definition rscan_stmt : Prop :=
  forall s, W s -> fn_of s = 4 -> rready s -> 1 <= d_lookahead s ->
    exists s2, rscan s = Some s2 /\ RSC s s2.

Definition rlit_stmt : Prop :=
  forall s ml,
    W s -> outok s -> quiet s -> fn_of s = 4 -> rready s -> 1 <= d_lookahead s -> 0 <= ml < MIN_MATCH ->
    exists s3 bf syms3, flit (set_d_match_length s ml) = Some (s3, bf) /\ RTS s3 syms3 bf /\ fr s s3 /\
      d_lookahead s3 < d_lookahead s.

Definition rdist_stmt : Prop :=
  forall s ml,
    W s -> outok s -> quiet s -> fn_of s = 4 -> rready s ->
    MIN_MATCH <= ml <= MAX_MATCH -> ml <= d_lookahead s -> 1 <= d_strstart s ->
    exists s3 bf syms3, rdist (set_d_match_length s ml) = Some (s3, bf) /\ RTS s3 syms3 bf /\ fr s s3 /\
      d_lookahead s3 < d_lookahead s.

Definition rfbw_stmt : Prop :=
  forall s z flush syms last,
    RTS0 s syms -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 -> 0 <= last <= 1 ->
    (last = 1 -> flush = Z_FINISH) ->
    (last = 0 -> Zlength syms = d_L s - 1 \/ (flush <> Z_NO_FLUSH /\ flush <> Z_FINISH)) ->
    exists s' z' e,
      c_flush_block_only s z last = Some (s', z') /\ crel s z flush s' z' [e] /\ ev_last e = last /\
      zall z' /\ z_adler z' = z_adler z /\ z_avail_in z' = z_avail_in z /\
      d_lookahead s' = d_lookahead s /\ d_strstart s' = d_strstart s /\ d_block_start s' = d_strstart s /\
      d_sym_next s' = 0 /\ d_bi_valid s' <= 7 /\ (last = 1 -> d_bi_valid s' = 0) /\
      (d_pending s' = 0 \/ z_avail_out z' = 0).

Definition rbflush_stmt : Prop :=
  forall s z flush syms bf,
    RTS s syms bf -> zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= flush <= 5 ->
    exists r, c_bflush s z bf = Some r /\
    match r with
    | inl (s', z') =>
        (exists evs, FI s z flush s' z' evs) /\ d_lookahead s' = d_lookahead s /\ z_avail_in z' = z_avail_in z
    | inr (s', z', o) =>
        o = Some need_more /\ exists evs, crel s z flush s' z' evs /\ bpost s z flush s' z' need_more evs
    end.

Definition rtail_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> zall z -> adler_ok (d_wrap s) (z_adler z) -> fn_of s = 4 ->
    0 <= flush <= 5 -> flush <> Z_NO_FLUSH ->
    d_lookahead s = 0 -> z_avail_in z = 0 -> d_strstart s < d_w_size s + MAX_DIST s ->
    exists s' z' bs evs,
      c_deflate_tail (set_d_insert s 0) z flush = Some (s', z', bs) /\
      crel s z flush s' z' evs /\ bpost s z flush s' z' bs evs.

(** ** Helper lemmas (Qed) *)

Lemma fn_of_rle s : prm s -> fn_of s = 4 -> 1 <= d_level s /\ d_strategy s = Z_RLE.
Proof.
  intros Hp Hf. destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hs & _).
  unfold fn_of in Hf.
  destruct (Z.eqb_spec (d_level s) 0) as [E0|N0]; [discriminate|].
  destruct (Z.eqb_spec (d_strategy s) Z_HUFFMAN_ONLY) as [E1|N1]; [discriminate|].
  destruct (Z.eqb_spec (d_strategy s) Z_RLE) as [E2|N2]; [split; [lia|exact E2]|].
  exfalso.
  assert (Hc : forall l, 0 <= l <= 9 -> l <> 0 -> cfg_f l <> 4).
  { intros l Hl' Hn Hc.
    assert (l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute in Hc; lia. }
  exact (Hc (d_level s) Hl N0 Hf).
Qed.

(** match_available = 0 outside deflate_slow *)
Lemma wmatch_avail0 s : wmatch s -> fn_of s = 4 -> d_match_available s = 0.
Proof.
  intros Hm Hfn. destruct Hm as (_ & _ & [A|A] & _ & B); [exact A|]. destruct (B A) as (C & _). lia.
Qed.

(** [W] from [RTS0] when sym_buf is not full. *)
Lemma RTS0_W s syms : RTS0 s syms -> Zlength syms <= d_L s - 2 -> W s.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & Ht & HL & Hf & Hb & Ho & Hq & Hfn & Hss) HL2.
  assert (Hlev := fn_of_rle s Hp Hfn).
  assert (Ha := wmatch_avail0 s Hm Hfn).
  unfold W. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [intros; lia|].
  exists syms. unfold wtrees. split; [exact Ht|]. split; [exact HL2|]. split; [exact Hf|].
  split; [intros; lia|]. intros _. rewrite Ha. lia.
Qed.

(** [RTS0] from [W]. *)
Lemma W_RTS0 s : W s -> outok s -> quiet s -> fn_of s = 4 -> d_strstart s < d_window_size s ->
  exists syms, RTS0 s syms /\ Zlength syms <= d_L s - 2.
Proof.
  intros (Hp & Hs & Hpos & Hw & Hh & Hm & H0 & syms & Ht & HL & Hf & Hz & Hb) Ho Hq Hfn Hss.
  assert (Hlev := fn_of_rle s Hp Hfn).
  assert (Ha := wmatch_avail0 s Hm Hfn).
  exists syms. split; [|exact HL].
  unfold RTS0. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hpos|]. split; [exact Hw|].
  split; [exact Hh|]. split; [exact Hm|]. split; [exact Ht|]. split; [lia|]. split; [exact Hf|].
  split; [rewrite Hb by lia; rewrite Ha; lia|]. split; [exact Ho|]. split; [exact Hq|]. split; [exact Hfn|].
  exact Hss.
Qed.

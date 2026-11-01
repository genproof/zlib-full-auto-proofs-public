(** * deflate_stored at level 0: the parts of [stored_ok2]

    [c_deflate_stored] is cut into: the first-phase loop ([ds_body], part [dsloop_stmt]), the window update
    [c_ds_window] ([dswin_stmt]), the second-phase window refill [ds_fill2] ([fill2_stmt]) and the second-phase
    stored block [ds_blk2] ([blk2_stmt]); [sblk_stmt] is _tr_stored_block.  Each part is a [Prop], proved in
    its own file (with [sblk_stmt] / [fpend_spec] as hypotheses where needed); RTDLTCStored2.v assembles them. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCLib.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Pieces of c_deflate_stored (verbatim) *)

Definition ds_min_block (s : dstate) : Z :=
  u32 (let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a).

(** "Fill the window with any remaining input" (second phase), up to the second [upd_high_water], then the
    continuation [K]. *)
Definition ds_fill2 {A : Type} (s : dstate) (z : strm) (K : dstate -> strm -> option A) : option A :=
  let have := u32 (u64 (d_window_size s - d_strstart s)) in
  let* (s, have) :=
    (if (z_avail_in z >? have) && (d_block_start s >=? d_w_size s) then
       let s := set_d_block_start s (d_block_start s - d_w_size s) in
       let s := set_d_strstart s (u32 (d_strstart s - d_w_size s)) in
       let* win := mb_move (d_window s) 0 (d_w_size s) (d_strstart s) in
       let s := set_d_window s win in
       let s := incr_matches s in
       let have := u32 (have + d_w_size s) in
       Some (clamp_insert s, have)
     else Some (s, have)) in
  let have := if have >? z_avail_in z then z_avail_in z else have in
  let* (s, z) :=
    (if have =? 0 then Some (s, z) else
     let* (z, data) := c_read_buf s z have in
     let* win := mb_write (d_window s) (d_strstart s) data in
     let s := set_d_window s win in
     let s := set_d_strstart s (u32 (d_strstart s + have)) in
     Some (add_insert s have, z)) in
  let s := upd_high_water s in
  K s z.

(** "A stored block from the window into pending" (second phase), then the continuation [K] (with last). *)
Definition ds_blk2 {A : Type} (s : dstate) (z : strm) (flush : Z) (K : dstate -> strm -> Z -> option A)
    : option A :=
  let have := stored_hdr s in
  let have := u32 (let a := u64 (d_pending_buf_size s - have) in if a >? MAX_STORED then MAX_STORED else a) in
  let min_block := if have >? d_w_size s then d_w_size s else have in
  let* _ := guard (in_long (d_strstart s - d_block_start s)) in
  let left := u32 (d_strstart s - d_block_start s) in
  let* (s, z, last) :=
  (if (left >=? min_block) ||
      ((negb (left =? 0) || (flush =? Z_FINISH)) && negb (flush =? Z_NO_FLUSH) &&
       (z_avail_in z =? 0) && (left <=? have)) then
     let len := if left >? have then have else left in
     let last := if (flush =? Z_FINISH) && (z_avail_in z =? 0) && (len =? left) then 1 else 0 in
     let* buf := (if len =? 0 then Some [] else mb_read (d_window s) (d_block_start s) len) in
     let* o := c_tr_stored_block (d_out s) buf len last in
     let s := set_d_out s o in
     let* _ := guard (in_long (d_block_start s + len)) in
     let s := set_d_block_start s (d_block_start s + len) in
     let* (s, z) := c_flush_pending s z in
     Some (s, z, last)
   else Some (s, z, 0)) in
  K s z last.

(** ** Frames *)

(** What the first phase and the second-phase block change: the output part (as [fp_keep]) and block_start. *)
Definition ob_keep (s : dstate) : dstate := set_d_block_start (fp_keep s) 0.

(** What c_ds_window and ds_fill2 change: the window, strstart, insert, block_start, high_water, matches. *)
Definition win_keep (s : dstate) : dstate :=
  set_d_matches (set_d_window (set_d_strstart (set_d_insert (set_d_block_start (set_d_high_water s 0) 0) 0) 0)
                              (mkMB [] [])) 0.

(** ** read_buf *)
Lemma read_buf_ok s z n :
  zall z -> adler_ok (d_wrap s) (z_adler z) -> 0 <= n ->
  exists z',
    c_read_buf s z n =
      Some (z', sublist (z_next_in z) (z_next_in z + Z.min n (z_avail_in z)) (z_in z)) /\
    zstep (d_wrap s) z z' (Z.min n (z_avail_in z)) [] /\
    z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\ z_total_out z' = z_total_out z.
Proof.
  intros Hz Ha Hn. pose proof Hz as Hz0. destruct Hz as [(Hb & Hni & Hai & Hl & Ht) (Ho & Hto & Hs)].
  unfold c_read_buf.
  replace (if z_avail_in z >? n then n else z_avail_in z) with (Z.min n (z_avail_in z))
    by (destruct (Z.gtb_spec (z_avail_in z) n); lia).
  set (k := Z.min n (z_avail_in z)).
  assert (Hk : 0 <= k <= z_avail_in z) by (unfold k; lia).
  destruct (Z.eqb_spec k 0) as [E|E].
  - exists z. rewrite E, Z.add_0_r, sublist_nil. split; [reflexivity|].
    split; [apply zstep_refl; auto|]. auto.
  - unfold rds. cbn [z_in z_next_in z_avail_in set_z_avail_in].
    replace ((0 <=? z_next_in z) && (0 <=? k) && (z_next_in z + k <=? Zlength (z_in z))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le; lia).
    cbn [bind].
    set (data := sublist (z_next_in z) (z_next_in z + k) (z_in z)).
    eexists. split; [reflexivity|].
    assert (Hu : u64 (z_total_out z + 0) = z_total_out z) by (rewrite Z.add_0_r; apply u64_id; lia).
    destruct (d_wrap s =? 1) eqn:W1; [|destruct (d_wrap s =? 2) eqn:W2];
      unfold set_z_total_in, set_z_next_in, set_z_adler, set_z_avail_in;
      cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg];
      (split; [unfold zstep; cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg];
               rewrite ?app_nil_r, ?Zlength_nil, ?Z.sub_0_r, ?Hu;
               repeat split; try reflexivity; try lia|repeat split]).
    + unfold adler_upd. rewrite W1. destruct Ha as [Ha _].
      apply Zlib.proof.adler32.Model.adler32_z_val_ref. apply Ha. apply Z.eqb_eq, W1.
    + unfold adler_upd. rewrite W1, W2. reflexivity.
    + unfold adler_upd. rewrite W1, W2. reflexivity.
Qed.

(** ** The parts *)

(** The hash chains at level 0 (whash): [chain_ok] survives a larger strstart, and a slide of the window by
    w_size (slide_hc) with strstart moved down by at most w_size. *)
Definition chain_stmt : Prop :=
  (forall s s', chain_ok s -> d_head s' = d_head s -> d_prev s' = d_prev s -> d_w_size s' = d_w_size s ->
     d_w_mask s' = d_w_mask s -> d_hash_size s' = d_hash_size s -> d_strstart s <= d_strstart s' ->
     chain_ok s') /\
  (forall s s', prm s -> wstruct s -> chain_ok s ->
     d_head s' = d_head s -> d_prev s' = d_prev s -> d_w_size s' = d_w_size s ->
     d_w_mask s' = d_w_mask s -> d_hash_size s' = d_hash_size s -> d_strstart s - d_w_size s <= d_strstart s' ->
     chain_ok (slide_hc s')).

(** _tr_stored_block of [len] bytes of [buf] (with [buf = []], [len = 0]: the empty block of the first phase). *)
Definition sblk_stmt : Prop :=
  forall o m buf len last,
    bits_ok o -> 0 <= last <= 1 -> 0 <= len <= Zlength buf -> len <= MAX_STORED -> bytes buf ->
    Zlength m = Zlength (o_buf o) ->
    o_pending o + (o_bi_valid o + 42) / 8 + len <= Zlength (o_buf o) ->
    exists o' m',
      c_tr_stored_block (o, m) buf len last = Some (o', m') /\
      o_pending o' = o_pending o + (o_bi_valid o + 42) / 8 + len /\
      o_bi_valid o' = 0 /\ bits_ok o' /\
      bitpos o' = 8 * ((bitpos o + 10) / 8) + 32 + 8 * len /\
      pb_grow o m o' m' /\
      (forall i, o_pending o <= i < o_pending o' -> Znth i m' = true).

(** The first phase: the do-while loop of direct stored blocks. *)
Definition dsloop_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> d_level s = 0 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    0 <= flush <= 5 -> z_avail_out z <= 1073741824 ->
    exists s1 z1 last evs k x,
      loop FUEL (ds_body flush (ds_min_block s)) (s, z) = Some (s1, z1, last) /\
      ob_keep s1 = ob_keep s /\
      d_block_start s <= d_block_start s1 <= d_strstart s /\
      outok s1 /\ quiet s1 /\
      pb_grow (tr_out (d_tr s)) (d_pbm s) (tr_out (d_tr s1)) (d_pbm s1) /\
      zstep (d_wrap s) z z1 k x /\ bytes x /\
      k + ub s = sum_len evs + ub s1 /\
      (0 < k -> d_block_start s1 = d_strstart s) /\
      ev_chain (Gb s (z_total_out z)) evs (Gb s1 (z_total_out z1)) /\
      Forall (ev_ok s flush) evs /\
      ((last = 0 /\ Forall (fun e => ev_last e = 0) evs /\
        (flush = Z_FINISH ->
         z_avail_out z1 < stored_hdr s1 + (d_strstart s - d_block_start s1) + z_avail_in z1)) \/
       (last = 1 /\ last_ev evs /\ flush = Z_FINISH /\ z_avail_in z1 = 0 /\
        d_block_start s1 = d_strstart s /\ d_bi_valid s1 = 0)).

(** The window update after the first phase ([used] bytes just before next_in were copied directly). *)
Definition dswin_stmt : Prop :=
  forall s z used,
    W s -> d_level s = 0 ->
    bytes (z_in z) -> 0 <= used <= z_next_in z -> z_next_in z <= Zlength (z_in z) -> used <= 1073741824 ->
    (0 < used -> d_block_start s = d_strstart s) ->
    exists s',
      c_ds_window s z used = Some s' /\ W s' /\ win_keep s' = win_keep s /\ ub s' = ub s.

(** The second-phase window refill. *)
Definition fill2_stmt : Prop :=
  forall s z,
    W s -> d_level s = 0 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    exists s' z' k,
      (forall A (K : dstate -> strm -> option A), ds_fill2 s z K = K s' z') /\ W s' /\ win_keep s' = win_keep s /\
      zstep (d_wrap s) z z' k [] /\ ub s' = ub s + k.

(** The second-phase stored block.  The hypothesis on Z_FINISH: the first phase stopped because the output
    space could not take everything. *)
Definition blk2_stmt : Prop :=
  forall s z flush,
    W s -> outok s -> quiet s -> d_level s = 0 -> zall z -> adler_ok (d_wrap s) (z_adler z) ->
    0 <= flush <= 5 ->
    (flush = Z_FINISH -> z_avail_out z < stored_hdr s + (d_strstart s - d_block_start s) + z_avail_in z) ->
    exists s' z' last evs x,
      (forall A (K : dstate -> strm -> Z -> option A), ds_blk2 s z flush K = K s' z' last) /\
      W s' /\ outok s' /\ ob_keep s' = ob_keep s /\
      zstep (d_wrap s) z z' 0 x /\ bytes x /\
      ub s = sum_len evs + ub s' /\
      ev_chain (Gb s (z_total_out z)) evs (Gb s' (z_total_out z')) /\
      Forall (ev_ok s flush) evs /\
      ((last = 0 /\ Forall (fun e => ev_last e = 0) evs /\ d_bi_valid s' <= 7) \/
       (last = 1 /\ last_ev evs /\ flush = Z_FINISH /\ z_avail_in z = 0 /\ ub s' = 0 /\
        d_bi_valid s' = 0 /\ z_avail_out z' = 0)).

(** ** c_deflate_stored through the pieces *)
Lemma c_deflate_stored_eq s z flush :
  c_deflate_stored s z flush =
  let used := z_avail_in z in
  let* (s, z, last) := loop FUEL (ds_body flush (ds_min_block s)) (s, z) in
  let used := u32 (used - z_avail_in z) in
  let* s := c_ds_window s z used in
  let s := upd_high_water s in
  if negb (last =? 0) then Some (set_d_bi_used s 8, z, finish_done) else
  if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z =? 0) &&
     (d_strstart s =? d_block_start s)
  then Some (s, z, block_done) else
  ds_fill2 s z (fun s z =>
  ds_blk2 s z flush (fun s z last =>
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started))).
Proof. reflexivity. Qed.

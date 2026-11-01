(** * Kit for the body proof of deflate_stored (Body_stored.v): the function's context, its statement split into
    fragments, the model split the same way, and the shapes of the fragment triples.

    The body of deflate_stored is

      min_block = ...; last = 0; used = s->strm->avail_in;
      do { BODY } while (last == 0);                          [S_body: one iteration, model DModel2.ds_body]
      used -= s->strm->avail_in;
      if (used) { ... }                                       [S_ifused: the window update, model c_ds_window]
      if (s->high_water < s->strstart) s->high_water = s->strstart;
      if (last) { s->bi_used = 8; return finish_done; }
      if (flush != Z_NO_FLUSH && ... ) return block_done;
      have = ...; ... return last ? finish_started : need_more;   [S_phase2: model ds_phase2]

    Fragment triples are proved in StoredBody.v, StoredWin.v, StoredTail.v; Body_stored.v puts them together.
    All fragments keep the whole stream [dfull] (DSpec.v) in their pre- and postconditions; the output space
    [rest] of a fragment's postcondition is [rest_after z z' rest] (the bytes not yet written). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Export Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Export Zlib.proof.deflate.Obligations.
Require Export Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The context of the body *)
Definition Delta_ds : tycontext := func_tycontext f_deflate_stored Vprog Gprog_compress nil.

(** ** Sub-statements of the body, by path: Ssequence a b: 0 = a, 1 = b; Sloop body incr: 0 = body, 1 = incr;
    Sifthenelse e a b: 1 = a, 2 = b. *)
Fixpoint sub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => sub a path'
    | Ssequence _ b, S O => sub b path'
    | Sloop a _, O => sub a path'
    | Sloop _ b, S O => sub b path'
    | Sifthenelse _ a _, S O => sub a path'
    | Sifthenelse _ _ b, S (S O) => sub b path'
    | _, _ => Sskip
    end
  end.

(** One iteration of the do-while loop (without the test [if (last == 0) ; else break;]). *)
Definition S_body : statement := sub (fn_body f_deflate_stored) [1;1;1;0;0]%nat.
(** The test of the do-while loop. *)
Definition S_incr : statement := sub (fn_body f_deflate_stored) [1;1;1;0;1]%nat.
(** [if (used) { ... s->block_start = s->strstart; }] *)
Definition S_ifused : statement := sub (fn_body f_deflate_stored) [1;1;1;1;1;0]%nat.
(** From [have = (unsigned)(s->window_size - s->strstart);] to the end (the final return). *)
Definition S_phase2 : statement := sub (fn_body f_deflate_stored) [1;1;1;1;1;1;1;1;1]%nat.

(** Show a fragment's statement concretely. *)
Ltac show_stmt := cbv [S_body S_incr S_ifused S_phase2 sub f_deflate_stored fn_body].

(** ** The model, split like the body *)
Section Model.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Definition ds_min_block (s : dstate) : Z :=
  u32 (let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a).

(** The second phase: fill the window, then a stored block from the window into pending. *)
Definition ds_phase2 (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
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
  if last =? 0 then Some (s, z, need_more) else Some (set_d_bi_used s 8, z, finish_started).

Lemma c_deflate_stored_eq s z flush :
  c_deflate_stored s z flush =
  let* (s1, z1, last) := loop FUEL (ds_body flush (ds_min_block s)) (s, z) in
  let used := u32 (z_avail_in z - z_avail_in z1) in
  let* s2 := c_ds_window s1 z1 used in
  let s3 := upd_high_water s2 in
  if negb (last =? 0) then Some (set_d_bi_used s3 8, z1, finish_done) else
  if negb (flush =? Z_NO_FLUSH) && negb (flush =? Z_FINISH) && (z_avail_in z1 =? 0) &&
     (d_strstart s3 =? d_block_start s3)
  then Some (s3, z1, block_done) else
  ds_phase2 s3 z1 flush.
Proof. reflexivity. Qed.
End Model.

(** ** The shapes of the fragment triples *)

(** The postcondition of one iteration [S_body] from (s, z), where the model's iteration is
    [ds_body flush min_block (s, z) = Some res]:
    - normal exit (the end of the body): the new state, [last] in the C variable, and
      [res = inl (s', z')] when last = 0, [res = inr (s', z', last)] otherwise;
    - break (one of the two [break]s, before anything is changed): [res = inr (s, z, 0)], the state unchanged. *)
Definition body_post (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (flush min_block used : Z) (res : (dstate * strm) + (dstate * strm * Z)) : ret_assert :=
  {| RA_normal :=
       EX s' : dstate, EX z' : strm, EX last : Z,
       PROP (res = (if last =? 0 then inl (s', z') else inr (s', z', last)))
       LOCAL (temp _min_block (vi min_block); temp _last (vi last); temp _used (vi used);
              gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv gv; deflate_globals gv);
     RA_break :=
       PROP (res = inr (s, z, 0))
       LOCAL (temp _min_block (vi min_block); temp _last (vi 0); temp _used (vi used);
              gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv);
     RA_continue := FF;
     RA_return := fun _ => FF |}.

(** The postcondition of the whole function, for the result [r] of a run from the stream [z]. *)
Definition ds_fun_post (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals)
    (z : strm) (r : dstate * strm * bstate) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_stored).

(** ** The output space *)

(** The output only grows. *)
Definition out_grows (z z' : strm) : Prop := exists bs, z_out z' = z_out z ++ bs.

Lemma rest_after_same z rest : rest_after z z rest = rest.
Proof.
  unfold rest_after. rewrite Z.sub_diag, sublist_same by lia. reflexivity.
Qed.

Lemma rest_after_trans z0 z1 z2 rest :
  out_grows z0 z1 -> out_grows z1 z2 ->
  Zlength (z_out z1) - Zlength (z_out z0) <= Zlength rest ->
  rest_after z1 z2 (rest_after z0 z1 rest) = rest_after z0 z2 rest.
Proof.
  intros [b1 E1] [b2 E2] Hl. unfold rest_after. rewrite E2, E1 in *.
  rewrite !Zlength_app in *. pose proof (Zlength_nonneg b1). pose proof (Zlength_nonneg b2).
  pose proof (Zlength_nonneg (z_out z0)).
  replace (Zlength (z_out z0) + Zlength b1 - Zlength (z_out z0)) with (Zlength b1) in * by lia.
  replace (Zlength (z_out z0) + Zlength b1 + Zlength b2 - (Zlength (z_out z0) + Zlength b1)) with (Zlength b2) by lia.
  replace (Zlength (z_out z0) + Zlength b1 + Zlength b2 - Zlength (z_out z0)) with (Zlength b1 + Zlength b2) by lia.
  rewrite Zlength_sublist by lia.
  destruct (Z_le_gt_dec (Zlength b2) (Zlength rest - Zlength b1)).
  - rewrite sublist_sublist by lia. f_equal; lia.
  - rewrite !sublist_nil_gen by lia. reflexivity.
Qed.

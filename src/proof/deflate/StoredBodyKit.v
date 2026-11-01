(** * Kit for ds_body_frag (StoredBody.v): one iteration of deflate_stored's first-phase loop, split after
    [last = ...] into three statement fragments with their models.

    S_body is a right-nested sequence of 17 elements (0: [len = MAX_STORED], ..., 8: [last = ...],
    9: [_tr_stored_block(s, (char * )0, 0L, last)], 10..13: the four length bytes of the dummy block,
    14: [flush_pending(s->strm)], 15: [if (left) { ... }] (window copy), 16: [if (len) { ... }] (input copy)).

    - [S_hdr] = elements 9..14 (model [c_hdr]),
    - [S_win] = element 15 (model [c_win]),
    - [S_in]  = element 16 (model [c_in]).
    [ds_body_split]: ds_body is the break tests followed by c_hdr, c_win, c_in. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredKit.
Require Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The fragments of S_body *)
Definition ones (n : nat) : list nat := repeat 1%nat n.
(** Element [k] (< 16) of S_body. *)
Definition S_el (k : nat) : statement := sub S_body (ones k ++ [0%nat]).
Definition S_call : statement := S_el 9.
Definition S_st1 : statement := S_el 10.
Definition S_st2 : statement := S_el 11.
Definition S_st3 : statement := S_el 12.
Definition S_st4 : statement := S_el 13.
Definition S_fp : statement := S_el 14.
(** [_tr_stored_block(...)]; the four length bytes; [flush_pending(s->strm)]. *)
Definition S_hdr : statement :=
  Ssequence S_call (Ssequence S_st1 (Ssequence S_st2 (Ssequence S_st3 (Ssequence S_st4 S_fp)))).
(** [if (left) { if (left > len) left = len; zmemcpy(next_out, window + block_start, left); ... len -= left; }] *)
Definition S_win : statement := S_el 15.
(** [if (len) { read_buf(s->strm, s->strm->next_out, len); next_out += len; ... }] *)
Definition S_in : statement := sub S_body (ones 16).

(** The tail of S_body after [last = ...]. *)
Definition S_tail : statement := sub S_body (ones 9).

Lemma S_tail_eq : S_tail =
  Ssequence S_call (Ssequence S_st1 (Ssequence S_st2 (Ssequence S_st3 (Ssequence S_st4
    (Ssequence S_fp (Ssequence S_win S_in)))))).
Proof. reflexivity. Qed.

(** Show the fragments' statements concretely. *)
Ltac show_frag :=
  unfold S_hdr, S_call, S_st1, S_st2, S_st3, S_st4, S_fp, S_win, S_in, S_tail, S_el, ones; show_stmt; simpl.

(** ** The models of the fragments *)
Section Model.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** [_tr_stored_block(s, (char * )0, 0L, last)], the four length bytes, [flush_pending(s->strm)]. *)
Definition c_hdr (s : dstate) (z : strm) (len last : Z) : option (dstate * strm) :=
  let* o := c_tr_stored_block (d_out s) [] 0 last in
  let s := set_d_out s o in
  let* s := c_pb_wr s (u64 (d_pending s - 4)) (u8 len) in
  let* s := c_pb_wr s (u64 (d_pending s - 3)) (u8 (Z.shiftr len 8)) in
  let* s := c_pb_wr s (u64 (d_pending s - 2)) (u8 (u32 (Z.lnot len))) in
  let* s := c_pb_wr s (u64 (d_pending s - 1)) (u8 (Z.shiftr (u32 (Z.lnot len)) 8)) in
  c_flush_pending s z.

(** The window copy; the result's third component is the new [len]. *)
Definition c_win (s : dstate) (z : strm) (len left : Z) : option (dstate * strm * Z) :=
  if left =? 0 then Some (s, z, len) else
  let left := if left >? len then len else left in
  let* bytes := mb_read (d_window s) (d_block_start s) left in
  let* z := out_put z bytes in
  let z := set_z_avail_out z (u32 (z_avail_out z - left)) in
  let z := set_z_total_out z (u64 (z_total_out z + left)) in
  let* _ := guard (in_long (d_block_start s + left)) in
  let s := set_d_block_start s (d_block_start s + left) in
  Some (s, z, u32 (len - left)).

(** The input copy. *)
Definition c_in (s : dstate) (z : strm) (len : Z) : option strm :=
  if len =? 0 then Some z else
  let* (z, data) := c_read_buf s z len in
  let* _ := guard (Zlength data =? len) in
  let* z := out_put z data in
  let z := set_z_avail_out z (u32 (z_avail_out z - len)) in
  Some (set_z_total_out z (u64 (z_total_out z + len))).

(** The values of the first part (elements 0..8). *)
Definition ds_have (s : dstate) (z : strm) : Z := u32 (z_avail_out z - stored_hdr s).
Definition ds_left (s : dstate) : Z := u32 (d_strstart s - d_block_start s).
Definition ds_len (s : dstate) (z : strm) : Z :=
  let left := ds_left s in
  let len := if MAX_STORED >? u64 (left + z_avail_in z) then u32 (left + z_avail_in z) else MAX_STORED in
  if len >? ds_have s z then ds_have s z else len.
Definition ds_break (s : dstate) (z : strm) (flush min_block : Z) : bool :=
  let left := ds_left s in let len := ds_len s z in
  (len <? min_block) &&
  (((len =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH) || negb (len =? u64 (left + z_avail_in z))).
Definition ds_last (s : dstate) (z : strm) (flush : Z) : Z :=
  if (flush =? Z_FINISH) && (ds_len s z =? u64 (ds_left s + z_avail_in z)) then 1 else 0.

End Model.

Lemma bind_some' {A B} (a : option A) (f : A -> option B) r :
  bind a f = Some r -> exists x, a = Some x /\ f x = Some r.
Proof. destruct a; simpl; [eauto | discriminate]. Qed.

(** ds_body = the break tests, then c_hdr, c_win, c_in. *)
Lemma ds_body_split flush min_block s z res :
  ds_body flush min_block (s, z) = Some res ->
  (z_avail_out z < stored_hdr s /\ res = inr (s, z, 0)) \/
  (stored_hdr s <= z_avail_out z /\ in_long (d_strstart s - d_block_start s) = true /\
   ((ds_break s z flush min_block = true /\ res = inr (s, z, 0)) \/
    (ds_break s z flush min_block = false /\
     exists s1 z1 s2 z2 len2 z3,
       c_hdr s z (ds_len s z) (ds_last s z flush) = Some (s1, z1) /\
       c_win s1 z1 (ds_len s z) (ds_left s) = Some (s2, z2, len2) /\
       c_in s2 z2 len2 = Some z3 /\
       res = (if ds_last s z flush =? 0 then inl (s2, z3) else inr (s2, z3, ds_last s z flush))))).
Proof.
  unfold ds_body. intros H.
  destruct (Z.ltb_spec (z_avail_out z) (stored_hdr s)) as [Hlt|Hge].
  { left. inversion H; auto. }
  right. split; [exact Hge|].
  apply bind_some' in H. destruct H as [[] [Hg H]].
  unfold guard in Hg. destruct (in_long _) eqn:El; [|discriminate]. split; [reflexivity|].
  change (u32 (z_avail_out z - stored_hdr s)) with (ds_have s z) in H.
  change (u32 (d_strstart s - d_block_start s)) with (ds_left s) in H.
  change (if (if MAX_STORED >? u64 (ds_left s + z_avail_in z) then u32 (ds_left s + z_avail_in z) else MAX_STORED)
             >? ds_have s z then ds_have s z else
          if MAX_STORED >? u64 (ds_left s + z_avail_in z) then u32 (ds_left s + z_avail_in z) else MAX_STORED)
    with (ds_len s z) in H.
  unfold ds_break. fold (ds_last s z flush) in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Eb end.
  { left. split; [reflexivity | inversion H; auto]. }
  right. split; [reflexivity|].
  set (len := ds_len s z) in *. set (left := ds_left s) in *. set (last := ds_last s z flush) in *.
  apply bind_some' in H. destruct H as [o [E1 H]].
  apply bind_some' in H. destruct H as [s1 [E2 H]].
  apply bind_some' in H. destruct H as [s2 [E3 H]].
  apply bind_some' in H. destruct H as [s3 [E4 H]].
  apply bind_some' in H. destruct H as [s4 [E5 H]].
  apply bind_some' in H. destruct H as [[s5 z5] [E6 H]].
  apply bind_some' in H. destruct H as [[[s6 z6] len6] [E7 H]].
  apply bind_some' in H. destruct H as [z7 [E8 H]].
  exists s5, z5, s6, z6, len6, z7.
  split; [unfold c_hdr; rewrite E1; cbn [bind]; rewrite E2; cbn [bind]; rewrite E3; cbn [bind];
          rewrite E4; cbn [bind]; rewrite E5; cbn [bind]; exact E6|].
  split; [exact E7|]. split; [exact E8|].
  destruct (last =? 0); inversion H; reflexivity.
Qed.

(** ** VST helpers *)

(** trees.c's part of the state without out_at, sym_at, dtype_at.  Keep it folded: it mentions trees.c's
    globals, which are not in deflate.c's type context (entailer refuses them). *)
Definition sb_trees_frame (cs : tstate * list bool) (sp : val) (gv : globals) : mpred :=
  (ltree_at (tr_ltree (fst cs)) sp * dtree_at (tr_dtree (fst cs)) sp * bltree_at (tr_bltree (fst cs)) sp *
   ldesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_ltree) sp) (tr_lmax (fst cs)) (gv Zlib.trees.code._static_l_desc) sp *
   ddesc_at (field_address t_ds (DOT Zlib.trees.code._dyn_dtree) sp) (tr_dmax (fst cs)) (gv Zlib.trees.code._static_d_desc) sp *
   bldesc_at (field_address t_ds (DOT Zlib.trees.code._bl_tree) sp) (tr_blmax (fst cs)) (gv Zlib.trees.code._static_bl_desc) sp *
   work_at (tr_wk (fst cs)) sp * lvl_at (fst cs) sp)%logic.

Lemma sb_trees_at_split cs sp pbp strmp gv :
  trees_at cs sp pbp strmp gv =
  (sb_trees_frame cs sp gv * out_at (tr_out (fst cs)) (snd cs) sp pbp * sym_at (fst cs) sp pbp *
   dtype_at (fst cs) sp strmp)%logic.
Proof. unfold trees_at, sb_trees_frame. apply pred_ext; cancel. Qed.

(** strm_at with the allocator fields (zutil.c's globals, not in deflate.c's type context) kept folded. *)
Definition sb_strm_zfuncs (strmp : val) (gv : globals) : mpred :=
  (@field_at DCS.CS Ews t_strm (DOT _zalloc) (gv _zcalloc) strmp *
   @field_at DCS.CS Ews t_strm (DOT _zfree) (gv _zcfree) strmp)%logic.

Lemma sb_strm_at_split z sp strmp pin pout msgv gv :
  strm_at z sp strmp pin pout msgv gv =
  (@field_at DCS.CS Ews t_strm (DOT _next_in) (offset_val (z_next_in z) pin) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_in) (vi (z_avail_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_in) (vl (z_total_in z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _next_out) (offset_val (Zlength (z_out z)) pout) strmp *
   @field_at DCS.CS Ews t_strm (DOT _avail_out) (vi (z_avail_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _total_out) (vl (z_total_out z)) strmp *
   @field_at DCS.CS Ews t_strm (DOT _msg) msgv strmp *
   @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
   sb_strm_zfuncs strmp gv *
   @field_at DCS.CS Ews t_strm (DOT _opaque) nullval strmp *
   @field_at DCS.CS Ews t_strm (DOT _adler) (vl (z_adler z)) strmp *
   @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp)%logic.
Proof. unfold strm_at, sb_strm_zfuncs. apply pred_ext; cancel. Qed.

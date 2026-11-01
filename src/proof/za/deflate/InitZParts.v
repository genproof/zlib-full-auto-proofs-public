(* Parts of the body proof of deflateInit2_ with a caller-supplied allocator: src/proof/deflate/InitParts.v's
   init_end / init_end_stream / init_ok_stream with the allocator's tokens and function pointers (the field
   groups are converted by InitParts' allocator-independent lemmas), deflateReset keeps the buffer sizes, and the
   arithmetic of the bytes the allocator holds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DModel3 Zlib.proof.deflate.DCS.
Require Import Zlib.deflate.code.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.InitKit Zlib.proof.deflate.InitKit2 Zlib.proof.deflate.InitFacts.
Require Import Zlib.proof.deflate.InitParts.
Local Open Scope logic.

Section ZA.
Context {ZA : zallocator}.

(** The failure path: the written fields (any values), the zero fields, the buffers each Z_NULL or allocated,
    the state's token are what deflateEnd needs ([dend_at_za] of [i_end_state]). *)
Lemma init_end_za (wbits mem : Z) (strmp sp pw pp ph pb : val)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : val) :
  let s := i_end_state wbits mem in
  let p := mkDP strmp sp pw pp ph pb nullval in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi (d_status s)) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) v1 sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) v2 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) v3 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) v4 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) v5 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) v6 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) v7 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) v8 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) v9 sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) v10 sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) v11 sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) v12 sp *
  zlate sp * zrest sp *
  @za_tok ZA DCS.CS t_ds sp *
  opt_alloc_za (tarray tuchar (4 * tr_lit_bufsize (d_tr s))) pb *
  opt_alloc_za (tarray tushort (d_hash_size s)) ph *
  opt_alloc_za (tarray tushort (d_w_size s)) pp *
  opt_alloc_za (tarray tuchar (2 * d_w_size s)) pw
  |-- dend_at_za s p.
Proof.
  intros s p. unfold zlate, zrest.
  eapply derives_trans.
  { repeat apply sepcon_derives;
    match goal with
    | |- @field_at _ _ _ (DOT ?f) _ _ |-- _ =>
        first [ constr_eq f _strm | constr_eq f _status | constr_eq f _window | constr_eq f _prev
              | constr_eq f _head | constr_eq f _pending_buf ];
        apply derives_refl
    | |- @field_at _ _ _ _ _ _ |-- _ => apply field_at_field_at_
    | |- _ => apply derives_refl
    end. }
  unfold dend_at_za. subst p. cbn [p_strm p_s p_pbuf p_head p_prev p_window].
  repeat match goal with
  | |- context [@field_at_ ?cs ?sh ?t ?gfs ?q] => generalize (@field_at_ cs sh t gfs q); intro
  | |- context [@field_at ?cs ?sh ?t ?gfs ?v ?q] => generalize (@field_at cs sh t gfs v q); intro
  | |- context [@za_tok ?z ?cs ?t ?q] => generalize (@za_tok z cs t q); intro
  | |- context [@opt_alloc_za ?z ?t ?q] => generalize (@opt_alloc_za z t q); intro
  end.
  cancel.
Qed.

(** The failure path: everything deflateEnd needs, as [dend_stream] with the pointers of the state. *)
Lemma init_end_stream_za (wbits mem : Z) (strmp sp pw pp ph pb dt : val) (gv : globals)
    (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : val) :
  field_compatible t_ds [] sp -> 0 <= i_wb9 wbits -> 0 <= mem + 6 ->
  let W := Z.shiftl 1 (i_wb9 wbits) in
  let HS := Z.shiftl 1 (mem + 7) in
  let LB := Z.shiftl 1 (mem + 6) in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (Vint (Int.repr 666)) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) v1 sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) v2 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) v3 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) v4 sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) v5 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) v6 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) v7 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) v8 sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) v9 sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) v10 sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) v11 sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) v12 sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp *
  zrest sp * zpad sp * @za_tok ZA DCS.CS t_ds sp *
  (if eq_dec pb nullval then emp else
     @za_tok ZA DCS.CS (tarray tuchar (4 * LB)) pb * @data_at_ DCS.CS Ews (tarray tuchar (4 * LB)) pb) *
  (if eq_dec ph nullval then emp else
     @za_tok ZA DCS.CS (tarray tushort HS) ph * @data_at_ DCS.CS Ews (tarray tushort HS) ph) *
  (if eq_dec pp nullval then emp else
     @za_tok ZA DCS.CS (tarray tushort W) pp * @data_at_ DCS.CS Ews (tarray tushort W) pp) *
  (if eq_dec pw nullval then emp else
     @za_tok ZA DCS.CS (tarray tuchar (2 * W)) pw * @data_at_ DCS.CS Ews (tarray tuchar (2 * W)) pw) *
  func_ptr' zalloc_spec za_alloc * func_ptr' zfree_spec za_free *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
  @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
  @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
  @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp
  |-- dend_stream (Some (i_end_state wbits mem)) (mkDP strmp sp pw pp ph pb nullval) strmp gv.
Proof.
  intros FC Hwb Hm W HS LB.
  assert (0 < W /\ 0 < HS /\ 0 < LB) as (PW & PH & PL)
    by (subst W HS LB; rewrite !Z.shiftl_1_l; repeat split; apply Z.pow_pos_nonneg; lia).
  sep_apply (zpad_ds_pad sp FC).
  assert (Z5 : @field_at DCS.CS Ews t_ds (DOT _sym_buf) nullval sp *
   @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _level) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _strategy) (vi 0) sp *
   @field_at DCS.CS Ews t_ds (DOT _method) (vi 0) sp |-- zlate sp) by (rewrite zlate_vals; cancel).
  sep_apply Z5.
  unfold dend_stream, zfuncs_za, za_funcs. cbn [p_strm p_s].
  pose proof (init_end_za wbits mem strmp sp pw pp ph pb v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12) as IE.
  cbv zeta in IE. unfold opt_alloc_za in IE.
  change (tr_lit_bufsize (d_tr (i_end_state wbits mem))) with LB in IE.
  change (d_hash_size (i_end_state wbits mem)) with HS in IE.
  change (d_w_size (i_end_state wbits mem)) with W in IE.
  change (d_status (i_end_state wbits mem)) with 666 in IE.
  sep_apply IE.
  Exists dt.
  entailer!. change (d_status (i_end_state wbits mem)) with 666.
  change (d_w_size (i_end_state wbits mem)) with W. change (d_hash_size (i_end_state wbits mem)) with HS.
  change (tr_lit_bufsize (d_tr (i_end_state wbits mem))) with LB. rep_lia.
Qed.

(** The success path: the state and the stream as [dstream_za] at level 0 (deflateReset's PRE). *)
Lemma init_ok_stream_za (level wbits mem strategy : Z) (strmp sp pw pp ph pb dt : val) (gv : globals) :
  -15 <= wbits -> i_bad level 8 wbits mem strategy = false -> s32_ok level -> s32_ok strategy -> s32_ok mem ->
  field_compatible t_ds [] sp ->
  let W := Z.shiftl 1 (i_wb9 wbits) in
  let HS := Z.shiftl 1 (mem + 7) in
  let LB := Z.shiftl 1 (mem + 6) in
  @field_at DCS.CS Ews t_ds (DOT _strm) strmp sp *
  @field_at DCS.CS Ews t_ds (DOT _status) (vi 42) sp *
  @field_at DCS.CS Ews t_ds (DOT _wrap) (vi (i_wr wbits)) sp *
  @field_at DCS.CS Ews t_ds (DOT _gzhead) nullval sp *
  @field_at DCS.CS Ews t_ds (DOT _w_bits) (vi (i_wb9 wbits)) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_size) (vi W) sp *
  @field_at DCS.CS Ews t_ds (DOT _w_mask) (vi (W - 1)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_bits) (vi (mem + 7)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_size) (vi HS) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_mask) (vi (HS - 1)) sp *
  @field_at DCS.CS Ews t_ds (DOT _hash_shift) (vi ((mem + 7 + 3 - 1) / 3)) sp *
  @field_at DCS.CS Ews t_ds (DOT _window) pw sp *
  @field_at DCS.CS Ews t_ds (DOT _prev) pp sp *
  @field_at DCS.CS Ews t_ds (DOT _head) ph sp *
  @field_at DCS.CS Ews t_ds (DOT _high_water) (vl 0) sp *
  @field_at DCS.CS Ews t_ds (DOT _lit_bufsize) (vi LB) sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf) pb sp *
  @field_at DCS.CS Ews t_ds (DOT _pending_buf_size) (vl (LB * 4)) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_buf) (offset_val LB pb) sp *
  @field_at DCS.CS Ews t_ds (DOT _sym_end) (vi ((LB - 1) * 3)) sp *
  @field_at DCS.CS Ews t_ds (DOT _level) (vi (i_lv level)) sp *
  @field_at DCS.CS Ews t_ds (DOT _strategy) (vi strategy) sp *
  @field_at DCS.CS Ews t_ds (DOT _method) (vi 8) sp *
  zrest sp * zpad sp *
  @data_at_ DCS.CS Ews (tarray tuchar (2 * W)) pw *
  @data_at DCS.CS Ews (tarray tushort W) (map vi (repeat 0 (Z.to_nat W))) pp *
  @data_at_ DCS.CS Ews (tarray tushort HS) ph *
  @data_at_ DCS.CS Ews (tarray tuchar (4 * LB)) pb *
  @za_tok ZA DCS.CS t_ds sp *
  @za_tok ZA DCS.CS (tarray tuchar (2 * W)) pw *
  @za_tok ZA DCS.CS (tarray tushort W) pp *
  @za_tok ZA DCS.CS (tarray tushort HS) ph *
  @za_tok ZA DCS.CS (tarray tuchar (4 * LB)) pb *
  func_ptr' zalloc_spec za_alloc * func_ptr' zfree_spec za_free *
  @field_at_ DCS.CS Ews t_strm (DOT _reserved) strmp *
  @field_at DCS.CS Ews t_strm (DOT _state) sp strmp *
  @field_at DCS.CS Ews t_strm (DOT _zalloc) za_alloc strmp *
  @field_at DCS.CS Ews t_strm (DOT _zfree) za_free strmp *
  @field_at DCS.CS Ews t_strm (DOT _opaque) za_opaque strmp *
  @field_at DCS.CS Ews t_strm (DOT _data_type) dt strmp
  |-- dstream_za 0 (Some (i_state level 8 wbits mem strategy)) strmp nullval gv.
Proof.
  intros Hw Hb Hl Hs Hm FC W HS LB.
  pose proof (init_d0 level 8 wbits mem strategy strmp sp pw pp ph pb dt gv Hw Hb Hl Hs ltac:(unfold s32_ok; rep_lia) Hm) as IE.
  cbv zeta in IE.
  set (s := i_state level 8 wbits mem strategy) in *.
  change (d_w_size s) with W in IE. change (d_hash_size s) with HS in IE.
  change (tr_lit_bufsize (d_tr s)) with LB in IE.
  change (Zlength (d_prev s)) with (Zlength (repeat 0 (Z.to_nat W))) in IE.
  change (d_prev s) with (repeat 0 (Z.to_nat W)) in IE.
  assert (HW0 : 0 <= W) by (apply (proj2 (Z.shiftl_nonneg 1 (i_wb9 wbits))); lia).
  replace (Zlength (repeat 0 (Z.to_nat W))) with W in IE by (rewrite Zlength_repeat', Z2Nat.id; lia).
  change (d_status s) with 42 in IE. change (d_wrap s) with (i_wr wbits) in IE.
  change (d_w_bits s) with (i_wb9 wbits) in IE. change (d_w_mask s) with (u32 (W - 1)) in IE.
  change (d_hash_bits s) with (mem + 7) in IE. change (d_hash_mask s) with (u32 (HS - 1)) in IE.
  change (d_hash_shift s) with ((mem + 7 + 3 - 1) / 3) in IE. change (d_high_water s) with 0 in IE.
  change (d_pending_buf_size s) with (u64 (LB * 4)) in IE.
  change (tr_sym_end (d_tr s)) with (u32 ((LB - 1) * 3)) in IE.
  change (tr_level (d_tr s)) with (i_lv level) in IE. change (tr_strategy (d_tr s)) with strategy in IE.
  change (d_method s) with 8 in IE.
  rewrite !vi_u32', vl_u64' in IE.
  pose proof (i_state_sizes level 8 wbits mem strategy Hw Hb) as SZ. fold s in SZ.
  unfold dstream_za, dstate_at', zfuncs_za, za_funcs. cbn [Z.eqb Pos.eqb].
  Exists (mkDP strmp sp pw pp ph pb nullval). cbn [p_strm p_gzhead p_s].
  sep_apply IE. sep_apply (zpad_ds_pad sp FC).
  unfold dtokens_za. cbn [p_s p_window p_prev p_head p_pbuf].
  change (d_w_size s) with W. change (d_hash_size s) with HS. change (tr_lit_bufsize (d_tr s)) with LB.
  entailer!.
Qed.

End ZA.

(** deflateReset keeps the sizes of the four buffers (the allocations deflateInit2_ made). *)
Ltac bind_all :=
  repeat match goal with
  | H : bind ?x ?f = Some _ |- _ =>
      let E := fresh "E" in destruct x eqn:E; cbn [bind] in H; [|discriminate H]
  | H : (if ?b then _ else _) = Some _ |- _ =>
      let E := fresh "E" in destruct b eqn:E; [|try discriminate H]
  | H : guard _ = Some _ |- _ => unfold guard in H
  | H : Some _ = Some _ |- _ => inv H
  | H : context [match ?p with pair _ _ => _ end] |- _ =>
      lazymatch type of p with prod _ _ => destruct p end
  end.

Lemma tr_init_lit_bufsize cs cs' : c_tr_init cs = Some cs' -> tr_lit_bufsize (fst cs') = tr_lit_bufsize (fst cs).
Proof.
  destruct cs as [t m]. unfold c_tr_init, c_init_block. intros H.
  bind_all; reflexivity.
Qed.

Definition bsizes (s : dstate) : Z * Z * Z := (d_w_size s, d_hash_size s, tr_lit_bufsize (d_tr s)).

Lemma resetkeep_sizes s z s' z' r : c_deflateResetKeep s z = Some (s', z', r) -> bsizes s' = bsizes s.
Proof.
  unfold c_deflateResetKeep. intros H.
  destruct (bad_state s); [inv H; reflexivity|].
  bind_all.
  all: match goal with Et : c_tr_init _ = Some _ |- _ => apply tr_init_lit_bufsize in Et end.
  all: unfold bsizes; cbn in *; congruence.
Qed.

Lemma lm_init_sizes s s' : c_lm_init s = Some s' -> bsizes s' = bsizes s.
Proof.
  unfold c_lm_init, c_clear_hash. intros H. bind_all.
  all: reflexivity.
Qed.

Lemma reset_sizes s z s' z' r : c_deflateReset s z = Some (s', z', r) ->
  d_w_size s' = d_w_size s /\ d_hash_size s' = d_hash_size s /\ tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s).
Proof.
  unfold c_deflateReset. intros H.
  destruct (c_deflateResetKeep s z) as [[[s1 z1] r1]|] eqn:E1; cbn [bind] in H; [|discriminate].
  apply resetkeep_sizes in E1.
  destruct (r1 =? Z_OK).
  - destruct (c_lm_init s1) as [s2|] eqn:E2; cbn [bind] in H; [|discriminate]. inv H.
    apply lm_init_sizes in E2. unfold bsizes in *.
    injection E1 as ? ? ?. injection E2 as ? ? ?. repeat split; congruence.
  - inv H. unfold bsizes in E1. injection E1 as ? ? ?. auto.
Qed.

(** The bytes the allocator holds after appending events. *)
Definition zev_delta (e : zev) : Z := match e with ZAlloc n => n | ZFree n => - n | ZFail => 0 end.

Lemma za_now_app tr l : za_now (tr ++ l) = za_now tr + fold_right (fun e a => zev_delta e + a) 0 l.
Proof.
  revert tr. induction l as [|e l IH]; intros tr.
  - rewrite app_nil_r. simpl. lia.
  - replace (tr ++ e :: l) with ((tr ++ [e]) ++ l) by (rewrite <- app_assoc; reflexivity).
    rewrite IH. destruct e; [rewrite za_now_alloc | rewrite za_now_free | rewrite za_now_fail]; simpl; lia.
Qed.

(** The event of a call of zalloc that returned q: an allocation of n bytes, or a failed allocation if q is
    Z_NULL. *)
Definition zalloc_ev (q : val) (n : Z) : list zev := if eq_dec q nullval then [ZFail] else [ZAlloc n].

Lemma zalloc_ev_null n : zalloc_ev nullval n = [ZFail].
Proof. unfold zalloc_ev. rewrite if_true by auto. reflexivity. Qed.
Lemma zalloc_ev_nn q n : q <> nullval -> zalloc_ev q n = [ZAlloc n].
Proof. intros. unfold zalloc_ev. rewrite if_false by auto. reflexivity. Qed.

Lemma za_now_zalloc_ev tr q n : za_now (tr ++ zalloc_ev q n) = za_now tr + (if eq_dec q nullval then 0 else n).
Proof.
  unfold zalloc_ev. destruct (eq_dec q nullval).
  - rewrite za_now_fail. lia.
  - rewrite za_now_alloc. reflexivity.
Qed.

Lemma za_now_dend_free tr q n : za_now (tr ++ dend_free q n) = za_now tr - (if eq_dec q nullval then 0 else n).
Proof.
  unfold dend_free. destruct (eq_dec q nullval).
  - rewrite app_nil_r. lia.
  - rewrite za_now_free. reflexivity.
Qed.

(** zalloc_spec's postcondition with the events as one list. *)
Lemma zalloc_post_eq {cs : compspecs} {ZA : zallocator} gv tr n t q :
  (if eq_dec q nullval then za_res gv (tr ++ [ZFail])
   else za_res gv (tr ++ [ZAlloc n]) * @za_tok ZA cs t q * @data_at_ cs Ews t q) =
  za_res gv (tr ++ zalloc_ev q n) * (if eq_dec q nullval then emp else @za_tok ZA cs t q * @data_at_ cs Ews t q).
Proof.
  unfold zalloc_ev. destruct (eq_dec q nullval).
  - rewrite sepcon_emp. reflexivity.
  - rewrite sepcon_assoc. reflexivity.
Qed.

(** A failed allocation among the events: some zalloc returned Z_NULL. *)
Lemma za_failed_zalloc_ev q n : za_failed (zalloc_ev q n) = (if eq_dec q nullval then true else false).
Proof. unfold zalloc_ev. destruct (eq_dec q nullval); reflexivity. Qed.

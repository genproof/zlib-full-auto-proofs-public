(** * Kit for deflate_slow's body (Body_slow.v): statement fragments of f_deflate_slow, the model split like the
    body, and the statements of the fragment lemmas (proved in SlowIns.v, SlowLm.v, SlowDist.v, SlowLoop.v,
    SlowLit.v).

    Paths: [SL path] is the sub-statement of f_deflate_slow's body at [path] (Ssequence: 0 = first, 1 = second;
    Sloop: 0 = body, 1 = increment; Sifthenelse: 1 = then, 2 = else). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition Delta_sl : tycontext := func_tycontext f_deflate_slow Vprog Gprog_compress nil.

Fixpoint ssub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => ssub a path'
    | Ssequence _ b, S O => ssub b path'
    | Sloop a _, O => ssub a path'
    | Sloop _ b, S O => ssub b path'
    | Sifthenelse _ a _, S O => ssub a path'
    | Sifthenelse _ _ b, S (S O) => ssub b path'
    | _, _ => Sskip
    end
  end.

Definition SL (path : list nat) : statement := ssub (fn_body f_deflate_slow) path.

(** ** The fragments *)
(** One iteration of the main loop (after its leading Sskip). *)
Definition S_iter := SL [0;0;1]%nat.
(** [if (s->lookahead < MIN_LOOKAHEAD) { fill_window(s); ... }] *)
Definition S_refill := SL [0;0;1;0]%nat.
(** [hash_head = NIL;] *)
Definition S_hh0 := SL [0;0;1;1;0]%nat.
(** [if (s->lookahead >= MIN_MATCH) { INSERT_STRING(s, s->strstart, hash_head); }] *)
Definition S_inshead := SL [0;0;1;1;1;0]%nat.
(** INSERT_STRING(s, s->strstart, hash_head) of the head (the then-branch of S_inshead). *)
Definition S_ins1 := SL [0;0;1;1;1;0;1;1]%nat.
(** [s->prev_length = s->match_length, s->prev_match = s->match_start;] *)
Definition S_prev := SL [0;0;1;1;1;1;0]%nat.
(** [s->match_length = MIN_MATCH-1;] *)
Definition S_ml := SL [0;0;1;1;1;1;1;0]%nat.
(** [if (hash_head != NIL && ...) { s->match_length = longest_match (s, hash_head); if (...) ... }] *)
Definition S_lmb := SL [0;0;1;1;1;1;1;1;0]%nat.
(** The previous-match / literal / wait decision. *)
Definition S_br := SL [0;0;1;1;1;1;1;1;1]%nat.
(** [s->prev_length >= MIN_MATCH && s->match_length <= s->prev_length] into _t'22. *)
Definition S_cond := SL [0;0;1;1;1;1;1;1;1;0]%nat.
(** The previous-match branch. *)
Definition S_match := SL [0;0;1;1;1;1;1;1;1;1;1]%nat.
(** [uInt max_insert = s->strstart + s->lookahead - MIN_MATCH;] *)
Definition S_maxins := SL [0;0;1;1;1;1;1;1;1;1;1;0]%nat.
(** [_tr_tally_dist(s, s->strstart - 1 - s->prev_match, s->prev_length - MIN_MATCH, bflush);] *)
Definition S_dist := SL [0;0;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [s->lookahead -= s->prev_length - 1;] *)
Definition S_lookst := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [s->prev_length -= 2;] *)
Definition S_plst := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [do { if (++s->strstart <= max_insert) { INSERT_STRING(s, s->strstart, hash_head); } }
     while (--s->prev_length != 0);] *)
Definition S_dowhile := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** INSERT_STRING(s, s->strstart, hash_head) inside the do-while. *)
Definition S_ins2 := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1]%nat.
(** [s->match_available = 0;] *)
Definition S_ma0 := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [s->match_length = MIN_MATCH-1;] *)
Definition S_ml2 := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [s->strstart++;] *)
Definition S_ssinc := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [if (bflush) FLUSH_BLOCK(s, 0);] *)
Definition S_ifbf := SL [0;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat.
(** The lookahead / prev_length updates, the do-while and the three stores, left-nested. *)
Definition S_insloop : statement :=
  Ssequence (Ssequence (Ssequence (Ssequence (Ssequence S_lookst S_plst) S_dowhile) S_ma0) S_ml2) S_ssinc.
(** [else if (s->match_available) { ... } else { ... }] *)
Definition S_else := SL [0;0;1;1;1;1;1;1;1;1;2]%nat.
(** The literal branch. *)
Definition S_litb := SL [0;0;1;1;1;1;1;1;1;1;2;1;1]%nat.
(** [_tr_tally_lit(s, s->window[s->strstart - 1], bflush);] *)
Definition S_lit := SL [0;0;1;1;1;1;1;1;1;1;2;1;1;0]%nat.
(** [if (bflush) { FLUSH_BLOCK_ONLY(s, 0); } s->strstart++; s->lookahead--; if (s->strm->avail_out == 0) return need_more;] *)
Definition S_litrest := SL [0;0;1;1;1;1;1;1;1;1;2;1;1;1]%nat.
(** [s->match_available = 1; s->strstart++; s->lookahead--;] *)
Definition S_avail := SL [0;0;1;1;1;1;1;1;1;1;2;1;2]%nat.
(** After the loop: [if (s->match_available) { _tr_tally_lit(...); s->match_available = 0; }] *)
Definition S_tlit := SL [1;0]%nat.
(** [s->insert = ...; if (flush == Z_FINISH) {...} if (s->sym_next) FLUSH_BLOCK(s, 0); return block_done;] *)
Definition S_tail := SL [1;1]%nat.

(** Show a fragment's statement concretely. *)
Ltac show_sl := cbv [S_iter S_refill S_hh0 S_inshead S_ins1 S_prev S_ml S_lmb S_br S_cond S_match S_maxins S_dist
  S_lookst S_plst S_dowhile S_ins2 S_ma0 S_ml2 S_ssinc S_ifbf S_insloop S_else S_litb S_lit S_litrest S_avail
  S_tlit S_tail SL ssub f_deflate_slow fn_body].

Lemma body_eq : fn_body f_deflate_slow = Ssequence (Sloop (Ssequence Sskip S_iter) Sskip) (Ssequence S_tlit S_tail).
Proof. reflexivity. Qed.
Lemma iter_eq : S_iter = Ssequence S_refill (Ssequence S_hh0 (Ssequence S_inshead (Ssequence S_prev
  (Ssequence S_ml (Ssequence S_lmb S_br))))).
Proof. reflexivity. Qed.
Lemma match_eq : S_match = Ssequence S_maxins (Ssequence S_dist (Ssequence S_lookst (Ssequence S_plst
  (Ssequence S_dowhile (Ssequence S_ma0 (Ssequence S_ml2 (Ssequence S_ssinc S_ifbf))))))).
Proof. reflexivity. Qed.
Lemma litb_eq : S_litb = Ssequence S_lit S_litrest.
Proof. reflexivity. Qed.

(** ** The model, split like the body *)
Section Model.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** dsl_step after INSERT_STRING up to the decision: prev_length / prev_match / match_length, longest_match and the
    FILTERED / TOO_FAR test ([S_prev; S_ml; S_lmb]). *)
Definition dsl_prep (s : dstate) (hash_head : Z) : option dstate :=
  let s := set_d_prev_length s (d_match_length s) in
  let s := set_d_prev_match s (d_match_start s) in
  let s := set_d_match_length s (MIN_MATCH - 1) in
  if negb (hash_head =? NIL) && (d_prev_length s <? d_max_lazy_match s) &&
     (u32 (d_strstart s - hash_head) <=? max_dist s) then
    let* (s, ml) := c_longest_match s hash_head in
    let s := set_d_match_length s ml in
    if (d_match_length s <=? 5) &&
       ((d_strategy s =? Z_FILTERED) ||
        ((d_match_length s =? MIN_MATCH) && (u32 (d_strstart s - d_match_start s) >? TOO_FAR)))
    then Some (set_d_match_length s (MIN_MATCH - 1))
    else Some s
  else Some s.

(** The decision ([S_br]). *)
Definition dsl_decide (s : dstate) (z : strm) : option ((dstate * strm) + dexit) :=
  if (d_prev_length s >=? MIN_MATCH) && (d_match_length s <=? d_prev_length s) then
    let max_insert := u32 (d_strstart s + d_lookahead s - MIN_MATCH) in
    let* (s, bflush) := c_dtally_dist s (u32 (d_strstart s - 1 - d_prev_match s))
                                        (u32 (d_prev_length s - MIN_MATCH)) in
    let s := set_d_lookahead s (u32 (d_lookahead s - u32 (d_prev_length s - 1))) in
    let s := set_d_prev_length s (u32 (d_prev_length s - 2)) in
    let* s := loop FUEL (dsl_insert_body max_insert) s in
    let s := set_d_match_available s 0 in
    let s := set_d_match_length s (MIN_MATCH - 1) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    c_bflush s z bflush
  else if negb (d_match_available s =? 0) then
    let* c := mb_rd (d_window s) (u32 (d_strstart s - 1)) in
    let* (s, bflush) := c_dtally_lit s c in
    let* (s, z) := (if bflush then c_flush_block_only s z 0 else Some (s, z)) in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
    if z_avail_out z =? 0 then Some (inr (s, z, Some need_more)) else Some (inl (s, z))
  else
    let s := set_d_match_available s 1 in
    let s := set_d_strstart s (u32 (d_strstart s + 1)) in
    Some (inl (set_d_lookahead s (u32 (d_lookahead s - 1)), z)).

Lemma dsl_step_eq s z : dsl_step s z =
  let* (s, hh) := c_insert_head s in let* s := dsl_prep s hh in dsl_decide s z.
Proof. reflexivity. Qed.

(** The previous-match branch around its do-while ([S_lookst; S_plst] before, [S_ma0; S_ml2; S_ssinc] after). *)
Definition dsl_max_insert (s : dstate) : Z := u32 (d_strstart s + d_lookahead s - MIN_MATCH).
Definition dsl_pre_loop (s : dstate) : dstate :=
  let s := set_d_lookahead s (u32 (d_lookahead s - u32 (d_prev_length s - 1))) in
  set_d_prev_length s (u32 (d_prev_length s - 2)).
Definition dsl_post_loop (s : dstate) : dstate :=
  let s := set_d_match_available s 0 in
  let s := set_d_match_length s (MIN_MATCH - 1) in
  set_d_strstart s (u32 (d_strstart s + 1)).

(** After the loop: the pending literal ([S_tlit]). *)
Definition dsl_tlit (s : dstate) : option dstate :=
  if negb (d_match_available s =? 0) then
    let* c := mb_rd (d_window s) (u32 (d_strstart s - 1)) in
    let* (s, _) := c_dtally_lit s c in
    Some (set_d_match_available s 0)
  else Some s.

Lemma c_insert_head_range s s' hh : dstate_ranges s -> c_insert_head s = Some (s', hh) -> 0 <= hh < 65536.
Proof.
  intros Hr H. unfold c_insert_head in H.
  destruct (d_lookahead s >=? MIN_MATCH).
  - unfold c_insert_string in H. inv_bind H. inv_bind H. inv_bind H.
    inv_bind H. inv_bind H. inversion H; subst hh. clear H.
    match goal with Hrd : rd _ _ = Some x1 |- _ => revert Hrd end. intro Hrd.
    unfold rd in Hrd. destruct (in_range _ _) eqn:Ei; [|discriminate]. inversion Hrd; subst.
    unfold in_range in Ei. apply andb_prop in Ei. destruct Ei as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn in E1, E2 |- *.
    destruct Hr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
    rewrite Forall_forall in Hh. apply Hh. apply Znth_In. lia.
  - inversion H; subst. unfold NIL. lia.
Qed.

End Model.

(** The INSERT_STRING inside the do-while, as a hypothesis of the do-while's lemma (SlowLoop.v); proved in
    SlowIns.v. *)
Definition ins2_ok : Prop :=
  forall (Espec : OracleKind) (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (b : val) (mi : Z) (s s' : dstate) (z : strm) (hh : Z),
  c_insert_string s (d_strstart s) = Some (s', hh) ->
  @semax DCS.CS Espec Delta_sl
    (PROP () LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    S_ins2
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush b; temp _max_insert (vi mi); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).

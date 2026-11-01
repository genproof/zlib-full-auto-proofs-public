(** * Kit for deflate_fast's body (Body_fast.v): the parts of the loop body, cut out of [f_deflate_fast]

    Each part is a statement of the loop body with a pre/postcondition on [dfull] (the stream and the output
    space unchanged: no part touches them) and the model of DModel2.df_step cut at the same place:
    - [fast_ins1]: the INSERT_STRING(s, s->strstart, hash_head) of [if (s->lookahead >= MIN_MATCH)];
    - [fast_ins2]: the INSERT_STRING(s, s->strstart, hash_head) inside the do-while insertion loop;
    - [fast_lm]: [if (hash_head != NIL && s->strstart - hash_head <= MAX_DIST(s))
                    s->match_length = longest_match(s, hash_head);];
    - [fast_dist]: [_tr_tally_dist(s, s->strstart - s->match_start, s->match_length - MIN_MATCH, bflush);];
    - [fast_after]: [s->lookahead -= s->match_length; if (s->match_length <= s->max_insert_length &&
                     s->lookahead >= MIN_MATCH) INSL else UH];
    - [fast_insl]: [s->match_length--; do { s->strstart++; INSERT_STRING(..); } while (--s->match_length != 0);
                    s->strstart++;];
    - [fast_uh]: [s->strstart += s->match_length; s->match_length = 0; s->ins_h = s->window[s->strstart];
                  UPDATE_HASH(s, s->ins_h, s->window[s->strstart + 1]);];
    - [fast_lit]: the literal case [_tr_tally_lit(s, s->window[s->strstart], bflush); s->lookahead--;
                  s->strstart++;].
    The part lemmas ([fast_X_ok : fast_X_stmt]) are proved in FastIns1.v, FastIns2.v, FastLm.v, FastDist.v, FastAfter.v,
    FastInsl.v, FastUh.v, FastLit.v; Body_fast.v assembles them ([fa_seq], [fa_apply]). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** ** The statements *)

Definition fast_body : statement := Eval cbv [f_deflate_fast fn_body] in fn_body f_deflate_fast.

(** INSERT_STRING at the top of an iteration (the then-branch of [if (s->lookahead >= MIN_MATCH)]). *)
Definition fast_ins1 : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oge (Etempvar _t'127 tuint) (Econst_int (Int.repr 3) tint) tint) ?a Sskip] => exact a
  end).

(** INSERT_STRING in the body of the do-while insertion loop (after [s->strstart++]). *)
Definition fast_ins2 : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sloop (Ssequence (Ssequence (Sset _t'104 _) _) ?a) _] => exact a
  end).

(** The longest_match call with its test. *)
Definition fast_lm : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Ssequence ?a (Ssequence (Ssequence (Sset _t'64 _) _) _)] => exact a
  end).

(** _tr_tally_dist (the first statement of the match case). *)
Definition fast_dist : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oge (Etempvar _t'64 tuint) (Econst_int (Int.repr 3) tint) tint)
               (Ssequence ?a _) _] => exact a
  end).

(** The rest of the match case. *)
Definition fast_after : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oge (Etempvar _t'64 tuint) (Econst_int (Int.repr 3) tint) tint)
               (Ssequence _ ?a) _] => exact a
  end).

(** The literal case. *)
Definition fast_lit : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Ebinop Oge (Etempvar _t'64 tuint) (Econst_int (Int.repr 3) tint) tint) _ ?a] => exact a
  end).

(** The insertion of the matched strings (then-branch of [if (t'11)]). *)
Definition fast_insl : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Etempvar _t'11 tint) ?a _] => exact a
  end).

(** Skipping the matched strings (else-branch of [if (t'11)]). *)
Definition fast_uh : statement := ltac:(
  let b := eval cbv [fast_body] in fast_body in
  lazymatch b with
  | context [Sifthenelse (Etempvar _t'11 tint) _ ?a] => exact a
  end).

Definition Delta_fast : tycontext := func_tycontext f_deflate_fast Vprog Gprog_compress nil.

(** ** Pre/postconditions *)

(** The locals kept by every part. *)
Definition fa_base (p : dptrs) (flush : Z) (gv : globals) : list localdef :=
  [gvars gv; temp _s (p_s p); temp _flush (vi flush)].

Definition fa (L : list localdef) (s : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) : environ -> mpred :=
  PROPx [] (LOCALx L (SEPx [dfull s z p pin pout ish R msgv gv; deflate_globals gv])).

(** ** The models of the parts (pieces of DModel2.df_step) *)

(** [if (hash_head != NIL && s->strstart - hash_head <= MAX_DIST(s)) s->match_length = longest_match(..)] *)
Definition fast_lm_m (s : dstate) (h : Z) : option dstate :=
  if andb (negb (h =? NIL)) (u32 (d_strstart s - h) <=? max_dist s) then
    let* (s, ml) := c_longest_match s h in Some (set_d_match_length s ml)
  else Some s.

Definition fast_insl_m (s : dstate) : option dstate :=
  let s := set_d_match_length s (u32 (d_match_length s - 1)) in
  let* s := loop FUEL df_insert_body s in
  Some (set_d_strstart s (u32 (d_strstart s + 1))).

Definition fast_uh_m (s : dstate) : option dstate :=
  let s := set_d_strstart s (u32 (d_strstart s + d_match_length s)) in
  let s := set_d_match_length s 0 in
  let* c0 := mb_rd (d_window s) (d_strstart s) in
  let s := set_d_ins_h s c0 in
  let* _ := guard (d_hash_shift s <? 32) in
  let* c1 := mb_rd (d_window s) (u32 (d_strstart s + 1)) in
  Some (set_d_ins_h s (update_hash s (d_ins_h s) c1)).

Definition fast_after_m (s : dstate) : option dstate :=
  let s := set_d_lookahead s (u32 (d_lookahead s - d_match_length s)) in
  if andb (d_match_length s <=? d_max_lazy_match s) (d_lookahead s >=? MIN_MATCH) then fast_insl_m s
  else fast_uh_m s.

Definition fast_lit_m (s : dstate) : option (dstate * bool) :=
  let* c := mb_rd (d_window s) (d_strstart s) in
  let* (s, bflush) := c_dtally_lit s c in
  let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
  Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush).

(** ** The part lemmas (statements) *)

Definition fast_ins1_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush h : Z),
  c_insert_string s (d_strstart s) = Some (s', h) ->
  semax Delta_fast (fa (fa_base p flush gv) s z p pin pout ish R msgv gv) fast_ins1
    (normal_ret_assert (fa (temp _hash_head (vi h) :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_ins2_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush h : Z) (vb : val),
  c_insert_string s (d_strstart s) = Some (s', h) ->
  semax Delta_fast (fa (temp _bflush vb :: fa_base p flush gv) s z p pin pout ish R msgv gv) fast_ins2
    (normal_ret_assert (fa (temp _bflush vb :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_lm_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush h : Z),
  0 <= h < 65536 ->
  fast_lm_m s h = Some s' ->
  semax Delta_fast (fa (temp _hash_head (vi h) :: fa_base p flush gv) s z p pin pout ish R msgv gv) fast_lm
    (normal_ret_assert (fa (fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_dist_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush : Z) (bf : bool),
  c_dtally_dist s (u32 (d_strstart s - d_match_start s)) (u32 (d_match_length s - MIN_MATCH)) = Some (s', bf) ->
  semax Delta_fast (fa (fa_base p flush gv) s z p pin pout ish R msgv gv) fast_dist
    (normal_ret_assert (fa (temp _bflush (vi (Z.b2z bf)) :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_insl_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush : Z) (vb : val),
  fast_insl_m s = Some s' ->
  semax Delta_fast (fa (temp _bflush vb :: fa_base p flush gv) s z p pin pout ish R msgv gv) fast_insl
    (normal_ret_assert (fa (temp _bflush vb :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_uh_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush : Z) (vb : val),
  fast_uh_m s = Some s' ->
  semax Delta_fast (fa (temp _bflush vb :: fa_base p flush gv) s z p pin pout ish R msgv gv) fast_uh
    (normal_ret_assert (fa (temp _bflush vb :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_after_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush : Z) (vb : val),
  fast_after_m s = Some s' ->
  semax Delta_fast (fa (temp _bflush vb :: fa_base p flush gv) s z p pin pout ish R msgv gv) fast_after
    (normal_ret_assert (fa (temp _bflush vb :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

Definition fast_lit_stmt : Prop :=
  forall {Espec : OracleKind} (s s' : dstate) (z : strm) (p : dptrs) (pin pout : val) (ish : share)
    (R : list val) (msgv : val) (gv : globals) (flush : Z) (bf : bool),
  fast_lit_m s = Some (s', bf) ->
  semax Delta_fast (fa (fa_base p flush gv) s z p pin pout ish R msgv gv) fast_lit
    (normal_ret_assert (fa (temp _bflush (vi (Z.b2z bf)) :: fa_base p flush gv) s' z p pin pout ish R msgv gv)).

(** ** Using a part lemma *)

Lemma fa_apply {Espec : OracleKind} Delta (P P' : environ -> mpred) c (Q : environ -> mpred) R :
  ENTAIL Delta, P |-- P' ->
  semax Delta P' c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
  intros HP H. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | exact H]; destruct R; simpl.
  - intros x. apply andp_left2, derives_refl.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

(** A part lemma (in [Delta_fast]) as the first statement of a sequence. *)
Lemma fa_seq {Espec : OracleKind} Delta P P' Q c1 c2 R :
  tycontext_sub Delta_fast Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_fast P' c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros HT HP H1 H2. eapply semax_seq; [|exact H2].
  apply (fa_apply Delta P P' c1 Q R HP). eapply semax_Delta_subsumption; eauto.
Qed.

(** A part lemma as the whole statement (a branch of an [if]). *)
Lemma fa_last {Espec : OracleKind} Delta P P' Q c R :
  tycontext_sub Delta_fast Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_fast P' c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
  intros HT HP H1. apply (fa_apply Delta P P' c Q R HP). eapply semax_Delta_subsumption; eauto.
Qed.

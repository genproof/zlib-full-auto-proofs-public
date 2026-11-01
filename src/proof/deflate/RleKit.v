(** * Kit for deflate_rle's body (Body_rle.v): statement fragments of f_deflate_rle, the model split like the
    body, and the statements of the fragment lemmas.

    Paths: [RL path] is the sub-statement of f_deflate_rle's body at [path] (Ssequence: 0 = first, 1 = second;
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

Definition Delta_rle : tycontext := func_tycontext f_deflate_rle Vprog Gprog_compress nil.

Fixpoint rsub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => rsub a path'
    | Ssequence _ b, S O => rsub b path'
    | Sloop a _, O => rsub a path'
    | Sloop _ b, S O => rsub b path'
    | Sifthenelse _ a _, S O => rsub a path'
    | Sifthenelse _ _ b, S (S O) => rsub b path'
    | _, _ => Sskip
    end
  end.

Definition RL (path : list nat) : statement := rsub (fn_body f_deflate_rle) path.

(** ** The fragments *)
(** One iteration of the main loop (after its leading Sskip). *)
Definition R_iter := RL [0;0;1]%nat.
(** [if (s->lookahead <= MAX_MATCH) { fill_window(s); ... }] *)
Definition R_refill := RL [0;0;1;0]%nat.
(** [s->match_length = 0;] *)
Definition R_ml0 := RL [0;0;1;1;0]%nat.
(** [if (s->lookahead >= MIN_MATCH && s->strstart > 0) { scan = ...; prev = *scan; if (...) { strend = ...;
     do {} while (...); s->match_length = ...; if (...) s->match_length = s->lookahead; } }] *)
Definition R_scan := RL [0;0;1;1;1;0]%nat.
(** [if (s->match_length >= MIN_MATCH) {...} else {...}] (with the read of match_length before it) *)
Definition R_tally := RL [0;0;1;1;1;1;0]%nat.
(** The match case: [_tr_tally_dist(s, 1, s->match_length - MIN_MATCH, bflush); s->lookahead -= s->match_length;
     s->strstart += s->match_length; s->match_length = 0;] *)
Definition R_dist := RL [0;0;1;1;1;1;0;1;1]%nat.
(** The literal case: [_tr_tally_lit(s, s->window[s->strstart], bflush); s->lookahead--; s->strstart++;] *)
Definition R_lit := RL [0;0;1;1;1;1;0;1;2]%nat.
(** [if (bflush) FLUSH_BLOCK(s, 0);] *)
Definition R_ifbf := RL [0;0;1;1;1;1;1]%nat.
(** After the loop: [s->insert = 0; if (flush == Z_FINISH) {...} if (s->sym_next) FLUSH_BLOCK(s, 0);
     return block_done;] *)
Definition R_tail := RL [1]%nat.

(** Show a fragment's statement concretely. *)
Ltac show_rl := cbv [R_iter R_refill R_ml0 R_scan R_tally R_dist R_lit R_ifbf R_tail RL rsub f_deflate_rle fn_body].

Lemma rle_body_eq : fn_body f_deflate_rle = Ssequence (Sloop (Ssequence Sskip R_iter) Sskip) R_tail.
Proof. reflexivity. Qed.
Lemma rle_iter_eq : R_iter = Ssequence R_refill (Ssequence R_ml0 (Ssequence R_scan (Ssequence R_tally R_ifbf))).
Proof. reflexivity. Qed.

(** ** The model, split like the body *)
Section Model.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** [R_scan]: the run length (match_length, set to 0 before). *)
Definition rle_scan_m (s : dstate) : option dstate :=
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

(** [R_dist]. *)
Definition rle_dist_m (s : dstate) : option (dstate * bool) :=
  let* (s, bflush) := c_dtally_dist s 1 (u32 (d_match_length s - MIN_MATCH)) in
  let s := set_d_lookahead s (u32 (d_lookahead s - d_match_length s)) in
  let s := set_d_strstart s (u32 (d_strstart s + d_match_length s)) in
  Some (set_d_match_length s 0, bflush).

(** [R_lit]. *)
Definition rle_lit_m (s : dstate) : option (dstate * bool) :=
  let* c := mb_rd (d_window s) (d_strstart s) in
  let* (s, bflush) := c_dtally_lit s c in
  let s := set_d_lookahead s (u32 (d_lookahead s - 1)) in
  Some (set_d_strstart s (u32 (d_strstart s + 1)), bflush).

Lemma rle_step_eq s z : rle_step s z =
  let s := set_d_match_length s 0 in
  let* s := rle_scan_m s in
  let* (s, bf) := (if d_match_length s >=? MIN_MATCH then rle_dist_m s else rle_lit_m s) in
  c_bflush s z bf.
Proof. reflexivity. Qed.

End Model.

(** ** The fragment lemmas (statements) *)

(** Proved in RleScan.v. *)
Definition rle_scan_stmt : Prop :=
  forall (Espec : OracleKind) (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s' : dstate) (z : strm),
  rle_scan_m s = Some s' ->
  @semax DCS.CS Espec Delta_rle
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    R_scan
    (normal_ret_assert
      (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).

(** Proved in RleDist.v. *)
Definition rle_dist_stmt : Prop :=
  forall (Espec : OracleKind) (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s' : dstate) (z : strm) (bf : bool),
  rle_dist_m s = Some (s', bf) ->
  @semax DCS.CS Espec Delta_rle
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    R_dist
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush (vi (Z.b2z bf)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).

(** Proved in RleLit.v. *)
Definition rle_lit_stmt : Prop :=
  forall (Espec : OracleKind) (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s' : dstate) (z : strm) (bf : bool),
  rle_lit_m s = Some (s', bf) ->
  @semax DCS.CS Espec Delta_rle
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    R_lit
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush (vi (Z.b2z bf)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).

(** ** Using a fragment lemma inside f_deflate_rle's proof *)

Lemma rl_apply {Espec : OracleKind} Delta (P P' : environ -> mpred) c (Q : environ -> mpred) R :
  tycontext_sub Delta_rle Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_rle P' c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
  intros HT HP H. eapply semax_pre; [exact HP|].
  eapply semax_post; [| | | | eapply semax_Delta_subsumption; [exact HT|exact H]]; destruct R; simpl.
  - intros x. apply andp_left2, derives_refl.
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros x. apply andp_left2. apply prop_left. intros [].
  - intros vl x. apply andp_left2. apply prop_left. intros [].
Qed.

Lemma rl_seq {Espec : OracleKind} Delta P P' Q c1 c2 R :
  tycontext_sub Delta_rle Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_rle P' c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros HT HP H1 H2. eapply semax_seq; [|exact H2].
  apply (rl_apply Delta P P' c1 Q R HT HP H1).
Qed.

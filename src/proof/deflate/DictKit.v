(** * Kit for the body proof of deflateSetDictionary: the function's context, its statement split
    into fragments, the fragment triples, model facts, and the corrected specification.

    The body (deflate.c):

      if (deflateStateCheck(strm) || dictionary == Z_NULL) return Z_STREAM_ERROR;
      s = strm->state; wrap = s->wrap;
      if (wrap == 2 || (wrap == 1 && s->status != INIT_STATE) || s->lookahead) return Z_STREAM_ERROR;
      if (wrap == 1) strm->adler = adler32(strm->adler, dictionary, dictLength);
      s->wrap = 0;
      if (dictLength >= s->w_size) {
          if (wrap == 0) { CLEAR_HASH(s); s->strstart = 0; s->block_start = 0L; s->insert = 0; }   [S_clear]
          dictionary += dictLength - s->w_size; dictLength = s->w_size;
      }
      avail = strm->avail_in; next = strm->next_in;
      strm->avail_in = dictLength; strm->next_in = dictionary;
      fill_window(s);
      while (s->lookahead >= MIN_MATCH) {                                                     [S_loop]
          str = s->strstart; n = s->lookahead - (MIN_MATCH-1);
          do { UPDATE_HASH(..); prev[str & w_mask] = head[ins_h]; head[ins_h] = str; str++; } while (--n);   [S_inner]
          s->strstart = str; s->lookahead = MIN_MATCH-1; fill_window(s);
      }
      s->strstart += s->lookahead; ...; strm->next_in = next; strm->avail_in = avail; s->wrap = wrap; return Z_OK;

    The dictionary is [opt_obj dsh (Some dict) dp] (v7: the token of an empty object gives a valid [dp] for
    [dictionary == Z_NULL] and adler32). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Export Zlib.proof.deflate.DSpec.
Require Export Zlib.proof.deflate.Obligations.
Require Export Zlib.deflate.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The context of the body *)
Definition Delta_sd : tycontext :=
  func_tycontext f_deflateSetDictionary Vprog Gprog_deflateSetDictionary nil.

(** ** Sub-statements of the body, by path: Ssequence a b: 0 = a, 1 = b; Sloop body incr: 0 = body, 1 = incr;
    Sifthenelse e a b: 1 = a, 2 = b. *)
Fixpoint sd_sub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => sd_sub a path'
    | Ssequence _ b, S O => sd_sub b path'
    | Sloop a _, O => sd_sub a path'
    | Sloop _ b, S O => sd_sub b path'
    | Sifthenelse _ a _, S O => sd_sub a path'
    | Sifthenelse _ _ b, S (S O) => sd_sub b path'
    | _, _ => Sskip
    end
  end.

(** [CLEAR_HASH(s); s->strstart = 0; s->block_start = 0L; s->insert = 0;] *)
Definition S_clear : statement := sd_sub (fn_body f_deflateSetDictionary) [1;1;1;1;1;1;0;1;1;0;1]%nat.
(** [while (s->lookahead >= MIN_MATCH) { ... }] *)
Definition S_loop : statement := sd_sub (fn_body f_deflateSetDictionary) [1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
(** [do { UPDATE_HASH(s, s->ins_h, s->window[str + MIN_MATCH-1]); s->prev[str & s->w_mask] = s->head[s->ins_h];
    s->head[s->ins_h] = (Pos)str; str++; } while (--n);] *)
Definition S_inner : statement := sd_sub S_loop [0;1;1;1;0]%nat.

Ltac show_sd_stmt := cbv [S_clear S_loop S_inner sd_sub f_deflateSetDictionary fn_body].

(** ** The fragment triples *)

(** CLEAR_HASH and the three resets, on the state alone ([wrap] is 0 in this branch). *)
Definition sd_clear_post (s1 : dstate) : dstate :=
  set_d_insert (set_d_block_start (set_d_strstart s1 0) 0) 0.

Definition sd_clear_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (gv : globals) (s s1 : dstate) (strmp dp : val) (len : Z)
    (Fr : mpred),
  c_clear_hash s = Some s1 ->
  semax Delta_sd
    (PROP () LOCAL (temp _s (p_s p); temp _strm strmp; temp _dictionary dp; temp _dictLength (vi len);
                    temp _wrap (vi 0); gvars gv)
     SEP (dstate_at s p gv; Fr))
    S_clear
    (normal_ret_assert
      (PROP () LOCAL (temp _s (p_s p); temp _strm strmp; temp _dictionary dp; temp _dictLength (vi len);
                      temp _wrap (vi 0); gvars gv)
       SEP (dstate_at (sd_clear_post s1) p gv; Fr))).

(** The inner do-while loop: [loop FUEL sd_insert_body (s, str, n) = Some (s', str')]. *)
Definition sd_inner_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (str n : Z) (s' : dstate) (str' : Z) (strmp next : val) (wrap avail : Z)
    (Fr : mpred),
  0 <= str <= Int.max_unsigned -> 0 <= n <= Int.max_unsigned ->
  loop FUEL sd_insert_body (s, str, n) = Some (s', str') ->
  semax Delta_sd
    (PROP () LOCAL (temp _str (vi str); temp _n (vi n); temp _s (p_s p); temp _strm strmp;
                    temp _wrap (vi wrap); temp _avail (vi avail); temp _next next; gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; Fr))
    S_inner
    (normal_ret_assert
      (PROP () LOCAL (temp _str (vi str'); temp _s (p_s p); temp _strm strmp;
                      temp _wrap (vi wrap); temp _avail (vi avail); temp _next next; gvars gv)
       SEP (dfull_in s' z p pin ish msgv gv; Fr))).

(** The outer while loop: [loop FUEL sd_body (s, z) = Some (s', z')]. *)
Definition sd_loop_triple : Prop :=
  forall {Espec : OracleKind} (p : dptrs) (pin : val) (ish : share) (msgv : val) (gv : globals)
    (s : dstate) (z : strm) (s' : dstate) (z' : strm) (strmp next : val) (wrap avail : Z) (Fr : mpred),
  loop FUEL sd_body (s, z) = Some (s', z') ->
  semax Delta_sd
    (PROP () LOCAL (temp _s (p_s p); temp _strm strmp; temp _wrap (vi wrap); temp _avail (vi avail);
                    temp _next next; gvars gv)
     SEP (dfull_in s z p pin ish msgv gv; deflate_globals gv; Fr))
    S_loop
    (normal_ret_assert
      (PROP () LOCAL (temp _s (p_s p); temp _strm strmp; temp _wrap (vi wrap); temp _avail (vi avail);
                      temp _next next; gvars gv)
       SEP (EX msgv' : val, dfull_in s' z' p pin ish msgv' gv; deflate_globals gv; Fr))).

(** ** Model facts: the sizes of the allocations and the lengths of the buffers are kept ([dlen]); the input
    object and the output side of the stream are kept ([zkeep]). *)
Definition dlen (s s' : dstate) : Prop :=
  d_gzhead s' = d_gzhead s /\ d_w_size s' = d_w_size s /\ d_hash_size s' = d_hash_size s /\
  tr_lit_bufsize (d_tr s') = tr_lit_bufsize (d_tr s) /\
  Zlength (mb_val (d_window s')) = Zlength (mb_val (d_window s)) /\
  Zlength (d_prev s') = Zlength (d_prev s) /\ Zlength (d_head s') = Zlength (d_head s) /\
  Zlength (o_buf (tr_out (d_tr s'))) = Zlength (o_buf (tr_out (d_tr s))).

Definition zkeep (z z' : strm) : Prop :=
  z_in z' = z_in z /\ z_out z' = z_out z /\ z_avail_out z' = z_avail_out z /\ z_total_out z' = z_total_out z.

Lemma dlen_refl s : dlen s s.
Proof. unfold dlen. repeat split. Qed.

Lemma dlen_trans s1 s2 s3 : dlen s1 s2 -> dlen s2 s3 -> dlen s1 s3.
Proof. unfold dlen. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; congruence. Qed.

Lemma zkeep_refl z : zkeep z z.
Proof. unfold zkeep. repeat split. Qed.

Lemma zkeep_trans z1 z2 z3 : zkeep z1 z2 -> zkeep z2 z3 -> zkeep z1 z3.
Proof. unfold zkeep. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; congruence. Qed.

Lemma dlen_dsizes s s' : dlen s s' -> dsizes s -> dsizes s'.
Proof.
  unfold dlen, dsizes. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; congruence.
Qed.

Lemma dlen_dtokens s s' p : dlen s s' -> dtokens s' p = dtokens s p.
Proof.
  unfold dlen, dtokens. intros. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : ?a = _ |- _ => rewrite H end. reflexivity.
Qed.

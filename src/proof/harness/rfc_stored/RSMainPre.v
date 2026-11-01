(* Law rfc_stored, main: statements 1-16 (the choices data_len, blocks, after, wrapper, window by upto; head_len,
   trailer_len, stream_len; the objects stream, data (alloc_any_bytes), expected (copy_of data) and out (malloc);
   `return 0` when one is NULL), from main's start to the header (rs_A). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.adler32.Spec.
Require Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rfc_stored.RSLawCS.
Require Import Zlib.proof.harness.rfc_stored.RSGlobals.
Require Import Zlib.proof.harness.rfc_stored.RSFacts.
Require Import Zlib.proof.harness.rfc_stored.RSMainKit.
Require Import Zlib.harness.rfc_stored.code.
Local Open Scope logic.

(* `x = f(...); y = (cast) x;` as two statements (forward_call takes the casting Sset only when neutral) *)
Ltac rs_split_call :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ => apply seq_assoc1 end;
  match goal with |- semax _ _ (Ssequence (Ssequence (Scall _ _ _) _) _) _ => apply seq_assoc1 end.

Lemma rs_hl_tl_range wr: 0 <= rs_hl wr <= 10 /\ 0 <= rs_tl wr <= 8.
Proof. unfold rs_hl, rs_tl. destruct (wr =? 1); [lia | destruct (wr =? 2); lia]. Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (e.g. _stream against _stream_len); each identifier comparison is decided by vm_compute instead. *)
Ltac rs_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rs_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rs_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* forward_if over `if (...) { head_len = ..; trailer_len = ..; }`: the join point sets the two lengths to h, t *)
Ltac rs_if_set h t := match goal with
  |- semax _ (PROPx _ (LOCALx (temp _trailer_len _ :: temp _head_len _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp _trailer_len (Vlong (Int64.repr t)) :: temp _head_len (Vlong (Int64.repr h))
                                :: Q) (SEPx R))) end.

(* a branch excluded by the value of its test *)
Ltac rs_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* `q == NULL` is defined for an allocated byte object q (of any size) *)
Ltac rs_tceq := match goal with |- _ |-- denote_tc_test_eq ?q _ =>
  match goal with |- context [data_at Ews (tarray tuchar ?n) ?v q] =>
    apply (malloc_test_eq _ n); [lia | sep_apply (data_at_data_at_ Ews (tarray tuchar n) v q); cancel] end end.

(* the value of `q == NULL` for an allocated object q *)
Ltac rs_cmp := match goal with |- context [sem_cmp_pp Ceq ?q _] =>
  match goal with Hf: field_compatible _ _ q |- _ =>
    let P := fresh in pose proof (field_compatible_isptr _ _ _ Hf) as P;
    destruct q; try contradiction; reflexivity end end.

Lemma seg_pre_ok {Espec: OracleKind} gv vs vwb:
  (forall n nb na wr window stp s0 dp d op ep, rs_A_facts n nb na wr window stp s0 dp d op ->
     semax Delta_m (rs_A gv vs vwb n nb na wr window stp s0 dp d op ep) rs_seg17 POST_B) ->
  semax Delta_m (rs_pre0 gv vs vwb) rs_seg1 POST_B.
Proof.
  intros K.
  unfold rs_pre0, rs_seg1, Delta_m, Gmain_k, POST_B, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call (2 ^ 60). Intros n.
  forward_call (2 ^ 60 - 1). Intros nb1.
  forward.
  forward_call (2 ^ 60). Intros na.
  rs_split_call. forward_call 2. Intros wr.
  forward.
  rs_split_call. forward_call 7. Intros w7.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small, Int.signed_repr by rep_lia. rep_lia. }
  rewrite !Int64.unsigned_repr by rep_lia. rewrite add_repr.
  change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr.
  forward. forward.
  rs_if_set (if wr =? 1 then 2 else 0) (if wr =? 1 then 4 else 0).
  { forward. forward. entailer!. }
  { forward. entailer!. destruct (Z.eqb_spec wr 1); [contradiction | auto]. }
  rs_if_set (rs_hl wr) (rs_tl wr).
  { forward. forward. entailer!. }
  { forward. entailer!. unfold rs_hl, rs_tl. destruct (Z.eqb_spec wr 2); [contradiction | auto]. }
  forward.
  change (Int.signed (Int.repr 5)) with 5. rewrite mul64_repr, !add64_repr.
  pose proof (rs_hl_tl_range wr) as Hht.
  set (sl := rs_hl wr + 5 * (1 + nb1) + n + rs_tl wr + na).
  assert (Esl: sl = rs_hl wr + 5 * (1 + nb1) + n + rs_tl wr + na) by reflexivity.
  assert (Hsl: 0 <= sl <= 7 * 2 ^ 60 + 18) by (subst sl; lia). clearbody sl.
  rs_split_call. forward_call (sl, gv).
  Intros vret. destruct vret as [stp s0]. simpl fst in *; simpl snd in *.
  forward.
  rs_split_call. forward_call (n, gv).
  Intros vret. destruct vret as [dp d]. simpl fst in *; simpl snd in *.
  forward.
  rewrite !rs_bytes_a, !rs_tok_a.
  (* statement 13: `if (stream == NULL || data == NULL) return 0;` *)
  destruct (eq_dec stp nullval) as [Es | Ns].
  { subst stp.
    ifpost _t'8 Int.one. { forward. entailer!. } { rs_nob. }
    forward_if False. { ret0. } { rs_nob. } }
  destruct (eq_dec stp nullval); [contradiction | ]. Intros.
  destruct (eq_dec dp nullval) as [Ed | Nd].
  { subst dp.
    ifpost _t'8 Int.one. { rs_nob. } { forward. entailer!. }
    forward_if False. { ret0. } { rs_nob. } }
  destruct (eq_dec dp nullval); [contradiction | ]. Intros.
  ifpost _t'8 Int.zero. { rs_nob. } { forward. entailer!; rs_cmp. }
  forward_if. { rs_nob. }
  (* statement 14: expected = copy_of(data, data_len) *)
  assert_PROP (isptr dp /\ Zlength d = n) as Pdn by entailer!. destruct Pdn as [Pdp Hdn].
  rewrite <- (rs_bytes_a Ews n (bytes_rep d) dp).
  rs_split_call. forward_call (dp, Ews, dp, 0, n, bytes_rep d, n, d, gv).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. subst n.
    rewrite sublist_same by (rewrite ?Zlength_bytes_rep; auto). repeat split; auto; try rep_lia. }
  Intros ep.
  forward.
  rewrite !rs_bytes_a, !rs_tok_a.
  (* statement 15: out = malloc(data_len) *)
  rs_split_call. forward_call (tarray tuchar n, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros op.
  forward.
  (* statement 16: `if (expected == NULL || out == NULL) return 0;` *)
  destruct (eq_dec ep nullval) as [Ee | Ne].
  { subst ep.
    ifpost _t'11 Int.one. { forward. entailer!. } { rs_nob. }
    forward_if False. { ret0. } { rs_nob. } }
  destruct (eq_dec ep nullval); [contradiction | ]. Intros.
  destruct (eq_dec op nullval) as [Eo | No].
  { subst op.
    ifpost _t'11 Int.one. { rs_nob. } { forward. entailer!; rs_cmp. }
    forward_if False. { ret0. } { rs_nob. } }
  Intros.
  ifpost _t'11 Int.zero. { rs_nob. } { forward. entailer!; rs_cmp. }
  forward_if. { rs_nob. }
  assert_PROP (isptr stp /\ isptr op) as Pt by entailer!. destruct Pt as (Pst & Pop).
  subst n. rewrite <- H4 in *.
  assert (F: rs_A_facts (Zlength d) (1 + nb1) na wr (8 + w7) stp s0 dp d op).
  { unfold rs_A_facts. split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [lia | ].
    split; [lia | ]. split; [reflexivity | ].
    split; [hnf; eapply Forall_impl; [ | exact H5]; intros b Hb; hnf; rep_lia | ].
    split; [hnf; eapply Forall_impl; [ | exact H7]; intros b Hb; hnf; rep_lia | ].
    auto. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K _ _ _ _ _ _ _ _ _ _ ep F)].
  unfold rs_A, rs_copy. entailer!.
Qed.

(* Law api_split_invariant, main: statements 1-15, window_bits = {-15, 15, 31, 47}, window = window_bits[upto(3)],
   input_len = nondet_u32(), room = nondet_u32(), input = alloc_any_bytes(input_len) and its NULL check (`return 0`),
   input_split = copy_of(input, input_len), out_one = malloc(room), out_split = malloc(room),
   flush = (int) nondet_u32(), gp_assume(flush != Z_BLOCK && flush != Z_TREES), and the NULL check of the other
   three objects (`return 0`) (sm_pre0 -> sm_A). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_split_invariant.SILawCS.
Require Import Zlib.proof.harness.api_split_invariant.SIGlobals.
Require Import Zlib.proof.harness.api_split_invariant.SIFacts.
Require Import Zlib.proof.harness.api_split_invariant.SIMainKit.
Require Import Zlib.harness.api_split_invariant.code.
Local Open Scope logic.

(* window_bits[k] for k = upto(3) is one of the four windows *)
Lemma sm_wb_pick k: 0 <= k <= 3 -> si_window (Znth k [-15; 15; 31; 47]).
Proof.
  intros Hk. unfold si_window.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia; cbv; lia.
Qed.

(* the value of gp_assume's argument `flush != Z_BLOCK && flush != Z_TREES` *)
Definition sm_ok_flush (fl: Z) : int := if Z.eq_dec fl 5 then Int.zero else if Z.eq_dec fl 6 then Int.zero else Int.one.

Lemma sm_ok_flush_ne5 fl: Int.min_signed <= fl <= Int.max_signed -> fl <> 5 ->
  Vint (sm_ok_flush fl) = bool2val (negb (Int.eq (Int.repr fl) (Int.repr 6))).
Proof.
  intros R N. unfold sm_ok_flush. destruct (Z.eq_dec fl 5); [contradiction | ].
  destruct (Z.eq_dec fl 6) as [-> | N6]; [reflexivity | ].
  rewrite Int.eq_false; [reflexivity | ]. intro E. apply repr_inj_signed in E; rep_lia.
Qed.

Lemma sm_ok_flush_true fl: sm_ok_flush fl <> Int.zero -> fl <> 5 /\ fl <> 6.
Proof.
  unfold sm_ok_flush. destruct (Z.eq_dec fl 5); [tauto | ]. destruct (Z.eq_dec fl 6); [tauto | ]. auto.
Qed.

(* a branch excluded by the value of its test *)
Ltac sm_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* the value of `q == NULL` for an allocated object q *)
Ltac sm_cmp := match goal with |- context [sem_cmp_pp Ceq ?q _] =>
  match goal with Hf: field_compatible _ _ q |- _ =>
    let P := fresh in pose proof (field_compatible_isptr _ _ _ Hf) as P;
    destruct q; try contradiction; reflexivity end end.

Lemma seg_pre_ok {Espec: OracleKind} gv vwb vone vsplit:
  (forall w src room flush inp ins o1 o2, sm_A_facts w src room flush inp ins o1 o2 ->
     semax Delta_m (sm_A gv vwb vone vsplit w src room flush inp ins o1 o2) sm_seg16 POST_B) ->
  semax Delta_m (sm_pre0 gv vwb vone vsplit) sm_seg1 POST_B.
Proof.
  intros K.
  unfold sm_pre0, sm_seg1, Delta_m, Gmain_k, POST_B, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward. forward.
  forward_call 3. Intros k.
  match goal with |- context [data_at Tsh (tarray tint 4) ?l vwb] =>
    replace l with (map Vint (map Int.repr [-15; 15; 31; 47])) by reflexivity end.
  forward.
  pose proof (sm_wb_pick k H) as Hw. set (w := Znth k [-15; 15; 31; 47]) in *. clearbody w.
  sm_split_call. forward_call tt. Intros n. forward.
  sm_split_call. forward_call tt. Intros room. forward.
  rewrite !Int.unsigned_repr by lia.
  (* input = alloc_any_bytes(input_len), and its NULL check *)
  sm_split_call. forward_call (n, gv).
  Intros vret. destruct vret as [inp src]. simpl fst in *; simpl snd in *.
  forward.
  destruct (eq_dec inp nullval) as [Ei | Ni].
  { subst inp. forward_if. { forward. Exists (Int.repr 0). entailer!. } { sm_nob. } }
  Intros. sm_aptr inp Pi.
  rewrite sm_bytes_a, sm_tok_a. forward_if. { contradiction. }
  (* input_split = copy_of(input, input_len) *)
  rewrite <- sm_bytes_a.
  sm_split_call. forward_call (inp, Ews, inp, 0, n, bytes_rep src, n, src, gv).
  { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto. rewrite Z.add_0_l. subst n.
    repeat split; auto; try lia. apply sublist_same; [lia | unfold bytes_rep; rewrite Zlength_map; lia]. }
  Intros ins.
  forward.
  sm_split_call. forward_call (tarray tuchar room, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros o1.
  forward.
  sm_split_call. forward_call (tarray tuchar room, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros o2.
  forward.
  sm_split_call. forward_call tt. Intros u.
  forward.
  rewrite <- (Int.repr_signed (Int.repr u)). pose proof (Int.signed_range (Int.repr u)) as Hfl.
  set (fl := Int.signed (Int.repr u)) in *. clearbody fl.
  ifpost _t'9 (sm_ok_flush fl).
  { forward. entailer!. apply sm_ok_flush_ne5; auto. }
  { forward. entailer!. }
  forward_call (sm_ok_flush fl). Intros. match goal with Hf: sm_ok_flush fl <> Int.zero |- _ =>
    destruct (sm_ok_flush_true fl Hf) as [Hf5 Hf6] end.
  rewrite !sm_bytes_a, !sm_tok_a.
  (* the NULL check of input_split, out_one and out_split *)
  destruct (eq_dec ins nullval) as [Ei | Ni'].
  { subst ins.
    ifpost _t'10 Int.one. { forward. entailer!. } { sm_nob. }
    ifpost _t'11 Int.one. { forward. entailer!. } { sm_nob. }
    forward_if False. { ret0. } { sm_nob. } }
  Intros.
  destruct (eq_dec o1 nullval) as [E1 | N1].
  { subst o1.
    ifpost _t'10 Int.one. { sm_nob. } { forward. entailer!. }
    ifpost _t'11 Int.one. { forward. entailer!. } { sm_nob. }
    forward_if False. { ret0. } { sm_nob. } }
  Intros.
  destruct (eq_dec o2 nullval) as [E2 | N2].
  { subst o2.
    ifpost _t'10 Int.zero. { sm_nob. } { forward. entailer!; sm_cmp. }
    ifpost _t'11 Int.one. { sm_nob. } { forward. entailer!. }
    forward_if False. { ret0. } { sm_nob. } }
  Intros.
  ifpost _t'10 Int.zero. { sm_nob. } { forward. entailer!; sm_cmp. }
  ifpost _t'11 Int.zero. { sm_nob. } { forward. entailer!; sm_cmp. }
  forward_if. { sm_nob. }
  assert_PROP (isptr ins /\ isptr o1 /\ isptr o2) as Pt by entailer!. destruct Pt as (Pc & P1 & P2).
  subst n.
  assert (F: sm_A_facts w src room fl inp ins o1 o2).
  { unfold sm_A_facts. repeat split; auto; rep_lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K _ _ _ _ _ _ _ _ F)].
  unfold sm_A. entailer!.
Qed.

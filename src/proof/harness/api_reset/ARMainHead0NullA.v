(* Law api_reset, main: the do-while body in phase 0, the test of the four new objects against NULL
   (`if (in_used == NULL || in_fresh == NULL || out_used == NULL || out_fresh == NULL) return 0;`): the
   assertion before it (null0_pre), the folded predicates of ARMainHead0*.v (the tactics are in
   ARMainHead0Call.v), and the cases where in_used or in_fresh is NULL.  The other cases: ARMainHead0NullB.v, ARMainHead0Null.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainHead0Call.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

(* A new object of n bytes (copy_of's or malloc's) with its token, kept folded during the test of the four
   pointers against NULL: comparing p with NULL needs valid_pointer p, which for an object of possibly 0 bytes
   comes from the token, and VST's automation searches for it slowly in a large assertion. *)
Definition objb (n: Z) (c: list val) (p: val) : mpred :=
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) c p.

Lemma objb_valid n c p: objb n c p |-- valid_pointer p.
Proof.
  unfold objb. destruct (zlt 0 (sizeof (tarray tuchar n))).
  - apply sepcon_valid_pointer2. apply data_at_valid_ptr; auto with share. lia.
  - apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. lia.
Qed.
#[export] Hint Resolve objb_valid : valid_pointer.

Lemma objb_local n c p: objb n c p |-- !! isptr p.
Proof.
  unfold objb. sep_apply (data_at_local_facts Ews (tarray tuchar n) c p). Intros. apply prop_right.
  match goal with H: field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ H) end.
Qed.
#[export] Hint Resolve objb_local : saturate_local.

(* the resources the test against NULL does not touch, as one predicate (a small assertion keeps the tests
   fast); at a `return` they give the two structs back to the stack frame *)
Definition rest0 (gv: globals) (va vb: val) (inp: val) (src: list Z) (za: zfields) (La: live) (zb: zfields)
    : mpred :=
  istreamA gv Tsh va za Vundef (Some La) * fresh_raw vb zb *
  malloc_token Ews (tarray tuchar (Zlength src)) inp * data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp *
  mem_mgr gv * zfuncs gv * tables_rep Ers gv * crc_table_at Ers gv * version_lit gv *
  hversion_at ___stringlit_api_reset_1 gv * ir_msg_lits gv * TT.

Lemma rest0_frame gv va vb inp src za La zb:
  rest0 gv va vb inp src za La zb |-- @data_at_ CS Tsh t_z va * @data_at_ CS Tsh t_z vb * TT.
Proof. unfold rest0. sep_apply a_frame. sep_apply fresh_frame. cancel. Qed.

(* `return 0` with both structs given back to the stack frame *)
Ltac ret0 := forward; Exists (Int.repr 0); sep_apply rest0_frame; entailer!.

(* the do-while body from its 8th statement, the test against NULL *)
Definition path_null0 : list nat := path_dbody ++ repeat 1%nat 7.
Definition seg_null0 : statement := ltac:(get_seg path_null0).

(* the state after the four allocations: copy_of and malloc give NULL or a new object *)
Definition opt_obj (n: Z) (c: list val) (p: val) : mpred := if eq_dec p nullval then emp else objb n c p.

Definition null0_pre (gv: globals) (va vb: val) (w: Z) (inp: val) (src: list Z) (pos take room flush: Z)
    (iu ifr ou ofr: val) (za: zfields) (La: live) (zb: zfields) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_fresh ofr; temp _out_used ou; temp _in_fresh ifr; temp _in_used iu;
         temp _flush (Vint (Int.repr flush)); temp _room (Vlong (Int64.repr room));
         temp _take (Vlong (Int64.repr take)); temp _window_bits (Vint (Int.repr w));
         temp _phase (Vint (Int.repr 0)); temp _input_len (Vlong (Int64.repr (Zlength src)));
         temp _input inp; temp _read (Vlong (Int64.repr pos)); lvar _used t_z va; lvar _fresh t_z vb; gvars gv)
  SEP (opt_obj take (bytes_rep (sublist pos (pos + take) src)) iu;
       opt_obj take (bytes_rep (sublist pos (pos + take) src)) ifr;
       opt_obj room (Zrepeat Vundef room) ou; opt_obj room (Zrepeat Vundef room) ofr;
       rest0 gv va vb inp src za La zb).

(* the do-while body from the test against NULL, in phase 0 *)
Definition null0_goal {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb
    : Prop :=
  semax Delta_m (null0_pre gv va vb w inp src pos take room flush iu ifr ou ofr za La zb) seg_null0
    (dpost J0 J1 gv va vb w 0 inp src).

Ltac null0_start :=
  unfold null0_goal, seg_null0, Delta_m, Gmain, dpost, POST_m, null0_pre, opt_obj;
  simplify_func_tycontext; abbreviate_semax; split_call.

(* in_used is NULL *)
Lemma null0_iu {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush ifr ou ofr za La zb:
  null0_goal J0 J1 gv va vb w inp src pos take room flush nullval ifr ou ofr za La zb.
Proof.
  null0_start.
  ifpostv _t'14 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  ifpostv _t'15 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  ifpostv _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  forward_if; [ret0 | infeas].
Qed.

(* in_fresh is NULL *)
Lemma null0_ifr {Espec: OracleKind} J0 J1 gv va vb w inp src pos take room flush iu ou ofr za La zb:
  iu <> nullval -> null0_goal J0 J1 gv va vb w inp src pos take room flush iu nullval ou ofr za La zb.
Proof.
  intros N1. null0_start.
  destruct (eq_dec iu nullval); [contradiction | ].
  ifpostv _t'14 (Vint (Int.repr 1)); [infeas | cmpz | ].
  ifpostv _t'15 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  ifpostv _t'16 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
  forward_if; [ret0 | infeas].
Qed.

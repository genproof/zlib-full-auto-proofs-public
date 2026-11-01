(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's statements 0-20 (the draws, the objects, deflateInit2_ and the stores before the deflate loop), from PRE0_t to the deflate loop's invariant DI_t. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegANull.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac st_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in st_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := st_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* the draws (level, window_bits, mem_level, strategy; gp_assume(deflate_params_ok(...)) makes them parameters in
   zlib.h's ranges, Facts.deflate_params_valid_rt: rparams_ok; data_len = upto(PTRDIFF_MAX), out_size =
   upto(PTRDIFF_MAX)), the allocation of data and its NULL test, its copy expected = copy_of(data, data_len), the
   allocations of compressed and out, and the NULL tests of expected and compressed; the rest is
   TSegANull.st_tests *)
Lemma tseg_a : segA_t_stmt.
Proof.
  intros Espec J gv vc vd va JF. unfold PRE0_t, segA_t, POST_t, lv_locals.
  unfold Delta_t; simplify_func_tycontext. abbreviate_semax.
  forward_call. Intros lv.
  forward_call. Intros wv.
  forward_call. Intros mv.
  forward_call. Intros sv.
  rewrite !sa_vi_signed.
  forward_call (Int.signed (Int.repr lv), Int.signed (Int.repr wv), Int.signed (Int.repr mv),
                Int.signed (Int.repr sv)).
  rewrite <- !sa_vi_signed.
  (* gp_assume(deflate_params_ok(...)): the parameters are in zlib.h's ranges *)
  destruct (Zlib.proof.harness.laws_session.Spec.deflate_params_valid (Int.signed (Int.repr lv))
              (Int.signed (Int.repr wv)) (Int.signed (Int.repr mv)) (Int.signed (Int.repr sv))) eqn:Hpv.
  2:{ forward_call (Int.zero). contradiction. }
  forward_call (Int.one).
  rewrite Zlib.proof.harness.laws_session.Facts.deflate_params_valid_rt in Hpv.
  forward_call max_size. Intros n.
  forward_call max_size. Intros cap.
  forward_call (n, gv). { unfold max_size in *; rep_lia. } Intros vret. destruct vret as [dp data]. cbn [fst snd] in *.
  subst n.
  (* data == NULL: return 0 *)
  destruct (eq_dec dp nullval) as [Pd | Pd].
  { subst dp. forward_if; [sa_ret | sa_nob]. }
  rewrite sa_dobj_fold. sa_mkptr dp bd od.
  forward_if; [sa_tceq | sa_nob | ].
  (* expected = copy_of(data, data_len) *)
  rewrite <- (sa_dobj_fold (Vptr bd od) data).
  forward_call (Vptr bd od, Ews, Vptr bd od, 0, Zlength data, bytes_rep data, Zlength data, data, gv).
  { cancel. }
  { split; [unfold max_size in *; rep_lia | ].
    unfold cbuf_ok. simpl offset_val. rewrite Ptrofs.add_zero.
    unfold bytes_rep; rewrite sublist_same by (rewrite ?Zlength_map; lia).
    repeat split; auto; lia. }
  Intros ep.
  gather_SEP (malloc_token _ _ (Vptr bd od)) (data_at _ _ _ (Vptr bd od)). rewrite (sa_dobj_fold (Vptr bd od) data).
  forward_call (tarray tuchar cap, gv). { simpl. rewrite Z.max_r by lia. unfold max_size in *; rep_lia. } Intros cp.
  forward_call (tarray tuchar (Zlength data), gv).
  { simpl. rewrite Z.max_r by (apply Zlength_nonneg). unfold max_size in *; rep_lia. } Intros op.
  (* the NULL tests of expected and compressed *)
  destruct (eq_dec ep nullval) as [Pe | Pe].
  { subst ep. ifpost _t'12 Int.one; [forward; entailer! | sa_nob | ]. sa_exit_ones. }
  rewrite sa_dobj_fold. sa_mkptr ep be oe.
  destruct (eq_dec cp nullval) as [Pc | Pc].
  { subst cp.
    ifpost _t'12 Int.one; [sa_tceq | sa_nob | forward; entailer! | ]. sa_exit_ones. }
  fold (sa_buf cap cp). sa_mkptr cp bc oc.
  match goal with Hn : 0 <= Zlength data <= max_size, Hcap : 0 <= cap <= max_size, Hb : is_bytes data |- _ =>
  eapply semax_pre;
    [ | exact (st_tests J gv vc vd va lv wv mv sv data cap bd od be oe bc oc op JF H H0 H1 H2 Hn Hcap Hb Hpv)] end.
  unfold PRE_tests_t. entailer!.
Qed.

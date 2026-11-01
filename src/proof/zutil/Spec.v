(* Specifications of zutil.c's allocator functions zcalloc and zcfree (the default zalloc/zfree of a stream),
   shared by the inflate and deflate proofs.

   Both are stated for ANY compspecs (the type allocated may be a struct of the caller's unit, e.g. struct
   inflate_state): zcalloc behaves as VST's malloc_spec' for a type of size items * size, zcfree as
   free_spec'.  The body proofs hold for every compspecs; a law instantiates them at its own compspecs, and
   zcalloc_spec_sub / zcfree_spec_sub move a unit's specification (its Gprog entry, at the unit's
   compspecs) to the law's, as QuickProof.Assembly's malloc_spec'_sub does for malloc. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Zlib.zutil.code.
Import Zlib.zutil.code.

Section Specs.
Context {cs: compspecs}.

(* zcalloc(opaque, items, size): malloc(items * size); opaque is ignored.  The product is computed in
   unsigned int: the precondition excludes overflow. *)
Definition zcalloc_spec :=
  DECLARE _zcalloc
  WITH t: type, gv: globals, op: val, items: Z, size: Z
  PRE [ tptr tvoid, tuint, tuint ]
    PROP (0 <= items <= Int.max_unsigned; 0 <= size <= Int.max_unsigned;
          (items * size <= Int.max_unsigned)%Z; sizeof t = (items * size)%Z;
          complete_legal_cosu_type t = true;
          natural_aligned natural_alignment t = true)
    PARAMS (op; Vint (Int.repr items); Vint (Int.repr size)) GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid ] EX p: val,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).

(* zcfree(opaque, ptr): free(ptr); opaque is ignored. *)
Definition zcfree_spec :=
  DECLARE _zcfree
  WITH t: type, p: val, gv: globals, op: val
  PRE [ tptr tvoid, tptr tvoid ]
    PROP ()
    PARAMS (op; p) GLOBALS (gv)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv).

(* The context of the two bodies: the environment's allocator. *)
Definition Vprog : varspecs := [].
Definition Gprog : funspecs :=
  [(_quickproof_malloc, @malloc_spec' cs); (_quickproof_free, @free_spec' cs)].

Lemma body_zcalloc: semax_body Vprog Gprog f_zcalloc zcalloc_spec.
Proof.
  start_function.
  forward_if (EX p: val, PROP () LOCAL (temp _t'1 p)
              SEP (mem_mgr gv;
                   if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p))).
  - forward_call (t, gv).
    + entailer!. simpl. unfold Vptrofs; simpl. rewrite H2. f_equal.
      unfold Int.mul. rewrite !Int.unsigned_repr by lia. reflexivity.
    + Intros p. forward. Exists p. entailer!.
  - exfalso. revert H5. rewrite !Int64.unsigned_repr by rep_lia. lia.
  - Intros p. forward. Exists p. entailer!.
Qed.

Lemma body_zcfree: semax_body Vprog Gprog f_zcfree zcfree_spec.
Proof.
  start_function.
  forward_call (t, p, gv).
  entailer!.
Qed.

End Specs.

(* The specifications at two compspecs: the law's (cs2) is a subspecification of a unit's (cs1). *)
Section Sub.
Variables cs1 cs2: compspecs.
Hypothesis CSUB: cspecs_sub cs1 cs2.
Hypothesis PRES: forall t, @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  cs_preserve_type cs1 cs2 (@coeq _ _ (CCE_any cs1 cs2)) t = true.

Lemma zcalloc_spec_sub: funspec_sub (snd (@zcalloc_spec cs2)) (snd (@zcalloc_spec cs1)).
Proof.
  do_funspec_sub. destruct w as [[[[t gv] op] items] size]. Exists (t, gv, op, items, size) emp.
  simpl. Intros.
  pose proof (PRES t H4) as P.
  pose proof (@sizeof_change_composite cs1 cs2 (CCE_any cs1 cs2) t P) as S.
  pose proof (@complete_legal_cosu_type_change_composite cs1 cs2 (CCE_any cs1 cs2) t P) as C.
  pose proof (natural_aligned_preserve cs1 cs2 CSUB PRES natural_alignment t H4) as N.
  pose proof (@malloc_token_change_composite cs1 cs2 (CCE_any cs1 cs2) Ews t P) as MT.
  pose proof (@data_at__change_composite cs1 cs2 (CCE_any cs1 cs2) Ews t P) as DT.
  rewrite <- S, N, <- C, <- MT, <- DT.
  apply andp_right; [ apply prop_right | cancel ].
  split; [ intros rho; apply andp_left2; rewrite emp_sepcon; apply derives_refl | ].
  repeat split; auto; lia.
Qed.

Lemma zcfree_spec_sub: funspec_sub (snd (@zcfree_spec cs2)) (snd (@zcfree_spec cs1)).
Proof.
  do_funspec_sub. destruct w as [[[t p] gv] op]. Exists (t, p, gv, op) emp. simpl. Intros.
  destruct (EqDec_val p nullval).
  - entailer!.
  - assert_PROP (@field_compatible cs1 t [] p) as FC by (rewrite data_at__memory_block; entailer!).
    destruct FC as [_ [HC _]].
    pose proof (PRES t HC) as P.
    pose proof (@malloc_token_change_composite cs1 cs2 (CCE_any cs1 cs2) Ews t P) as MT.
    pose proof (@data_at__change_composite cs1 cs2 (CCE_any cs1 cs2) Ews t P) as DT.
    rewrite MT, DT. apply andp_right; [apply prop_right | cancel].
    split; auto. intros rho. apply andp_left2. rewrite emp_sepcon. apply derives_refl.
Qed.
End Sub.

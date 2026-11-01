(* Specifications of deflate.c for ANY caller-supplied allocator, as one funspec per function.

   The allocator-generic specifications (src/proof/za/deflate/: DSpec.v's *_za, Obligations9.v's *_v9_za,
   ZSpec.v's za_deflateInit2__spec / za_deflateEnd_spec) are families indexed by the allocator [ZA].  A law's
   program has one specification per function, fixed before main runs; the allocator of the res_* harnesses
   is the counting one of main's own struct count (its opaque is the address of a local of main), so no
   single family member serves.  [za_sigma] is the specification whose WITH is the pair of an allocator (from a set [k]) and
   the member's WITH: a caller picks the allocator at each call.  It is a subspecification of every member
   ([za_sigma_sub]), and its body proof is the family's ([semax_body_za_sigma]).

   [za_any I k F] builds it from a family F of DECLARE ... WITH specifications (the WITH, PRE and POST of [F ZA]
   for a bound ZA). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.zutil.ZAlloc.

(* [k]: the allocators the specification covers, indexed by a small type [I] (a [zallocator] itself cannot be a
   WITH component: it holds compspecs-dependent predicates, of a larger universe) *)
Definition za_sigma (I : Type) (k : I -> zallocator) (sig : compcert_rmaps.typesig) (cc : calling_convention)
    (A : Type) (P : zallocator -> A -> argsEnviron -> mpred) (Q : zallocator -> A -> environ -> mpred) : funspec :=
  NDmk_funspec sig cc (I * A) (fun x => P (k (fst x)) (snd x)) (fun x => Q (k (fst x)) (snd x)).

(* an allocator (its values are never used: [za_any] reads off the parts of a family that do not depend on it) *)
Definition za_dummy : zallocator :=
  ZAllocator nullval nullval nullval (fun _ _ => emp) (fun _ _ _ => emp) 0.

Lemma za_sigma_sub I k sig cc A P Q (j : I) :
  funspec_sub (za_sigma I k sig cc A P Q) (NDmk_funspec sig cc A (P (k j)) (Q (k j))).
Proof.
  apply NDsubsume_subsume; [ simpl; split; reflexivity | ].
  split; [ split; reflexivity | ].
  intros x gargs. simpl.
  Exists (j, x) emp. rewrite emp_sepcon. simpl.
  apply andp_right; [ apply andp_left2; apply derives_refl | ].
  apply prop_right. intros rho. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma semax_body_za_sigma {cs : compspecs} (V : varspecs) (G : funspecs) (f : function) (i : ident)
    I k sig cc A P Q (j0 : I) :
  (forall j, @semax_body V G cs f (i, NDmk_funspec sig cc A (P (k j)) (Q (k j)))) ->
  @semax_body V G cs f (i, za_sigma I k sig cc A P Q).
Proof.
  intros H. destruct (H j0) as [H1 [H2 _]].
  split; [ exact H1 | split; [ exact H2 | ] ].
  intros Espec ts [j x]. destruct (H j) as [_ [_ H3]]. exact (H3 Espec ts x).
Qed.

(* [za_any_with I k F H]: the za_sigma over [k] of the family [F : zallocator -> ident * funspec], a constant
   of DECLARE form or one defined by the DECLARE-form constant [H] ([za_any I k F]: F itself). *)
Ltac za_any_with I k F H :=
  let t0 := eval cbv delta [F H] beta in (@F za_dummy) in
  lazymatch t0 with
  | (?i, NDmk_funspec ?sig ?cc ?A _ _) =>
    exact (i, za_sigma I k sig cc A
      (fun ZA => ltac:(let t := eval cbv delta [F H] beta in (@F ZA) in
                       lazymatch t with (_, NDmk_funspec _ _ _ ?P _) => exact P end))
      (fun ZA => ltac:(let t := eval cbv delta [F H] beta in (@F ZA) in
                       lazymatch t with (_, NDmk_funspec _ _ _ _ ?Q) => exact Q end)))
  end.
Ltac za_any I k F := za_any_with I k F F.

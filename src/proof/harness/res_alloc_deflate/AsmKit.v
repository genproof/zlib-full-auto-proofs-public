(* Laws res_free_deflate and res_memory_deflate: the assembly of an entry of the law's specifications for an
   allocator-generic specification (ZAny.za_sigma): from the body proofs of the family's members, one per
   allocator, each in its own context (QuickProof.Assembly.entry_moved for a family). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Assembly.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import VST.veric.Clight_initial_world.
From compcert Require Import Maps.
Require Import Zlib.proof.harness.res_alloc_deflate.ZAny.

Lemma entry_za (Espec : OracleKind) (cs cs1 : compspecs) (p : QP.program function) (G : funspecs)
    (V1 : varspecs) (G1 : zallocator -> funspecs) (i : ident) (f : function)
    (I : Type) (k : I -> zallocator) sig cc A P Q (j0 : I) :
  (forall j, @semax_body V1 (G1 (k j)) cs1 f (i, NDmk_funspec sig cc A (P (k j)) (Q (k j)))) ->
  PTree.get i (QP.prog_defs p) = Some (Gfun (Internal f)) ->
  @internal_static_ok cs f (za_sigma I k sig cc A P Q) = true ->
  QPsub_b (QPce cs1) (QPce cs) = true ->
  complete_vars_b cs1 f = true ->
  Forall (fun x => find_id (fst x) (QPvarspecs p) = Some (snd x)) V1 ->
  (forall j, compute_list_norepet (map fst V1 ++ map fst (G1 (k j))) = true) ->
  compute_list_norepet (map fst (QPvarspecs p) ++ map fst G) = true ->
  (forall j, ctx_sub (G1 (k j)) G) ->
  entry_of_prog Espec cs p G (i, za_sigma I k sig cc A P Q).
Proof.
  intros B GET S CSUB VARS V LNR1 LNR CTX.
  apply (entry_internal_intro Espec cs p G (i, za_sigma I k sig cc A P Q) f GET S).
  apply (semax_body_za_sigma _ _ _ _ I k sig cc A P Q j0). intros j.
  apply (semax_body_move V1 (QPvarspecs p) (G1 (k j)) G f _ (B j)); auto.
  - apply cspecs_sub_by_computation; auto.
  - unfold complete_vars_b in VARS. rewrite forallb_forall in VARS. rewrite Forall_forall. auto.
  - apply compute_list_norepet_e; auto.
  - apply compute_list_norepet_e; auto.
Qed.

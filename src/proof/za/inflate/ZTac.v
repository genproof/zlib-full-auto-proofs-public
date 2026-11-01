(* VST's simplify_Delta (floyd/semax_tactics.v, run by abbreviate_semax and forward) for the generated
   allocator-generic proofs (src/proof/za/inflate*, docs/port-za/cfg_inflate.py).

   simplify_Delta unfolds the goal's type context when it is a constant (`semax Delta_inflate ...`).  In the
   port the type contexts are applied to the section's allocator and adler cell (`@Delta_inflate_za ZA ZAV`):
   `unfold D` fails on an application, the tactic then falls through to its catch-all case and calls itself
   forever (a stack overflow).  This redefinition adds the cases of a constant applied to one or two
   arguments; everything else is VST's definition. *)
Require Import VST.floyd.proofauto.
Import compcert.lib.Maps.

Ltac simplify_Delta ::=
match goal with
 | Delta := @abbreviate tycontext _ |- _ => clear Delta; simplify_Delta
 | DS := @abbreviate (PTree.t funspec) _ |- _ => clear DS; simplify_Delta
 | D1 := @abbreviate tycontext _ |- semax ?D _ _ _ =>
       constr_eq D1 D
 | D1 := @abbreviate tycontext _ |- ENTAIL ?D, _ |-- _ =>
       constr_eq D1 D
 | |- semax ?D _ _ _ => unfold D; simplify_Delta
 | |- ENTAIL ?D, _ |-- _ => unfold D; simplify_Delta
 | |- semax (?D _ _) _ _ _ => unfold D; simplify_Delta
 | |- ENTAIL (?D _ _), _ |-- _ => unfold D; simplify_Delta
 | |- semax (?D _) _ _ _ => unfold D; simplify_Delta
 | |- ENTAIL (?D _), _ |-- _ => unfold D; simplify_Delta
 | |- _ => simplify_func_tycontext; simplify_Delta
 | Delta := @abbreviate tycontext ?D
      |- semax ?DD _ _ _ => simplify_Delta' Delta D DD; simplify_Delta
 | Delta := @abbreviate tycontext ?D
      |- ENTAIL ?DD, _ |-- _ => simplify_Delta' Delta D DD; simplify_Delta
 | |- semax ?DD _ _ _ =>  simplify_Delta
 |  |- ENTAIL (ret_tycon ?DD), _ |-- _ =>
        let D := fresh "D" in
          set (D := ret_tycon DD);
          hnf in D; simpl is_void_type in D;
          cbv beta iota in D;
          pose (Delta := @abbreviate tycontext D);
          change D with Delta; subst D; simplify_Delta
 |  |- ENTAIL (ret0_tycon ?DD), _ |-- _ =>
        let D := fresh "D" in
          set (D := ret0_tycon DD);
          hnf in D; simpl is_void_type in D;
          cbv beta iota in D;
          pose (Delta := @abbreviate tycontext D);
          change D with Delta; subst D; simplify_Delta
 | |- ENTAIL (ret_tycon ?DD), _ |-- _ => simplify_Delta
 | |- _ => fail "simplify_Delta did not put Delta_specs and Delta into canonical form"
 end.

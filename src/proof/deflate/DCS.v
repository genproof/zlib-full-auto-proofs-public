(* The compspecs of the deflate proofs: the composites of deflate.c and trees.c linked (z_stream_s,
   gz_header_s, internal_state, ct_data_s and its two unions, tree_desc_s, static_tree_desc_s, config_s).
   Every function of deflate.c and trees.c is proved under it (QuickProof.Assembly moves a body into each law
   that links both units: cspecs_sub DCS.CS law.CS holds by computation). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import QuickProof.Assembly.
Require Zlib.units.Deflate.
Require Zlib.units.Trees.

Definition dt_prog := ltac:(QPlink_progs Zlib.units.Deflate.qp Zlib.units.Trees.qp).
Definition comps := ltac:(let x := eval vm_compute in (prog_composites dt_prog) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.

Lemma deflate_unit_sub: cspecs_sub Zlib.units.Deflate.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.
Lemma trees_unit_sub: cspecs_sub Zlib.units.Trees.CS CS.
Proof. apply cspecs_sub_by_computation; vm_compute; reflexivity. Qed.

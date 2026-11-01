(** * deflate_slow: the postconditions of the main loop's iteration and of the function, as definitions, for the
    branch lemmas of Body_slow.v (SlowPartM.v, SlowPartL.v, SlowPartW.v, SlowPartT.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.SlowKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

(** The function's postcondition (after start_function). *)
Definition slow_fpost (z : strm) (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share)
    (rest : list val) (gv : globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_slow).

(** The loop invariant and the break condition. *)
Definition slow_inv (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (dsl_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv).

Definition slow_brk (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv).

(** The postcondition of one iteration. *)
Definition slow_lpost (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm)
    (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals)
    : ret_assert :=
  loop_nocontinue_ret_assert (slow_inv flush s1 z1 rx z p pin pout ish rest gv)
    (overridePost (slow_brk flush s1 z1 rx z p pin pout ish rest gv) (slow_fpost z r p pin pout ish rest gv)).

Ltac slow_open_post :=
  unfold slow_lpost, slow_inv, slow_brk, slow_fpost, Delta_sl; abbreviate_semax.

(** * deflate_rle: the postconditions of the loop and the function (for RlePartF, RlePartT). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.RleKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Ltac rl_unfold X := let c := eval cbv [X RL rsub f_deflate_rle fn_body] in X in change X with c.

Definition rle_fpost (z : strm) (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share)
    (rest : list val) (gv : globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_rle).

Definition rle_inv (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (rle_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv).

Definition rle_brk (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv).

Definition rle_lpost (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm)
    (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals)
    : ret_assert :=
  loop_nocontinue_ret_assert (rle_inv flush s1 z1 rx z p pin pout ish rest gv)
    (overridePost (rle_brk flush s1 z1 rx z p pin pout ish rest gv) (rle_fpost z r p pin pout ish rest gv)).

Ltac rle_open_post :=
  unfold rle_lpost, rle_inv, rle_brk, rle_fpost, Delta_rle; abbreviate_semax.

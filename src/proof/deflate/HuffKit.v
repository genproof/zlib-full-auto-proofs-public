(** * deflate_huff: the fragments of its body, its postconditions (for the part lemmas HuffPartF, HuffPartT). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Definition Delta_hf : tycontext := func_tycontext f_deflate_huff Vprog Gprog_compress nil.

Fixpoint hf_ssub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => hf_ssub a path'
    | Ssequence _ b, S O => hf_ssub b path'
    | Sloop a _, O => hf_ssub a path'
    | Sloop _ b, S O => hf_ssub b path'
    | Sifthenelse _ a _, S O => hf_ssub a path'
    | Sifthenelse _ _ b, S (S O) => hf_ssub b path'
    | _, _ => Sskip
    end
  end.

Definition HF (path : list nat) : statement := hf_ssub (fn_body f_deflate_huff) path.

(** [if (bflush) FLUSH_BLOCK(s, 0);] at the end of an iteration *)
Definition HS_ifbf := HF [0;0;1;1;1;1;1;1]%nat.
(** after the loop: [s->insert = 0], FLUSH_BLOCK(s, 1) / FLUSH_BLOCK(s, 0) and the returns *)
Definition HS_tail := HF [1]%nat.

(** The function's postcondition (after start_function). *)
Definition huff_fpost (z : strm) (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share)
    (rest : list val) (gv : globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_huff).

(** The loop invariant and the break condition. *)
Definition huff_inv (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (huff_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv).

Definition huff_brk (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv).

(** The postcondition of one iteration. *)
Definition huff_lpost (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm)
    (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals)
    : ret_assert :=
  loop_nocontinue_ret_assert (huff_inv flush s1 z1 rx z p pin pout ish rest gv)
    (overridePost (huff_brk flush s1 z1 rx z p pin pout ish rest gv) (huff_fpost z r p pin pout ish rest gv)).

Ltac huff_open_post :=
  unfold huff_lpost, huff_inv, huff_brk, huff_fpost, Delta_hf; abbreviate_semax.

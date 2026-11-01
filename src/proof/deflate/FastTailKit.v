(** * deflate_fast: the end of an iteration and the tail as statements, the postconditions (FastPartF, FastPartT). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.FastKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Fixpoint fs_ssub (s : statement) (path : list nat) : statement :=
  match path with
  | nil => s
  | i :: path' =>
    match s, i with
    | Ssequence a _, O => fs_ssub a path'
    | Ssequence _ b, S O => fs_ssub b path'
    | Sloop a _, O => fs_ssub a path'
    | Sloop _ b, S O => fs_ssub b path'
    | Sifthenelse _ a _, S O => fs_ssub a path'
    | Sifthenelse _ _ b, S (S O) => fs_ssub b path'
    | _, _ => Sskip
    end
  end.

(** The last statement of a sequence. *)
Fixpoint fs_last (s : statement) : statement :=
  match s with Ssequence _ b => fs_last b | _ => s end.

(** [if (bflush) FLUSH_BLOCK(s, 0);]: the last statement of an iteration *)
Definition FS_ifbf := fs_last (fs_ssub (fn_body f_deflate_fast) [0;0;1]%nat).
(** after the loop: s->insert, FLUSH_BLOCK(s, 1) / FLUSH_BLOCK(s, 0) and the returns *)
Definition FS_tail := fs_ssub (fn_body f_deflate_fast) [1]%nat.

Definition fast_fpost (z : strm) (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share)
    (rest : list val) (gv : globals) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
       (PROP () RETURN (vi (bstate_num (snd r)))
        SEP (dfull_post z (fst r) p pin pout ish rest gv; deflate_globals gv)))
    (stackframe_of f_deflate_fast).

Definition fast_inv (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX s' : dstate, EX z' : strm, EX msgv' : val,
     PROP (runs (df_body flush) (s', z') (s1, z1, rx); out_grow z z')
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s' z' p pin pout ish (rest_after z z' rest) msgv' gv; deflate_globals gv).

Definition fast_brk (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm) (p : dptrs)
    (pin pout : val) (ish : share) (rest : list val) (gv : globals) : environ -> mpred :=
  EX msgv' : val,
     PROP (rx = None; out_grow z z1)
     LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s1 z1 p pin pout ish (rest_after z z1 rest) msgv' gv; deflate_globals gv).

Definition fast_lpost (flush : Z) (s1 : dstate) (z1 : strm) (rx : option bstate) (z : strm)
    (r : dstate * strm * bstate) (p : dptrs) (pin pout : val) (ish : share) (rest : list val) (gv : globals)
    : ret_assert :=
  loop_nocontinue_ret_assert (fast_inv flush s1 z1 rx z p pin pout ish rest gv)
    (overridePost (fast_brk flush s1 z1 rx z p pin pout ish rest gv) (fast_fpost z r p pin pout ish rest gv)).

Ltac fast_open_post :=
  unfold fast_lpost, fast_inv, fast_brk, fast_fpost, Delta_fast; abbreviate_semax.

Ltac fa_contra :=
  exfalso; first [ discriminate | match goal with Hc : _ <> _ |- _ => exact (Hc eq_refl) end ].

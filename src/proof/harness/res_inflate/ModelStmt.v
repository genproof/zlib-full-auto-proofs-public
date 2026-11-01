(* The model facts of res_free_inflate and res_memory_inflate (harness/res_free_inflate.c,
   harness/res_memory_inflate.c), about the state of inflate.c between two inflate() calls.

   The allocator sees inflateInit2_'s state (7160 bytes), then the window: inflate() allocates it (2^wbits
   bytes, updatewindow) at the end of the first call that has output to keep, and never frees it; when that
   allocation fails the call enters the mode MEM and returns Z_MEM_ERROR, and every later call returns
   Z_MEM_ERROR at once (ZEvents.win_ev: the call that enters MEM is the event ZFail).

   [res_inv hw s]: the state between two calls: no gz_header request, a mode of the decoder proper (HEAD ..
   BAD) or MEM, and state->wbits at most hw, the harness's w (`w = window_bits & 15; if (window_bits < 0)
   w = -window_bits; if (w == 0) w = 15;`), 0 only when that w is 15 (the window size comes from the header,
   at most 15).

   [res_model_stmt]: inflateInit2_'s state satisfies it, and one call (Model2.run2 from the state) keeps it, keeps
   the window once allocated, leaves a state in MEM unchanged, enters MEM only when it has no window, and
   returns Z_MEM_ERROR only in MEM. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.inflate.InvW.

(* the harness's w *)
Definition harness_w (window_bits : Z) : Z :=
  if window_bits <? 0 then - window_bits
  else if Z.land window_bits 15 =? 0 then 15 else Z.land window_bits 15.

Definition res_inv (hw : Z) (s : istate) : Prop :=
  i_head s = false /\
  (i_mode s = MEM \/ HEAD <= i_mode s <= BAD) /\
  i_wbits s <= hw /\ (i_wbits s = 0 -> hw = 15).

(* inflateInit2_ with an accepted windowBits w *)
Definition res_init_stmt : Prop :=
  forall (w : Z) (sp : val), wbits_ok w = true -> res_inv (harness_w w) (l_s (init_live sp w)).

(* one inflate() call on a live stream L with the input inp and the application's fields z *)
Definition res_call_stmt : Prop :=
  forall (hw flush : Z) (z : zfields) (L : live) (inp : list Z) (res : result),
    res_inv hw (l_s L) -> swfW (l_s L) -> live_ok L -> zf_ok z ->
    bytes_ok inp -> Zlength inp <= Int.max_unsigned ->
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    res_inv hw (m_s (r_m res)) /\
    (i_win (l_s L) = true -> i_win (m_s (r_m res)) = true) /\
    (i_mode (l_s L) = MEM -> m_s (r_m res) = l_s L) /\
    (i_mode (l_s L) <> MEM -> i_mode (m_s (r_m res)) = MEM -> i_win (m_s (r_m res)) = false) /\
    (r_ret res = Z_MEM_ERROR -> i_mode (m_s (r_m res)) = MEM).

Definition res_model_stmt : Prop := res_init_stmt /\ res_call_stmt.

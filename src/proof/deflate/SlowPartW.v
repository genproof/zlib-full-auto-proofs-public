(** * deflate_slow: the wait branch (S_avail): match_available = 1, strstart++, lookahead--. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.FlushKit.
Require Import Zlib.proof.deflate.SlowKit.
Require Import Zlib.proof.deflate.SlowPost.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.
Local Strategy opaque [loop loop2].

Lemma slow_avail_part {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (gv : globals) (flush : Z) (z : strm) (r : dstate * strm * bstate) (s1 : dstate) (z1 : strm) (rx : option bstate)
    (s4 : dstate) (z2 : strm) (msgv2 : val) :
  runs (dsl_body flush)
    (set_d_lookahead (set_d_strstart (set_d_match_available s4 1)
                         (u32 (d_strstart (set_d_match_available s4 1) + 1)))
                         (u32 (d_lookahead (set_d_strstart (set_d_match_available s4 1)
                                (u32 (d_strstart (set_d_match_available s4 1) + 1))) - 1)), z2) (s1, z1, rx) ->
  out_grow z z2 ->
  semax Delta_sl
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s4 z2 p pin pout ish (rest_after z z2 rest) msgv2 gv; deflate_globals gv))
    S_avail (slow_lpost flush s1 z1 rx z r p pin pout ish rest gv).
Proof.
  intros Hbody Hgrow2.
  cbv [S_avail SL ssub f_deflate_slow fn_body].
  slow_open_post.
  assert_PROP (dstate_ranges s4) as Hr4 by (unfold dfull, dstate_at; entailer!).
  unfold dfull, dstate_at. Intros. unfold match_at. Intros.
           assert (0 <= d_strstart s4 <= Int.max_unsigned) by drange.
           assert (0 <= d_lookahead s4 <= Int.max_unsigned) by drange.
           forward. forward. forward. forward. forward.
           set (s8 := set_d_lookahead (set_d_strstart (set_d_match_available s4 1)
                         (u32 (d_strstart (set_d_match_available s4 1) + 1)))
                         (u32 (d_lookahead (set_d_strstart (set_d_match_available s4 1)
                                (u32 (d_strstart (set_d_match_available s4 1) + 1))) - 1))) in Hbody.
           assert (Hr8 : dstate_ranges s8) by (subst s8; dranges_tac Hr4).
           Exists s8 z2 msgv2.
           (subst s8; dfull_close_entail).
Qed.

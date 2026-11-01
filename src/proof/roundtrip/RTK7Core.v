(* The wide core of the deflate laws' theory for its invariant W3 (RTK7Defs.core_facts7): from the generated wide
   port (src/proof/wide/roundtrip/, docs/port-wide/cfg_rtd.py); its compression facts hold for every call (the
   left disjunct of RTK7Defs.cpost7). *)
Require Import Zlib.proof.roundtrip.RTK7Defs.
From Coq Require Import ZArith List Lia.
Require Import Zlib.proof.wide.roundtrip.RTDLTCore.
Require Import Zlib.proof.wide.roundtrip.RTDLTCFill Zlib.proof.wide.roundtrip.RTDLTCTrees2.
Require Import Zlib.proof.wide.roundtrip.RTDLTCLm Zlib.proof.wide.roundtrip.RTDLTCSpecs2.
Require Zlib.proof.deflate.LTWDict.
Import ListNotations.
Local Open Scope Z_scope.

(* deflateSetDictionary for a dictionary of up to 2^32 - 1 bytes and any total_in: the bounds area proved it
   (LTWDict.W3_dict_w) for LTCore.W3, of which RTDLTCore.W3 is a verbatim copy, so the statement is the same up
   to unfolding. *)
Lemma rtk7_dict : forall s z d,
    W3 s -> 0 <= d_wrap s <= 1 -> bad_state s = false -> (d_wrap s = 1 -> d_status s = INIT_STATE) ->
    d_strstart s = 0 -> d_lookahead s = 0 -> d_block_start s = 0 ->
    bytes d -> Zlength d <= 4294967295 -> 0 <= z_total_in z <= 18446744073709551615 ->
    adler_pre (d_wrap s) (z_adler z) ->
    exists s' z' k,
      c_deflateSetDictionary s z (Some d) = Some (s', z', Z_OK) /\ W3 s' /\
      api_eq s s' /\ out_eq s s' /\ same_prm s s' /\
      d_lookahead s' = 0 /\ d_strstart s' = d_block_start s' /\
      (d_strstart s' = 0 <-> d = []) /\
      d_sym_next s' = d_sym_next s /\ 0 <= k <= Zlength d /\
      z' = mkST (z_in z) (z_next_in z) (z_avail_in z) (u64 (z_total_in z + k)) (z_out z) (z_avail_out z)
                (z_total_out z)
                (if d_wrap s =? 1 then Zlib.proof.adler32.Model.ref_adler32 (z_adler z) d else z_adler z)
                (z_msg z).
Proof. exact Zlib.proof.deflate.LTWDict.W3_dict_w. Qed.

Theorem rtk7_core_ok : core7_stmt.
Proof.
  intros Hov.
  destruct (trees_ok2 Hov) as (Htal & Htf & Hroom).
  pose proof (fbo_ok_w Htf Hroom) as Hfbo. pose proof fpend2_ok_w as Hfp.
  pose proof fill_ok_w as Hfill. destruct lm_ok as [Hins Hlm].
  constructor.
  - exact W3_prm.
  - exact W3_pos.
  - exact W3_frame.
  - exact rtk7_dict.
  - intros s z flush HW Ho Hq Hf Hz Hw Ha.
    destruct (core_compress3_w Hfill Hins Hlm Htal Hfbo Hfp s z flush HW Ho Hq Hf Hz Hw Ha)
      as (s' & z' & bs & evs & E & P).
    exists s', z', bs, evs. split; [exact E|left; exact P].
  - exact (W3_still_w Hfill Hins Hlm Htal Hfbo Hfp).
  - exact W3_full.
Qed.

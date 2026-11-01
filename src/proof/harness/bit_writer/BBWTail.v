(* Law rj_bad_block, main: statements 30-31 of main's body (BBWKit.bbw_tail_stmt): after the loop, one more
   inflate() call when the code is Z_OK and flush is Z_TREES (it returns Z_DATA_ERROR: BBWDefs.bbw_extra), then
   gp_assert(code == Z_DATA_ERROR) and return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.bit_writer.BWSpec.
Require Import Zlib.proof.harness.bit_writer.BBWDefs.
Require Import Zlib.proof.harness.bit_writer.BWLawCS Zlib.proof.harness.bit_writer.BWGlobals.
Require Import Zlib.proof.harness.bit_writer.BBWKit.
Require Import Zlib.proof.harness.bit_writer.BBWHelp.

(* the input object (the whole stream, offered from pos) and the output object (room bytes, offered from |ob|)
   as inflate()'s buffers before the call *)
Lemma bbw_tail_bufs vs L strp pos n S outp lo room (oc: list val):
  isptr vs -> Zlength oc = room -> 0 <= lo <= room ->
  (data_at Ews (tarray tuchar n) (bytes_rep S) strp * malloc_token Ews (tarray tuchar n) strp *
   data_at Ews (tarray tuchar room) oc outp * malloc_token Ews (tarray tuchar room) outp)%logic
  |-- bufs_opt (is_live vs (Some L)) (InBuf Ews strp pos n (bytes_rep S)) (Some (OutBuf Ews outp lo room oc))
        [] true true.
Proof.
  intros Pv Ho Hlo. unfold is_live. rewrite if_false by (destruct vs; try contradiction; discriminate).
  unfold bufs_opt, in_rep, out_opt, out_rep, in_tok, out_tok.
  rewrite Zlength_nil, Z.add_0_r. simpl byte_vals. rewrite app_nil_l.
  rewrite <- (sublist_split 0 lo room oc), sublist_same by lia.
  cancel. rewrite (bb_tok_i Ews n strp), (bb_tok_i Ews room outp). cancel.
Qed.

(* the call after the loop returns Z_DATA_ERROR: it runs on the stream's state s from pos with the output space
   left, which is what BBWDefs.bbw_extra speaks of *)
Lemma bbw_tail_ret S0 kind which lits room pos ob z L flush vs strp n c o inp r z' st' ow:
  isptr vs -> zf_ok z -> live_ok L -> Zlength lits <= room -> zf_ao z = room - Zlength ob ->
  inp = sublist pos (Zlength (bb_bytes S0 kind which lits)) (bb_bytes S0 kind which lits) ->
  bbw_extra S0 kind which lits pos ob (l_s L) flush ->
  inflate_rel flush vs z (Some L) (InBuf Ews strp pos n c) inp (Some o) r z' st' ow ->
  r = Z_DATA_ERROR.
Proof.
  intros Pv Zo Lo Hl Hao Ei Hx Hrel.
  destruct Hrel as [[Hib _] | [_ [L0 [o0 [res [winp [E1 [E2 [Hrun [_ [Er _]]]]]]]]]]].
  { exfalso. unfold inflate_bad, is_live in Hib.
    rewrite if_false in Hib by (destruct vs; try contradiction; discriminate).
    destruct Hib as [Hib | [Hib | [Hib _]]]; discriminate. }
  injection E1 as E1. subst L0 r inp.
  apply (Hx L z res eq_refl Lo Zo ltac:(lia) Hrun).
Qed.

Lemma bbw_tail : bbw_tail_stmt.
Proof.
  intros Espec gv vs vbt vbit S0 kind which lits room flush strp outp Hargs.
  unfold bbw_seg30, bbw_AT, bbw_Delta, POST_B, bbw_POST. simplify_func_tycontext. abbreviate_semax.
  Intros code pos ob z L oc.
  assert_PROP (isptr vs) as Pvs by entailer!.
  destruct Hargs as (Hok & Hroom & Hfl & Pstr & Pout).
  match goal with H: code = Z_DATA_ERROR \/ _ |- _ => destruct H as [Hc | Hc] end.
  - subst code.
    bb_if BBC._t'21 (Vint (Int.repr 0)).
    { bb_infeas. }
    { forward. entailer!. }
    forward_if (PROP () LOCAL (temp BBC._code (Vint (Int.repr Z_DATA_ERROR));
                               lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt;
                               lvar BBC._bit tulong vbit; gvars gv)
                SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT)).
    { bb_infeas. }
    { forward. sep_apply bb_istreamA_undef. entailer!. }
    forward_call Int.one.
    forward. Exists (Int.repr 0). entailer!.
  - destruct Hc as (-> & -> & Hsw & Hhd & Hpos & Hob & Eni & Eai & Eno & Eao & Hx).
    destruct (bb_bytes_ok S0 kind which lits Hok) as [LS BS].
    set (S := bb_bytes S0 kind which lits) in *.
    bb_if BBC._t'21 (Vint (Int.repr 1)).
    { forward. entailer!. }
    { bb_infeas. }
    forward_if (PROP () LOCAL (temp BBC._code (Vint (Int.repr Z_DATA_ERROR));
                               lvar BBC._strm t_zsb vs; lvar BBC._btype (tarray tuint 5) vbt;
                               lvar BBC._bit tulong vbit; gvars gv)
                SEP (data_at_ Tsh t_zsb vs; data_at_ Tsh (tarray tuint 5) vbt; data_at_ Tsh tulong vbit; TT)).
    2: { bb_infeas. }
    { assert_PROP (zf_ok z /\ live_ok L) as ZL by (unfold istreamA; entailer!).
      destruct ZL as [Zo Lo].
      forward_call (gv, Tsh, vs, z, Vundef, Some L, InBuf Ews strp pos (Zlength S0) (bytes_rep S),
                    sublist pos (Zlength S) S, Some (OutBuf Ews outp (Zlength ob) room oc), Z_TREES, Ers, Ers,
                    true, true).
      { unfold istreamA_opt. rewrite if_false by (destruct vs; try contradiction; discriminate).
        unfold is_live at 1. rewrite if_false by (destruct vs; try contradiction; discriminate).
        unfold head_opt, head_mem. rewrite Hhd.
        sep_apply (bbw_tail_bufs vs L strp pos (Zlength S0) S outp (Zlength ob) room oc Pvs
                     ltac:(assumption) ltac:(pose proof (Zlength_nonneg ob); lia)).
        cancel. }
      { unfold in_ok, out_ok, in_ptr, out_ptr. rewrite Eni, Eai, Eno, Eao, !Z.add_0_r.
        rewrite Zlength_sublist by lia.
        assert (Zlength (bytes_rep S) = Zlength S0) by (unfold bytes_rep; rewrite Zlength_map; lia).
        assert (Zlength S0 <= Int64.max_signed) by (destruct Hok as (_ & _ & _ & _ & _ & Hz & _); lia).
        repeat match goal with |- _ /\ _ => split end; auto; try rep_lia; try lia.
        - replace (pos + (Zlength S - pos)) with (Zlength S) by lia.
          unfold bytes_rep, byte_vals. rewrite sublist_map. reflexivity.
        - apply Forall_sublist. exact BS. }
      Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
      match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into Hrel end.
      pose proof (bbw_tail_ret S0 kind which lits room pos ob z L Z_TREES vs strp _ _ _ _ r z' st' ow
                    Pvs Zo Lo ltac:(lia) Eao eq_refl Hx Hrel) as Hd.
      subst r.
      forward.
      unfold istreamA_opt. rewrite if_false by (destruct vs; try contradiction; discriminate).
      destruct st' as [L'|].
      + sep_apply bb_istreamA_undef. entailer!.
      + unfold istreamA, zstrm_atA. Intros. rewrite bb_zs_i. sep_apply data_at_data_at_. entailer!. }
    forward_call Int.one.
    forward. Exists (Int.repr 0). entailer!.
Qed.

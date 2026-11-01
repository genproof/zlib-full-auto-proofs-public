(* Law res_free_inflate: the facts main's body proof uses after its inflate() call: the call's model run and
   return value, the range of the stream's fields, and why a return of Z_MEM_ERROR means a failed allocation. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_inflate.ResIKit.
Require Import Zlib.proof.harness.res_inflate.ResITheory.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Zlib.proof.uncompr.URunRet.

(* inflate() on a live stream, an input object and an output space: the model's run, its return value (one of
   zlib's codes, so main's int code is it) and a live stream *)
Lemma inflate_rel_ret flush strmp z L ib inp o r z' st' ow :
  strmp <> nullval -> ib <> InNull ->
  inflate_rel flush strmp z (Some L) ib inp (Some o) r z' st' ow ->
  exists res winp, st' = Some (Live (l_sp L) winp (m_s (r_m res)) (m_h (r_m res)) (l_headp L) (l_hsh L)
                                   (l_xb L) (l_nb L) (l_cb L)) /\
    Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res /\ r = r_ret res /\
    -5 <= r <= 2.
Proof.
  intros Hs Hi [(Hb & _) | (Hb & L1 & o1 & res & winp & E1 & E2 & Hrun & _ & Er & _ & _ & _ & Est)].
  - exfalso. unfold inflate_bad, is_live in Hb. rewrite if_false in Hb by auto.
    destruct Hb as [Hb | [Hb | [Hb _]]]; congruence.
  - injection E1 as E1. subst L1. exists res, winp. split; [exact Est | ]. split; [exact Hrun | ].
    split; [exact Er | ]. subst r.
    eapply Zlib.proof.uncompr.URunRet.run2_ret; [ | exact Hrun ]. simpl. unfold Z_OK. lia.
Qed.

(* the application's fields after set_buffer(strm, input, n, out, room) are in range *)
Lemma zinit_ok dp n op room w :
  0 <= n <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned -> zf_ok (zinit dp n op room w).
Proof.
  intros Hn Hr. unfold zf_ok, zinit, init_adler; cbn.
  assert (0 <= Z.land (init_wrap w) 1 <= 1).
  { pose proof (Z.land_ones (init_wrap w) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. rewrite E.
    pose proof (Z.mod_pos_bound (init_wrap w) (2^1) ltac:(lia)). simpl in *. lia. }
  destruct (init_wrap w =? 0); rep_lia.
Qed.

(* inflate() on the state of inflateInit2_ returned Z_MEM_ERROR: by the model (res_model_stmt) the call
   entered the mode MEM with no window, so the allocation of the window failed (win_ev is [ZFail]) and the
   allocator's events record a failure *)
Lemma call_mem_failed sp w flush z inp res :
  res_model_stmt -> wbits_ok w = true -> live_ok (init_live sp w) -> zf_ok z -> bytes_ok inp ->
  Zlength inp <= Int.max_unsigned ->
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z (init_live sp w) inp) res ->
  r_ret res = -4 ->
  za_failed (([ZAlloc ZEvents.state_size] ++ ZEvents.win_ev (l_s (init_live sp w)) (m_s (r_m res))) ++
             ZEvents.end_ev (m_s (r_m res))) = true.
Proof.
  intros [HI HC] Hwb HL Hz Hb Hn Hrun Hr.
  destruct (HC (harness_w w) flush z (init_live sp w) inp res (HI w sp Hwb) (init_swfW sp w) HL Hz Hb Hn Hrun)
    as (_ & _ & _ & Hmem & Hret).
  specialize (Hret Hr).
  assert (W' : i_win (m_s (r_m res)) = false) by (apply Hmem; [rewrite init_mode; discriminate | exact Hret]).
  rewrite !za_failed_app. unfold ZEvents.win_ev. rewrite init_win, W', init_mode, Hret. reflexivity.
Qed.


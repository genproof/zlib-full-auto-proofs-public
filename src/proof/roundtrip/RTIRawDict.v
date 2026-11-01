(* RT-I, part rti_rawdict: RTIIface.if_rawdict (raw stream, inflateSetDictionary right after inflateInit2), from the decode theory. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.roundtrip.RTIRawDictKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rti_rawdict : decode_parts ->
  forall wb dict D O sp z0 alloc_ok winp,
    RF.dfinal dict 0 wb None D O -> dict <> [] -> Zlength dict <= 32768 ->
    Zlength D <= 1048576 -> Zlength O <= 4194304 -> live_ok (init_live sp (- wb)) ->
    let sd := setdict_f dict alloc_ok winp z0 (init_live sp (- wb)) in
    (fst3 sd = Z_OK \/ fst3 sd = Z_MEM_ERROR) /\
    (fst3 sd = Z_OK -> forall z res,
       live_ok (thd3 sd) -> zcall_ok z O D ->
       run2 4 lenfix_list distfix_list (m_init z (thd3 sd) O) res -> rdone O D res).
Proof.
  intros DP wb dict D O sp z0 alloc_ok winp HF Hne Hdl HD HO HL sd.
  destruct HF as (Hwb & bs & Hwf & Hdata & HOb).
  destruct (rrd_setdict_check wb sp dict ltac:(lia)) as (Ls & Ck & Wi).
  unfold sd, setdict_f. rewrite Ls, Ck, Wi.
  destruct alloc_ok; [ | split; [right; reflexivity | intros E; discriminate E]].
  split; [left; reflexivity | ].
  intros _ z res LV ZC RUN. unfold thd3 in *. cbn [snd] in *.
  set (L' := set_l_winp (set_l_s (init_live sp (- wb)) (setdict_s (init_s 0 wb) dict)) winp) in *.
  set (G := DCtx WRaw wb dict bs (- wb) O).
  destruct ZC as (ZF & Zai & Zao & Zto).
  assert (CTX: dctx_ok G) by (apply rrd_ctx_ok; [lia | exact Hwf | exact HOb | lia]).
  assert (DI: dinv G 0 dict (l_s L') (zf_tout z)) by (rewrite Zto; apply rrd_dinv; lia).
  destruct (decode_of_parts DP) as [_ DC].
  assert (SL: slen G = Zlength O) by (unfold slen; cbn; rewrite <- HOb; reflexivity).
  unfold decode_call_stmt in DC.
  assert (SRC: dc_src G = O) by reflexivity.
  specialize (DC G 0 dict L' z O 4 res CTX DI LV ZF ltac:(lia) ltac:(lia) ltac:(rewrite SRC; lia)
    ltac:(rewrite SRC, Z.add_0_l, sublist_same by lia; reflexivity) RUN).
  cbv zeta in DC.
  destruct DC as [MEM | (RET & SNX & SOW & AOUT & (rest & FULL) & _ & _ & ENDP & NEND & _)];
    [left; exact MEM | right].
  assert (FD: full G = expand dict bs) by reflexivity.
  assert (DD: D = sublist (Zlength dict) (Zlength (full G)) (full G)) by (rewrite <- Hdata; reflexivity).
  destruct (Z.eq_dec (r_ret res) Z_STREAM_END) as [E | NE].
  - destruct (ENDP E) as [F P].
    assert (OW: m_ow (r_m res) = D).
    { pose proof (Zlength_nonneg dict). pose proof (Zlength_nonneg (m_ow (r_m res))).
      rewrite DD, <- F. rewrite Zlength_app. rewrite sublist_app2 by lia.
      rewrite Z.sub_diag, Z.add_simpl_l. symmetry. apply sublist_same; lia. }
    split; [exact E | split; [lia | split; [exact OW | split; [rewrite SOW, OW; reflexivity | lia]]]].
  - exfalso. destruct (NEND NE) as [(A & B) | [(A & B) | B]].
    + lia.
    + pose proof (Zlength_nonneg dict). pose proof (Zlength_nonneg (m_ow (r_m res))).
      pose proof (Zlength_nonneg rest).
      assert (LF: Zlength (full G) = Zlength dict + Zlength (m_ow (r_m res)) + Zlength rest)
        by (rewrite FULL, !Zlength_app; lia).
      assert (LD: Zlength D = Zlength (full G) - Zlength dict)
        by (rewrite DD, Zlength_sublist by lia; reflexivity).
      rewrite Zlength_app in B. lia.
    + unfold Z_BLOCK, Z_TREES in B. lia.
Qed.

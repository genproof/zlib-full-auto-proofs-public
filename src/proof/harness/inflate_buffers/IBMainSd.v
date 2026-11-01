(* Law inflate_buffers, main: the branch inflateSetDictionary(&s, ob, aout) (220 <= op < 230) and its assert. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

Lemma sd_cases bs aok winp z L: ib_facts -> ib_inv L ->
  let '(r, z', L') := setdict_f bs aok winp z L in
  z' = z /\ ib_inv L' /\ (r = 0 \/ r = -2 \/ r = -3 \/ r = -4).
Proof.
  intros FI HI. pose proof (fi_setdict FI (l_s L) bs HI) as [A B].
  unfold setdict_f, Z_OK, Z_STREAM_ERROR, Z_DATA_ERROR, Z_MEM_ERROR, ib_inv.
  destruct (setdict_check (l_s L) bs); [ | | destruct (i_win (l_s L)); [ | destruct aok]]; simpl; auto 10.
Qed.

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | match goal with H: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero H) end
                              | match goal with H: Int.repr _ = Int.repr _ |- _ =>
                                  apply repr_inj_signed in H; [lia | rep_lia | rep_lia] end
                              | lia ].

Ltac gpa := forward_call (Int.repr 1); [ solve [entailer!; try reflexivity] .. | ].

Ltac sd_or t v := ifpost t (Int.repr v);
  [ first [ infeas | solve [forward; entailer!; try reflexivity] ]
  | first [ infeas | solve [forward; entailer!; try reflexivity] ] | ].

Lemma seg_sd_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 220 <= op < 230 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_sd
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  assert_PROP (live_ok L /\ zf_ok (ib_zcall z false false ibp obp ain aout)) as LZ by (unfold istream; entailer!).
  destruct LZ as (LOK & ZOK).
  unfold seg_sd, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  rewrite <- (bytes_inflate_cs Ews aout _ obp), <- (tok_inflate_cs Ews aout obp).
  forward_call (gv, Tsh, vs, ib_zcall z false false ibp obp ain aout, Some L, Ews, obp, 0, aout, bytes_rep bs, bs, true).
  { entailer!. }
  { rewrite ib_istream_opt by auto. cancel. }
  { split; [rewrite Zlength_bytes_rep; lia | ]. rewrite sublist_same; [reflexivity | lia | rewrite Zlength_bytes_rep; lia]. }
  Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
  pose proof (sd_cases bs aok winp (ib_zcall z false false ibp obp ain aout) L FI HI) as SC.
  unfold on_live. rewrite ib_is_live by auto.
  destruct (setdict_f bs aok winp (ib_zcall z false false ibp obp ain aout) L) as [[r z'] L'] eqn:E.
  destruct SC as (-> & HI' & Hr).
  unfold fst3, snd3, thd3; simpl.
  rewrite ib_istream_opt by auto.
  try rewrite (bytes_inflate_cs Ews aout _ obp); try rewrite (tok_inflate_cs Ews aout obp).
  destruct Hr as [-> | [-> | [-> | ->]]];
  [ sd_or _t'34 1; sd_or _t'35 1 | sd_or _t'34 1; sd_or _t'35 1 | sd_or _t'34 0; sd_or _t'35 1 | sd_or _t'34 0; sd_or _t'35 0 ];
  sd_or _t'36 1; gpa;
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal;
  unfold ops_post, ops_post_at, ops_locals; rewrite ib_nin_ge, ib_nout_ge by lia.
  1: Exists 0. 2: Exists (-2). 3: Exists (-3). 4: Exists (-4).
  all: Exists 0 (ib_zcall z false false ibp obp ain aout) L' bs bs; entailer!;
  apply ops_out_same; auto; rep_lia.
Qed.

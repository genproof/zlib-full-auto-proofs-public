(* Law inflate_buffers, main: the branch inflateSync (200 <= op < 210) and its assert. *)
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

(* the outcome of inflateSync on the live stream: its code, the invariant, and what the join knows *)
Lemma ib_sync_out op ain aout ibp obp z L sub r z' L':
  200 <= op -> ib_facts -> live_ok L -> ib_inv L -> zf_ok (ib_zcall z false false ibp obp ain aout) ->
  isptr ibp -> isptr obp -> Zlength sub = ain -> 0 <= aout ->
  sync_f (InBuf Ews ibp 0 ain (bytes_rep sub)) sub (ib_zcall z false false ibp obp ain aout) L = (r, z', L') ->
  (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_DATA_ERROR) /\ ib_inv L' /\
  forall obl, Zlength obl = aout -> is_bytes obl ->
  ops_out op ain aout false false ibp obp z z' r 0 obl obl.
Proof.
  intros Hop FI LOK HI ZOK Pib Pob Hsl Haout E.
  assert (SWF: swf (l_s L)) by (destruct LOK as (_ & W & _); exact W).
  pose proof ZOK as ZOK'.
  destruct ZOK as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). cbn [ib_zcall zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler] in *.
  unfold sync_f in E.
  destruct (sync_s (l_s L) sub) as [ | s1 len | s1 len] eqn:ES; inversion E; subst; clear E.
  - split; [right; left; reflexivity | split; [exact HI |]].
    intros obl Hl Hb. apply ops_out_same; auto; unfold Z_BUF_ERROR; rep_lia.
  - destruct (fi_sync FI _ _ _ _ SWF HI (or_introl ES)) as (Hlen & HI').
    split; [right; right; reflexivity | split; [exact HI' |]].
    unfold Zlib.proof.inflate.Model.u64.
    intros obl Hl Hb.
    unfold ops_out; cbn [set_zf_in ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no in_ptr].
    rewrite Z.sub_diag, Z.add_0_r, Z.add_0_l.
    replace (Zlength sub - (Zlength sub - len)) with len by lia.
    unfold Zlib.proof.inflate.Model.u64.
    rewrite (Z.mod_small (zf_tout z)) by rep_lia.
    repeat split; auto; try rep_lia; try discriminate; try (unfold Z_DATA_ERROR, Z_OK; rep_lia).
    destruct obp; try contradiction; simpl; rewrite ?Ptrofs.add_zero; reflexivity.
  - destruct (fi_sync FI _ _ _ _ SWF HI (or_intror ES)) as (Hlen & HI').
    split; [left; reflexivity | split; [exact HI' |]].
    unfold Zlib.proof.inflate.Model.u64.
    intros obl Hl Hb.
    unfold ops_out; cbn [set_zf_counters reset_keep_z set_zf_in ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no in_ptr].
    rewrite Z.sub_diag, Z.add_0_r, Z.add_0_l.
    replace (Zlength sub - (Zlength sub - len)) with len by lia.
    unfold Zlib.proof.inflate.Model.u64.
    rewrite (Z.mod_small (zf_tout z)) by rep_lia.
    repeat split; auto; try rep_lia; try discriminate; try (unfold Z_DATA_ERROR, Z_OK; rep_lia).
    destruct obp; try contradiction; simpl; rewrite ?Ptrofs.add_zero; reflexivity.
Qed.

(* forward_if whose join adds `temp v (Vint (Int.repr k))` to the current precondition *)
Ltac fif_temp v k :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp v (Vint (Int.repr k)) :: Q) (SEPx R)))
  end.

(* a branch of the result checks: contradictory (the branch condition is false for the known r), or one assignment *)
Ltac fif_contra := exfalso; match goal with
  | H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: Int.repr _ = Int.repr _ |- _ =>
      unfold Z_OK, Z_BUF_ERROR, Z_DATA_ERROR in H; apply repr_inj_signed in H; rep_lia
  end.
Ltac fif_br := first [ fif_contra | (forward; entailer!) ].

Lemma seg_sync_ok {Espec: OracleKind} gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L
    Fr (Post: ret_assert) :
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> 200 <= op < 210 ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_sync
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).
Proof.
  intros H Hop.
  destruct H as (FI & HI & Hpos & Hain & Hpa & Hsrc & Hsb & Haout & Hbsl & Hbsb & Hfl & Harg & Hopr & Hin & Hout & Hst & Psrc & Pib & Pob & Pq).
  unfold ops_pre, ops_locals.
  assert_PROP (isptr vs) as Pvs by entailer!.
  rewrite ib_nin_ge, ib_nout_ge by lia.
  unfold seg_sync, Delta_m, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  set (sub := sublist pos (pos + ain) src).
  assert_PROP (zf_ok (ib_zcall z false false ibp obp ain aout) /\ live_ok L) as ZL
    by (unfold istream; entailer!).
  destruct ZL as (ZOK & LOK).
  assert (Hsl: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  forward_call (gv, Tsh, vs, ib_zcall z false false ibp obp ain aout, Some L, InBuf Ews ibp 0 ain (bytes_rep sub), sub).
  { rewrite ib_istream_opt by auto. cancel. }
  { assert (Hsbb: is_bytes sub) by (unfold sub; apply Forall_sublist; auto).
    cbn [in_ok zf_ni zf_ai ib_zcall in_ptr]. unfold bytes_rep, byte_vals.
    split.
    - rewrite Zlength_map, Z.add_0_l, sublist_same by (rewrite ?Zlength_map; lia).
      repeat split; auto; try lia. rep_lia.
    - destruct ibp; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity. }
  rewrite ib_istream_opt by auto. unfold on_live. rewrite ib_is_live by auto.
  destruct (sync_f (InBuf Ews ibp 0 ain (bytes_rep sub)) sub (ib_zcall z false false ibp obp ain aout) L)
    as [[r z'] L'] eqn:ES.
  destruct (ib_sync_out op ain aout ibp obp z L sub r z' L' ltac:(lia) FI LOK HI ZOK Pib Pob Hsl ltac:(lia) ES)
    as (Hr & HI' & OUT).
  cbn [fst3 snd3 thd3 fst snd].
  destruct Post as [Pn Pb Pc Pr]; unfold overridePost; simpl RA_normal.
  destruct Hr as [-> | [-> | ->]].
  - fif_temp _t'27 1; [fif_br | fif_br |].
    fif_temp _t'28 1; [fif_br | fif_br |].
    fif_temp _t'29 1; [fif_br | fif_br |].
    forward_call (Int.repr 1).
    unfold ops_post, ops_post_at, ops_locals.
    Exists Z_OK 0 z' L' bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    cbn [in_rep].
    entailer!.
  - fif_temp _t'27 1; [fif_br | fif_br |].
    fif_temp _t'28 1; [fif_br | fif_br |].
    fif_temp _t'29 1; [fif_br | fif_br |].
    forward_call (Int.repr 1).
    unfold ops_post, ops_post_at, ops_locals.
    Exists Z_BUF_ERROR 0 z' L' bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    cbn [in_rep].
    entailer!.
  - fif_temp _t'27 0; [fif_br | fif_br |].
    fif_temp _t'28 1; [fif_br | fif_br |].
    fif_temp _t'29 1; [fif_br | fif_br |].
    forward_call (Int.repr 1).
    unfold ops_post, ops_post_at, ops_locals.
    Exists Z_DATA_ERROR 0 z' L' bs bs.
    rewrite ib_nin_ge, ib_nout_ge by lia.
    cbn [in_rep].
    entailer!.
Qed.

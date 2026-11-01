(* uncompress2 for any sizes on any input: the facts of one inflate() call of uncompress2_z's loop and the loop
   invariant, whatever the source holds (UTheoryWAny.uw_any).

   Between two calls the stream m is a live stream (UWLive.uw_mlive) in a mode of the decoder proper (HEAD ..
   BAD: inflate() has not run out of memory), with the counters of the code in range ([uwa_I]).  One call
   ([uwa_call]) offered up to 2^32 - 1 bytes of input and of output space consumes at most the input offered,
   writes at most the space offered and returns Z_MEM_ERROR or a code zlib.h documents for inflate() (never
   Z_STREAM_ERROR); one that does not run out of memory leaves a live stream in a mode HEAD .. BAD.  The facts
   come from the call theory of the laws rj_any_input / api_counters (inflate_pieces/Theory.v: pc_loop's ppost),
   UWLive.uw_live (the stream stays live) and the wide machine invariant along the loop (InvW.mwf3W, kept by
   StepW.stepf2_mwf3W: the consumption bound, for every way the call ends). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.uncompr.UModelW.
Require Import Zlib.proof.uncompr.UWLive.
Require Import Zlib.proof.harness.inflate_pieces.Theory.
Require Import Zlib.proof.inflate.StepW.
Require Zlib.proof.harness.inflate_buffers.IBRun.
Require Zlib.proof.uncompr.UWLoop.
Require Zlib.proof.roundtrip.RTUTheory.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* One call                                                                                       *)

(* the wide machine invariant along inflate()'s loop, up to the exit *)
Lemma uwa_loop_mwf flush m o : loop2 flush lenfix_list distfix_list m o -> mwf3W m -> m_leave m = 0 ->
  match o with IBrk m' => mwf3W m' | IRet _ m' => mwf3W m' end.
Proof.
  intros LP. induction LP as [m r m' E | m m' E Lv | m m' o E Lv LP IH]; intros W L0;
    pose proof (stepf2_mwf3W flush m W L0) as W'; rewrite E in W'.
  - exact W'.
  - exact W'.
  - apply IH; [exact W'|]. pose proof (mwW_leave _ (proj1 W')). lia.
Qed.

(* a call consumes at most its input, however it ends (Z_MEM_ERROR of the window allocation too) *)
Lemma uwa_snx flush m0 res : run2 flush lenfix_list distfix_list m0 res -> mwf3W m0 -> m_leave m0 = 0 ->
  0 <= m_snx (r_m res) <= Zlength (m_inp (r_m res)).
Proof.
  intros (o & LP & HO) W L0. pose proof (uwa_loop_mwf flush m0 o LP W L0) as W'.
  destruct o as [m'|r m'].
  - pose proof (mwW_nx _ (proj1 W')) as NX. destruct HO as [_ _ | ].
    + cbn. exact NX.
    + destruct (IBRun.ib_leave_fin flush m') as (F1 & _ & _ & _ & F5 & _). rewrite F1, F5. exact NX.
  - subst res. cbn [r_m]. exact (mwW_snx _ (proj1 W')).
Qed.

Lemma uwa_call (m: mst) (inp: list Z) (aout: Z) (res: result) :
  uw_mlive m -> HEAD <= i_mode (m_s m) <= BAD ->
  Zlength inp <= Int.max_unsigned -> bytes_ok inp -> 0 <= aout <= Int.max_unsigned ->
  run2 0 lenfix_list distfix_list (m_next m inp aout) res ->
  0 <= m_snx (r_m res) <= Zlength inp /\ Zlength (m_ow (r_m res)) <= aout /\
  (r_ret res = Z_MEM_ERROR \/ code_doc (r_ret res)) /\
  (r_ret res <> Z_MEM_ERROR -> uw_mlive (r_m res) /\ HEAD <= i_mode (m_s (r_m res)) <= BAD).
Proof.
  intros ML MD IL BI AO RUN.
  pose proof ML as ((L & LOK & ES & EH) & SW & HD & T1 & T2 & T3).
  set (z := ZF nullval (Zlength inp) (m_tin m) nullval aout (m_tout m) (m_msg m) 0 (m_adler m) nullval).
  assert (EN: m_next m inp aout = m_init z L inp).
  { unfold m_next, m_init, z. cbn [zf_ao zf_adler zf_msg zf_tin zf_tout]. rewrite ES, EH. reflexivity. }
  assert (ZOK: zf_ok z).
  { unfold zf_ok, z, lrange in *; cbn [zf_ai zf_ao zf_tin zf_tout zf_dt zf_adler].
    pose proof (Zlength_nonneg inp). rep_lia. }
  assert (PI: pinv z L) by (unfold pinv; rewrite ES; auto).
  pose proof (pc_J_init z L inp LOK ZOK BI IL PI) as J0.
  pose proof RUN as RUN0. rewrite EN in RUN.
  pose proof RUN as (o & LP & HO).
  pose proof (pc_loop 0 z L inp stepf2_mwf3W ZOK IL _ o LP J0) as H.
  assert (Hp: ppost z L inp res).
  { destruct o as [m'|r' m']; [exact (H res HO) | subst res; exact H]. }
  destruct Hp as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). cbn [z zf_ao] in Q4.
  pose proof (uwa_snx 0 _ res RUN (proj1 J0) (proj1 (proj2 J0))) as SNX. rewrite Q1 in SNX.
  split; [exact SNX|]. split; [exact Q4|].
  split.
  - destruct (Z.eq_dec (r_ret res) Z_MEM_ERROR) as [E|E]; [left; exact E|right].
    destruct (Q7 E) as (_ & _ & _ & C & _). exact C.
  - intros NM. destruct (Q7 NM) as (_ & _ & M & _).
    destruct (uw_live 0 m inp aout res ML IL BI AO RUN0 NM) as (ML' & _).
    split; [exact ML'|]. unfold m_mode in M. exact M.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

(* the stream between two calls, with `used` bytes consumed, `out` written and ai / ao the avail_in /
   avail_out the last call left *)
Definition uwa_I (src: list Z) (cap: Z) (m: mst) (used: Z) (out: list Z) (ai ao: Z) : Prop :=
  uw_mlive m /\ HEAD <= i_mode (m_s m) <= BAD /\
  0 <= used /\ 0 <= ai <= uw_max /\ used + ai <= Zlength src /\
  0 <= ao <= uw_max /\ Zlength out + ao <= cap.

Lemma uwa_step (src: list Z) (cap: Z) (m: mst) (used: Z) (out: list Z) (ai ao: Z) (res: result) :
  bytes_ok src -> uwa_I src cap m used out ai ao ->
  run2 0 lenfix_list distfix_list (uw_call src cap m used out ai ao) res ->
  0 <= used + m_snx (r_m res) <= Zlength src /\ Zlength (out ++ m_ow (r_m res)) <= cap /\
  (r_ret res = Z_MEM_ERROR \/ code_doc (r_ret res)) /\
  (r_ret res <> Z_MEM_ERROR ->
     uwa_I src cap (r_m res) (used + m_snx (r_m res)) (out ++ m_ow (r_m res))
       (uw_ain src used ai - m_snx (r_m res)) (uw_aout cap out ao - Zlength (m_ow (r_m res)))).
Proof.
  intros BS (ML & MD & U0 & AI & UA & AO & OA) RUN.
  destruct (Zlib.proof.uncompr.UWLoop.uw_ain_range src used ai U0 AI UA) as (AIN & UAIN & _).
  destruct (Zlib.proof.uncompr.UWLoop.uw_aout_range cap out ao AO OA) as (AOUT & OAOUT & _).
  unfold uw_call in RUN.
  set (ain := uw_ain src used ai) in *.
  set (aout := uw_aout cap out ao) in *.
  set (inp := sublist used (used + ain) src) in *.
  assert (LI: Zlength inp = ain) by (unfold inp; rewrite Zlength_sublist; lia).
  assert (BI: bytes_ok inp) by (unfold inp; apply Forall_sublist; exact BS).
  unfold uw_max in *.
  destruct (uwa_call m inp aout res ML MD ltac:(rep_lia) BI ltac:(rep_lia) RUN) as (SNX & OW & RC & NX).
  rewrite LI in SNX. rewrite Zlength_app.
  split; [lia|]. split; [lia|]. split; [exact RC|].
  intros NM. destruct (NX NM) as (ML' & MD').
  split; [exact ML'|]. split; [exact MD'|].
  pose proof (Zlength_nonneg (m_ow (r_m res))). rewrite Zlength_app. repeat split; unfold uw_max; lia.
Qed.

Lemma uwa_loop (src: list Z) (cap: Z) : bytes_ok src ->
  forall m used out ai ao err used' out',
  uncw_loop src cap m used out ai ao err used' out' -> uwa_I src cap m used out ai ao ->
  (err = Z_MEM_ERROR \/ code_doc err) /\ err <> Z_OK /\ Zlength out' <= cap /\ 0 <= used' <= Zlength src.
Proof.
  intros BS m used out ai ao err used' out' U.
  induction U as [m used out ai ao res RUN NOK | m used out ai ao res err used' out' RUN EOK U IH]; intros RI;
    destruct (uwa_step src cap m used out ai ao res BS RI RUN) as (S1 & S2 & S3 & S4).
  - auto.
  - apply IH. apply S4. rewrite EOK. discriminate.
Qed.

(* the stream after inflateInit_ (UModel.m_first), nothing offered yet *)
Lemma uwa_I_first (src: list Z) (cap: Z) : 0 <= cap -> uwa_I src cap m_first 0 [] 0 0.
Proof.
  intros CAP.
  set (sp := Vptr xH Ptrofs.zero).
  split.
  - split; [exists (init_live sp 15); split; [apply Zlib.proof.roundtrip.RTUTheory.rtu_init_live_ok; exact I|];
            split; reflexivity|].
    split; [unfold swfW; split; intros E; vm_compute in E; discriminate|].
    split; [vm_compute; reflexivity|].
    unfold lrange; cbn; rep_lia.
  - split; [vm_compute; split; discriminate|].
    pose proof (Zlength_nonneg src). unfold uw_max. rewrite Zlength_nil. rep_lia.
Qed.

(* uncompress2_z's return value from the last code of the loop *)
Lemma uwa_unc_ret (err rest: Z) : (err = Z_MEM_ERROR \/ code_doc err) -> err <> Z_OK ->
  unc_ret err rest = Z_OK \/ unc_ret err rest = Z_MEM_ERROR \/ unc_ret err rest = Z_BUF_ERROR \/
  unc_ret err rest = Z_DATA_ERROR.
Proof.
  unfold code_doc. intros [E|[E|[E|[E|[E|E]]]]] N; subst err; try (contradiction N; reflexivity);
    unfold unc_ret; cbn -[Z.eqb]; try (destruct (rest =? 0); cbn); tauto.
Qed.

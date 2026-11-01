(* The laws res_free_deflate and res_memory_deflate: what the model of deflateInit2_ says about its outcome,
   for the harness's call deflateInit2(&strm, level, Z_DEFLATED, window_bits, mem_level, strategy) whose five
   allocations may each fail ([a1] .. [a5] of za_deflateInit2__spec's postcondition).

   - It returns Z_OK exactly when it made a state.
   - Then every allocation succeeded (so the model call is the one za_deflate_model_stmt speaks of), the
     parameters are accepted, the state has no gzip header, and the stream has total_in = total_out = 0, no
     message and adler 0 or 1;
   - its state has the sizes of the parameters (w_size, hash_size, lit_bufsize). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInitKit.
#[local] Existing Instance DCS.CS.

Lemma init_none_code level method wbits mem strategy a1 a2 a3 a4 a5 z r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r ->
  fst (fst r) = None -> snd r <> Z_OK.
Proof.
  intros H N. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P.
  2:{ inversion H; subst r; cbn; discriminate. }
  destruct a1. 2:{ inversion H; subst r; cbn; discriminate. }
  destruct (a2 && a3 && a4 && a5)%bool. 2:{ inversion H; subst r; cbn; discriminate. }
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst r. discriminate.
Qed.

(* the stream a successful deflateInit2_ returns *)
Definition init_strm_ok (z : strm) : Prop :=
  z_total_in z = 0 /\ z_total_out z = 0 /\ z_msg z = None /\ 0 <= z_adler z <= 1.

Lemma init_some level method wbits mem strategy a1 a2 a3 a4 a5 z s z' code :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', code) ->
  code = Z_OK /\ params_ok level method wbits mem strategy = true /\
  c_deflateInit2_ true true false level method wbits mem strategy true true true true true z
    = Some (Some s, z', code) /\
  d_gzhead s = None /\ init_strm_ok z'.
Proof.
  intros H. pose proof H as H0. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P; [ | discriminate].
  destruct a1; [ | discriminate].
  destruct (a2 && a3 && a4 && a5)%bool; [ | discriminate].
  pose proof H as H1.
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst. clear H.
  split; [reflexivity | ]. split; [reflexivity | ]. split; [exact H1 | ].
  split.
  - rewrite Zlib.proof.deflate.LTCInitKit.fin_eq. reflexivity.
  - unfold init_strm_ok, Zlib.proof.deflate.LTCInitKit.rk_strm. cbn.
    repeat split; try reflexivity. all: destruct (_ =? 2); lia.
Qed.

(* the return code tells whether there is a state *)
Lemma init_code_ok level method wbits mem strategy a1 a2 a3 a4 a5 z r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r ->
  (snd r = Z_OK <-> exists s, fst (fst r) = Some s).
Proof.
  intros H. destruct r as [[[s|] z'] code].
  - destruct (init_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as [E _]. cbn. split; eauto.
  - pose proof (init_none_code _ _ _ _ _ _ _ _ _ _ _ _ H eq_refl). cbn in *. split; [tauto | ].
    intros [s E]; discriminate.
Qed.

(* A successful deflateInit2_ had accepted parameters, and its state has the sizes of those parameters. *)
Lemma init_sizes level method wbits mem strategy a1 a2 a3 a4 a5 z s z' r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', r) ->
  params_ok level method wbits mem strategy = true /\
  d_w_size s = 2 ^ Z.max 9 (wb_of wbits) /\ d_hash_size s = 2 ^ (mem + 7) /\
  tr_lit_bufsize (d_tr s) = 2 ^ (mem + 6).
Proof.
  intros H. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P; [ | discriminate].
  destruct a1; [ | discriminate].
  destruct (a2 && a3 && a4 && a5)%bool; [ | discriminate].
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst s. clear H.
  pose proof (Zlib.proof.deflate.LTCInitKit.params_bounds _ _ _ _ _ P) as (_ & Hw & _ & Hm & _).
  rewrite Zlib.proof.deflate.LTCInitKit.fin_eq.
  unfold Zlib.proof.deflate.LTCInitKit.sG. cbn [d_w_size d_hash_size d_tr tr_lit_bufsize].
  rewrite !Z.shiftl_1_l. auto.
Qed.

(* its return code is Z_OK, Z_STREAM_ERROR or Z_MEM_ERROR *)
Lemma init_code_range level method wbits mem strategy a1 a2 a3 a4 a5 z r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some r ->
  -4 <= snd r <= 0.
Proof.
  intros H. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P.
  2:{ inversion H; subst r; cbn; unfold Z_STREAM_ERROR; lia. }
  destruct a1. 2:{ inversion H; subst r; cbn; unfold Z_MEM_ERROR; lia. }
  destruct (a2 && a3 && a4 && a5)%bool. 2:{ inversion H; subst r; cbn; unfold Z_MEM_ERROR; lia. }
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst r. cbn; unfold Z_OK; lia.
Qed.

(* Law rt_gzip_header on the round-2 harness, inflate side: the loop of one inflate() call while it is in the gzip
   header (G2IDefs.Km2 at its loop heads, from the cases G2ICases.g2_cases): the call either leaves the loop inside
   the header (out of input), or reaches the TYPE loop head after the header, from where the decode theory takes
   over; and the exit (inf_leave) inside the header. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Zlib.proof.harness.inflate_header.IHTCall.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass, the loop                                                                             *)

Ltac g2l_stepto c :=
  match goal with |- ok_out2 _ _ _ _ _ _ _ _ (stepf2 ?f ?fx ?dx ?m) =>
    replace (stepf2 f fx dx m) with (c m) by (unfold stepf2, step2; unfold m_mode in *;
      match goal with E: i_mode (m_s m) = _ |- _ => rewrite E end; reflexivity) end.

Lemma g2l_step : g2_cases_stmt -> forall g src h0 wb pos inp aout tin flush m,
  g2h_ok g -> hwf8 h0 -> lay2 g src -> ctx2 src pos inp ->
  Km2 g src h0 wb pos inp aout tin m -> m_leave m = 0 -> m_mode m <> Zlib.proof.inflate.Model.TYPE ->
  ok_out2 g src h0 wb pos inp aout tin (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros C g src h0 wb pos inp aout tin flush m G W LY X K L NT.
  destruct C as (CHE & CFL & CTI & COS & CEL & CEX & CNA & CCO & CHC).
  pose proof (km2_j _ _ _ _ _ _ _ _ _ K) as JJ.
  destruct JJ;
    match goal with E: i_mode (m_s m) = ?md |- _ => assert (Em: m_mode m = md) by exact E end;
    first
    [ solve [g2l_stepto c_HEAD2; apply CHE; auto] | solve [g2l_stepto c_FLAGS2; apply CFL; auto]
    | solve [g2l_stepto c_TIME2; apply CTI; auto] | solve [g2l_stepto c_OS2; apply COS; auto]
    | solve [g2l_stepto c_EXLEN2; apply CEL; auto] | solve [g2l_stepto c_EXTRA2; apply CEX; auto]
    | solve [g2l_stepto c_NAME2; apply CNA; auto] | solve [g2l_stepto c_COMMENT2; apply CCO; auto]
    | solve [g2l_stepto c_HCRC; apply CHC; auto]
    | contradiction ].
Qed.

(* the loop from a loop head inside the header: it leaves inside the header, or reaches the TYPE loop head *)
Lemma g2l_loop : g2_cases_stmt -> forall g src h0 wb pos inp aout tin flush m o,
  g2h_ok g -> hwf8 h0 -> lay2 g src -> ctx2 src pos inp ->
  loop2 flush lenfix_list distfix_list m o ->
  Km2 g src h0 wb pos inp aout tin m -> m_leave m = 0 -> m_mode m <> Zlib.proof.inflate.Model.TYPE ->
  (exists m', o = IBrk m' /\ Km2 g src h0 wb pos inp aout tin m' /\ m_leave m' = 1) \/
  (exists mT, Km2 g src h0 wb pos inp aout tin mT /\ m_leave mT = 0 /\
              m_mode mT = Zlib.proof.inflate.Model.TYPE /\ loop2 flush lenfix_list distfix_list mT o).
Proof.
  intros C g src h0 wb pos inp aout tin flush m o G W LY X LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K L0 NT.
  - pose proof (g2l_step C g src h0 wb pos inp aout tin flush m G W LY X K L0 NT) as S.
    rewrite E in S. destruct S.
  - pose proof (g2l_step C g src h0 wb pos inp aout tin flush m G W LY X K L0 NT) as S.
    rewrite E in S. cbn in S. left. exists m'. auto.
  - pose proof (g2l_step C g src h0 wb pos inp aout tin flush m G W LY X K L0 NT) as S.
    rewrite E in S. cbn in S.
    assert (L': m_leave m' = 0) by (destruct (km2_lv _ _ _ _ _ _ _ _ _ S) as [A|(A & _)]; [exact A | contradiction]).
    destruct (Z.eq_dec (m_mode m') Zlib.proof.inflate.Model.TYPE) as [T|T].
    + right. exists m'. auto.
    + exact (IH S L' T).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit inside the header                                                                     *)

(* inf_leave of a machine that wrote nothing, has no window and returns Z_OK: no window update (so no
   Z_MEM_ERROR), the struct keeps the fields of the header passes, and inflate(Z_FINISH) returns Z_BUF_ERROR *)
Lemma g2l_fin m : i_wsize (m_s m) = 0 -> m_out m = m_aout m -> m_ow m = [] -> m_tout m = 0 ->
  i_total (m_s m) = 0 -> m_ret m = Z_OK ->
  let res := leave_fin Z_FINISH m in
  r_ret res = Z_BUF_ERROR /\ m_ow (r_m res) = [] /\ m_sow (r_m res) = 0 /\ m_aout (r_m res) = m_aout m /\
  m_snx (r_m res) = m_nx m /\ m_inp (r_m res) = m_inp m /\ m_tout (r_m res) = 0 /\ m_h (r_m res) = m_h m /\
  i_mode (m_s (r_m res)) = m_mode m /\ i_last (m_s (r_m res)) = i_last (m_s m) /\
  i_check (m_s (r_m res)) = i_check (m_s m) /\ i_flags (m_s (r_m res)) = i_flags (m_s m) /\
  i_length (m_s (r_m res)) = i_length (m_s m) /\ i_wrap (m_s (r_m res)) = i_wrap (m_s m) /\
  i_head (m_s (r_m res)) = i_head (m_s m) /\ i_wsize (m_s (r_m res)) = 0 /\ i_total (m_s (r_m res)) = 0 /\
  i_wbits (m_s (r_m res)) = i_wbits (m_s m) /\
  i_hold (m_s (r_m res)) = m_hold m /\ i_bits (m_s (r_m res)) = m_bits m /\
  m_s (r_m res) = set_i_bits (set_i_hold (set_i_total (m_s m) 0) (m_hold m)) (m_bits m).
Proof.
  intros Ws O W T Tt R. cbv zeta. unfold leave_fin.
  rewrite (Zlib.proof.harness.inflate_header.IHTCall.ihl_leave_ok Z_FINISH m Ws O W).
  cbv zeta.
  assert (Eo: u32 (m_out (restore m) - m_left (restore m)) = 0).
  { unfold m_left. cbn. rewrite O, W, Zlength_nil, Z.sub_0_r, Z.sub_diag. reflexivity. }
  rewrite Eo. rewrite andb_false_r.
  cbn. unfold m_mode. rewrite Ws, Tt, T, W, R. cbn.
  split; [rewrite orb_true_r; reflexivity|].
  repeat split; auto.
Qed.

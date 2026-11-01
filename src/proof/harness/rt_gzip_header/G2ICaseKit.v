(* Law rt_gzip_header on the round-2 harness, inflate side: small facts and tactics shared by the header case
   proofs G2ICase*.v (G2IDefs.case_ok2).  They adapt law inflate_header's IHTCaseKit.v (whose reduction tactic
   ihk_red and list facts are reused) to the state J2 over any input src (lay2), to the call's fixed fields and to
   the ranges of the state (Km2). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Export Zlib.proof.harness.inflate_header.IHTCaseKit.
Require Zlib.proof.inflate.Step3Header.
Require Zlib.proof.inflate.MwfLemmas.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The ranges of the state (Inv.swf) under the setters the header cases use                        *)

Definition g2k_swf_check := Zlib.proof.inflate.Step3Header.swf_check.
Definition g2k_swf_flags := Zlib.proof.inflate.Step3Header.swf_flags.
Definition g2k_swf_length := Zlib.proof.inflate.Step3Header.swf_length.
Definition g2k_swf_wbits := Zlib.proof.inflate.Step3Header.swf_wbits.
Definition g2k_swf_mode := Zlib.proof.inflate.MwfLemmas.swf_set_mode.
Definition g2k_crc_lrange := Zlib.proof.inflate.Step3Header.ref_crc32_lrange.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine                                                                                    *)

(* what holds in every mode, kept by setters that do not touch wrap, head, wsize, total, wbits and the maxima *)
Lemma g2k_jc wb h0 s h s' h' : Jc2 wb h0 s h ->
  i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_wsize s' = i_wsize s -> i_total s' = i_total s ->
  i_wbits s' = i_wbits s ->
  h_extra_max h' = h_extra_max h -> h_name_max h' = h_name_max h -> h_comm_max h' = h_comm_max h ->
  Jc2 wb h0 s' h'.
Proof. intros [A B C D E F G H I] ? ? ? ? ? ? ? ?. constructor; congruence || exact I. Qed.

Ltac g2k_jc := eapply g2k_jc; [eassumption | ..]; ihk_red; reflexivity.

(* Km2 of a machine m' reached from m in the same call: the fields of the call kept, the position moved on *)
Lemma g2k_km g src h0 wb pos inp aout tin m m' :
  Km2 g src h0 wb pos inp aout tin m ->
  m_inp m' = m_inp m -> m_nx m <= m_nx m' <= Zlength inp -> m_ow m' = [] -> m_out m' = m_out m ->
  m_aout m' = m_aout m -> m_tout m' = 0 -> m_ret m' = Z_OK -> m_in m' = m_in m -> m_tin m' = m_tin m ->
  m_snx m' = m_snx m -> m_sow m' = m_sow m -> lrange (m_adler m') ->
  (m_leave m' = 0 \/
   (m_leave m' = 1 /\ m_nx m' = Zlength inp /\ pos + m_nx m' < ih_nh g /\
    m_mode m' <> Zlib.proof.inflate.Model.TYPE)) ->
  Jc2 wb h0 (m_s m') (m_h m') -> J2 g src h0 (pos + m_nx m') (m_s m') (m_h m') (m_hold m') (m_bits m') ->
  swf (m_s m') ->
  Km2 g src h0 wb pos inp aout tin m'.
Proof.
  intros K I N O U A T R Ii Ti S W D L C J SW.
  destruct K as [Ki Kn Kw Ko Kt Kr Kl Kc Kj Ks (Fa & Fi & Ft & Fs & Fw & Fd)].
  constructor; try congruence; try lia; auto.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ D))))); congruence.
Qed.

(* the same machine, nothing changed but what the arguments say: m' keeps the adler field *)
Lemma g2k_km_ad g src h0 wb pos inp aout tin m m' :
  Km2 g src h0 wb pos inp aout tin m ->
  m_inp m' = m_inp m -> m_nx m <= m_nx m' <= Zlength inp -> m_ow m' = [] -> m_out m' = m_out m ->
  m_aout m' = m_aout m -> m_tout m' = 0 -> m_ret m' = Z_OK -> m_in m' = m_in m -> m_tin m' = m_tin m ->
  m_snx m' = m_snx m -> m_sow m' = m_sow m -> m_adler m' = m_adler m ->
  (m_leave m' = 0 \/
   (m_leave m' = 1 /\ m_nx m' = Zlength inp /\ pos + m_nx m' < ih_nh g /\
    m_mode m' <> Zlib.proof.inflate.Model.TYPE)) ->
  Jc2 wb h0 (m_s m') (m_h m') -> J2 g src h0 (pos + m_nx m') (m_s m') (m_h m') (m_hold m') (m_bits m') ->
  swf (m_s m') ->
  Km2 g src h0 wb pos inp aout tin m'.
Proof.
  intros K I N O U A T R Ii Ti S W D L C J SW. eapply g2k_km; eauto.
  rewrite D. apply (proj2 (proj2 (proj2 (proj2 (proj2 (km2_fr _ _ _ _ _ _ _ _ _ K)))))).
Qed.

(* close the fields of g2k_km_ad that are equalities of the machine's projections, leaving the leave
   condition, Jc2, J2 and swf *)
Ltac g2k_km K :=
  eapply (g2k_km_ad _ _ _ _ _ _ _ _ _ _ K);
  ihk_red; [reflexivity | lia | apply (km2_ow _ _ _ _ _ _ _ _ _ K) | reflexivity | reflexivity
           | apply (km2_tout _ _ _ _ _ _ _ _ _ K) | apply (km2_ret _ _ _ _ _ _ _ _ _ K) | reflexivity
           | reflexivity | reflexivity | reflexivity | reflexivity | .. ].

(* the return code: Z_OK at every loop head of Km2 *)
Lemma g2k_ret g src h0 wb pos inp aout tin m : Km2 g src h0 wb pos inp aout tin m -> m_ret m = Z_OK.
Proof. intros K. exact (km2_ret _ _ _ _ _ _ _ _ _ K). Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header                                                                                      *)

Lemma g2k_flg g : g2h_ok g -> 0 <= g_flg g <= 255.
Proof. unfold g2h_ok. lia. Qed.

Lemma g2k_badcrc g : g2h_ok g -> ih_badcrc g = false.
Proof.
  unfold g2h_ok, ih_badcrc. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D). rewrite D.
  destruct (fl g 2); reflexivity.
Qed.

(* crc_if on a gzip header (wrap 6) with state->flags = 8 + 256 FLG *)
Lemma g2k_crc_if (KIT: g2_kit) g m d :
  0 <= g_flg g <= 255 -> i_flags (m_s m) = 8 + 256 * g_flg g -> i_wrap (m_s m) = 6 ->
  crc_if m d = if fl g 2 then upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d)) else m.
Proof.
  intros R F W. destruct (proj1 (k2_bits KIT) (g_flg g) R) as (_ & _ & _ & F512 & _).
  unfold crc_if. rewrite F, F512, W. cbn [Z.land Z.eqb negb]. rewrite andb_true_r.
  unfold fl. destruct (negb _); auto.
Qed.

(* the bit buffer of the bytes src[a .. a) *)
Lemma g2k_bb0 src a : bb2 src a a 0 0.
Proof. unfold bb2. rewrite sublist_nil. split; reflexivity || lia. Qed.

Lemma g2k_lay_src g src : lay2 g src -> 10 <= ih_xs g /\ ih_nh g <= Zlength src /\ 10 <= ih_nh g.
Proof.
  intros LY. pose proof (l2_len _ _ LY). pose proof (l2_ord _ _ LY). unfold ih_xs in *.
  destruct (fl g 4); lia.
Qed.

(* the input offered: src[pos .. pos + |inp|) *)
Lemma g2k_ctx src pos inp : ctx2 src pos inp ->
  0 <= pos /\ pos + Zlength inp <= Zlength src /\ inp = sublist pos (pos + Zlength inp) src.
Proof. auto. Qed.

(* close a side goal of a case without risking a conversion over CRCs: hypotheses, arithmetic, the header
   predicates on unchanged fields *)
Ltac g2k_safe :=
  solve [ assumption | lia | apply g2k_bb0
        | unfold hx0, hn0, hc0, hT, hM, hO, hxf, hnf, hcf, hxk, hnk, hck, fg in *; ihk_red; assumption
        | unfold hx0, hn0, hc0, hT, hM, hO, hxf, hnf, hcf, hxk, hnk, hck, fg in *; ihk_red; tauto
        | unfold fg; ihk_red; reflexivity
        | unfold ih_reserved in *; assumption ].

Definition g2k_hb2 := Zlib.proof.inflate.Step3Header.hbytes2_bytes.
Definition g2k_hb4 := Zlib.proof.inflate.Step3Header.hbytes4_bytes.

(* swf of a state built by the header cases' setters from a state with swf: the setters peeled off, the ranges of
   the values left (modes, flags, CRCs of bytes, lengths) *)
Ltac g2k_swf :=
  repeat first [ assumption
               | apply g2k_swf_mode | apply g2k_swf_check | apply g2k_swf_flags | apply g2k_swf_length ];
  try solve [ unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE,
                SYNC; lia
            | apply g2k_crc_lrange; first [apply g2k_hb2 | apply g2k_hb4 | apply Forall_sublist; assumption]
            | unfold lrange, urange, srange in *; rep_lia ].

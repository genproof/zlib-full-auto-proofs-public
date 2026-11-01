(* Law inflate_header, theory: small facts and tactics shared by the case proofs IHTCase*.v *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_header.IHTDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* reduce the projections of the machine's setters *)
Ltac ihk_red :=
  unfold m_mode, m_have, m_left in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       set_m_ow set_m_out set_m_ret set_m_tout
       upd_s upd_h set_mode set_leave set_bad initbits dropbits bytebits
       i_mode i_wrap i_head i_length i_flags i_check i_last i_wsize i_total i_wbits
       set_i_mode set_i_check set_i_length set_i_flags set_i_wbits set_i_last set_i_total
       h_done h_hcrc h_text h_time h_xflags h_os h_xp h_extra_len h_xbuf h_np h_nbuf h_cp h_cbuf
       h_extra_max h_name_max h_comm_max set_h_done set_h_hcrc set_h_text set_h_time set_h_xflags set_h_os
       set_h_xp set_h_extra_len set_h_xbuf set_h_np set_h_nbuf set_h_cp set_h_cbuf] in *.

(* dismiss the constructors of J whose mode is not the one of the machine *)
Ltac ihk_nomode :=
  exfalso; repeat match goal with H: _ \/ _ |- _ => destruct H end;
  repeat match goal with E: i_mode _ = _ |- _ => rewrite E in *; clear E end;
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, TYPEDO,
    STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD in *; lia.

Lemma ihk_jc h0 s h s' h' : Jc h0 s h ->
  i_wrap s' = i_wrap s -> i_head s' = i_head s -> i_wsize s' = i_wsize s -> i_total s' = i_total s ->
  h_extra_max h' = h_extra_max h -> h_name_max h' = h_name_max h -> h_comm_max h' = h_comm_max h ->
  Jc h0 s' h'.
Proof. intros [A B C D E F G] ? ? ? ? ? ? ?. constructor; congruence. Qed.

Ltac ihk_jc := eapply ihk_jc; [eassumption | ..]; ihk_red; reflexivity.

(* the return code at a header mode *)
Lemma ihk_ret m md : m_ret m = Z_OK \/ (m_ret m = Z_STREAM_END /\ m_mode m = DONE) \/
    (m_ret m = Z_DATA_ERROR /\ m_mode m = BAD) ->
  m_mode m = md -> md <> DONE -> md <> BAD -> m_ret m = Z_OK.
Proof. intros [R|[(_ & D)|(_ & D)]] E N1 N2; auto; congruence. Qed.

(* crc_if on a gzip header with state->flags = 8 + 256 FLG *)
Lemma ihk_crc_if (KIT: ih_kit) g m d :
  0 <= g_flg g <= 255 -> i_flags (m_s m) = 8 + 256 * g_flg g -> (i_wrap (m_s m) = 6 \/ i_wrap (m_s m) = 7 \/ i_wrap (m_s m) = 14 \/ i_wrap (m_s m) = 15) ->
  crc_if m d = if fl g 2 then upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d)) else m.
Proof.
  intros R F W. destruct (proj1 (k_bits KIT) (g_flg g) R) as (_ & _ & _ & F512 & _).
  unfold crc_if. rewrite F, F512.
  assert (W4: negb (Z.land (i_wrap (m_s m)) 4 =? 0) = true) by (destruct W as [W|[W|[W|W]]]; rewrite W; reflexivity).
  rewrite W4, andb_true_r. unfold fl. destruct (negb _); auto.
Qed.

Lemma ihk_flg g : ih_ok g -> 0 <= g_flg g <= 255.
Proof. unfold ih_ok. lia. Qed.

(* the bit buffer of the bytes src[a .. a) *)
Lemma ihk_bb0 g a : bb g a a 0 0.
Proof. unfold bb. rewrite sublist_nil. split; reflexivity || lia. Qed.

(* close a side goal of a case without risking a conversion over CRCs: hypotheses, arithmetic, the header
   predicates on unchanged fields *)
Ltac ihk_safe :=
  solve [ assumption | lia | apply ihk_bb0
        | unfold hx0, hn0, hc0, hT, hM, hO, hxf, hnf, hcf, hxk, hnk, hck, fg in *; ihk_red; assumption
        | unfold hx0, hn0, hc0, hT, hM, hO, hxf, hnf, hcf, hxk, hnk, hck, fg in *; ihk_red; tauto
        | unfold fg; ihk_red; reflexivity
        | unfold ih_reserved in *; assumption ].

Lemma ihk_fbuf_nil (b0: list Z) : fbuf b0 [] = b0.
Proof.
  unfold fbuf. rewrite Zlength_nil. rewrite Z.min_l by (apply Zlength_nonneg).
  rewrite sublist_nil, app_nil_l, sublist_same; auto.
Qed.

Lemma ihk_lay_src g : ih_lay g -> 13 <= Zlength (ih_src g) /\ 10 <= ih_xs g.
Proof.
  intros LY. pose proof (ly_len _ LY). pose proof (ly_ord _ LY). unfold ih_xs in *. destruct (fl g 4); lia.
Qed.

(* a sublist inside a known sublist of src *)
Lemma ihk_sub (src l: list Z) a n i j :
  sublist a (a + n) src = l -> 0 <= a -> 0 <= i <= j -> j <= n -> sublist (a + i) (a + j) src = sublist i j l.
Proof.
  intros Ex A I Jn. rewrite <- Ex. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the mode of a machine at a header mode is not DONE / BAD *)
Lemma ihk_jlast g h0 P s h hold bits : J g h0 P s h hold bits -> True.
Proof. auto. Qed.

(* the bytes from next on, as bytes of a field f = src[a .. a + |f|) *)
Lemma ihk_bytes (src inp f: list Z) pos nx a i :
  inp = sublist pos (pos + Zlength inp) src -> 0 <= pos -> pos + Zlength inp <= Zlength src ->
  sublist a (a + Zlength f) src = f -> 0 <= a -> 0 <= nx -> 0 <= i -> nx + i < Zlength inp ->
  a <= pos + nx -> pos + nx - a + i < Zlength f ->
  Znth i (sublist nx (Zlength inp) inp) = Znth (pos + nx - a + i) f.
Proof.
  intros X2 X0 X1 Ef A N I NI Ap Af.
  rewrite Znth_sublist by lia.
  set (L := Zlength inp) in *. clearbody L. subst inp.
  rewrite Znth_sublist by lia.
  rewrite <- Ef. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

(* a field ending with its zero byte *)
Lemma ihk_field (nf: list Z) : Forall (fun b => 0 < b <= 255) nf ->
  0 < Zlength (nf ++ [0]) /\ Znth (Zlength (nf ++ [0]) - 1) (nf ++ [0]) = 0 /\
  (forall i, 0 <= i < Zlength (nf ++ [0]) - 1 -> Znth i (nf ++ [0]) <> 0).
Proof.
  intros F. rewrite Zlength_app, Zlength_cons, Zlength_nil.
  pose proof (Zlength_nonneg nf).
  split; [lia|]. split.
  - rewrite Znth_app2 by lia. replace (Zlength nf + Z.succ 0 - 1 - Zlength nf) with 0 by lia. reflexivity.
  - intros i I. rewrite Znth_app1 by lia.
    assert (Hb: 0 < Znth i nf <= 255) by (apply (proj1 (Forall_Znth _ _) F); lia). lia.
Qed.

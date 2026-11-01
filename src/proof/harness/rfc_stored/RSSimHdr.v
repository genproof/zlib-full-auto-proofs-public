(* Law rfc_stored, the padding simulation: the header passes (HEAD, FLAGS, TIME, OS, with the fallthroughs of OS
   into EXLEN .. HCRC) read only header bytes, which the real input shares with the canonical one, so they do
   the same on both. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Require Import Zlib.proof.rfc1951.DecHdr Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The header bytes                                                                               *)

(* the real input agrees with the canonical one on the bytes of the header: the first bytes of blocks, the
   only places where they differ, come after it *)
Lemma rs_hdr_agree (L: rs_lay_stmt) G pos x inp' : rs_xrel G pos x inp' ->
  forall i, 0 <= i -> 8 * (pos + i) < D0 G -> Znth i x = Znth i inp'.
Proof.
  intros (Hl & _ & Hx) i Hi Hd.
  destruct (Z_lt_le_dec i (Zlength x)) as [Lt|Ge].
  - destruct (Hx i ltac:(lia)) as [E|((k & Hk & Hb) & _)]; [exact E|].
    pose proof (rl_D0 L G k ltac:(lia)). lia.
  - rewrite !Znth_overflow by lia. reflexivity.
Qed.

(* NEEDBITS(n) inside the header reads the same bytes on both inputs *)
Lemma rs_nb_hdr (L: rs_lay_stmt) G pos x m n : rs_xrel G pos x (m_inp m) -> 0 <= m_nx m -> 0 <= m_bits m ->
  n <= 32 -> 8 * (pos + m_nx m) - m_bits m + n <= D0 G ->
  needbits n (set_m_inp m x) = set_m_inp (needbits n m) x.
Proof.
  intros Hx Hnx Hb Hn Hq. apply rs_needbits_inp4; auto.
  - destruct Hx as (Hl & _). exact Hl.
  - intros i H1 H2. apply (rs_hdr_agree L G pos x (m_inp m) Hx); lia.
Qed.

(* the header in the bits of the source *)
Lemma rs_hdr_bits G : dctx_ok7a G -> sublist 0 (D0 G) (sbits G) = bytes_bits (hdr_bytes (dc_w G)).
Proof.
  intros (_ & _ & _ & _ & Hs & _ & _ & Heq).
  destruct (dh_hdr_prefix (dc_w G) (dc_hist G) (dc_bs G)) as (r & Er).
  assert (Sl : 0 <= slen G) by (unfold slen; apply Zlength_nonneg).
  assert (Es : dc_src G = hdr_bytes (dc_w G) ++ r ++ sublist (slen G) (Zlength (dc_src G)) (dc_src G)).
  { rewrite <- (sublist_same 0 (Zlength (dc_src G)) (dc_src G)) at 1 by lia.
    rewrite <- (sublist_rejoin 0 (slen G) (Zlength (dc_src G))) by lia.
    rewrite Heq, Er, <- app_assoc. reflexivity. }
  unfold sbits, D0. rewrite Es.
  pose proof (dh_sub_bb [] (hdr_bytes (dc_w G)) (r ++ sublist (slen G) (Zlength (dc_src G)) (dc_src G))) as X.
  replace (Zlength (@nil Z)) with 0 in X by reflexivity. rewrite app_nil_l in X.
  replace (8 * 0) with 0 in X by lia. rewrite Z.add_0_l in X. exact X.
Qed.

Lemma rs_gz_facts G h : dctx_ok7a G -> dc_w G = WGzip h ->
  gz_simple h /\ D0 G = 80 /\ dh_gzf (8 + 256 * gz_flg h).
Proof.
  intros (_ & _ & Hs & _) E. specialize (Hs h E). destruct (dh_gz_simple_bytes h Hs) as (_ & F).
  split; [exact Hs|]. split.
  - unfold D0. rewrite E. cbn [hdr_bytes]. rewrite (dh_gz_len h Hs). reflexivity.
  - unfold dh_gzf. rewrite F. destruct (gz_text h); auto.
Qed.

(* the bytes 2, 3 of a gzip header: CM = 8 and FLG *)
Lemma rs_gz_hold_flags G h : dctx_ok7a G -> dc_w G = WGzip h ->
  bval (sublist 16 32 (sbits G)) = 8 + 256 * gz_flg h.
Proof.
  intros Hok Ew. destruct (rs_gz_facts G h Hok Ew) as (Hs & HD0 & _).
  assert (X0 : sublist 16 32 (sbits G) = sublist 16 32 (bytes_bits (hdr_bytes (dc_w G)))).
  { rewrite <- (rs_hdr_bits G Hok), HD0. rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite X0, Ew. cbn [hdr_bytes].
  destruct (dh_gz_simple_bytes h Hs) as (B & F). rewrite B, F.
  pose proof (dh_sub_bb [31; 139] [8; if gz_text h then 1 else 0] (le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h])) as X.
  replace (Zlength [31; 139]) with 2 in X by reflexivity.
  replace (Zlength [8; if gz_text h then 1 else 0]) with 2 in X by reflexivity.
  change (8 * 2 + 8 * 2) with 32 in X. change (8 * 2) with 16 in X. rewrite X.
  destruct (gz_text h); reflexivity.
Qed.

(* a raw stream: inflateInit2 set wrap = 0 *)
Lemma rs_raw_wrap G s : dctx_ok7a G -> dc_w G = WRaw -> glob_ok G s -> i_wrap s = 0.
Proof.
  intros ((Hwb & _) & Ha & _) E ((wb0 & Er & _) & _).
  destruct Ha as [Ha|(wb & fl & did & Ez & _)]; [|congruence].
  unfold accepts in Ha. rewrite E in Ha. rewrite Ha in Er.
  destruct (dh_reset2_vals _ Hwb) as (R1 & _). rewrite (init_wrap_wb_of _ _ _ R1) in Er.
  injection Er as Er1 _. rewrite <- Er1. apply dh_rw. lia.
Qed.

(* a wrapped stream: the header has at least two bytes *)
Lemma rs_wrapped_D0 G : dctx_ok7a G -> dc_w G <> WRaw -> 16 <= D0 G.
Proof.
  intros Hok Ew. destruct (dc_w G) as [|wb fl did|h] eqn:E; [congruence| |].
  - unfold D0. rewrite E. cbn [hdr_bytes]. rewrite Zlength_app.
    replace (Zlength (zlib_hdr wb fl (match did with Some _ => true | None => false end))) with 2 by reflexivity.
    pose proof (Zlength_nonneg (match did with Some i => be_bytes i 4 | None => [] end)). lia.
  - destruct (rs_gz_facts G h Hok E) as (_ & D & _). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine with another input                                                                 *)

Lemma rs_mv_inp m x a b c : dh_mv (set_m_inp m x) a b c = set_m_inp (dh_mv m a b c) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_mode_inp m x v : set_mode (set_m_inp m x) v = set_m_inp (set_mode m v) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_upds_inp m x f : upd_s (set_m_inp m x) f = set_m_inp (upd_s m f) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_adler_inp m x v : set_m_adler (set_m_inp m x) v = set_m_inp (set_m_adler m v) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_init_inp m x : initbits (set_m_inp m x) = set_m_inp (initbits m) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_drop_inp m x n : dropbits n (set_m_inp m x) = set_m_inp (dropbits n m) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_updh_inp m x f : upd_h (set_m_inp m x) f = set_m_inp (upd_h m f) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_bad_inp m x e : set_bad (set_m_inp m x) e = set_m_inp (set_bad m e) x.
Proof. destruct m; reflexivity. Qed.

Lemma rs_if_inp (b: bool) m1 m2 x :
  (if b then set_m_inp m1 x else set_m_inp m2 x) = set_m_inp (if b then m1 else m2) x.
Proof. destruct b; reflexivity. Qed.

(* the setters of the header passes commute with replacing the input *)
Ltac rs_push := repeat first [rewrite rs_if_inp | rewrite rs_mv_inp | rewrite rs_mode_inp | rewrite rs_upds_inp | rewrite rs_adler_inp
  | rewrite rs_init_inp | rewrite rs_leave_inp | rewrite rs_drop_inp | rewrite rs_updh_inp | rewrite rs_bad_inp].

Lemma rs_f_s m x : m_s (set_m_inp m x) = m_s m.
Proof. reflexivity. Qed.
Lemma rs_f_hold m x : m_hold (set_m_inp m x) = m_hold m.
Proof. reflexivity. Qed.
Lemma rs_f_leave m x : m_leave (set_m_inp m x) = m_leave m.
Proof. reflexivity. Qed.
Lemma rs_f_bits m x : m_bits (set_m_inp m x) = m_bits m.
Proof. reflexivity. Qed.

Lemma rs_iom_leave m x : IBrk (set_leave (set_m_inp m x)) = rs_iom x (IBrk (set_leave m)).
Proof. rewrite rs_leave_inp. reflexivity. Qed.

(* EXLEN .. HCRC on a covered gzip header read nothing *)
Lemma rs_exlen_tail M x : i_head (m_s M) = false -> dh_gzf (i_flags (m_s M)) ->
  c_EXLEN2 (set_m_inp M x) = rs_iom x (c_EXLEN2 M).
Proof.
  intros Hhd Hf. destruct (dh_gzf_land _ Hf) as (F1 & F2 & F3 & F4 & _).
  rewrite (dh_exlen M), (dh_exlen (set_m_inp M x)) by assumption.
  rewrite (dh_extra (set_mode M EXTRA)), (dh_extra (set_mode (set_m_inp M x) EXTRA)) by assumption.
  rewrite dh_name by assumption. rewrite dh_name by assumption.
  rewrite dh_comment by assumption. rewrite dh_comment by assumption.
  rewrite dh_hcrc by assumption. rewrite dh_hcrc by assumption.
  cbn [rs_iom]. rs_push. reflexivity.
Qed.

(* the common hypotheses of a stage: the canonical machine m inside the call, x the real input *)
Definition rs_stage (G: dctx) (pos: Z) (x: list Z) (m: mst) : Prop :=
  rs_xrel G pos x (m_inp m) /\ dh_in G pos m /\ hold_ok G (pos + m_nx m) (m_hold m) (m_bits m).

(* OS: 16 bits at bit 64, then EXLEN .. HCRC *)
Lemma rs_os_stage (L: rs_lay_stmt) G pos x m : D0 G = 80 -> rs_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 64 -> m_bits m < 16 ->
  i_head (m_s m) = false -> dh_gzf (i_flags (m_s m)) -> m_leave m = 0 ->
  c_OS2 (set_m_inp m x) = rs_iom x (c_OS2 m).
Proof.
  intros HD0 (Hx & Hin & Hh) Hq Hb Hhd Hf Hlv.
  pose proof Hin as (_ & _ & _ & _ & Hnx). pose proof Hh as (Hb0 & _).
  assert (NB : needbits 16 (set_m_inp m x) = set_m_inp (needbits 16 m) x)
    by (apply (rs_nb_hdr L G pos); auto; lia).
  destruct (dh_nb dkit G pos 4 16 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 16 m) with (needbits 16 m) in E.
  rewrite E in NB.
  destruct (dh_os_step m Hhd Hlv Hf) as (La & _).
  destruct (dh_os_step (set_m_inp m x) Hhd Hlv Hf) as (Lb & _).
  destruct lv.
  - rewrite (La _ _ _ E). rewrite <- rs_leave_inp, <- rs_mv_inp in NB. rewrite (Lb _ _ _ NB). rewrite rs_mv_inp. apply rs_iom_leave.
  - rewrite <- rs_mv_inp in NB.
    rewrite (dh_os1 m nx' h' b' Hhd Hlv (proj1 (dh_gzf_land _ Hf)) E).
    rewrite (dh_os1 (set_m_inp m x) nx' h' b' Hhd Hlv (proj1 (dh_gzf_land _ Hf)) NB).
    rs_push.
    apply rs_exlen_tail; assumption.
Qed.

(* TIME: 32 bits at bit 32, then OS *)
Lemma rs_time_stage (L: rs_lay_stmt) G pos x m : D0 G = 80 -> rs_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 32 -> m_bits m < 32 ->
  i_head (m_s m) = false -> dh_gzf (i_flags (m_s m)) -> m_leave m = 0 ->
  c_TIME2 (set_m_inp m x) = rs_iom x (c_TIME2 m).
Proof.
  intros HD0 (Hx & Hin & Hh) Hq Hb Hhd Hf Hlv.
  pose proof Hin as (Hp & Hl & Hi & Hby & Hnx). pose proof Hh as (Hb0 & _).
  assert (NB : needbits 32 (set_m_inp m x) = set_m_inp (needbits 32 m) x)
    by (apply (rs_nb_hdr L G pos); auto; lia).
  destruct (dh_nb dkit G pos 4 32 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 32 m) with (needbits 32 m) in E.
  rewrite E in NB.
  destruct (dh_time_step m Hhd Hlv Hf) as (La & Sa).
  destruct (dh_time_step (set_m_inp m x) Hhd Hlv Hf) as (Lb & Sb).
  destruct lv.
  - rewrite (La _ _ _ E). rewrite <- rs_leave_inp, <- rs_mv_inp in NB. rewrite (Lb _ _ _ NB). rewrite rs_mv_inp. apply rs_iom_leave.
  - destruct R4 as (R4 & R5 & _). specialize (R5 ltac:(lia)).
    assert (B32 : b' = 32) by lia. subst b'.
    rewrite <- rs_mv_inp in NB.
    rewrite (Sa _ _ _ E), (Sb _ _ _ NB).
    rs_push.
    apply (rs_os_stage L G pos); auto.
    + split; [exact Hx|]. split.
      * unfold dh_in. dh_red. repeat split; auto; lia.
      * dh_red. apply (dh_hold0 _ _ _ _ R3). lia.
    + dh_red. lia.
    + dh_red. lia.
Qed.

(* FLAGS: 16 bits at bit 16 (CM, FLG), then TIME *)
Lemma rs_flags_stage (L: rs_lay_stmt) G pos x m h : dctx_ok7a G -> dc_w G = WGzip h -> rs_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 16 -> m_bits m < 16 ->
  i_head (m_s m) = false -> m_leave m = 0 ->
  c_FLAGS2 (set_m_inp m x) = rs_iom x (c_FLAGS2 m).
Proof.
  intros Hok Ew (Hx & Hin & Hh) Hq Hb Hhd Hlv.
  destruct (rs_gz_facts G h Hok Ew) as (_ & HD0 & Hgzf).
  pose proof Hin as (Hp & Hl & Hi & Hby & Hnx). pose proof Hh as (Hb0 & _).
  assert (NB : needbits 16 (set_m_inp m x) = set_m_inp (needbits 16 m) x)
    by (apply (rs_nb_hdr L G pos); auto; lia).
  destruct (dh_nb dkit G pos 4 16 m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 16 m) with (needbits 16 m) in E.
  rewrite E in NB.
  destruct (dh_flags_step m Hhd Hlv) as (La & Sa).
  destruct (dh_flags_step (set_m_inp m x) Hhd Hlv) as (Lb & Sb).
  destruct lv.
  - rewrite (La _ _ _ E). rewrite <- rs_leave_inp, <- rs_mv_inp in NB. rewrite (Lb _ _ _ NB). rewrite rs_mv_inp. apply rs_iom_leave.
  - destruct R4 as (R4 & R5 & _). specialize (R5 ltac:(lia)).
    assert (B16 : b' = 16) by lia. rewrite B16 in E, NB, R3.
    assert (Hv : h' = 8 + 256 * gz_flg h).
    { destruct R3 as (_ & _ & R3). rewrite R3. replace (8 * (pos + nx') - 16) with 16 by lia.
      replace (8 * (pos + nx')) with 32 by lia. apply (rs_gz_hold_flags G h Hok Ew). }
    subst h'.
    rewrite <- rs_mv_inp in NB.
    rewrite (Sa _ _ _ E Hgzf), (Sb _ _ _ NB Hgzf).
    rs_push.
    apply (rs_time_stage L G pos); auto.
    + split; [exact Hx|]. split.
      * unfold dh_in. dh_red. repeat split; auto; lia.
      * dh_red. apply (dh_hold0 _ _ _ _ R3). lia.
    + dh_red. lia.
    + dh_red. lia.
Qed.

(* HEAD: nothing read (raw), or NEEDBITS(16) of the first two bytes; the rest of the case reads nothing *)
Lemma rs_head_gen m x :
  (i_wrap (m_s m) <> 0 -> needbits 16 (set_m_inp m x) = set_m_inp (needbits 16 m) x) ->
  c_HEAD2 (set_m_inp m x) = rs_iom x (c_HEAD2 m).
Proof.
  intros NB. unfold c_HEAD2. cbv zeta.
  change (i_wrap (m_s (set_m_inp m x))) with (i_wrap (m_s m)).
  destruct (Z.eqb_spec (i_wrap (m_s m)) 0) as [W|W].
  { cbn [rs_iom]. rs_push. reflexivity. }
  rewrite (NB W). generalize (needbits 16 m). intros m1.
  repeat (rs_push; rewrite ?rs_f_s, ?rs_f_hold, ?rs_f_leave, ?rs_f_bits;
          match goal with |- context [if ?b then _ else _] => destruct b end);
    cbn [rs_iom]; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header passes                                                                              *)

Lemma rs_pass_hdr : rs_lay_stmt -> rs_pass_ok md_hdr.
Proof.
  intros L G pos x inp' ob flush m' Hok Hso Hp Hl Hi Hx HK Hw Hlv Hmd.
  pose proof (kd_inp _ _ _ _ _ HK) as I. subst inp'.
  pose proof (mwW_nx _ (proj1 Hw)) as Hnx.
  assert (Hin : dh_in G pos m').
  { unfold dh_in. destruct Hok as (_ & _ & _ & _ & _ & _ & Hby & _). repeat split; auto; lia. }
  pose proof (kd_glob _ _ _ _ _ HK) as Hg. pose proof Hg as (_ & Hhd & _).
  pose proof (kd_at _ _ _ _ _ HK) as A.
  destruct Hmd as [Md|Md].
  - (* HEAD *)
    destruct (dh_at_head _ _ _ _ _ _ A Md) as (Hh & (_ & Hq & Hb16 & _)).
    assert (St : forall m, m_mode m = HEAD -> stepf2 flush lenfix_list distfix_list m = c_HEAD2 m).
    { intros m E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. }
    rewrite (St m' Md), (St (set_m_inp m' x) Md).
    apply rs_head_gen. intros W.
    assert (Ew : dc_w G <> WRaw) by (intros E; apply W; exact (rs_raw_wrap G _ Hok E Hg)).
    pose proof (rs_wrapped_D0 G Hok Ew). pose proof Hh as (Hb0 & _).
    apply (rs_nb_hdr L G pos); auto; lia.
  - (* FLAGS, TIME, OS *)
    destruct (dh_at_gz _ _ _ _ _ _ A Md) as (Hh & (h & Ew & _ & _ & _ & D)).
    destruct (rs_gz_facts G h Hok Ew) as (_ & HD0 & _).
    assert (Hst : rs_stage G pos x m') by (split; [exact Hx|split; assumption]).
    destruct (dh_step_md flush lenfix_list distfix_list m') as (SF & ST & SO).
    destruct (dh_step_md flush lenfix_list distfix_list (set_m_inp m' x)) as (SF' & ST' & SO').
    destruct Md as [Md|[Md|Md]]; unfold m_mode in Md; rewrite Md in D;
      destruct D as [(DM & Dq & Db)|[(DM & Dq & Db & Df)|(DM & Dq & Db & Df)]];
      try (dh_modes_in DM; lia).
    + rewrite (SF Md), (SF' Md). apply (rs_flags_stage L G pos x m' h); auto.
    + rewrite (ST Md), (ST' Md). apply (rs_time_stage L G pos x m'); auto.
      rewrite Df. destruct (rs_gz_facts G h Hok Ew) as (_ & _ & X). exact X.
    + rewrite (SO Md), (SO' Md). apply (rs_os_stage L G pos x m'); auto.
      rewrite Df. destruct (rs_gz_facts G h Hok Ew) as (_ & _ & X). exact X.
Qed.

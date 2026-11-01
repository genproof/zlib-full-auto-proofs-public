(* Part of the decode theory: one inflate() call from the passes.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms_Prop.
Require Import compcert.lib.Integers.
Require Zlib.proof.crc32.Combine.
Require Import Zlib.proof.rfc1951.DecCallAout Zlib.proof.rfc1951.DecCallWin Zlib.proof.rfc1951.DecCallOut.
Require Import Zlib.proof.rfc1951.DecCallWkeep.
Import ListNotations.
Local Open Scope Z_scope.

Ltac dc_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH Z_BLOCK Z_TREES] in *; lia.

Ltac dc_rep := change Int.max_signed with 2147483647 in *; change Int.max_unsigned with 4294967295 in *;
  change Int64.max_unsigned with 18446744073709551615 in *; lia.

Ltac dc_split D :=
  destruct D as [[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|
    [[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[[?M ?X]|[?M ?X]]]]]]]]]]]]]]]]].

(* ---------------------------------------------------------------------------------------------- *)
(* The modes                                                                                      *)

Lemma dc_groups G s c h b o : at_mode G s c h b o ->
  md_hdr (i_mode s) \/ md_type (i_mode s) \/ md_tab (i_mode s) \/ md_dec (i_mode s) \/ md_trl (i_mode s).
Proof.
  intros [_ D]. unfold md_hdr, md_type, md_tab, md_dec, md_trl.
  dc_split D; tauto.
Qed.

Lemma dc_at_type G s c h b o : at_mode G s c h b o -> i_mode s = Zlib.proof.inflate.Model.TYPE ->
  at_type G s (8 * c - b) b o.
Proof.
  intros [_ D] E. dc_split D; try exact X; exfalso; rewrite E in M; dc_md.
Qed.

Lemma dc_at_done G s c h b o : at_mode G s c h b o -> i_mode s = DONE -> at_done G s (8 * c - b) b o.
Proof.
  intros [_ D] E. dc_split D; try exact X; exfalso; rewrite E in M; dc_md.
Qed.

Lemma dc_at_length G s c h b o : at_mode G s c h b o -> i_mode s = LENGTH -> exists hh, dc_w G = WGzip hh.
Proof.
  intros [_ D] E. dc_split D; try (exfalso; rewrite E in M; dc_md; fail).
  destruct X as (_ & _ & _ & _ & _ & X). exact X.
Qed.

Definition dc_all : Prop :=
  forall G pos inp ob flush m,
    dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
    inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 ->
    dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).

Lemma dc_step : group_ok md_hdr -> group_ok md_type -> group_ok md_tab -> group_ok md_dec -> group_ok md_trl ->
  dc_all.
Proof.
  intros H1 H2 H3 H4 H5 G pos inp ob flush m C P0 PL IE K W L.
  destruct (dc_groups _ _ _ _ _ _ (kd_at _ _ _ _ _ K)) as [M|[M|[M|[M|M]]]];
    [apply H1|apply H2|apply H3|apply H4|apply H5]; auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

Lemma dc_loop (SM: stepf2_mwf3_stmt) (ST: dc_all) G pos inp ob flush :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  forall m o, loop2 flush lenfix_list distfix_list m o -> Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 ->
  exists mE, o = IBrk mE /\ Kd G pos inp ob mE /\ mwf3 mE /\ m_leave mE = 1 /\
    (exists d, m_ow mE = m_ow m ++ d) /\ leave_why G pos inp ob flush mE /\ m_aout mE = m_aout m.
Proof.
  intros C P0 PL IE m o LP.
  induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros K W L0.
  - pose proof (ST G pos inp ob flush m C P0 PL IE K W L0) as P. rewrite E in P.
    unfold dstep_post in P. destruct P.
  - pose proof (ST G pos inp ob flush m C P0 PL IE K W L0) as P. rewrite E in P.
    unfold dstep_post in P. destruct P as (K' & D & WHY).
    pose proof (SM flush m W L0) as W'. rewrite E in W'.
    pose proof (dca_aout flush m) as A. rewrite E in A.
    exists m'. split; [reflexivity|]. split; [exact K'|]. split; [exact W'|]. split; [exact L1|].
    split; [exact D|]. split; [exact (WHY L1)|exact A].
  - pose proof (ST G pos inp ob flush m C P0 PL IE K W L0) as P. rewrite E in P.
    unfold dstep_post in P. destruct P as (K' & (d & D) & _).
    pose proof (SM flush m W L0) as W'. rewrite E in W'.
    pose proof (dca_aout flush m) as A. rewrite E in A.
    assert (L': m_leave m' = 0) by (pose proof (mw_leave _ (mwf3_mwf _ W')); lia).
    destruct (IH K' W' L') as (mE & -> & KE & WE & LE & (d2 & D2) & WY & AE).
    exists mE. split; [reflexivity|]. split; [exact KE|]. split; [exact WE|]. split; [exact LE|].
    split; [exists (d ++ d2); rewrite D2, D, app_assoc; reflexivity|]. split; [exact WY|]. congruence.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* at_mode depends only on the decoding fields of the state                                       *)

Definition dsame (s s': istate) : Prop :=
  i_mode s' = i_mode s /\ i_last s' = i_last s /\ i_wrap s' = i_wrap s /\ i_flags s' = i_flags s /\
  i_head s' = i_head s /\ i_wbits s' = i_wbits s /\ i_length s' = i_length s /\ i_offset s' = i_offset s /\
  i_extra s' = i_extra s /\ i_nlen s' = i_nlen s /\ i_ndist s' = i_ndist s /\ i_ncode s' = i_ncode s /\
  i_have s' = i_have s /\ i_lens s' = i_lens s /\ i_lencode s' = i_lencode s /\ i_lenbits s' = i_lenbits s /\
  i_distcode s' = i_distcode s /\ i_distbits s' = i_distbits s /\ i_codes s' = i_codes s.

Lemma dc_tdec_iff (s s': istate) t r ty l : i_codes s' = i_codes s -> (tdec s t r ty l <-> tdec s' t r ty l).
Proof.
  intros E. unfold tdec, twalk, tab_entry. rewrite E. reflexivity.
Qed.

Lemma dc_at_ext0 G s s' c h b o : dsame s s' -> i_total s' = i_total s ->
  at_mode G s c h b o -> at_mode G s' c h b o.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19) ET A.
  assert (TD: forall t r ty l, tdec s' t r ty l <-> tdec s t r ty l).
  { intros. symmetry. apply dc_tdec_iff. exact E19. }
  unfold at_mode, at_head, at_gzhdr, at_type, at_stored, at_copy, at_table, at_lenlens, at_codelens, at_len,
    at_lenext, at_dist, at_distext, at_match, at_lit, at_check, at_length, at_done, in_huff, in_blk in *.
  rewrite E1, E2, E4, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, ET.
  setoid_rewrite TD. exact A.
Qed.

Definition dc_hdr_mode (md: Z) : Prop := md = HEAD \/ md = FLAGS \/ md = TIME \/ md = OS.

Lemma classic_hdr (md: Z) : dc_hdr_mode md \/ ~ dc_hdr_mode md.
Proof.
  unfold dc_hdr_mode.
  destruct (Z.eq_dec md HEAD); [left; auto|]. destruct (Z.eq_dec md FLAGS); [left; auto|].
  destruct (Z.eq_dec md TIME); [left; auto|]. destruct (Z.eq_dec md OS); [left; auto|].
  right. intros [E|[E|[E|E]]]; contradiction.
Qed.

(* outside the header modes, at_mode does not look at total *)
Lemma dc_at_tot G s v c h b o : ~ dc_hdr_mode (i_mode s) ->
  at_mode G (set_i_total s v) c h b o -> at_mode G s c h b o.
Proof.
  intros N [HO [[M _]|[[M _]|R]]].
  - exfalso. apply N. left. exact M.
  - exfalso. apply N. right. exact M.
  - split; [exact HO|]. right; right. exact R.
Qed.

Lemma dc_at_ext G s s' c h b o : dsame s s' -> (i_total s' = i_total s \/ ~ dc_hdr_mode (i_mode s)) ->
  at_mode G s c h b o -> at_mode G s' c h b o.
Proof.
  intros D [ET|N] A; [exact (dc_at_ext0 G s s' c h b o D ET A)|].
  pose proof D as (E1 & _).
  apply (dc_at_tot G s' (i_total s)); [rewrite E1; exact N|].
  apply (dc_at_ext0 G s); [|reflexivity|exact A].
  destruct D as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
  unfold dsame; cbn [set_i_total i_mode i_last i_wrap i_flags i_head i_wbits i_length i_offset i_extra i_nlen i_ndist
    i_ncode i_have i_lens i_lencode i_lenbits i_distcode i_distbits i_codes]; auto 20.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine at the loop head (Spec5.m_init)                                                    *)

Lemma dc_set_typedo_swf (s: istate) : swf s -> swf (set_i_mode s TYPEDO).
Proof. intros S. destruct S; constructor; cbn; auto. unfold HEAD, TYPEDO, SYNC; lia. Qed.

Lemma dc_set_typedo_modewf (s: istate) : modewf s -> modewf (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Lemma dc_set_typedo_swf3 (s: istate) : swf3 s -> swf3 (set_i_mode s TYPEDO).
Proof.
  intros M. destruct M; constructor; cbn; unfold decode_mode;
    unfold HEAD, TYPEDO, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; intros; lia.
Qed.

Lemma dc_init_s G pos out s t :
  dinv G pos out s t -> swf s -> modewf s -> swf3 s ->
  let s' := if i_mode s =? Zlib.proof.inflate.Model.TYPE then set_i_mode s TYPEDO else s in
  at_mode G s' pos (i_hold s') (i_bits s') out /\ glob_ok G s' /\ (i_mode s' < CHECK -> win_ok G s' out) /\
  chk_ok G s' out [] /\ swf s' /\ modewf s' /\ swf3 s'.
Proof.
  intros (DA & DG & DW & DC & _) SW MW S3. cbv zeta.
  destruct (Z.eqb_spec (i_mode s) Zlib.proof.inflate.Model.TYPE) as [ET|ET].
  - pose proof (dc_at_type _ _ _ _ _ _ DA ET) as T.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + destruct DA as [HO _]. split; [exact HO|]. right; right; left. split; [right; reflexivity | exact T].
    + destruct DG as ((wb0 & R & H) & HD & WB & FL). split; [exists wb0; split; [exact R | intros E; cbn in E; dc_md]|].
      split; [exact HD|]. split; [intros _; apply WB; rewrite ET; dc_md|].
      intros W1 _ _. apply FL; [exact W1 | rewrite ET; dc_md | rewrite ET; dc_md].
    + intros _. apply DW. rewrite ET. dc_md.
    + unfold chk_ok in *. cbn [i_mode set_i_mode i_check i_total]. intros W1 _ _ _ _.
      destruct (DC W1) as (A & B & P); try (rewrite ET; dc_md). rewrite ET in A, B. exact (conj A (conj B P)).
    + apply dc_set_typedo_swf; exact SW.
    + apply dc_set_typedo_modewf; exact MW.
    + apply dc_set_typedo_swf3; exact S3.
  - split; [exact DA|]. split; [exact DG|]. split; [exact DW|]. split; [exact DC|].
    split; [exact SW|]. split; [exact MW|]. exact S3.
Qed.

Lemma dc_init G pos out L z inp :
  dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= Int.max_signed ->
  Zlength inp <= Int.max_signed -> bytes_ok inp ->
  Kd G pos inp out (m_init z L inp) /\ mwf3 (m_init z L inp).
Proof.
  intros DI LV ZF AO LI BI.
  destruct LV as (SP & SW & MW & HW & S3 & WS & LV1 & LV2 & LV3).
  destruct ZF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  pose proof DI as (_ & _ & _ & _ & DT).
  destruct (dc_init_s G pos out (l_s L) (zf_tout z) DI SW MW S3) as (A & GL & W & CK & SW' & MW' & S3').
  unfold m_init. cbv zeta.
  set (s' := if i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE then set_i_mode (l_s L) TYPEDO else l_s L) in *.
  split.
  - constructor; unfold m_mode, m_left; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
      m_adler m_tin m_tout m_snx m_sow m_msg].
    + reflexivity.
    + rewrite Z.add_0_r, app_nil_r. exact A.
    + exact GL.
    + exact W.
    + exact CK.
    + rewrite app_nil_r. destruct (after_check G (i_mode s')); exact DT.
    + rewrite Zlength_nil. destruct (after_check G (i_mode s')); lia.
    + change (0 =? 1) with false. rewrite andb_false_r. reflexivity.
  - split; [|exact S3'].
    constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_tin m_tout
      m_snx m_sow]; rewrite ?Zlength_nil; unfold urange, lrange, Z_OK in *; auto.
    all: first [apply (sw_hold _ SW') | apply (sw_bits _ SW') | split; [dc_rep | constructor] |
                pose proof (Zlength_nonneg inp); dc_rep].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inf_leave (leave_fin): what the final state keeps                                              *)

Lemma dc_uw (s: istate) (d: list Z) :
  dsame s (updatewindow s d) /\ i_hold (updatewindow s d) = i_hold s /\ i_bits (updatewindow s d) = i_bits s /\
  i_check (updatewindow s d) = i_check s /\ i_total (updatewindow s d) = i_total s.
Proof.
  unfold updatewindow, dsame. cbv zeta.
  destruct (i_wsize s =? 0); cbn [set_i_whave set_i_wnext set_i_wsize i_wsize];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; repeat split.
Qed.

Definition dc_s1 (m: mst) : istate := set_i_bits (set_i_hold (m_s m) (m_hold m)) (m_bits m).
Definition dc_oc (m: mst) : Z := u32 (m_out m - m_left m).
Definition dc_wd (m: mst) : list Z := sublist (Zlength (m_ow m) - dc_oc m) (Zlength (m_ow m)) (m_ow m).
Definition dc_s2 (flush: Z) (m: mst) : istate :=
  if leave_ok flush m then set_i_win (updatewindow (dc_s1 m) (dc_wd m)) true else dc_s1 m.

Lemma dc_s2_facts flush m :
  dsame (m_s m) (dc_s2 flush m) /\ i_hold (dc_s2 flush m) = m_hold m /\ i_bits (dc_s2 flush m) = m_bits m /\
  i_check (dc_s2 flush m) = i_check (m_s m) /\ i_total (dc_s2 flush m) = i_total (m_s m).
Proof.
  unfold dc_s2. destruct (leave_ok flush m).
  - destruct (dc_uw (dc_s1 m) (dc_wd m)) as (D & H & B & C & T).
    destruct D as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19).
    unfold dsame; cbn [i_mode i_last i_wrap i_flags i_head i_wbits i_length i_offset i_extra i_nlen i_ndist i_ncode
      i_have i_lens i_lencode i_lenbits i_distcode i_distbits i_codes i_hold i_bits i_check i_total set_i_win].
    rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18, E19, H, B, C, T.
    unfold dc_s1. cbn. repeat split.
  - unfold dc_s1, dsame. cbn. repeat split.
Qed.

Lemma dc_lf flush m :
  let res := leave_fin flush m in let mF := r_m res in
  let oc := dc_oc m in
  let upd := negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (oc =? 0) in
  let c := update_check (i_flags (m_s m)) (i_check (m_s m)) (dc_wd m) in
  let s3 := set_i_total (dc_s2 flush m) (u64 (i_total (m_s m) + oc)) in
  m_s mF = (if upd then set_i_check s3 c else s3) /\
  m_adler mF = (if upd then c else m_adler m) /\ m_tout mF = u64 (m_tout m + oc) /\
  m_ow mF = m_ow m /\ m_snx mF = m_nx m /\ m_sow mF = Zlength (m_ow m) /\ m_inp mF = m_inp m /\
  m_aout mF = m_aout m /\ m_bits mF = m_bits m /\ m_ret mF = m_ret m /\
  r_ret res = (if (((u32 (m_in m - m_have m) =? 0) && (oc =? 0)) || (flush =? Z_FINISH)) && (m_ret m =? Z_OK)
               then Z_BUF_ERROR else m_ret m) /\
  r_dtype res = Some (m_bits m + (if i_last (m_s m) =? 0 then 0 else 64) +
     (if m_mode m =? Zlib.proof.inflate.Model.TYPE then 128 else 0) +
     (if (m_mode m =? LEN_) || (m_mode m =? COPY_) then 256 else 0)).
Proof.
  cbv zeta. unfold leave_fin. cbv zeta.
  set (upd0 := leave_ok flush m).
  set (m1 := restore m).
  set (m2 := if upd0 then _ else m1).
  destruct (dc_s2_facts flush m) as (D & _ & _ & SC & ST).
  destruct D as (E1 & E2 & E3 & E4 & _).
  assert (E: m_s m2 = dc_s2 flush m /\ m_snx m2 = m_nx m /\ m_sow m2 = Zlength (m_ow m) /\ m_inp m2 = m_inp m /\
             m_aout m2 = m_aout m /\ m_ow m2 = m_ow m /\ m_out m2 = m_out m /\ m_in m2 = m_in m /\
             m_nx m2 = m_nx m /\ m_tout m2 = m_tout m /\ m_adler m2 = m_adler m /\ m_bits m2 = m_bits m /\
             m_ret m2 = m_ret m /\ m_tin m2 = m_tin m).
  { unfold m2, m1, upd0, dc_s2. destruct (leave_ok flush m); repeat split. }
  clearbody m2.
  destruct E as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  unfold m_left, m_have, m_mode in *. rewrite A4, A5, A6, A7, A8, A9.
  fold (m_left m). fold (dc_oc m).
  set (m3 := upd_s (set_m_tout _ _) _).
  assert (B: m_s m3 = set_i_total (dc_s2 flush m) (u64 (i_total (m_s m) + dc_oc m)) /\
             m_ow m3 = m_ow m /\ m_adler m3 = m_adler m /\ m_tout m3 = u64 (m_tout m + dc_oc m) /\
             m_snx m3 = m_nx m /\ m_sow m3 = Zlength (m_ow m) /\ m_inp m3 = m_inp m /\ m_aout m3 = m_aout m /\
             m_bits m3 = m_bits m /\ m_ret m3 = m_ret m).
  { unfold m3, upd_s. cbn [m_s set_m_s set_m_tout set_m_tin m_ow m_adler m_tout m_snx m_sow m_inp m_aout m_bits m_ret].
    rewrite A1, A2, A3, A4, A5, A6, A10, A11, A12, A13, ST. repeat split. }
  clearbody m3. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  assert (W3: i_wrap (m_s m3) = i_wrap (m_s m) /\ i_flags (m_s m3) = i_flags (m_s m) /\
              i_check (m_s m3) = i_check (m_s m) /\ i_last (m_s m3) = i_last (m_s m) /\
              i_mode (m_s m3) = i_mode (m_s m)).
  { rewrite B1. cbn [i_wrap i_flags i_check i_last i_mode set_i_total]. auto. }
  destruct W3 as (W1 & W2 & W3 & W4 & W5).
  rewrite W1, B2. unfold dc_wd.
  destruct (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (dc_oc m =? 0)); cbn [r_m r_ret r_dtype];
    unfold upd_s; cbn [m_s set_m_s set_m_adler i_wrap i_flags i_check i_mode i_last m_ow m_adler m_tout m_snx m_sow
      m_inp m_aout m_bits m_ret set_i_check];
    rewrite ?W1, ?W2, ?W3, ?W4, ?W5, ?B1, ?B2, ?B3, ?B4, ?B5, ?B6, ?B7, ?B8, ?B9, ?B10; repeat split.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Small facts                                                                                    *)

Lemma dc_win_ext G s s' o :
  i_wsize s' = i_wsize s -> i_wbits s' = i_wbits s -> i_whave s' = i_whave s -> i_wnext s' = i_wnext s ->
  i_wdata s' = i_wdata s -> win_ok G s o -> win_ok G s' o.
Proof.
  intros A B C D E W. unfold win_ok, win_at in *. rewrite A, B, C, D, E. exact W.
Qed.

Lemma dc_glob_ext G s s' : dsame s s' -> glob_ok G s -> glob_ok G s'.
Proof.
  intros (E1 & E2 & E3 & E4 & E5 & E6 & _) GL. unfold glob_ok in *. rewrite E1, E3, E4, E5, E6. exact GL.
Qed.

Lemma dc_dsame_trans s1 s2 s3 : dsame s1 s2 -> dsame s2 s3 -> dsame s1 s3.
Proof. unfold dsame. intuition congruence. Qed.

Lemma dc_swf_s1 m : mwf m -> swf (dc_s1 m).
Proof.
  intros W. pose proof (mw_s _ W) as S. pose proof (mw_hold _ W). pose proof (mw_bits _ W).
  unfold dc_s1. destruct S; constructor; cbn; auto.
Qed.

Lemma dc_wrap4 G s : dctx_ok G -> glob_ok G s -> wrapped G = true -> Z.land (i_wrap s) 4 <> 0.
Proof.
  intros (SO & AC & _) ((wb0 & R0 & _) & _) WR.
  destruct (init_wrap_wb_bits _ _ _ R0) as (wrap & R & _ & _ & -> & _).
  destruct SO as (WB & _).
  unfold accepts, wrapped in *. unfold reset2_wb in R.
  assert (P: 0 <= dc_iw G < 48).
  { destruct (dc_w G); [discriminate| |]; lia. }
  destruct (Z.ltb_spec (dc_iw G) 0); [lia|].
  destruct ((_ =? 0) || _); [|discriminate]. inversion R as [[E1 E2]].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  assert (D: dc_iw G / 16 = 0 \/ dc_iw G / 16 = 1 \/ dc_iw G / 16 = 2).
  { assert (0 <= dc_iw G / 16 < 3) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
  destruct D as [D|[D|D]]; rewrite D; cbv; discriminate.
Qed.

Lemma dc_prod_hist G d : produced G (dc_hist G ++ d) = d.
Proof.
  unfold produced. pose proof (Zlength_nonneg (dc_hist G)). pose proof (Zlength_nonneg d).
  rewrite Zlength_app, sublist_app2 by lia. rewrite Z.sub_diag.
  replace (Zlength (dc_hist G) + Zlength d - Zlength (dc_hist G)) with (Zlength d) by lia.
  apply sublist_same; lia.
Qed.

Lemma dc_produced_app G ob ow : (exists d0, ob = dc_hist G ++ d0) -> produced G (ob ++ ow) = produced G ob ++ ow.
Proof.
  intros (d0 & ->). rewrite <- app_assoc, !dc_prod_hist. reflexivity.
Qed.

Lemma dc_adler_valid1 : Zlib.proof.adler32.Model.adler_valid 1.
Proof. unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; discriminate. Qed.

Lemma dc_upd_chk G s d ow : dctx_ok G -> glob_ok G s -> wrapped G = true -> i_mode s <> HEAD -> i_mode s <> FLAGS ->
  bytes_ok d -> update_check (i_flags s) (chkv G d) ow = chkv G (d ++ ow).
Proof.
  intros C (_ & _ & _ & FL) WR N1 N2 B. specialize (FL WR N1 N2).
  unfold chkv, update_check, wrapped in *. destruct (dc_w G) as [| wb fl did | h]; [discriminate| |].
  - rewrite FL, Z.eqb_refl.
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref
      by (apply Zlib.proof.adler32.Model.ref_adler32_valid; exact dc_adler_valid1).
    apply Zlib.proof.adler32.Model.ref_adler32_app. exact dc_adler_valid1.
  - rewrite FL. destruct (Z.eqb_spec (8 + 256 * gz_flg h) 0); [lia|].
    apply Zlib.proof.crc32.Combine.ref_crc32_app. exact B.
Qed.

Definition dc_dt (b: Z) (x y w: bool) : Z :=
  b + (if x then 0 else 64) + (if y then 128 else 0) + (if w then 256 else 0).

Definition dc_dt_okb (b: Z) : bool :=
  forallb (fun x => forallb (fun y => forallb (fun w =>
    Bool.eqb (Z.land (dc_dt b x y w) 128 =? 0) (negb y) && Bool.eqb (Z.land (dc_dt b x y w) 64 =? 0) x)
    [true; false]) [true; false]) [true; false].

Lemma dc_dt_all : forallb dc_dt_okb (map Z.of_nat (seq 0 64)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dc_dt_bits b x y w : 0 <= b < 64 ->
  (Z.land (dc_dt b x y w) 128 <> 0 <-> y = true) /\ (Z.land (dc_dt b x y w) 64 <> 0 <-> x = false).
Proof.
  intros R.
  assert (OK: dc_dt_okb b = true).
  { pose proof dc_dt_all as A. rewrite forallb_forall in A. apply A.
    replace b with (Z.of_nat (Z.to_nat b)) by lia. apply in_map. apply in_seq. lia. }
  unfold dc_dt_okb in OK. cbn [forallb] in OK. rewrite !andb_true_r in OK.
  destruct x, y, w; cbn [negb] in OK; rewrite !andb_true_iff in OK; repeat match goal with H: _ /\ _ |- _ => destruct H end;
    repeat match goal with H: Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H end;
    repeat match goal with H: (_ =? 0) = true |- _ => apply Z.eqb_eq in H
                       | H: (_ =? 0) = false |- _ => apply Z.eqb_neq in H end;
    split; split; intros; try congruence; try discriminate; tauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The state after leave_fin: window, check, total_out                                            *)

Lemma dc_u32_id (x: Z) : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros H. unfold u32. apply Z.mod_small; lia. Qed.

Lemma dc_fin_win G pos inp ob flush mE : Kd G pos inp ob mE -> mwf3 mE -> m_mode mE < CHECK ->
  win_ok G (dc_s2 flush mE) (ob ++ m_ow mE).
Proof.
  intros K W M. pose proof (kd_win _ _ _ _ _ K M) as W0. pose proof (kd_out _ _ _ _ _ K) as KO.
  pose proof (mwf3_mwf _ W) as MW. destruct (mw_ow _ MW) as [OWL _]. pose proof (mw_aout _ MW) as AO.
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  assert (AC: after_check G (m_mode mE) = false).
  { unfold after_check. rewrite (proj2 (Z.eqb_neq (m_mode mE) LENGTH)) by dc_md.
    rewrite (proj2 (Z.eqb_neq (m_mode mE) DONE)) by dc_md. rewrite andb_false_r. reflexivity. }
  rewrite AC in KO.
  assert (S1: win_ok G (dc_s1 mE) ob) by (apply dc_win_ext with (m_s mE); try reflexivity; exact W0).
  unfold dc_s2. destruct (leave_ok flush mE) eqn:LO.
  - assert (WD: dc_wd mE = m_ow mE).
    { unfold dc_wd, dc_oc, m_left. rewrite KO.
      replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by lia.
      rewrite dc_u32_id by dc_rep. rewrite Z.sub_diag. apply sublist_same; lia. }
    rewrite WD. apply dc_win_ext with (updatewindow (dc_s1 mE) (m_ow mE)); try reflexivity.
    apply dcw_win; [apply dc_swf_s1; exact MW | exact S1].
  - unfold leave_ok in LO. cbv zeta in LO. rewrite orb_false_iff in LO. destruct LO as [L1 L2].
    assert (OWN: m_ow mE = []).
    { destruct (Z.eqb_spec (m_out mE) (m_left mE)) as [E|E].
      - unfold m_left in E. rewrite KO in E. apply Zlength_nil_inv. lia.
      - exfalso.
        rewrite (proj2 (Z.ltb_lt (m_mode mE) BAD)) in L2 by dc_md.
        rewrite (proj2 (Z.ltb_lt (m_mode mE) CHECK)) in L2 by exact M. discriminate. }
    rewrite OWN, app_nil_r. exact S1.
Qed.

Lemma dc_fin_tout G pos inp ob mE : Kd G pos inp ob mE -> mwf3 mE -> (exists d0, ob = dc_hist G ++ d0) ->
  u64 (m_tout mE + dc_oc mE) = Zlength (produced G (ob ++ m_ow mE)) mod 2 ^ 64.
Proof.
  intros K W HP. pose proof (kd_out _ _ _ _ _ K) as KO. pose proof (kd_tout _ _ _ _ _ K) as KT.
  pose proof (mwf3_mwf _ W) as MW. destruct (mw_ow _ MW) as [OWL _]. pose proof (mw_aout _ MW) as AO.
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  unfold dc_oc, u64. rewrite KT.
  destruct (after_check G (m_mode mE)).
  - rewrite KO, Z.sub_diag. change (u32 0) with 0. rewrite Z.add_0_r, Zmod_mod. reflexivity.
  - unfold m_left. rewrite KO.
    replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by lia.
    rewrite dc_u32_id by dc_rep. rewrite Zplus_mod_idemp_l, dc_produced_app, Zlength_app by exact HP. reflexivity.
Qed.

Lemma dc_fin_chk G pos inp ob mE sF : dctx_ok G -> Kd G pos inp ob mE -> mwf3 mE ->
  (exists d0, ob = dc_hist G ++ d0) -> bytes_ok ob -> dsame (m_s mE) sF ->
  i_total sF = u64 (i_total (m_s mE) + dc_oc mE) ->
  i_check sF = (if negb (Z.land (i_wrap (m_s mE)) 4 =? 0) && negb (dc_oc mE =? 0)
                then update_check (i_flags (m_s mE)) (i_check (m_s mE)) (dc_wd mE) else i_check (m_s mE)) ->
  chk_ok G sF (ob ++ m_ow mE) [].
Proof.
  intros C K W HP BO DS T CK. destruct DS as (E1 & _).
  pose proof (kd_out _ _ _ _ _ K) as KO.
  pose proof (mwf3_mwf _ W) as MW. destruct (mw_ow _ MW) as [OWL _]. pose proof (mw_aout _ MW) as AO.
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  assert (BP: bytes_ok (produced G ob)).
  { destruct HP as (d0 & ->). rewrite dc_prod_hist. unfold bytes_ok in *. apply Forall_app in BO. tauto. }
  unfold chk_ok. rewrite E1. intros WR N1 N2 N3 N4. rewrite app_nil_r.
  destruct (kd_chk _ _ _ _ _ K WR N1 N2 N3 N4) as (C1 & T1 & _).
  assert (PRE: exists d', ob ++ m_ow mE = dc_hist G ++ d')
    by (destruct HP as (d0 & ->); exists (d0 ++ m_ow mE); rewrite app_assoc; reflexivity).
  pose proof (dc_wrap4 G (m_s mE) C (kd_glob _ _ _ _ _ K) WR) as W4.
  assert (AC: after_check G (m_mode mE) = (i_mode (m_s mE) =? LENGTH) || (i_mode (m_s mE) =? DONE))
    by (unfold after_check, m_mode; rewrite WR; reflexivity).
  rewrite AC in KO.
  destruct ((i_mode (m_s mE) =? LENGTH) || (i_mode (m_s mE) =? DONE)).
  - assert (OC: dc_oc mE = 0) by (unfold dc_oc; rewrite KO, Z.sub_diag; reflexivity).
    rewrite T, CK, OC, Z.eqb_refl, andb_false_r, Z.add_0_r. unfold u64. rewrite T1, Zmod_mod. auto.
  - assert (OC: dc_oc mE = Zlength (m_ow mE)).
    { unfold dc_oc, m_left. rewrite KO.
      replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by lia.
      apply dc_u32_id. dc_rep. }
    rewrite T, CK, OC. rewrite dc_produced_app by exact HP.
    split.
    + destruct (Z.eqb_spec (Zlength (m_ow mE)) 0) as [Z0|Z0].
      * apply Zlength_nil_inv in Z0. rewrite Z0, app_nil_r, andb_false_r. exact C1.
      * rewrite (proj2 (Z.eqb_neq _ _) W4). cbn [negb andb].
        assert (WD: dc_wd mE = m_ow mE) by (unfold dc_wd; rewrite OC, Z.sub_diag; apply sublist_same; lia).
        rewrite WD, C1. apply (dc_upd_chk G (m_s mE)); auto.
        apply (kd_glob _ _ _ _ _ K).
    + split; [unfold u64; rewrite T1, Zplus_mod_idemp_l, Zlength_app; reflexivity | exact PRE].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit: inf_leave's normal path                                                              *)

Lemma dc_at_hdr G s c h b o : at_mode G s c h b o -> dc_hdr_mode (i_mode s) -> o = dc_hist G /\ i_total s = 0.
Proof.
  intros [_ D] HM. unfold dc_hdr_mode in HM.
  dc_split D; try (exfalso; destruct HM as [E|[E|[E|E]]]; rewrite E in M; dc_md; fail).
  - destruct X as (O & _ & _ & _ & T & _). auto.
  - destruct X as (hh & _ & O & _ & T & _). auto.
Qed.

Lemma dc_hdr_tot G pos inp ob mE : Kd G pos inp ob mE -> mwf3 mE -> (exists d0, ob = dc_hist G ++ d0) ->
  dc_hdr_mode (m_mode mE) -> m_ow mE = [] /\ i_total (m_s mE) = 0 /\ dc_oc mE = 0.
Proof.
  intros K W (d0 & HP) HM.
  destruct (dc_at_hdr _ _ _ _ _ _ (kd_at _ _ _ _ _ K) HM) as (O & T).
  assert (OW: m_ow mE = []).
  { rewrite HP, <- app_assoc in O. apply (f_equal (@Zlength Z)) in O. rewrite !Zlength_app in O.
    pose proof (Zlength_nonneg d0). pose proof (Zlength_nonneg (m_ow mE)). apply Zlength_nil_inv. lia. }
  pose proof (kd_out _ _ _ _ _ K) as KO.
  assert (AC: after_check G (m_mode mE) = false).
  { unfold after_check. unfold dc_hdr_mode in HM.
    rewrite (proj2 (Z.eqb_neq (m_mode mE) LENGTH)) by dc_md.
    rewrite (proj2 (Z.eqb_neq (m_mode mE) DONE)) by dc_md. rewrite andb_false_r. reflexivity. }
  rewrite AC in KO.
  split; [exact OW|]. split; [exact T|].
  unfold dc_oc, m_left. rewrite KO, OW, Zlength_nil, Z.sub_0_r, Z.sub_diag. reflexivity.
Qed.

Lemma dc_fin (K: dkit_stmt) G pos inp ob flush mE :
  dctx_ok G -> Kd G pos inp ob mE -> mwf3 mE -> m_leave mE = 1 -> leave_why G pos inp ob flush mE ->
  (exists d0, ob = dc_hist G ++ d0) -> bytes_ok ob ->
  let res := leave_fin flush mE in let m := r_m res in
  (r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
  0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = m_aout mE /\ m_ow m = m_ow mE /\
  (exists rest, full G = ob ++ m_ow m ++ rest) /\
  dinv G (pos + m_snx m) (ob ++ m_ow m) (m_s m) (m_tout m) /\
  (r_ret res = Z_STREAM_END -> ob ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
  (r_ret res <> Z_STREAM_END ->
     (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
     (Zlength (m_ow m) = m_aout mE /\ Zlength (ob ++ m_ow m) < Zlength (full G)) \/
     flush = Z_BLOCK \/ flush = Z_TREES) /\
  exists dt, r_dtype res = Some dt /\ dtype_ok G (ob ++ m_ow m) dt.
Proof.
  intros C KE WE LE WHY HP BO. cbv zeta.
  destruct (dc_lf flush mE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
  set (res := leave_fin flush mE) in *.
  pose proof (mwf3_mwf _ WE) as MW.
  pose proof (kd_inp _ _ _ _ _ KE) as KI.
  pose proof (mw_nx _ MW) as NX. rewrite KI in NX.
  pose proof (mw_bits _ MW) as BT.
  pose proof (kd_at _ _ _ _ _ KE) as KA.
  pose proof (kd_ret _ _ _ _ _ KE) as KR. rewrite LE in KR. change (1 =? 1) with true in KR. rewrite andb_true_r in KR.
  destruct (dco_shape K G _ _ _ _ _ C KA) as (H1 & H2 & H3 & H4 & H5).
  destruct (dc_s2_facts flush mE) as (D2 & HO2 & BI2 & SC2 & _).
  set (upd := negb (Z.land (i_wrap (m_s mE)) 4 =? 0) && negb (dc_oc mE =? 0)) in *.
  set (c := update_check (i_flags (m_s mE)) (i_check (m_s mE)) (dc_wd mE)) in *.
  assert (DS: dsame (m_s mE) (m_s (r_m res))).
  { rewrite F1. apply dc_dsame_trans with (dc_s2 flush mE); [exact D2|].
    destruct upd; unfold dsame; cbn [i_mode i_last i_wrap i_flags i_head i_wbits i_length i_offset i_extra i_nlen
      i_ndist i_ncode i_have i_lens i_lencode i_lenbits i_distcode i_distbits i_codes set_i_check set_i_total];
      repeat split. }
  assert (SF: i_hold (m_s (r_m res)) = m_hold mE /\ i_bits (m_s (r_m res)) = m_bits mE /\
              i_wsize (m_s (r_m res)) = i_wsize (dc_s2 flush mE) /\ i_wbits (m_s (r_m res)) = i_wbits (dc_s2 flush mE) /\
              i_whave (m_s (r_m res)) = i_whave (dc_s2 flush mE) /\ i_wnext (m_s (r_m res)) = i_wnext (dc_s2 flush mE) /\
              i_wdata (m_s (r_m res)) = i_wdata (dc_s2 flush mE) /\
              i_total (m_s (r_m res)) = u64 (i_total (m_s mE) + dc_oc mE) /\
              i_check (m_s (r_m res)) = (if upd then c else i_check (m_s mE))).
  { rewrite F1, <- HO2, <- BI2.
    destruct upd; cbn [i_hold i_bits i_wsize i_wbits i_whave i_wnext i_wdata i_total i_check set_i_check set_i_total];
      repeat split; exact SC2. }
  destruct SF as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  pose proof DS as (E1 & E2 & _).
  set (sF := m_s (r_m res)) in *. set (mF := r_m res) in *.
  assert (RET: r_ret res = Z_BUF_ERROR \/ r_ret res = m_ret mE).
  { rewrite F11. destruct (_ && (m_ret mE =? Z_OK)); [left|right]; reflexivity. }
  assert (SE: r_ret res = Z_STREAM_END -> m_mode mE = DONE).
  { intros R. destruct RET as [B|B]; rewrite R in B; [dc_md|].
    rewrite KR in B. destruct (Z.eqb_spec (m_mode mE) DONE); [auto | dc_md]. }
  split.
  { destruct RET as [B|B]; [right; left; exact B|]. rewrite B, KR.
    destruct (m_mode mE =? DONE); [right; right | left]; reflexivity. }
  split; [rewrite F5; exact NX|].
  split; [rewrite F6, F4; reflexivity|].
  split; [exact F8|].
  split; [exact F4|].
  split; [destruct H2 as (r & R); exists r; rewrite F4, R, app_assoc; reflexivity|].
  split.
  { rewrite F5, F4, F3. split; [|split; [|split; [|split]]].
    - rewrite S1, S2. apply dc_at_ext with (m_s mE); [exact DS | | exact KA].
      destruct (classic_hdr (m_mode mE)) as [HM|HM]; [left|right; exact HM].
      destruct (dc_hdr_tot G pos inp ob mE KE WE HP HM) as (_ & T0 & O0).
      rewrite S8, T0, O0. reflexivity.
    - exact (dc_glob_ext _ _ _ DS (kd_glob _ _ _ _ _ KE)).
    - intros M. rewrite E1 in M. apply dc_win_ext with (dc_s2 flush mE); auto.
      exact (dc_fin_win G pos inp ob flush mE KE WE M).
    - apply (dc_fin_chk G pos inp ob mE sF C KE WE HP BO DS S8 S9).
    - exact (dc_fin_tout G pos inp ob mE KE WE HP). }
  split.
  { intros R. pose proof (SE R) as MD. destruct (dc_at_done _ _ _ _ _ _ KA MD) as (O & _ & Q & B0).
    rewrite F4, F5. split; [exact O|]. rewrite B0 in Q. lia. }
  split.
  { intros NR. destruct WHY as [MD|[(N1 & N2)|[(N1 & N2)|N1]]].
    - exfalso. apply NR. destruct RET as [B|B].
      + rewrite F11 in B |- *. rewrite KR, MD, Z.eqb_refl in *.
        destruct (_ && (Z_STREAM_END =? Z_OK)) eqn:X; [|reflexivity].
        rewrite andb_true_iff in X. destruct X as [_ X]. discriminate.
      + rewrite B, KR, MD, Z.eqb_refl. reflexivity.
    - left. rewrite F5. auto.
    - right; left. rewrite F4. unfold m_left in N1. split; [lia | exact N2].
    - right; right. exact N1. }
  exists (dc_dt (m_bits mE) (i_last (m_s mE) =? 0) (m_mode mE =? Zlib.proof.inflate.Model.TYPE)
            ((m_mode mE =? LEN_) || (m_mode mE =? COPY_))).
  split; [rewrite F12; reflexivity|].
  destruct (dc_dt_bits (m_bits mE) (i_last (m_s mE) =? 0) (m_mode mE =? Zlib.proof.inflate.Model.TYPE)
            ((m_mode mE =? LEN_) || (m_mode mE =? COPY_)) ltac:(lia)) as [[B1 _] [B2 B3]].
  rewrite F4. unfold dtype_ok. split; [|split].
  - intros N. apply B1, Z.eqb_eq in N.
    destruct (dc_at_type _ _ _ _ _ _ KA N) as (k & Rk & _ & Ok & _). exists k. auto.
  - intros N. apply B2, Z.eqb_neq in N. exact (H4 N).
  - intros N. apply H5. destruct (Z.eqb_spec (i_last (m_s mE)) 0) as [Z0|Z0]; [exact Z0|].
    exfalso. exact (B3 eq_refl N).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The window beyond CHECK (non-gzip)                                                             *)

Lemma dc_uw_wsize s d : i_wsize s <> 0 -> i_wsize (updatewindow s d) = i_wsize s.
Proof.
  intros N. unfold updatewindow. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) N).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma dc_loop_w flush m o : loop2 flush lenfix_list distfix_list m o -> i_wbits (m_s m) <> 0 ->
  forall mE, o = IBrk mE -> dcwk_rel m mE.
Proof.
  intros LP. induction LP as [m r m' E | m m' E L1 | m m' o E L1 LP IH]; intros W mE EO.
  - discriminate.
  - inversion EO; subst. pose proof (dcwk_keep flush m W) as R. rewrite E in R. exact R.
  - pose proof (dcwk_keep flush m W) as R. rewrite E in R.
    assert (W': i_wbits (m_s m') <> 0) by (destruct R as (_ & _ & _ & _ & _ & R); rewrite R; exact W).
    specialize (IH W' mE EO). unfold dcwk_rel in *. intuition congruence.
Qed.

Lemma dc_fin_w G pos inp ob flush mE : Kd G pos inp ob mE -> mwf3 mE -> m_leave mE = 1 ->
  (forall h, dc_w G <> WGzip h) -> i_wsize (m_s mE) <> 0 -> win_ok G (m_s mE) ob ->
  (r_ret (leave_fin flush mE) <> Z_STREAM_END \/ wrapped G = false) ->
  i_wsize (m_s (r_m (leave_fin flush mE))) <> 0 /\ win_ok G (m_s (r_m (leave_fin flush mE))) (ob ++ m_ow mE).
Proof.
  intros K W LE NG WS WO RW.
  destruct (dc_lf flush mE) as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _).
  pose proof (kd_out _ _ _ _ _ K) as KO. pose proof (kd_ret _ _ _ _ _ K) as KR.
  pose proof (mwf3_mwf _ W) as MW. destruct (mw_ow _ MW) as [OWL _]. pose proof (mw_aout _ MW) as AO.
  pose proof (Zlength_nonneg (m_ow mE)) as OW0.
  assert (AC: after_check G (m_mode mE) = false).
  { destruct (after_check G (m_mode mE)) eqn:A; [|reflexivity]. exfalso.
    unfold after_check in A. apply andb_true_iff in A. destruct A as [WR LD]. apply orb_true_iff in LD.
    destruct RW as [NR|WF]; [|congruence].
    destruct LD as [L|D]; apply Z.eqb_eq in L || apply Z.eqb_eq in D.
    - destruct (dc_at_length _ _ _ _ _ _ (kd_at _ _ _ _ _ K) L) as (hh & Hh). exact (NG hh Hh).
    - assert (MR: m_ret mE = Z_STREAM_END) by (rewrite KR, LE; unfold m_mode in *; rewrite D; reflexivity).
      apply NR. rewrite F11, MR. change (Z_STREAM_END =? Z_OK) with false. rewrite andb_false_r. reflexivity. }
  rewrite AC in KO.
  assert (WD: dc_wd mE = m_ow mE).
  { unfold dc_wd, dc_oc, m_left. rewrite KO.
    replace (m_aout mE - (m_aout mE - Zlength (m_ow mE))) with (Zlength (m_ow mE)) by lia.
    rewrite dc_u32_id by dc_rep. rewrite Z.sub_diag. apply sublist_same; lia. }
  assert (LO: leave_ok flush mE = true).
  { unfold leave_ok. cbv zeta. rewrite (proj2 (Z.eqb_neq _ _) WS). reflexivity. }
  set (X := updatewindow (dc_s1 mE) (m_ow mE)).
  assert (EF: i_wsize (m_s (r_m (leave_fin flush mE))) = i_wsize X /\
              i_wbits (m_s (r_m (leave_fin flush mE))) = i_wbits X /\
              i_whave (m_s (r_m (leave_fin flush mE))) = i_whave X /\
              i_wnext (m_s (r_m (leave_fin flush mE))) = i_wnext X /\
              i_wdata (m_s (r_m (leave_fin flush mE))) = i_wdata X).
  { rewrite F1. unfold dc_s2. rewrite LO, WD.
    destruct (negb (Z.land (i_wrap (m_s mE)) 4 =? 0) && negb (dc_oc mE =? 0)); repeat split. }
  destruct EF as (A1 & A2 & A3 & A4 & A5).
  split.
  - rewrite A1. unfold X. rewrite dc_uw_wsize by exact WS. exact WS.
  - apply dc_win_ext with X; auto. apply dcw_win; [apply dc_swf_s1; exact MW|].
    apply dc_win_ext with (m_s mE); try reflexivity. exact WO.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The call                                                                                       *)

Definition dc_call_post (G: dctx) (pos: Z) (out: list Z) (L: live) (z: zfields) (inp: list Z) (flush: Z) (res: result) : Prop :=
    let m := r_m res in
    r_ret res = Z_MEM_ERROR \/
    ((r_ret res = Z_OK \/ r_ret res = Z_BUF_ERROR \/ r_ret res = Z_STREAM_END) /\
     0 <= m_snx m <= Zlength inp /\ m_sow m = Zlength (m_ow m) /\ m_aout m = zf_ao z /\
     (exists rest, full G = out ++ m_ow m ++ rest) /\
     dinv G (pos + m_snx m) (out ++ m_ow m) (m_s m) (m_tout m) /\
     ((forall h, dc_w G <> WGzip h) -> i_wsize (l_s L) <> 0 -> win_ok G (l_s L) out ->
      (r_ret res <> Z_STREAM_END \/ wrapped G = false) ->
      i_wsize (m_s m) <> 0 /\ win_ok G (m_s m) (out ++ m_ow m)) /\
     (r_ret res = Z_STREAM_END -> out ++ m_ow m = full G /\ pos + m_snx m = slen G) /\
     (r_ret res <> Z_STREAM_END ->
        (m_snx m = Zlength inp /\ pos + Zlength inp < slen G) \/
        (Zlength (m_ow m) = zf_ao z /\ Zlength (out ++ m_ow m) < Zlength (full G)) \/
        flush = Z_BLOCK \/ flush = Z_TREES) /\
     exists dt, r_dtype res = Some dt /\ dtype_ok G (out ++ m_ow m) dt).

(* decode_call_stmt with avail_out <= Int.max_signed (inflate_spec's precondition; needed for mwf3 of m_init) *)
Lemma dec_call_fx : dkit_stmt -> stepf2_mwf3_stmt -> group_ok md_hdr -> group_ok md_type -> group_ok md_tab ->
  group_ok md_dec -> group_ok md_trl ->
  forall G pos out L z inp flush res,
    dctx_ok G -> dinv G pos out (l_s L) (zf_tout z) -> live_ok L -> zf_ok z -> zf_ao z <= 2 ^ 31 - 1 ->
    0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) -> inp = sublist pos (pos + Zlength inp) (dc_src G) ->
    run2 flush lenfix_list distfix_list (m_init z L inp) res ->
    dc_call_post G pos out L z inp flush res.
Proof.
  intros K SM H1 H2 H3 H4 H5 G pos out L z inp flush res C DI LV ZF AO P0 PL IE RUN.
  pose proof (dc_step H1 H2 H3 H4 H5) as ST.
  pose proof C as (_ & _ & _ & _ & _ & CSRC & CB & _).
  assert (LI: Zlength inp <= Int.max_signed) by dc_rep.
  assert (BI: bytes_ok (sublist pos (pos + Zlength inp) (dc_src G))) by (apply Forall_sublist; exact CB).
  rewrite <- IE in BI.
  destruct (dc_init G pos out L z inp DI LV ZF ltac:(dc_rep) LI BI) as (K0 & W0).
  destruct (dco_shape K G _ _ _ _ _ C (proj1 DI)) as (HP & _ & BO & _).
  destruct RUN as (o & LP & RO).
  destruct (dc_loop SM ST G pos inp out flush C P0 PL IE _ _ LP K0 W0 eq_refl)
    as (mE & -> & KE & WE & LE & _ & WHY & AE).
  change (m_aout (m_init z L inp)) with (zf_ao z) in AE.
  inversion RO; subst.
  - left. reflexivity.
  - right.
    destruct (dc_fin K G pos inp out flush mE C KE WE LE WHY HP BO)
      as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    rewrite AE in R4, R9.
    assert (WIN: (forall h, dc_w G <> WGzip h) -> i_wsize (l_s L) <> 0 -> win_ok G (l_s L) out ->
      (r_ret (leave_fin flush mE) <> Z_STREAM_END \/ wrapped G = false) ->
      i_wsize (m_s (r_m (leave_fin flush mE))) <> 0 /\
      win_ok G (m_s (r_m (leave_fin flush mE))) (out ++ m_ow (r_m (leave_fin flush mE)))).
    { intros NG WS WO RW. rewrite R5.
      assert (WB: i_wbits (l_s L) <> 0).
      { destruct LV as (_ & SW & _ & _ & _ & _ & LV1 & _).
        destruct (sw_wsize _ SW) as [Z0|[WN _]]; [contradiction|].
        intros E0. destruct (LV1 E0) as [_ WF]. congruence. }
      assert (I0: i_wsize (m_s (m_init z L inp)) = i_wsize (l_s L) /\
                  i_wbits (m_s (m_init z L inp)) = i_wbits (l_s L) /\
                  i_whave (m_s (m_init z L inp)) = i_whave (l_s L) /\
                  i_wnext (m_s (m_init z L inp)) = i_wnext (l_s L) /\
                  i_wdata (m_s (m_init z L inp)) = i_wdata (l_s L)).
      { unfold m_init. cbn [m_s]. destruct (i_mode (l_s L) =? Zlib.proof.inflate.Model.TYPE); repeat split. }
      destruct I0 as (I1 & I2 & I3 & I4 & I5).
      assert (WB0: i_wbits (m_s (m_init z L inp)) <> 0) by (rewrite I2; exact WB).
      destruct (dc_loop_w flush _ _ LP WB0 mE eq_refl) as (J1 & J3 & J4 & J5 & _ & J2).
      apply (dc_fin_w G pos inp out flush mE KE WE LE NG); auto.
      - rewrite J1, I1. exact WS.
      - apply dc_win_ext with (l_s L); auto; congruence. }
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
    split; [exact R6|]. split; [exact R7|]. split; [exact WIN|]. split; [exact R8|]. split; [|exact R10].
    intros NR. destruct (R9 NR) as [A|[(A & B)|A]]; [left; exact A | right; left; exact (conj A B) |
      right; right; exact A].
Qed.

Lemma dec_call : dkit_stmt -> stepf2_mwf3_stmt -> group_ok md_hdr -> group_ok md_type -> group_ok md_tab -> group_ok md_dec -> group_ok md_trl -> decode_call_stmt.
Proof.
  intros K SM H1 H2 H3 H4 H5 G pos out L z inp flush res C DI LV ZF AO P0 PL IE RUN.
  exact (dec_call_fx K SM H1 H2 H3 H4 H5 G pos out L z inp flush res C DI LV ZF AO P0 PL IE RUN).
Qed.

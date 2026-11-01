(* Law rj_bad_checksum: the header passes (HEAD; FLAGS falling through TIME, OS and, for zlib's default gzip
   header, EXLEN .. HCRC) read only header bytes and write no output.  An input x that agrees with the
   stream's input inp' on the header bytes gives the same pass but for the input (the machine m' is at a
   loop head of the decode theory on the true stream: Kd). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Require Import Zlib.proof.rfc1951.DecHdr Zlib.proof.rfc1951.DecKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The input kit                                                                                  *)

Lemma bh_have_inp m x : Zlength x = Zlength (m_inp m) -> m_have (set_m_inp m x) = m_have m.
Proof. intros E. unfold m_have. destruct m; cbn in *. rewrite E. reflexivity. Qed.

Lemma bh_leave_inp m x : set_leave (set_m_inp m x) = set_m_inp (set_leave m) x.
Proof. destruct m; reflexivity. Qed.

(* PULLBYTE reads the byte at nx *)
Lemma bh_pull_inp m x : Znth (m_nx m) x = Znth (m_nx m) (m_inp m) -> pull (set_m_inp m x) = set_m_inp (pull m) x.
Proof. intros E. destruct m; unfold pull; cbn in *. rewrite E. reflexivity. Qed.

(* NEEDBITS(n), n <= 32, from the bit position q = 8 nx - bits reads the bytes i >= nx with 8 i < q + n *)
Lemma bh_needbits_inp k : forall n m x,
  Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> n <= 32 ->
  (forall i, m_nx m <= i -> 8 * i < 8 * m_nx m - m_bits m + n -> Znth i x = Znth i (m_inp m)) ->
  needbits_f k n (set_m_inp m x) = set_m_inp (needbits_f k n m) x.
Proof.
  induction k as [|k IH]; intros n m x Hl Hb Hn Ha; [reflexivity|].
  cbn [needbits_f]. change (m_bits (set_m_inp m x)) with (m_bits m).
  destruct (Z.ltb_spec (m_bits m) n) as [Lt|Ge]; [|reflexivity].
  rewrite (bh_have_inp m x Hl).
  destruct (Z.eqb (m_have m) 0); [apply bh_leave_inp|].
  rewrite bh_pull_inp by (apply Ha; lia).
  assert (Bp : m_bits (pull m) = m_bits m + 8).
  { unfold pull, u32. cbn. apply Z.mod_small. lia. }
  assert (Np : m_nx (pull m) = m_nx m + 1) by reflexivity.
  assert (Ip : m_inp (pull m) = m_inp m) by reflexivity.
  apply IH; rewrite ?Bp, ?Np, ?Ip; auto; try lia.
  intros i H1 H2. apply Ha; lia.
Qed.

(* the common hypotheses of a stage: m the machine on the true input inside the call that started at byte pos,
   x an input of the same length that agrees with it on the header bytes *)
Definition bh_stage (G: dctx) (pos: Z) (x: list Z) (m: mst) : Prop :=
  Zlength x = Zlength (m_inp m) /\
  (forall i, 0 <= i -> 8 * (pos + i) < D0 G -> Znth i x = Znth i (m_inp m)) /\
  dh_in G pos m /\ hold_ok G (pos + m_nx m) (m_hold m) (m_bits m).

(* NEEDBITS(n) inside the header reads the same bytes on both inputs *)
Lemma bh_nb G pos x m n : bh_stage G pos x m -> n <= 32 -> 8 * (pos + m_nx m) - m_bits m + n <= D0 G ->
  needbits n (set_m_inp m x) = set_m_inp (needbits n m) x.
Proof.
  intros (Hl & Ha & Hin & Hh) Hn Hq. pose proof Hin as (Hp & _ & _ & _ & Hnx). pose proof Hh as (Hb & _).
  apply bh_needbits_inp; auto; [lia|].
  intros i H1 H2. apply Ha; lia.
Qed.

(* NEEDBITS(n) inside the header: where it ends, and that it stays inside the header *)
Lemma bh_nb_end G pos x m n : bh_stage G pos x m -> 0 < n <= 32 -> m_bits m < n ->
  8 * (pos + m_nx m) - m_bits m + n <= D0 G -> (8 * (pos + m_nx m) - m_bits m) mod 8 = 0 -> n mod 8 = 0 ->
  exists nx' hold' bits' (lv: bool),
    needbits n m = (if lv then set_leave (dh_mv m nx' hold' bits') else dh_mv m nx' hold' bits') /\
    needbits n (set_m_inp m x) = set_m_inp (needbits n m) x /\
    m_nx m <= nx' <= Zlength (m_inp m) /\ bits' = m_bits m + 8 * (nx' - m_nx m) /\
    hold_ok G (pos + nx') hold' bits' /\ 8 * (pos + nx') <= D0 G /\ (lv = false -> bits' = n).
Proof.
  intros Hst Hn Hlt Hq Hq8 Hn8.
  pose proof (bh_nb G pos x m n Hst ltac:(lia) Hq) as NB.
  destruct Hst as (Hl & Ha & Hin & Hh). pose proof Hh as (Hb & _).
  destruct (dh_nb dkit G pos 4 n m Hin Hh ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (nx' & h' & b' & lv & E & R1 & R2 & R3 & R4).
  change (needbits_f 4 n m) with (needbits n m) in E.
  exists nx', h', b', lv. split; [exact E|]. split; [exact NB|]. split; [lia|]. split; [lia|]. split; [exact R3|].
  destruct lv.
  - destruct R4 as (_ & R4). split; [lia|]. discriminate.
  - destruct R4 as (R4 & R5 & _). specialize (R5 Hlt).
    (* q and n are byte-aligned, so NEEDBITS stops with exactly n bits *)
    assert (B : b' = n).
    { destruct (Z.eq_dec b' n) as [Q|Q]; [exact Q|exfalso].
      assert (8 * (pos + nx') - b' = 8 * (pos + m_nx m) - m_bits m) by lia.
      set (q := 8 * (pos + m_nx m) - m_bits m) in *. set (c := pos + nx') in *.
      assert (b' mod 8 = 0).
      { replace b' with (8 * c - q) by lia. rewrite Zminus_mod, Z.mul_comm, Z_mod_mult, Hq8. reflexivity. }
      pose proof (Z.div_mod b' 8 ltac:(lia)). pose proof (Z.div_mod n 8 ltac:(lia)). lia. }
    split; [lia|intros _; exact B].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header bytes                                                                               *)

(* the header in the bits of the source *)
Lemma bh_hdr_bits G : dctx_ok7a G -> sublist 0 (D0 G) (sbits G) = bytes_bits (hdr_bytes (dc_w G)).
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

Lemma bh_gz_facts G h : dctx_ok7a G -> dc_w G = WGzip h ->
  gz_simple h /\ D0 G = 80 /\ dh_gzf (8 + 256 * gz_flg h).
Proof.
  intros (_ & _ & Hs & _) E. specialize (Hs h E). destruct (dh_gz_simple_bytes h Hs) as (_ & F).
  split; [exact Hs|]. split.
  - unfold D0. rewrite E. cbn [hdr_bytes]. rewrite (dh_gz_len h Hs). reflexivity.
  - unfold dh_gzf. rewrite F. destruct (gz_text h); auto.
Qed.

(* the bytes 2, 3 of a gzip header: CM = 8 and FLG *)
Lemma bh_gz_hold_flags G h : dctx_ok7a G -> dc_w G = WGzip h ->
  bval (sublist 16 32 (sbits G)) = 8 + 256 * gz_flg h.
Proof.
  intros Hok Ew. destruct (bh_gz_facts G h Hok Ew) as (Hs & HD0 & _).
  assert (X0 : sublist 16 32 (sbits G) = sublist 16 32 (bytes_bits (hdr_bytes (dc_w G)))).
  { rewrite <- (bh_hdr_bits G Hok), HD0. rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite X0, Ew. cbn [hdr_bytes].
  destruct (dh_gz_simple_bytes h Hs) as (B & F). rewrite B, F.
  pose proof (dh_sub_bb [31; 139] [8; if gz_text h then 1 else 0] (le_bytes (gz_mtime h) 4 ++ [gz_xfl h; gz_os h])) as X.
  replace (Zlength [31; 139]) with 2 in X by reflexivity.
  replace (Zlength [8; if gz_text h then 1 else 0]) with 2 in X by reflexivity.
  change (8 * 2 + 8 * 2) with 32 in X. change (8 * 2) with 16 in X. rewrite X.
  destruct (gz_text h); reflexivity.
Qed.

(* a raw stream: inflateInit2 set wrap = 0 *)
Lemma bh_raw_wrap G s : dctx_ok7a G -> dc_w G = WRaw -> glob_ok G s -> i_wrap s = 0.
Proof.
  intros ((Hwb & _) & Ha & _) E ((wb0 & Er & _) & _).
  destruct Ha as [Ha|(wb & fl & did & Ez & _)]; [|congruence].
  unfold accepts in Ha. rewrite E in Ha. rewrite Ha in Er.
  destruct (dh_reset2_vals _ Hwb) as (R1 & _). rewrite (init_wrap_wb_of _ _ _ R1) in Er.
  injection Er as Er1 _. rewrite <- Er1. apply dh_rw. lia.
Qed.

(* a wrapped stream: the header has at least two bytes *)
Lemma bh_wrapped_D0 G : dctx_ok7a G -> dc_w G <> WRaw -> 16 <= D0 G.
Proof.
  intros Hok Ew. destruct (dc_w G) as [|wb fl did|h] eqn:E; [congruence| |].
  - unfold D0. rewrite E. cbn [hdr_bytes]. rewrite Zlength_app.
    replace (Zlength (zlib_hdr wb fl (match did with Some _ => true | None => false end))) with 2 by reflexivity.
    pose proof (Zlength_nonneg (match did with Some i => be_bytes i 4 | None => [] end)). lia.
  - destruct (bh_gz_facts G h Hok E) as (_ & D & _). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine with another input                                                                 *)

Lemma bh_mv_inp m x a b c : dh_mv (set_m_inp m x) a b c = set_m_inp (dh_mv m a b c) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_mode_inp m x v : set_mode (set_m_inp m x) v = set_m_inp (set_mode m v) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_upds_inp m x f : upd_s (set_m_inp m x) f = set_m_inp (upd_s m f) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_adler_inp m x v : set_m_adler (set_m_inp m x) v = set_m_inp (set_m_adler m v) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_init_inp m x : initbits (set_m_inp m x) = set_m_inp (initbits m) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_drop_inp m x n : dropbits n (set_m_inp m x) = set_m_inp (dropbits n m) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_updh_inp m x f : upd_h (set_m_inp m x) f = set_m_inp (upd_h m f) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_bad_inp m x e : set_bad (set_m_inp m x) e = set_m_inp (set_bad m e) x.
Proof. destruct m; reflexivity. Qed.

Lemma bh_if_inp (b: bool) m1 m2 x :
  (if b then set_m_inp m1 x else set_m_inp m2 x) = set_m_inp (if b then m1 else m2) x.
Proof. destruct b; reflexivity. Qed.

(* the setters of the header passes commute with replacing the input *)
Ltac bh_push := repeat first [rewrite bh_if_inp | rewrite bh_mv_inp | rewrite bh_mode_inp | rewrite bh_upds_inp
  | rewrite bh_adler_inp | rewrite bh_init_inp | rewrite bh_leave_inp | rewrite bh_drop_inp | rewrite bh_updh_inp
  | rewrite bh_bad_inp].

Lemma bh_f_s m x : m_s (set_m_inp m x) = m_s m.
Proof. reflexivity. Qed.
Lemma bh_f_hold m x : m_hold (set_m_inp m x) = m_hold m.
Proof. reflexivity. Qed.
Lemma bh_f_leave m x : m_leave (set_m_inp m x) = m_leave m.
Proof. reflexivity. Qed.
Lemma bh_f_bits m x : m_bits (set_m_inp m x) = m_bits m.
Proof. reflexivity. Qed.

(* what a pass must show: the same on x but for the input; a break inside the header with no output *)
Definition bh_out (G: dctx) (pos: Z) (x: list Z) (m: mst) (f: mst -> iout) : Prop :=
  f (set_m_inp m x) = iomap (fun m => set_m_inp m x) (f m) /\
  (forall m1, f m = IBrk m1 -> pos + m_nx m1 <= hlen G /\ m_ow m1 = m_ow m).

(* NEEDBITS running out of input *)
Lemma bh_leave_out G pos x m f nx h b :
  f m = IBrk (set_leave (dh_mv m nx h b)) ->
  f (set_m_inp m x) = IBrk (set_leave (dh_mv (set_m_inp m x) nx h b)) -> 8 * (pos + nx) <= D0 G ->
  bh_out G pos x m f.
Proof.
  intros E1 E2 Hq. split.
  - rewrite E1, E2. bh_push. reflexivity.
  - intros m1 E. rewrite E1 in E. inversion E. subst m1. cbn. unfold hlen. unfold D0 in Hq. split; [lia|reflexivity].
Qed.

(* EXLEN .. HCRC on a covered gzip header read nothing *)
Lemma bh_exlen_tail M x : i_head (m_s M) = false -> dh_gzf (i_flags (m_s M)) ->
  c_EXLEN2 (set_m_inp M x) = iomap (fun m => set_m_inp m x) (c_EXLEN2 M).
Proof.
  intros Hhd Hf. destruct (dh_gzf_land _ Hf) as (F1 & F2 & F3 & F4 & _).
  rewrite (dh_exlen M), (dh_exlen (set_m_inp M x)) by assumption.
  rewrite (dh_extra (set_mode M EXTRA)), (dh_extra (set_mode (set_m_inp M x) EXTRA)) by assumption.
  rewrite dh_name by assumption. rewrite dh_name by assumption.
  rewrite dh_comment by assumption. rewrite dh_comment by assumption.
  rewrite dh_hcrc by assumption. rewrite dh_hcrc by assumption.
  cbn [iomap]. bh_push. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The stages                                                                                     *)

(* OS: 16 bits at bit 64, then EXLEN .. HCRC *)
Lemma bh_os_stage G pos x m : D0 G = 80 -> bh_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 64 -> m_bits m < 16 ->
  i_head (m_s m) = false -> dh_gzf (i_flags (m_s m)) -> m_leave m = 0 ->
  bh_out G pos x m c_OS2.
Proof.
  intros HD0 Hst Hq Hb Hhd Hf Hlv.
  destruct (bh_nb_end G pos x m 16 Hst ltac:(lia) Hb ltac:(lia) ltac:(rewrite Hq; reflexivity) eq_refl)
    as (nx' & h' & b' & lv & E & NB & R1 & R2 & R3 & R4 & R5).
  rewrite E in NB.
  destruct (dh_os_step m Hhd Hlv Hf) as (La & Sa).
  destruct (dh_os_step (set_m_inp m x) Hhd Hlv Hf) as (Lb & _).
  destruct lv.
  - rewrite <- bh_leave_inp, <- bh_mv_inp in NB.
    apply (bh_leave_out G pos x m c_OS2 nx' h' b'); [exact (La _ _ _ E) | exact (Lb _ _ _ NB) | exact R4].
  - rewrite <- bh_mv_inp in NB. split.
    + rewrite (dh_os1 m nx' h' b' Hhd Hlv (proj1 (dh_gzf_land _ Hf)) E).
      rewrite (dh_os1 (set_m_inp m x) nx' h' b' Hhd Hlv (proj1 (dh_gzf_land _ Hf)) NB).
      bh_push.
      apply bh_exlen_tail; assumption.
    + intros m1 Em. destruct (Sa _ _ _ E) as (m2 & E2 & S2 & _ & N2 & _).
      rewrite E2 in Em. inversion Em. subst m1.
      split; [unfold hlen; unfold D0 in R4; lia|]. apply S2.
Qed.

(* TIME: 32 bits at bit 32, then OS *)
Lemma bh_time_stage G pos x m : D0 G = 80 -> bh_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 32 -> m_bits m < 32 ->
  i_head (m_s m) = false -> dh_gzf (i_flags (m_s m)) -> m_leave m = 0 ->
  bh_out G pos x m c_TIME2.
Proof.
  intros HD0 Hst Hq Hb Hhd Hf Hlv.
  destruct (bh_nb_end G pos x m 32 Hst ltac:(lia) Hb ltac:(lia) ltac:(rewrite Hq; reflexivity) eq_refl)
    as (nx' & h' & b' & lv & E & NB & R1 & R2 & R3 & R4 & R5).
  rewrite E in NB.
  destruct (dh_time_step m Hhd Hlv Hf) as (La & Sa).
  destruct (dh_time_step (set_m_inp m x) Hhd Hlv Hf) as (Lb & Sb).
  destruct lv.
  - rewrite <- bh_leave_inp, <- bh_mv_inp in NB.
    apply (bh_leave_out G pos x m c_TIME2 nx' h' b'); [exact (La _ _ _ E) | exact (Lb _ _ _ NB) | exact R4].
  - specialize (R5 eq_refl). rewrite R5 in E, NB, R3.
    rewrite <- bh_mv_inp in NB.
    assert (Hst' : bh_stage G pos x (set_mode (initbits (dh_mv m nx' h' 32)) OS)).
    { destruct Hst as (Hl & Ha & Hin & Hh). pose proof Hin as (Hp & Hl2 & Hi & Hby & Hnx).
      split; [exact Hl|]. split; [exact Ha|]. split.
      * unfold dh_in. dh_red. repeat split; auto; lia.
      * dh_red. apply (dh_hold0 _ _ _ _ R3). lia. }
    destruct (bh_os_stage G pos x (set_mode (initbits (dh_mv m nx' h' 32)) OS)) as (O1 & O2);
      auto; try (dh_red; lia).
    split.
    + rewrite (Sa _ _ _ E), (Sb _ _ _ NB). bh_push. exact O1.
    + intros m1 Em. rewrite (Sa _ _ _ E) in Em. apply O2 in Em. exact Em.
Qed.

(* FLAGS: 16 bits at bit 16 (CM, FLG), then TIME *)
Lemma bh_flags_stage G pos x m h : dctx_ok7a G -> dc_w G = WGzip h -> bh_stage G pos x m ->
  8 * (pos + m_nx m) - m_bits m = 16 -> m_bits m < 16 ->
  i_head (m_s m) = false -> m_leave m = 0 ->
  bh_out G pos x m c_FLAGS2.
Proof.
  intros Hok Ew Hst Hq Hb Hhd Hlv.
  destruct (bh_gz_facts G h Hok Ew) as (_ & HD0 & Hgzf).
  destruct (bh_nb_end G pos x m 16 Hst ltac:(lia) Hb ltac:(lia) ltac:(rewrite Hq; reflexivity) eq_refl)
    as (nx' & h' & b' & lv & E & NB & R1 & R2 & R3 & R4 & R5).
  rewrite E in NB.
  destruct (dh_flags_step m Hhd Hlv) as (La & Sa).
  destruct (dh_flags_step (set_m_inp m x) Hhd Hlv) as (Lb & Sb).
  destruct lv.
  - rewrite <- bh_leave_inp, <- bh_mv_inp in NB.
    apply (bh_leave_out G pos x m c_FLAGS2 nx' h' b'); [exact (La _ _ _ E) | exact (Lb _ _ _ NB) | exact R4].
  - specialize (R5 eq_refl). rewrite R5 in E, NB, R3.
    assert (Hv : h' = 8 + 256 * gz_flg h).
    { destruct R3 as (_ & _ & R3). rewrite R3. replace (8 * (pos + nx') - 16) with 16 by lia.
      replace (8 * (pos + nx')) with 32 by lia. apply (bh_gz_hold_flags G h Hok Ew). }
    subst h'.
    rewrite <- bh_mv_inp in NB.
    set (m2 := set_mode (initbits (upd_s (dh_mv m nx' (8 + 256 * gz_flg h) 16)
                 (fun s => set_i_flags s (8 + 256 * gz_flg h)))) TIME).
    assert (Hst' : bh_stage G pos x m2).
    { destruct Hst as (Hl & Ha & Hin & Hh). pose proof Hin as (Hp & Hl2 & Hi & Hby & Hnx).
      split; [exact Hl|]. split; [exact Ha|]. split.
      * unfold dh_in, m2. dh_red. repeat split; auto; lia.
      * unfold m2. dh_red. apply (dh_hold0 _ _ _ _ R3). lia. }
    destruct (bh_time_stage G pos x m2) as (O1 & O2); auto; try (unfold m2; dh_red; auto; lia).
    split.
    + rewrite (Sa _ _ _ E Hgzf), (Sb _ _ _ NB Hgzf). bh_push. exact O1.
    + intros m1 Em. rewrite (Sa _ _ _ E Hgzf) in Em. apply O2 in Em. exact Em.
Qed.

(* HEAD: nothing read (raw), or NEEDBITS(16) of the first two bytes; the rest of the case reads nothing *)
Lemma bh_head_gen m x :
  (i_wrap (m_s m) <> 0 -> needbits 16 (set_m_inp m x) = set_m_inp (needbits 16 m) x) ->
  c_HEAD2 (set_m_inp m x) = iomap (fun m => set_m_inp m x) (c_HEAD2 m).
Proof.
  intros NB. unfold c_HEAD2. cbv zeta.
  change (i_wrap (m_s (set_m_inp m x))) with (i_wrap (m_s m)).
  destruct (Z.eqb_spec (i_wrap (m_s m)) 0) as [W|W].
  { cbn [iomap]. bh_push. reflexivity. }
  rewrite (NB W). generalize (needbits 16 m). intros m1.
  repeat (bh_push; rewrite ?bh_f_s, ?bh_f_hold, ?bh_f_leave, ?bh_f_bits;
          match goal with |- context [if ?b then _ else _] => destruct b end);
    cbn [iomap]; reflexivity.
Qed.

(* HEAD after NEEDBITS(16) moves neither the input nor the output *)
Lemma bh_head_nx m m2 : i_wrap (m_s m) <> 0 -> c_HEAD2 m = IBrk m2 ->
  m_nx m2 = m_nx (needbits 16 m) /\ m_ow m2 = m_ow (needbits 16 m).
Proof.
  intros W. unfold c_HEAD2. cbv zeta.
  destruct (Z.eqb_spec (i_wrap (m_s m)) 0) as [W0|W0]; [contradiction|].
  generalize (needbits 16 m). intros m1.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    intros E; inversion E; subst m2; split; reflexivity.
Qed.

Lemma bad_pass_hdr G pos inp' x ob flush m' :
  dctx_ok7a G -> 0 <= pos -> pos + Zlength inp' <= Zlength (dc_src G) ->
  inp' = sublist pos (pos + Zlength inp') (dc_src G) ->
  Zlength x = Zlength inp' -> bytes_ok x ->
  (forall i, 0 <= i < Zlength x -> pos + i < hlen G -> Znth i x = Znth i inp') ->
  Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 -> md_hdr (m_mode m') ->
  stepf2 flush lenfix_list distfix_list (set_m_inp m' x) =
    iomap (fun m => set_m_inp m x) (stepf2 flush lenfix_list distfix_list m') /\
  (forall m1', stepf2 flush lenfix_list distfix_list m' = IBrk m1' ->
     pos + m_nx m1' <= hlen G /\ m_ow m1' = m_ow m').
Proof.
  intros Hok Hp Hl Hi Hxl _ Hx HK Hw Hlv Hmd.
  pose proof (kd_inp _ _ _ _ _ HK) as I. subst inp'.
  pose proof (mwW_nx _ (proj1 Hw)) as Hnx.
  assert (Hin : dh_in G pos m').
  { unfold dh_in. destruct Hok as (_ & _ & _ & _ & _ & _ & Hby & _). repeat split; auto; lia. }
  pose proof (kd_glob _ _ _ _ _ HK) as Hg. pose proof Hg as (_ & Hhd & _).
  pose proof (kd_at _ _ _ _ _ HK) as A.
  assert (Ha : forall i, 0 <= i -> 8 * (pos + i) < D0 G -> Znth i x = Znth i (m_inp m')).
  { intros i H1 H2. destruct (Z_lt_le_dec i (Zlength x)) as [Lt|Ge].
    - apply Hx; [lia|]. unfold hlen. unfold D0 in H2. lia.
    - rewrite !Znth_overflow by lia. reflexivity. }
  destruct Hmd as [Md|Md].
  - (* HEAD *)
    destruct (dh_at_head _ _ _ _ _ _ A Md) as (Hh & (_ & Hq & Hb16 & _ & _ & Hraw & _)).
    pose proof Hh as (Hb0 & _).
    assert (Hst : bh_stage G pos x m') by (split; [exact Hxl|split; [exact Ha|split; assumption]]).
    assert (St : forall m, m_mode m = HEAD -> stepf2 flush lenfix_list distfix_list m = c_HEAD2 m).
    { intros m E. unfold stepf2, step2. cbv zeta. rewrite E. reflexivity. }
    rewrite (St m' Md), (St (set_m_inp m' x) Md).
    assert (Wr : i_wrap (m_s m') <> 0 -> 16 <= D0 G).
    { intros W. apply bh_wrapped_D0; [exact Hok|]. intros E. apply W. exact (bh_raw_wrap G _ Hok E Hg). }
    split.
    + apply bh_head_gen. intros W. specialize (Wr W). apply (bh_nb G pos); auto; lia.
    + intros m1 Em. destruct (Z.eqb_spec (i_wrap (m_s m')) 0) as [W|W].
      * unfold c_HEAD2 in Em. rewrite W in Em. inversion Em. subst m1. cbn.
        split; [|reflexivity].
        (* nothing read: q = 0 and at most one byte held, none for a raw stream *)
        assert (Hh0 : 0 <= hlen G) by (unfold hlen; apply Zlength_nonneg).
        destruct (wrapped G) eqn:Wg.
        -- assert (dc_w G <> WRaw) by (intros E; unfold wrapped in Wg; rewrite E in Wg; discriminate).
           pose proof (bh_wrapped_D0 G Hok H). unfold D0 in H0. unfold hlen. lia.
        -- specialize (Hraw eq_refl). lia.
      * specialize (Wr W).
        destruct (bh_nb_end G pos x m' 16 Hst ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hq; reflexivity) eq_refl)
          as (nx' & h' & b' & lv & E & _ & R1 & R2 & R3 & R4 & R5).
        destruct (bh_head_nx m' m1 W Em) as (N1 & O1). rewrite N1, O1, E.
        destruct lv; cbn; (split; [unfold hlen; unfold D0 in R4; lia | reflexivity]).
  - (* FLAGS, TIME, OS *)
    destruct (dh_at_gz _ _ _ _ _ _ A Md) as (Hh & (h & Ew & _ & _ & _ & D)).
    destruct (bh_gz_facts G h Hok Ew) as (_ & HD0 & Hgzf).
    assert (Hst : bh_stage G pos x m') by (split; [exact Hxl|split; [exact Ha|split; assumption]]).
    destruct (dh_step_md flush lenfix_list distfix_list m') as (SF & ST & SO).
    destruct (dh_step_md flush lenfix_list distfix_list (set_m_inp m' x)) as (SF' & ST' & SO').
    destruct Md as [Md|[Md|Md]]; unfold m_mode in Md; rewrite Md in D;
      destruct D as [(DM & Dq & Db)|[(DM & Dq & Db & Df)|(DM & Dq & Db & Df)]];
      try (dh_modes_in DM; lia).
    + rewrite (SF Md), (SF' Md). apply (bh_flags_stage G pos x m' h); auto.
    + rewrite (ST Md), (ST' Md). apply (bh_time_stage G pos x m'); auto. rewrite Df. exact Hgzf.
    + rewrite (SO Md), (SO' Md). apply (bh_os_stage G pos x m'); auto. rewrite Df. exact Hgzf.
Qed.

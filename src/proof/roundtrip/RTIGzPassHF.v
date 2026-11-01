(* RT-I part rti_gz_pass: the HEAD pass and the cases FLAGS, TIME, OS of the gzip header pass (stages 0 -> 1 -> 2 -> 3) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Zlib.proof.harness.inflate_header.IHTKitNb Zlib.proof.harness.inflate_header.IHTKitLay Zlib.proof.harness.inflate_header.IHTKitMisc.
Require Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

Module IHD := Zlib.proof.harness.inflate_header.IHTDefs.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS(16 / 32) from an empty bit buffer, enough input                                       *)

Lemma gp_nb m n :
  bytes_ok (m_inp m) -> m_bits m = 0 -> m_hold m = 0 -> 0 <= m_nx m -> (n = 16 \/ n = 32) ->
  m_nx m + n / 8 <= Zlength (m_inp m) ->
  needbits n m =
  set_m_bits (set_m_hold (set_m_nx m (m_nx m + n / 8)) (IHD.ih_le (sublist (m_nx m) (m_nx m + n / 8) (m_inp m)))) n.
Proof.
  intros B Hb Hh Hn N L.
  assert (Q: (n + 7) / 8 = n / 8) by (destruct N; subst n; reflexivity).
  destruct (Zlib.proof.harness.inflate_header.IHTKitNb.ihn_nbf (m_inp m) (m_inp m) 0 (m_nx m) n 4 m B
              ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_l, sublist_same; auto) eq_refl
              ltac:(destruct N; subst n; cbn in L; lia) ltac:(destruct N; subst n; lia) ltac:(lia)
              ltac:(rewrite Q; destruct N; subst n; cbn; lia) ltac:(rewrite Q; destruct N; subst n; cbn; lia)
              ltac:(rewrite Hb; lia) ltac:(rewrite Hh, Z.add_0_l, sublist_nil; reflexivity))
    as (nx' & lv' & E & R & C).
  rewrite Q in C. destruct C as [(_ & C1 & C2) | (C1 & C2)]; [lia|].
  unfold needbits. rewrite E, C1. rewrite Z.add_0_l in C2. rewrite C2.
  replace (8 * (0 + (m_nx m + n / 8) - m_nx m)) with n by (destruct N; subst n; cbn; lia).
  rewrite Z.add_0_l. destruct m; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fixed part of the header in O                                                              *)

Lemma gp_O_split gh xfl O : gp_ok gh xfl O ->
  let H := gp_H gh xfl in
  exists t, O = [31; 139] ++ [8; gz_flg H] ++ le_bytes (gz_mtime H) 4 ++ [gz_xfl H; gz_os H] ++ t.
Proof.
  intros ((r & E) & _). cbv zeta. unfold gp_H. rewrite E.
  unfold gz_bytes. destruct (gz_hcrc _); unfold gz_bytes0; eexists; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma gp_le4 v : Zlength (le_bytes v 4) = 4.
Proof. reflexivity. Qed.

Lemma gp_sub (a l t: list Z) : sublist (Zlength a) (Zlength a + Zlength l) (a ++ l ++ t) = l.
Proof.
  rewrite app_assoc. rewrite sublist_app1 by (rewrite ?Zlength_app; pose proof (Zlength_nonneg a); pose proof (Zlength_nonneg l); lia).
  rewrite sublist_app2 by (pose proof (Zlength_nonneg a); lia). rewrite Z.sub_diag. replace (Zlength a + Zlength l - Zlength a) with (Zlength l) by lia.
  apply sublist_same; reflexivity.
Qed.

Lemma gp_pre (a t: list Z) : sublist 0 (Zlength a) (a ++ t) = a.
Proof. rewrite sublist_app1 by (pose proof (Zlength_nonneg a); lia). apply sublist_same; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* FLG                                                                                            *)

Lemma gp_flg H : let F := gz_flg H in
  0 <= F <= 31 /\ s32 (8 + 256 * F) = 8 + 256 * F /\ Z.land (8 + 256 * F) 255 = 8 /\
  Z.land (8 + 256 * F) 57344 = 0 /\ (Z.land (8 + 256 * F) 512 =? 0) = negb (gz_hcrc H) /\
  Z.land (Z.shiftr (8 + 256 * F) 8) 1 = (if gz_text H then 1 else 0) /\
  Z.land (Z.shiftr (8 + 256 * F) 9) 1 = (if gz_hcrc H then 1 else 0).
Proof.
  destruct H as [t mt x o e n c hc]. unfold gz_flg. cbn.
  destruct t, hc, e, n, c; repeat split; try reflexivity; discriminate.
Qed.

Lemma gp_set_leave_id m : set_m_leave m (m_leave m) = m.
Proof. destruct m; reflexivity. Qed.

Ltac gp_red := cbn [set_mode upd_s set_m_s initbits set_m_adler set_m_bits set_m_hold set_m_nx set_m_leave upd_h
  set_m_h set_i_check set_i_flags set_i_wbits set_i_mode m_s m_h m_inp m_ow m_out m_aout m_ret m_tout m_leave
  m_nx m_hold m_bits m_adler i_last i_total i_wrap i_head i_wsize i_mode i_wbits i_flags i_check].

(* ---------------------------------------------------------------------------------------------- *)
(* HEAD                                                                                           *)

Lemma gp_head : gp_head_stmt.
Proof.
  intros gh xfl O z L OK HS.
  set (s0 := l_s L) in *.
  (* inflateInit2(32): wrap 7 with bit 3 set by fix F8 (windowBits 0), wbits 0 *)
  assert (F0: i_mode s0 = HEAD /\ i_wrap s0 = 15 /\ i_wbits s0 = 0 /\ i_hold s0 = 0 /\ i_bits s0 = 0 /\
              i_last s0 = 0 /\ i_total s0 = 0 /\ i_wsize s0 = 0)
    by (destruct HS as [E|E]; rewrite E; repeat split; reflexivity).
  destruct F0 as (Fm & Fw & Fb & Fh & Fbi & Fl & Ft & Fs).
  assert (M0: m_init z L O = MS s0 (l_h L) O (zf_ao z) 0 [] 0 0 (Zlength O) (zf_ao z) Z_OK 0 (zf_adler z)
                               (zf_msg z) (zf_tin z) (zf_tout z) 0 0).
  { unfold m_init. cbv zeta. fold s0. rewrite Fm. change (HEAD =? Zlib.proof.inflate.Model.TYPE) with false.
    cbv iota. rewrite Fh, Fbi. reflexivity. }
  rewrite M0. set (m0 := MS s0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  destruct (gp_O_split gh xfl O OK) as (t & Et). pose proof OK as (_ & BO & _ & _ & _).
  assert (S2: sublist 0 2 O = [31; 139]) by (rewrite Et; apply (gp_pre [31; 139])).
  assert (LO: 10 <= Zlength O) by (rewrite Et, !Zlength_app, gp_le4; pose proof (Zlength_nonneg t); cbn; lia).
  assert (NB: needbits 16 m0 = set_m_bits (set_m_hold (set_m_nx m0 2) 35615) 16).
  { rewrite (gp_nb m0 16 BO eq_refl eq_refl ltac:(cbn; lia) ltac:(auto) ltac:(cbn; lia)). cbn [m_nx m0 m_inp].
    change (0 + 16 / 8) with 2. rewrite S2. reflexivity. }
  assert (St: stepf2 Z_FINISH lenfix_list distfix_list m0 = c_HEAD2 m0).
  { unfold stepf2, step2, m_mode. cbn [m_s m0]. rewrite Fm. reflexivity. }
  rewrite St. unfold c_HEAD2. cbn [m_s m0]. rewrite Fw. cbv zeta. rewrite NB.
  cbn [m_leave m_s m0 set_m_bits set_m_hold set_m_nx]. rewrite Fw. change (15 =? 0) with false. change (0 =? 1) with false.
  change (negb (Z.land 15 2 =? 0) && (35615 =? 35615)) with true. cbv iota beta.
  eexists; split; [reflexivity|]. rewrite S2. change (hbytes2 35615) with [31; 139].
  subst m0. split; [constructor|]; gp_red; rewrite ?Fb, ?Fl, ?Ft, ?Fw, ?Fs; try reflexivity.
  split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers of the cases                                                                           *)

Lemma gp_crc O a b : bytes_ok O -> 0 <= a <= b -> b <= Zlength O ->
  Zlib.proof.crc32.Model.ref_crc32 (Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 a O)) (sublist a b O) =
  Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 b O).
Proof. intros B A L. exact (Zlib.proof.harness.inflate_header.IHTKitMisc.ihm_crc O a b B A L). Qed.

Lemma gp_os_bits a b : 0 <= a <= 255 -> 0 <= b <= 255 -> Z.land (a + 256 * b) 255 = a /\ s32 (Z.shiftr (a + 256 * b) 8) = b.
Proof. exact (proj2 Zlib.proof.harness.inflate_header.IHTKitMisc.ihm_bits a b). Qed.

(* the header fields of fhdr_of *)
Lemma gp_H_rng gh xfl : (forall g, gh = Some g -> RF.rhdr_ok g) -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  let H := gp_H gh xfl in
  0 <= gz_mtime H < 2 ^ 32 /\ gz_xfl H = xfl /\ 0 <= gz_os H <= 255.
Proof.
  intros R X. unfold gp_H, RF.fhdr_of. destruct gh as [g|]; cbn.
  - destruct (R g eq_refl) as (_ & _ & _ & T & _). split; [lia|]. split; [reflexivity|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (DS.gz_os g) (2 ^ 8) ltac:(lia)). change (2 ^ 8) with 256 in *. change (Z.ones 8) with 255. lia.
  - split; [lia|]. split; [reflexivity|]. lia.
Qed.

Lemma gp_H_some gh xfl g : gh = Some g -> RF.rhdr_ok g ->
  let H := gp_H gh xfl in
  (if gz_text H then 1 else 0) = DS.gz_text g /\ gz_mtime H = DS.gz_time g /\ gz_os H = DS.gz_os g /\
  (if gz_hcrc H then 1 else 0) = DS.gz_hcrc g.
Proof.
  intros E (T & C & O & _). subst gh. unfold gp_H, RF.fhdr_of. cbn.
  split; [destruct T as [T|T]; rewrite T; reflexivity|]. split; [reflexivity|].
  split; [|destruct C as [C|C]; rewrite C; reflexivity].
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Lemma gp_le4_eq v : 0 <= v < 2 ^ 32 ->
  le_bytes v 4 = [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; (v / 16777216) mod 256].
Proof.
  intros V. unfold le_bytes. cbn [seq map Z.to_nat].
  change (seq 0 (Pos.to_nat 4)) with [0%nat; 1%nat; 2%nat; 3%nat]. cbn [map Z.of_nat].
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16. change (8 * 3) with 24.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_1_r. reflexivity.
Qed.

Lemma gp_O_len gh xfl O : gp_ok gh xfl O -> Zlength (gz_bytes (gp_H gh xfl)) <= Zlength O.
Proof.
  intros ((r & E) & _). unfold gp_H. rewrite E, Zlength_app. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma gp_bytes_len H : 10 <= Zlength (gz_bytes0 H) <= Zlength (gz_bytes H).
Proof.
  assert (A: Zlength (gz_bytes0 H) = 10 + Zlength (gX H) + Zlength (gN H) + Zlength (gC H)).
  { rewrite gz_bytes0_split, !Zlength_app. unfold gA. rewrite !Zlength_app, gp_le4, !Zlength_cons, Zlength_nil. lia. }
  pose proof (Zlength_nonneg (gX H)). pose proof (Zlength_nonneg (gN H)). pose proof (Zlength_nonneg (gC H)).
  split; [lia|]. unfold gz_bytes. destruct (gz_hcrc H); [|lia].
  rewrite Zlength_app. pose proof (Zlength_nonneg (le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (gz_bytes0 H)) 2)). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* FLAGS                                                                                          *)

Lemma gp_flags : gp_flags_stmt.
Proof.
  intros gh xfl O z hd h0 m OK M Ck Hh HB.
  destruct (gp_O_split gh xfl O OK) as (t & Et). pose proof OK as (_ & BO & R & X & _).
  pose proof (gp_O_len gh xfl O OK) as LH. pose proof (gp_bytes_len (gp_H gh xfl)) as LB.
  destruct (gp_flg (gp_H gh xfl)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  set (F := gz_flg (gp_H gh xfl)) in *.
  assert (S2: sublist 0 2 O = [31; 139]) by (rewrite Et; apply (gp_pre [31; 139])).
  assert (S4: sublist 2 4 O = [8; F]) by (rewrite Et; apply (gp_sub [31; 139] [8; F])).
  destruct M as [Mi Mn Mh Mb Ml Mo Mu Ma Mr Mt Mm Mla Mto Mw Ms Mwb Mhd].
  assert (NB: needbits 16 m = set_m_bits (set_m_hold (set_m_nx m 4) (8 + 256 * F)) 16).
  { rewrite (gp_nb m 16); rewrite ?Mi, ?Mn; auto; try (cbn; lia). change (2 + 16 / 8) with 4. rewrite S4.
    rewrite Zlib.proof.harness.inflate_header.IHTKitLay.ihl2_le2. reflexivity. }
  unfold c_FLAGS2. cbv zeta. rewrite NB. gp_red. rewrite Ml. change (0 =? 1) with false. cbv iota.
  rewrite F2, F3, F4. change (negb (8 =? 8)) with false. change (negb (0 =? 0)) with false. cbv iota.
  rewrite Mhd.
  eexists; split; [reflexivity|].
  rewrite F6.
  assert (HB2: hbytes2 (8 + 256 * F) = sublist 2 4 O)
    by (rewrite S4; apply Zlib.proof.harness.inflate_header.IHTKitLay.ihl2_hb2; lia).
  assert (CK: gz_hcrc (gp_H gh xfl) = true ->
              Zlib.proof.crc32.Model.ref_crc32 (i_check (m_s m)) (sublist 2 4 O) =
              Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 4 O))
    by (intros _; rewrite Ck; apply gp_crc; [exact BO | lia | lia]).
  destruct hd; unfold crc_if; gp_red; rewrite HB2, Mw; change (negb (Z.land 15 4 =? 0)) with true; rewrite F5;
    destruct (gz_hcrc (gp_H gh xfl)) eqn:HC; cbn [negb andb]; gp_red.
  all: split; [constructor; gp_red; first [reflexivity | assumption] |].
  all: split; [unfold gp_fl, gp_F; gp_red; reflexivity |].
  all: split; [unfold gp_ck; change (gp_p gh xfl 1) with 4; gp_red; intros HCt; rewrite HC in HCt;
                first [discriminate HCt | exact (CK eq_refl)] |].
  all: unfold gp_hh; intros E; try discriminate E.
  all: destruct (HB eq_refl) as (g & x & nm & cm & Eg & Bf & Hd0);
       exists g, x, nm, cm; split; [exact Eg|]; split; [exact Bf|]; split; [exact Hd0|];
       gp_red; rewrite Hh; unfold gh_at; cbn [Nat.leb];
       rewrite (proj1 (gp_H_some gh xfl g Eg (R g Eg))); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* TIME                                                                                           *)

Lemma gp_time : gp_time_stmt.
Proof.
  intros gh xfl O z hd h0 m OK (M & Fl & Ck & Hh).
  destruct (gp_O_split gh xfl O OK) as (t & Et). pose proof OK as (_ & BO & R & X & _).
  pose proof (gp_O_len gh xfl O OK) as LH. pose proof (gp_bytes_len (gp_H gh xfl)) as LB.
  destruct (gp_H_rng gh xfl R X) as (T1 & T2 & T3).
  set (mt := gz_mtime (gp_H gh xfl)) in *.
  set (F := gz_flg (gp_H gh xfl)) in *.
  assert (S8: sublist 4 8 O = le_bytes mt 4)
    by (rewrite Et, app_assoc; apply (gp_sub ([31; 139] ++ [8; F]) (le_bytes mt 4))).
  pose proof (Zlib.proof.harness.inflate_header.IHTKitLay.ihl2_mt mt T1) as (L1 & L2).
  rewrite <- (gp_le4_eq mt T1) in L1, L2.
  destruct M as [Mi Mn Mh Mb Ml Mo Mu Ma Mr Mt Mm Mla Mto Mw Ms Mwb Mhd].
  change (gp_p gh xfl 1) with 4 in *.
  assert (NB: needbits 32 m = set_m_bits (set_m_hold (set_m_nx m 8) mt) 32).
  { rewrite (gp_nb m 32); rewrite ?Mi, ?Mn; auto; try (cbn; lia). change (4 + 32 / 8) with 8. rewrite S8, L1.
    reflexivity. }
  unfold c_TIME2. cbv zeta. rewrite NB. gp_red. rewrite Ml. change (0 =? 1) with false. cbv iota.
  rewrite Mhd.
  eexists; split; [reflexivity|].
  assert (CK: gz_hcrc (gp_H gh xfl) = true ->
              Zlib.proof.crc32.Model.ref_crc32 (i_check (m_s m)) (sublist 4 8 O) =
              Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 8 O))
    by (intros HC; rewrite (Ck HC); apply gp_crc; [exact BO | lia | lia]).
  unfold gp_fl, gp_F in Fl.
  destruct (gp_flg (gp_H gh xfl)) as (_ & _ & _ & _ & F5 & _).
  destruct hd; gp_red; rewrite L2, <- S8; unfold crc_if; gp_red; rewrite Mw, Fl;
    change (negb (Z.land 15 4 =? 0)) with true; rewrite F5;
    destruct (gz_hcrc (gp_H gh xfl)) eqn:HC; cbn [negb andb]; gp_red.
  all: split; [constructor; gp_red; first [reflexivity | assumption] |].
  all: split; [unfold gp_fl, gp_F; gp_red; exact Fl |].
  all: split; [unfold gp_ck; change (gp_p gh xfl 2) with 8; gp_red; intros HCt; rewrite HC in HCt;
                first [discriminate HCt | exact (CK eq_refl)] |].
  all: unfold gp_hh; intros E; try discriminate E.
  all: destruct (Hh E) as (g & x & nm & cm & Eg & Bf & Hd0 & Hm);
       exists g, x, nm, cm; split; [exact Eg|]; split; [exact Bf|]; split; [exact Hd0|];
       gp_red; rewrite Hm; unfold gh_at; cbn [Nat.leb]; unfold mt;
       rewrite (proj1 (proj2 (gp_H_some gh xfl g Eg (R g Eg)))); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* OS                                                                                             *)

Lemma gp_os : gp_os_stmt.
Proof.
  intros gh xfl O z hd h0 m OK (M & Fl & Ck & Hh).
  destruct (gp_O_split gh xfl O OK) as (t & Et). pose proof OK as (_ & BO & R & X & _).
  pose proof (gp_O_len gh xfl O OK) as LH. pose proof (gp_bytes_len (gp_H gh xfl)) as LB.
  destruct (gp_H_rng gh xfl R X) as (T1 & T2 & T3).
  set (mt := gz_mtime (gp_H gh xfl)) in *.
  set (F := gz_flg (gp_H gh xfl)) in *.
  set (xf := gz_xfl (gp_H gh xfl)) in *.
  set (os := gz_os (gp_H gh xfl)) in *.
  assert (S10: sublist 8 10 O = [xf; os])
    by (rewrite Et, app_assoc, app_assoc; apply (gp_sub ([31; 139] ++ [8; F] ++ le_bytes mt 4) [xf; os])).
  assert (XR: 0 <= xf <= 255) by (rewrite T2; lia).
  destruct (gp_os_bits xf os XR T3) as (B1 & B2).
  destruct M as [Mi Mn Mh Mb Ml Mo Mu Ma Mr Mt Mm Mla Mto Mw Ms Mwb Mhd].
  change (gp_p gh xfl 2) with 8 in *.
  assert (NB: needbits 16 m = set_m_bits (set_m_hold (set_m_nx m 10) (xf + 256 * os)) 16).
  { rewrite (gp_nb m 16); rewrite ?Mi, ?Mn; auto; try (cbn; lia). change (8 + 16 / 8) with 10. rewrite S10.
    rewrite Zlib.proof.harness.inflate_header.IHTKitLay.ihl2_le2. reflexivity. }
  unfold c_OS2. cbv zeta. rewrite NB. gp_red. rewrite Ml. change (0 =? 1) with false. cbv iota.
  rewrite Mhd.
  eexists; split; [reflexivity|].
  assert (CK: gz_hcrc (gp_H gh xfl) = true ->
              Zlib.proof.crc32.Model.ref_crc32 (i_check (m_s m)) (sublist 8 10 O) =
              Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 10 O))
    by (intros HC; rewrite (Ck HC); apply gp_crc; [exact BO | lia | lia]).
  unfold gp_fl, gp_F in Fl.
  destruct (gp_flg (gp_H gh xfl)) as (_ & _ & _ & _ & F5 & _).
  destruct hd; gp_red; rewrite (Zlib.proof.harness.inflate_header.IHTKitLay.ihl2_hb2 xf os XR T3), <- S10;
    unfold crc_if; gp_red; rewrite Mw, Fl; change (negb (Z.land 15 4 =? 0)) with true; rewrite F5;
    destruct (gz_hcrc (gp_H gh xfl)) eqn:HC; cbn [negb andb]; gp_red.
  all: split; [constructor; gp_red; first [reflexivity | assumption] |].
  all: split; [unfold gp_fl, gp_F; gp_red; exact Fl |].
  all: split; [unfold gp_ck; change (gp_p gh xfl 3) with 10; gp_red; intros HCt; rewrite HC in HCt;
                first [discriminate HCt | exact (CK eq_refl)] |].
  all: unfold gp_hh; intros E; try discriminate E.
  all: destruct (Hh E) as (g & x & nm & cm & Eg & Bf & Hd0 & Hm);
       exists g, x, nm, cm; split; [exact Eg|]; split; [exact Bf|]; split; [exact Hd0|];
       gp_red; rewrite Hm, B1, B2, T2; unfold gh_at; cbn [Nat.leb]; unfold os;
       rewrite (proj1 (proj2 (proj2 (gp_H_some gh xfl g Eg (R g Eg))))); reflexivity.
Qed.

Lemma gp_hf_ok : gp_head_stmt /\ gp_flags_stmt /\ gp_time_stmt /\ gp_os_stmt.
Proof. exact (conj gp_head (conj gp_flags (conj gp_time gp_os))). Qed.

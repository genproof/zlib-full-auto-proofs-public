(* RT-I part rti_gz_pass: the cases NAME and COMMENT of the gzip header pass (stages 5 -> 6 -> 7) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Require Import Zlib.proof.roundtrip.RTIGzPassDefs.
Require Import VST.zlist.list_solver.
Require Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

(* the do-while of NAME / COMMENT on a whole zero-terminated field f (all of it offered) *)
Lemma gpnc_zstr_gen (f bytes b0: list Z) (have max: Z) :
  0 < Zlength f -> Znth (Zlength f - 1) f = 0 -> (forall i, 0 <= i < Zlength f - 1 -> Znth i f <> 0) ->
  Zlength f <= have -> (forall i, 0 <= i < Zlength f -> Znth i bytes = Znth i f) ->
  max = Zlength f -> Zlength b0 = Zlength f ->
  forall (k: nat) (copy: Z), 0 <= copy < Zlength f -> Zlength f - copy <= Z.of_nat k ->
    zstr_f k bytes have copy max true (sublist 0 copy f ++ sublist copy (Zlength f) b0) copy =
    (Zlength f, 0, Zlength f, f).
Proof.
  intros Fl Fz Fnz Hv BY Mx B0 k. induction k as [|k IH]; intros copy C Ck.
  - cbn in Ck. lia.
  - cbn [zstr_f]. rewrite (BY copy) by lia.
    replace (copy <? max) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
    replace (upd_Znth copy (sublist 0 copy f ++ sublist copy (Zlength f) b0) (Znth copy f))
      with (sublist 0 (copy + 1) f ++ sublist (copy + 1) (Zlength f) b0) by list_solve.
    destruct (Z.eq_dec (copy + 1) (Zlength f)) as [E|E].
    + replace (Znth copy f) with 0 by (rewrite <- Fz; f_equal; lia). cbn [Z.eqb negb andb].
      rewrite E, sublist_same, sublist_nil, app_nil_r by lia. reflexivity.
    + replace (negb (Znth copy f =? 0)) with true
        by (symmetry; apply negb_true_iff, Z.eqb_neq, Fnz; lia).
      replace (copy + 1 <? have) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
      apply IH; lia.
Qed.

Lemma gpnc_zstr_ro (f bytes b0: list Z) (have max: Z) :
  0 < Zlength f -> Znth (Zlength f - 1) f = 0 -> (forall i, 0 <= i < Zlength f - 1 -> Znth i f <> 0) ->
  Zlength f <= have -> (forall i, 0 <= i < Zlength f -> Znth i bytes = Znth i f) ->
  forall (k: nat) (copy: Z), 0 <= copy < Zlength f -> Zlength f - copy <= Z.of_nat k ->
    zstr_f k bytes have 0 max false b0 copy = (Zlength f, 0, 0, b0).
Proof.
  intros Fl Fz Fnz Hv BY k. induction k as [|k IH]; intros copy C Ck.
  - cbn in Ck. lia.
  - cbn [zstr_f]. rewrite (BY copy) by lia. cbn [andb].
    destruct (Z.eq_dec (copy + 1) (Zlength f)) as [E|E].
    + replace (Znth copy f) with 0 by (rewrite <- Fz; f_equal; lia). cbn [Z.eqb negb andb].
      rewrite E. reflexivity.
    + replace (negb (Znth copy f =? 0)) with true
        by (symmetry; apply negb_true_iff, Z.eqb_neq, Fnz; lia).
      replace (copy + 1 <? have) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
      apply IH; lia.
Qed.

Lemma gpnc_zstr (n bytes b0: list Z) (have max: Z) (wr: bool) :
  Forall (fun b => 0 < b < 256) n ->
  Zlength (n ++ [0]) <= have -> (forall i, 0 <= i < Zlength (n ++ [0]) -> Znth i bytes = Znth i (n ++ [0])) ->
  (wr = true -> max = Zlength (n ++ [0]) /\ Zlength b0 = Zlength (n ++ [0])) ->
  zstr_f (Z.to_nat have) bytes have 0 max wr b0 0 =
    (Zlength (n ++ [0]), 0, if wr then Zlength (n ++ [0]) else 0, if wr then n ++ [0] else b0).
Proof.
  intros FN Hv BY W.
  assert (Lf: Zlength (n ++ [0]) = Zlength n + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  set (f := n ++ [0]) in *.
  pose proof (Zlength_nonneg n).
  assert (Fl: 0 < Zlength f) by lia.
  assert (Fz: Znth (Zlength f - 1) f = 0).
  { rewrite Lf. unfold f. rewrite Znth_app2 by lia. replace (Zlength n + 1 - 1 - Zlength n) with 0 by lia. reflexivity. }
  assert (Fnz: forall i, 0 <= i < Zlength f - 1 -> Znth i f <> 0).
  { intros i I. rewrite Lf in I. unfold f. rewrite Znth_app1 by lia.
    assert (Hb: 0 < Znth i n < 256) by (apply (proj1 (Forall_Znth _ _) FN); lia). lia. }
  clearbody f.
  destruct wr.
  - destruct (W eq_refl) as [Mx B0].
    pose proof (gpnc_zstr_gen f bytes b0 have max Fl Fz Fnz Hv BY Mx B0 (Z.to_nat have) 0) as G.
    rewrite sublist_nil, app_nil_l, <- B0, sublist_same in G by lia.
    rewrite B0 in G. apply G; lia.
  - apply (gpnc_zstr_ro f bytes b0 have max Fl Fz Fnz Hv BY); lia.
Qed.

(* state->flags = 8 + 256 FLG: the FNAME, FCOMMENT, FHCRC tests *)
Lemma gpnc_flg (H: gzhdr) :
  (Z.land (8 + 256 * gz_flg H) 2048 =? 0) = (match gz_name H with Some _ => false | None => true end) /\
  (Z.land (8 + 256 * gz_flg H) 4096 =? 0) = (match gz_comment H with Some _ => false | None => true end) /\
  (Z.land (8 + 256 * gz_flg H) 512 =? 0) = negb (gz_hcrc H).
Proof.
  unfold gz_flg. destruct (gz_text H), (gz_hcrc H), (gz_extra H), (gz_name H), (gz_comment H).
  all: split; [reflexivity | split; reflexivity].
Qed.

Lemma gpnc_crc_if (H: gzhdr) m d :
  i_flags (m_s m) = 8 + 256 * gz_flg H -> i_wrap (m_s m) = 15 ->
  crc_if m d = if gz_hcrc H then upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d)) else m.
Proof.
  intros F W. unfold crc_if. rewrite F, W. destruct (gpnc_flg H) as (_ & _ & E). rewrite E.
  destruct (gz_hcrc H); reflexivity.
Qed.

(* a field in the middle of O *)
Lemma gpnc_mid (A B C O: list Z) : O = A ++ B ++ C ->
  Zlength A + Zlength B <= Zlength O /\
  sublist (Zlength A) (Zlength A + Zlength B) O = B /\
  (forall i, 0 <= i < Zlength B -> Znth i (sublist (Zlength A) (Zlength O) O) = Znth i B).
Proof.
  intros E. subst O. pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B). pose proof (Zlength_nonneg C).
  rewrite !Zlength_app. split; [lia|]. split.
  - rewrite sublist_app2 by lia. rewrite Z.sub_diag. replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
    rewrite sublist_app1 by lia. apply sublist_same; lia.
  - intros i I. rewrite Znth_sublist by (rewrite ?Zlength_app; lia).
    rewrite Znth_app2 by lia. replace (i + Zlength A - Zlength A) with i by lia.
    rewrite Znth_app1 by lia. reflexivity.
Qed.

(* the CRC of the bytes consumed, continued *)
Lemma gpnc_crc (O: list Z) a b : bytes_ok O -> 0 <= a <= b -> b <= Zlength O ->
  ref_crc32 (ref_crc32 0 (sublist 0 a O)) (sublist a b O) = ref_crc32 0 (sublist 0 b O).
Proof.
  intros B A L. rewrite Zlib.proof.crc32.Combine.ref_crc32_app.
  - rewrite <- sublist_split by lia. reflexivity.
  - apply Zlib.proof.adler32.Bytes.is_bytes_sublist. exact B.
Qed.

(* the header's name and comment: deflateSetHeader's without their zero byte *)
Lemma gpnc_name gh xfl : (forall g, gh = Some g -> RF.rhdr_ok g) ->
  match gz_name (gp_H gh xfl) with
  | Some n => Forall (fun b => 0 < b < 256) n /\ (forall g, gh = Some g -> DS.gz_name g = Some (n ++ [0]))
  | None => forall g, gh = Some g -> DS.gz_name g = None
  end.
Proof.
  intros R. unfold gp_H, RF.fhdr_of. destruct gh as [g|]; cbn [gz_name]; [|intros g E; discriminate].
  destruct (R g eq_refl) as (_ & _ & _ & _ & _ & _ & RN & _).
  destruct (DS.gz_name g) as [l|] eqn:E; cbn [option_map].
  - destruct (RN l eq_refl) as (l0 & El & _ & F). subst l. rewrite removelast_last.
    split; [exact F | intros g' Eg; injection Eg as <-; exact E].
  - intros g' Eg; injection Eg as <-; exact E.
Qed.

Lemma gpnc_comment gh xfl : (forall g, gh = Some g -> RF.rhdr_ok g) ->
  match gz_comment (gp_H gh xfl) with
  | Some n => Forall (fun b => 0 < b < 256) n /\ (forall g, gh = Some g -> DS.gz_comment g = Some (n ++ [0]))
  | None => forall g, gh = Some g -> DS.gz_comment g = None
  end.
Proof.
  intros R. unfold gp_H, RF.fhdr_of. destruct gh as [g|]; cbn [gz_comment]; [|intros g E; discriminate].
  destruct (R g eq_refl) as (_ & _ & _ & _ & _ & _ & _ & RN).
  destruct (DS.gz_comment g) as [l|] eqn:E; cbn [option_map].
  - destruct (RN l eq_refl) as (l0 & El & _ & F). subst l. rewrite removelast_last.
    split; [exact F | intros g' Eg; injection Eg as <-; exact E].
  - intros g' Eg; injection Eg as <-; exact E.
Qed.

Lemma gpnc_bytes (H: gzhdr) : exists T, gz_bytes H = gz_bytes0 H ++ T.
Proof. unfold gz_bytes. destruct (gz_hcrc H); [eexists; reflexivity | exists []; rewrite app_nil_r; reflexivity]. Qed.

(* reduce the projections of the machine's setters *)
Ltac gpnc_red :=
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

Lemma gp_name_ok : gp_name_stmt.
Proof.
  intros gh xfl O z hd h0 m OK ST L0.
  destruct OK as ((rest & EO) & BO & RH & XF & LO).
  destruct ST as (M & FL & CK & HH).
  unfold gp_fl, gp_F in FL.
  pose proof M as [Mi Mn Mh Mb Ml Mow Mo Ma Mr Mt Mmd Mla Mtot Mw Mws Mwb Mhd].
  cbn [gp_p] in Mn.
  destruct (gpnc_bytes (gp_H gh xfl)) as [T ET].
  change (RF.fhdr_of gh xfl) with (gp_H gh xfl) in EO. rewrite ET, gz_bytes0_split in EO.
  unfold c_NAME2. cbv zeta.
  rewrite FL. destruct (gpnc_flg (gp_H gh xfl)) as (FN & _ & _). rewrite FN.
  pose proof (gpnc_name gh xfl RH) as NM.
  destruct (gz_name (gp_H gh xfl)) as [n|] eqn:EN.
  - (* FNAME *)
    cbn [negb]. destruct NM as [NF NG].
    assert (EG: gN (gp_H gh xfl) = n ++ [0]) by (unfold gN; rewrite EN; reflexivity).
    destruct (gpnc_mid (gA (gp_H gh xfl) ++ gX (gp_H gh xfl)) (gN (gp_H gh xfl))
                (gC (gp_H gh xfl) ++ T ++ rest) O) as (ML & MS & MZ).
    { rewrite EO. rewrite <- !app_assoc. reflexivity. }
    rewrite EG in ML, MS, MZ.
    assert (LF: Zlength (n ++ [0]) = Zlength n + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    pose proof (Zlength_nonneg n). pose proof (Zlength_nonneg (gA (gp_H gh xfl) ++ gX (gp_H gh xfl))).
    replace (m_have m =? 0) with false
      by (unfold m_have; rewrite Mi, Mn; symmetry; apply Z.eqb_neq; lia).
    rewrite L0.
    assert (HB: hd = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0 /\
                  m_h m = gh_at xfl h0 5 g x nm cm /\ nm = n ++ [0]).
    { intros E. destruct (HH E) as (g & x & nm & cm & G & HB & D & Hm). exists g, x, nm, cm.
      split; [exact G|]. split; [exact HB|]. split; [exact D|]. split; [exact Hm|].
      destruct HB as (_ & HN & _). rewrite (NG g G) in HN. injection HN as <-. reflexivity. }
    assert (WR: i_head (m_s m) && h_np (m_h m) = hd).
    { rewrite Mhd. destruct hd; [|reflexivity].
      destruct (HB eq_refl) as (g & x & nm & cm & _ & HB' & _ & Hm & _). rewrite Hm.
      destruct HB' as (_ & _ & _ & _ & _ & _ & NP & _). unfold gh_at. cbn. exact NP. }
    rewrite (gpnc_zstr n _ _ _ _ _ NF).
    2: { unfold m_have. rewrite Mi, Mn. lia. }
    2: { intros i I. rewrite Mi, Mn. apply MZ. exact I. }
    2: { rewrite WR. intros E. destruct (HB E) as (g & x & nm & cm & _ & HB' & _ & Hm & Enm).
         subst nm. rewrite Hm. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & NX & NL & _).
         unfold gh_at. cbn. split; assumption. }
    rewrite WR. cbv beta iota. rewrite Z.eqb_refl. cbn [negb].
    rewrite (gpnc_crc_if (gp_H gh xfl) m _ FL Mw).
    assert (P5: gp_p gh xfl 5 = Zlength (gA (gp_H gh xfl) ++ gX (gp_H gh xfl))) by reflexivity.
    assert (P6: gp_p gh xfl 6 = gp_p gh xfl 5 + Zlength (n ++ [0])).
    { rewrite P5. cbn [gp_p]. rewrite <- EG, <- Zlength_app, app_assoc. reflexivity. }
    assert (IB: inbytes m (Zlength (n ++ [0])) = sublist (gp_p gh xfl 5) (gp_p gh xfl 6) O).
    { unfold inbytes. rewrite Mi, Mn, P6, P5. reflexivity. }
    rewrite IB.
    eexists; split; [reflexivity|].
    destruct (gz_hcrc (gp_H gh xfl)) eqn:HC; gpnc_red.
    + split; [|reflexivity]. split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; lia.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck. gpnc_red. intros _. rewrite (CK HC). rewrite P6. apply gpnc_crc; [exact BO | lia | lia].
      * unfold gp_hh. gpnc_red. intros E. destruct (HB E) as (g & x & nm & cm & G & HB' & D & Hm & Enm).
        exists g, x, nm, cm. split; [exact G|]. split; [exact HB'|]. split; [exact D|].
        subst nm. rewrite Hm, E. reflexivity.
    + split; [|reflexivity]. split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; lia.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck. gpnc_red. rewrite HC. discriminate.
      * unfold gp_hh. gpnc_red. intros E. destruct (HB E) as (g & x & nm & cm & G & HB' & D & Hm & Enm).
        exists g, x, nm, cm. split; [exact G|]. split; [exact HB'|]. split; [exact D|].
        subst nm. rewrite Hm, E. reflexivity.
  - (* no FNAME: with a gz_header impossible *)
    cbn [negb].
    assert (EG: gN (gp_H gh xfl) = []) by (unfold gN; rewrite EN; reflexivity).
    assert (P6: gp_p gh xfl 6 = gp_p gh xfl 5) by (cbn [gp_p]; rewrite EG, app_nil_r; reflexivity).
    rewrite Mhd. destruct hd.
    + exfalso. destruct (HH eq_refl) as (g & x & nm & cm & G & HB & _).
      destruct HB as (_ & HN & _). rewrite (NM g G) in HN. discriminate.
    + eexists; split; [reflexivity|].
      split; [|reflexivity]. split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; rewrite ?P6; try assumption; reflexivity.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck in *. gpnc_red. rewrite P6. exact CK.
      * unfold gp_hh. intros E. discriminate.
Qed.

Lemma gp_comment_ok : gp_comment_stmt.
Proof.
  intros gh xfl O z hd h0 m OK ST L0.
  destruct OK as ((rest & EO) & BO & RH & XF & LO).
  destruct ST as (M & FL & CK & HH).
  unfold gp_fl, gp_F in FL.
  pose proof M as [Mi Mn Mh Mb Ml Mow Mo Ma Mr Mt Mmd Mla Mtot Mw Mws Mwb Mhd].
  cbn [gp_p] in Mn.
  destruct (gpnc_bytes (gp_H gh xfl)) as [T ET].
  change (RF.fhdr_of gh xfl) with (gp_H gh xfl) in EO. rewrite ET, gz_bytes0_split in EO.
  unfold c_COMMENT2. cbv zeta.
  rewrite FL. destruct (gpnc_flg (gp_H gh xfl)) as (_ & FN & _). rewrite FN.
  pose proof (gpnc_comment gh xfl RH) as NM.
  assert (P7: gp_p gh xfl 7 = gp_p gh xfl 6 + Zlength (gC (gp_H gh xfl))).
  { cbn [gp_p]. rewrite gz_bytes0_split, <- Zlength_app, !app_assoc. reflexivity. }
  destruct (gz_comment (gp_H gh xfl)) as [n|] eqn:EN.
  - (* FCOMMENT *)
    cbn [negb]. destruct NM as [NF NG].
    assert (EG: gC (gp_H gh xfl) = n ++ [0]) by (unfold gC; rewrite EN; reflexivity).
    destruct (gpnc_mid (gA (gp_H gh xfl) ++ gX (gp_H gh xfl) ++ gN (gp_H gh xfl)) (gC (gp_H gh xfl))
                (T ++ rest) O) as (ML & MS & MZ).
    { rewrite EO. rewrite <- !app_assoc. reflexivity. }
    rewrite EG in ML, MS, MZ, P7.
    assert (LF: Zlength (n ++ [0]) = Zlength n + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    pose proof (Zlength_nonneg n).
    pose proof (Zlength_nonneg (gA (gp_H gh xfl) ++ gX (gp_H gh xfl) ++ gN (gp_H gh xfl))).
    replace (m_have m =? 0) with false
      by (unfold m_have; rewrite Mi, Mn; symmetry; apply Z.eqb_neq; lia).
    rewrite L0.
    assert (HB: hd = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0 /\
                  m_h m = gh_at xfl h0 6 g x nm cm /\ cm = n ++ [0]).
    { intros E. destruct (HH E) as (g & x & nm & cm & G & HB & D & Hm). exists g, x, nm, cm.
      split; [exact G|]. split; [exact HB|]. split; [exact D|]. split; [exact Hm|].
      destruct HB as (_ & _ & HN & _). rewrite (NG g G) in HN. injection HN as <-. reflexivity. }
    assert (WR: i_head (m_s m) && h_cp (m_h m) = hd).
    { rewrite Mhd. destruct hd; [|reflexivity].
      destruct (HB eq_refl) as (g & x & nm & cm & _ & HB' & _ & Hm & _). rewrite Hm.
      destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CP & _). unfold gh_at. cbn. exact CP. }
    rewrite (gpnc_zstr n _ _ _ _ _ NF).
    2: { unfold m_have. rewrite Mi, Mn. lia. }
    2: { intros i I. rewrite Mi, Mn. apply MZ. exact I. }
    2: { rewrite WR. intros E. destruct (HB E) as (g & x & nm & cm & _ & HB' & _ & Hm & Enm).
         subst cm. rewrite Hm. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CX & CL).
         unfold gh_at. cbn. split; assumption. }
    rewrite WR. cbv beta iota. rewrite Z.eqb_refl. cbn [negb].
    rewrite (gpnc_crc_if (gp_H gh xfl) m _ FL Mw).
    assert (P6: gp_p gh xfl 6 = Zlength (gA (gp_H gh xfl) ++ gX (gp_H gh xfl) ++ gN (gp_H gh xfl))) by reflexivity.
    assert (IB: inbytes m (Zlength (n ++ [0])) = sublist (gp_p gh xfl 6) (gp_p gh xfl 7) O).
    { unfold inbytes. rewrite Mi, Mn, P7, P6. reflexivity. }
    rewrite IB.
    eexists; split; [reflexivity|].
    destruct (gz_hcrc (gp_H gh xfl)) eqn:HC; gpnc_red.
    + split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; lia.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck. gpnc_red. intros _. rewrite (CK HC). rewrite P7. apply gpnc_crc; [exact BO | lia | lia].
      * unfold gp_hh. gpnc_red. intros E. destruct (HB E) as (g & x & nm & cm & G & HB' & D & Hm & Enm).
        exists g, x, nm, cm. split; [exact G|]. split; [exact HB'|]. split; [exact D|].
        subst cm. rewrite Hm, E. reflexivity.
    + split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; lia.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck. gpnc_red. rewrite HC. discriminate.
      * unfold gp_hh. gpnc_red. intros E. destruct (HB E) as (g & x & nm & cm & G & HB' & D & Hm & Enm).
        exists g, x, nm, cm. split; [exact G|]. split; [exact HB'|]. split; [exact D|].
        subst cm. rewrite Hm, E. reflexivity.
  - (* no FCOMMENT: with a gz_header impossible *)
    cbn [negb].
    assert (EG: gC (gp_H gh xfl) = []) by (unfold gC; rewrite EN; reflexivity).
    rewrite EG, Zlength_nil, Z.add_0_r in P7.
    rewrite Mhd. destruct hd.
    + exfalso. destruct (HH eq_refl) as (g & x & nm & cm & G & HB & _).
      destruct HB as (_ & _ & HN & _). rewrite (NM g G) in HN. discriminate.
    + eexists; split; [reflexivity|].
      split; [|split; [|split]].
      * constructor; gpnc_red; try assumption; rewrite ?P7; try assumption; reflexivity.
      * unfold gp_fl, gp_F. gpnc_red. exact FL.
      * unfold gp_ck in *. gpnc_red. rewrite P7. exact CK.
      * unfold gp_hh. intros E. discriminate.
Qed.

Lemma gp_nc_ok : gp_name_stmt /\ gp_comment_stmt.
Proof. exact (conj gp_name_ok gp_comment_ok). Qed.

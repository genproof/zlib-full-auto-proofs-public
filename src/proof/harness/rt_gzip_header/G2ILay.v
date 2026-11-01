(* Law rt_gzip_header on the round-2 harness, inflate side: what the deflate side's result (RTFinal.dfinal of no
   data with deflateSetHeader's header gh) gives the inflate theory: the layout of the header at the start of O
   (G2IDefs.lay2 over the ghost g2_g), the decode context after it (RTIGW.rtigw_ok of G2IDefs.g2_G, with no data),
   and the reported header in the terms of the harness's checks (G2IFacts.g2_hdr_out). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.rt_gzip_header.G2IDefs.
Require Import Zlib.proof.harness.inflate_header.IHTKitLay.
Require Zlib.proof.roundtrip.RTIGzPassCtx.
Require Zlib.proof.roundtrip.RTDDict2.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream: header, deflate data of no data (any window: there is no reference), trailer *)
Definition g2_lay_stmt : Prop := forall wbd wb gh O,
  RF.dfinal [] 2 wbd (Some gh) [] O -> g2_hdr_ok gh -> 9 <= wb <= 15 -> Zlength O <= max_u64 ->
  exists xfl bs,
    (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\
    O = F.stream_bytes (F.WGzip (g2_H gh xfl)) [] bs /\
    g2h_ok (g2_g gh xfl) /\ lay2 (g2_g gh xfl) O /\
    ih_nh (g2_g gh xfl) = Zlength (F.gz_bytes (g2_H gh xfl)) /\
    RTIGW.rtigw_ok (g2_G gh xfl wb bs O) /\ Zlib.proof.rfc1951.DecodeDefs.full (g2_G gh xfl wb bs O) = [].

(* the header inflate reported (IHFacts.ih_done_ok of the ghost, for inflateGetHeader's h0 with done 0), state->flags
   of the header: every field the harness checks *)
Definition g2_out_stmt : Prop := forall gh xfl h0 s h,
  g2_hdr_ok gh -> g2_bufs gh h0 -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  i_head s = true -> hdr_mode (i_mode s) = false -> i_flags s = 8 + 256 * g_flg (g2_g gh xfl) ->
  ih_done_ok (g2_g gh xfl) (set_h_done h0 0) h ->
  h_extra_max h = h_extra_max h0 -> h_name_max h = h_name_max h0 -> h_comm_max h = h_comm_max h0 ->
  g2_hdr_out gh h0 s h.


(* ---------------------------------------------------------------------------------------------- *)
(* The ghost of a Format header                                                                    *)

(* the ghost (IHFacts.ihg) of any Format header: g2_g gh xfl is the ghost of g2_H gh xfl *)
Definition g2_gf (H: F.gzhdr) : ihg :=
  IHG (F.gz_flg H) (F.gz_mtime H) (F.gz_xfl H) (F.gz_os H)
      (match F.gz_extra H with Some x => x | None => [] end)
      (match F.gz_name H with Some n => n | None => [] end)
      (match F.gz_comment H with Some c => c | None => [] end) 0.

Lemma g2_g_gf gh xfl : g2_g gh xfl = g2_gf (g2_H gh xfl).
Proof. reflexivity. Qed.

(* a field is present *)
Definition g2_some {A: Type} (o: option A) : bool := match o with Some _ => true | None => false end.

(* the flag bits of FLG are the header's options *)
Lemma g2_flags H : let g := g2_gf H in
  0 <= g_flg g <= 31 /\ ih_reserved g = false /\
  fl g 2 = F.gz_hcrc H /\ fl g 4 = g2_some (F.gz_extra H) /\ fl g 8 = g2_some (F.gz_name H) /\
  fl g 16 = g2_some (F.gz_comment H) /\
  Z.land (g_flg g) 1 = (if F.gz_text H then 1 else 0) /\
  Z.land (Z.shiftr (g_flg g) 1) 1 = (if F.gz_hcrc H then 1 else 0) /\
  negb (Z.land (8 + 256 * g_flg g) 1024 =? 0) = g2_some (F.gz_extra H).
Proof.
  unfold g2_gf, fl, ih_reserved, F.gz_flg; cbn [g_flg].
  destruct (F.gz_text H), (F.gz_hcrc H), (F.gz_extra H), (F.gz_name H), (F.gz_comment H);
    cbn; repeat split; first [reflexivity | lia].
Qed.

(* the low 16 bits of c, as two little-endian bytes *)
Lemma g2_le2 c : F.le_bytes c 2 = [Z.land c 65535 mod 256; Z.land c 65535 / 256].
Proof.
  unfold F.le_bytes. change (Z.to_nat 2) with 2%nat. cbn [seq map].
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with (256 * 256).
  change (2 ^ 8) with 256. rewrite Z.rem_mul_r by lia.
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)). pose proof (Z.mod_pos_bound (c / 256) 256 ltac:(lia)).
  f_equal; [|f_equal].
  - apply Z.mod_unique with ((c / 256) mod 256); lia.
  - apply Z.div_unique with (c mod 256); lia.
Qed.

(* the header bytes without the header CRC are ih_hdr of the ghost *)
Lemma g2_hdr_bytes0 H : (forall x, F.gz_extra H = Some x -> Zlength x <= 65535) ->
  ih_hdr (g2_gf H) = F.gz_bytes0 H.
Proof.
  intros XL. destruct (g2_flags H) as (_ & _ & _ & F4 & F8 & F16 & _).
  unfold ih_hdr. rewrite F4, F8, F16. unfold F.gz_bytes0, g2_gf; cbn [g_flg g_mtime g_xfl g_os g_xf g_nf g_cf].
  assert (LE4: F.le_bytes (F.gz_mtime H) 4 =
    [F.gz_mtime H mod 256; (F.gz_mtime H / 256) mod 256; (F.gz_mtime H / 65536) mod 256;
     (F.gz_mtime H / 16777216) mod 256]).
  { unfold F.le_bytes. change (Z.to_nat 4) with 4%nat. cbn [seq map].
    change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16.
    change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_0_r, !Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (XB: forall x, F.gz_extra H = Some x -> F.le_bytes (Zlength x) 2 = [Zlength x mod 256; Zlength x / 256]).
  { intros x Ex. pose proof (XL x Ex) as L. pose proof (Zlength_nonneg x).
    rewrite g2_le2. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    rewrite (Z.mod_small (Zlength x) 65536) by lia. reflexivity. }
  rewrite LE4. destruct (F.gz_extra H) as [x|] eqn:Ex; cbn [g2_some]; [rewrite (XB x eq_refl)|];
    destruct (F.gz_name H), (F.gz_comment H); reflexivity.
Qed.

(* with the header CRC: the header CRC bytes are those of the ghost (ih_stored with delta 0) *)
Lemma g2_hdr_bytes H : (forall x, F.gz_extra H = Some x -> Zlength x <= 65535) ->
  F.gz_bytes H = ih_hdr (g2_gf H) ++ ihH (g2_gf H).
Proof.
  intros XL. destruct (g2_flags H) as (_ & _ & F2 & _).
  unfold F.gz_bytes, ihH. rewrite F2, <- (g2_hdr_bytes0 H XL).
  destruct (F.gz_hcrc H); [|rewrite app_nil_r; reflexivity].
  f_equal. unfold ih_stored. cbn [g_delta]. rewrite Z.lxor_0_r, <- Z.land_assoc, Z.land_diag.
  apply g2_le2.
Qed.

(* the ranges of the ghost of a well-formed header with names and comments of up to 2^32 - 2 bytes *)
Lemma g2_gf_ok H : F.gz_ok H ->
  (forall n, F.gz_name H = Some n -> Zlength n <= 4294967294) ->
  (forall c, F.gz_comment H = Some c -> Zlength c <= 4294967294) -> g2h_ok (g2_gf H).
Proof.
  intros (GT & GX & GO & GE & GN & GC) LN LC. unfold F.byte_ok in *.
  destruct (g2_flags H) as (G1 & G2 & _).
  unfold g2h_ok. split; [lia|]. split; [exact G2|].
  unfold g2_gf in *; cbn [g_flg g_mtime g_xfl g_os g_xf g_nf g_cf g_delta] in *.
  split; [exact GT|]. split; [lia|]. split; [lia|].
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - destruct (F.gz_extra H); [exact (proj1 GE) | rewrite Zlength_nil; lia].
  - unfold is_bytes. change Byte.max_unsigned with 255. destruct (F.gz_extra H) as [x|]; [|constructor].
    eapply Forall_impl; [|exact (proj2 GE)]. cbv beta. intros; lia.
  - destruct (F.gz_name H) as [n|]; [exact (LN n eq_refl) | rewrite Zlength_nil; lia].
  - destruct (F.gz_name H) as [n|]; [|constructor]. eapply Forall_impl; [|exact GN]. cbv beta. intros; lia.
  - destruct (F.gz_comment H) as [c|]; [exact (LC c eq_refl) | rewrite Zlength_nil; lia].
  - destruct (F.gz_comment H) as [c|]; [|constructor]. eapply Forall_impl; [|exact GC]. cbv beta. intros; lia.
  - reflexivity.
Qed.

(* deflateSetHeader's header gives a well-formed Format header (RTIGzPassCtx.gpc_gz_ok with the round-2 bounds) *)
Lemma g2_H_ok gh xfl : g2_hdr_ok gh -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  F.gz_ok (g2_H gh xfl) /\
  (forall n, F.gz_name (g2_H gh xfl) = Some n -> Zlength n <= 4294967294) /\
  (forall c, F.gz_comment (g2_H gh xfl) = Some c -> Zlength c <= 4294967294) /\
  (forall x, DS.gz_extra gh = Some x -> F.gz_extra (g2_H gh xfl) = Some x).
Proof.
  intros (_ & _ & HOS & HT & HE & HXB & HN & HC) HX.
  assert (EXq: forall x, DS.gz_extra gh = Some x -> F.gz_extra (g2_H gh xfl) = Some x).
  { intros x Ex. unfold g2_H, RF.fhdr_of; cbn [F.gz_extra]. rewrite Ex. cbn [Datatypes.option_map].
    destruct (HXB x Ex) as (L & _). rewrite <- L, sublist_same by reflexivity. reflexivity. }
  split; [|split; [|split; [|exact EXq]]].
  - unfold F.gz_ok, g2_H, RF.fhdr_of;
      cbn [F.gz_mtime F.gz_xfl F.gz_os F.gz_extra F.gz_name F.gz_comment Datatypes.option_map].
    unfold F.byte_ok.
    split; [change (2 ^ 32) with 4294967296; lia|]. split; [lia|]. split.
    { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
      pose proof (Z.mod_pos_bound (DS.gz_os gh) 256 ltac:(lia)). lia. }
    split; [|split].
    + destruct (DS.gz_extra gh) as [x|] eqn:Ex; cbn [Datatypes.option_map]; [|exact I].
      destruct (HXB x eq_refl) as (L & B). rewrite <- L, sublist_same by reflexivity. split; [lia|]. exact B.
    + destruct (DS.gz_name gh) as [l|] eqn:En; cbn [Datatypes.option_map]; [|exact I].
      destruct (HN l eq_refl) as (l0 & -> & _ & B). rewrite removelast_last. exact B.
    + destruct (DS.gz_comment gh) as [l|] eqn:En; cbn [Datatypes.option_map]; [|exact I].
      destruct (HC l eq_refl) as (l0 & -> & _ & B). rewrite removelast_last. exact B.
  - intros n. unfold g2_H, RF.fhdr_of; cbn [F.gz_name]. destruct (DS.gz_name gh) as [l|] eqn:En; cbn [Datatypes.option_map];
      [|discriminate]. intros E; injection E as <-.
    destruct (HN l eq_refl) as (l0 & -> & L & _). rewrite removelast_last. exact L.
  - intros n. unfold g2_H, RF.fhdr_of; cbn [F.gz_comment]. destruct (DS.gz_comment gh) as [l|] eqn:En; cbn [Datatypes.option_map];
      [|discriminate]. intros E; injection E as <-.
    destruct (HC l eq_refl) as (l0 & -> & L & _). rewrite removelast_last. exact L.
Qed.

(* the layout of any input that starts with the header bytes of a well-formed header (IHTKitLay.ih_lay_proof, over
   src = header ++ rest in place of law inflate_header's fixed member) *)
Lemma g2_lay H rest : F.gz_ok H ->
  (forall n, F.gz_name H = Some n -> Zlength n <= 4294967294) ->
  (forall c, F.gz_comment H = Some c -> Zlength c <= 4294967294) ->
  is_bytes (F.gz_bytes H ++ rest) -> lay2 (g2_gf H) (F.gz_bytes H ++ rest).
Proof.
  intros GZ LN LC BY. pose proof (g2_gf_ok H GZ LN LC) as G.
  assert (XL: forall x, F.gz_extra H = Some x -> Zlength x <= 65535).
  { destruct GZ as (_ & _ & _ & GE & _). intros x Ex. rewrite Ex in GE. exact (proj1 GE). }
  set (g := g2_gf H) in *.
  assert (SE: F.gz_bytes H ++ rest = ihA g ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest).
  { unfold g. rewrite (g2_hdr_bytes H XL), ihl2_hdr_eq, <- !app_assoc. reflexivity. }
  rewrite SE in *. clear SE. set (src := ihA g ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest) in *.
  pose proof (ihl2_lens g) as (LA & LX & LN' & LC' & LH & _).
  assert (NE: ih_ne g = 10 + Zlength (ihX g)) by lia.
  assert (Xs: ih_xs g = if fl g 4 then 12 else 10) by reflexivity.
  pose proof (Zlength_nonneg (ihX g)). pose proof (Zlength_nonneg (ihN g)).
  pose proof (Zlength_nonneg (ihC g)). pose proof (Zlength_nonneg (ihH g)). pose proof (Zlength_nonneg rest).
  destruct G as (G1 & _ & G2 & G3 & G4 & G5 & G6 & _).
  assert (XL': 0 <= Zlength (g_xf g) < 65536) by (pose proof (Zlength_nonneg (g_xf g)); lia).
  destruct (ihl2_split2 _ XL') as (XS1 & XS2 & XS3).
  constructor.
  - (* bytes *)
    exact BY.
  - (* length *)
    unfold src. rewrite !Zlength_app. lia.
  - (* order *)
    rewrite Xs. unfold ihX in LX. destruct (fl g 4); rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in LX;
      pose proof (Zlength_nonneg (g_xf g)); lia.
  - (* the header *)
    rewrite ihl2_hdr_eq. apply (ihl2_mid _ [] _ (ihH g ++ rest)); [unfold src; rewrite !app_assoc; reflexivity | reflexivity |].
    rewrite Zlength_nil, !Zlength_app. lia.
  - (* 1f 8b *)
    rewrite (ihl2_mid src [] [31; 139] (sublist 2 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest) 0 2);
      [split; reflexivity | reflexivity | reflexivity | reflexivity].
  - (* CM FLG *)
    rewrite (ihl2_mid src [31; 139] [8; g_flg g] (sublist 4 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest) 2 4);
      [ | reflexivity | reflexivity | reflexivity].
    rewrite ihl2_le2. split; [reflexivity | apply ihl2_hb2; lia].
  - (* MTIME *)
    rewrite (ihl2_mid src (sublist 0 4 (ihA g)) (sublist 4 8 (ihA g)) (sublist 8 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest) 4 8);
      [ | reflexivity | reflexivity | reflexivity].
    exact (ihl2_mt _ G2).
  - (* XFL OS *)
    rewrite (ihl2_mid src (sublist 0 8 (ihA g)) [g_xfl g; g_os g] (ihX g ++ ihN g ++ ihC g ++ ihH g ++ rest) 8 10);
      [ | reflexivity | reflexivity | reflexivity].
    rewrite ihl2_le2. split; [reflexivity | apply ihl2_hb2; lia].
  - (* XLEN *)
    intros F4. assert (EXq: ihX g = [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g)
      by (unfold ihX; rewrite F4; reflexivity).
    rewrite (ihl2_mid src (ihA g) [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]
               (g_xf g ++ ihN g ++ ihC g ++ ihH g ++ rest) 10 12);
      [ | unfold src; rewrite EXq, <- !app_assoc; reflexivity | rewrite LA; reflexivity | rewrite LA; reflexivity].
    rewrite ihl2_le2. split; [exact XS1|].
    rewrite <- XS1 at 1. apply ihl2_hb2; lia.
  - (* the extra field *)
    intros F4. assert (EXq: ihX g = [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g)
      by (unfold ihX; rewrite F4; reflexivity).
    apply (ihl2_mid _ (ihA g ++ [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]) _ (ihN g ++ ihC g ++ ihH g ++ rest));
      [unfold src; rewrite EXq, <- !app_assoc; reflexivity | rewrite Zlength_app, LA; reflexivity |].
    rewrite Zlength_app, LA. unfold ih_ne. rewrite F4.
    change (Zlength [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]) with 2. lia.
  - (* the name *)
    intros F8. assert (EN: ihN g = g_nf g ++ [0]) by (unfold ihN; rewrite F8; reflexivity).
    apply (ihl2_mid _ (ihA g ++ ihX g) _ (ihC g ++ ihH g ++ rest));
      [unfold src; rewrite EN, <- !app_assoc; reflexivity | rewrite Zlength_app; lia | rewrite Zlength_app, <- EN; lia].
  - (* the comment *)
    intros F16. assert (EC: ihC g = g_cf g ++ [0]) by (unfold ihC; rewrite F16; reflexivity).
    apply (ihl2_mid _ (ihA g ++ ihX g ++ ihN g) _ (ihH g ++ rest));
      [unfold src; rewrite EC, <- !app_assoc; reflexivity | rewrite !Zlength_app; lia | rewrite <- EC, !Zlength_app; lia].
  - (* the header CRC *)
    intros F2. assert (EH: ihH g = [ih_stored g mod 256; ih_stored g / 256]) by (unfold ihH; rewrite F2; reflexivity).
    rewrite (ihl2_mid src (ihA g ++ ihX g ++ ihN g ++ ihC g) [ih_stored g mod 256; ih_stored g / 256] rest
               (ih_nc g) (ih_nc g + 2));
      [ | unfold src; rewrite EH, <- !app_assoc; reflexivity | rewrite !Zlength_app; lia | rewrite !Zlength_app; cbn; lia].
    rewrite ihl2_le2. destruct (ihl2_split2 _ (ihl2_stored g)) as (S1 & _ & _). rewrite S1.
    rewrite (ihl2_mid src [] (ih_hdr g) (ihH g ++ rest) 0 (ih_nc g));
      [ | unfold src; rewrite ihl2_hdr_eq, <- !app_assoc; reflexivity | reflexivity | rewrite ihl2_hdr_eq, !Zlength_app; cbn; lia].
    unfold ih_stored. rewrite ihl2_hcrc. unfold ih_badcrc. rewrite F2. cbn [andb]. rewrite negb_involutive. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Blocks of no data are accepted under any window: they hold no back reference                   *)

Lemma g2_blocks_nil wm wm' : forall bs, F.blocks_ok wm [] bs -> F.expand [] bs = [] -> F.blocks_ok wm' [] bs.
Proof.
  induction bs as [|b r IH]; intros Hb E; [exact I|].
  destruct Hb as [Hb Hr]. unfold F.expand in E. cbn [fold_left] in E.
  assert (Eb : F.block_data [] b = []).
  { pose proof (Zlib.proof.roundtrip.RTDDict2.expand_len r (F.block_data [] b)) as L.
    unfold F.expand in L. rewrite E, Zlength_nil in L. apply Zlength_nil_inv.
    pose proof (Zlength_nonneg (F.block_data [] b)). lia. }
  rewrite Eb in Hr, E. split; [|rewrite Eb; exact (IH Hr E)].
  destruct b as [bs0|syms|nlen ndist cl toks syms]; cbn [F.block_ok F.block_data] in *.
  - exact Hb.
  - rewrite (Zlib.proof.roundtrip.RTDDict2.syms_nil _ _ _ _ Hb Eb). exact I.
  - destruct Hb as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    rewrite (Zlib.proof.roundtrip.RTDDict2.syms_nil _ _ _ _ A10 Eb).
    repeat (split; [assumption|]). exact I.
Qed.

Lemma g2_wf_nil wm wm' bs : F.wf wm [] bs -> F.data [] bs = [] -> F.wf wm' [] bs /\ F.expand [] bs = [].
Proof.
  intros (N & B & W) D.
  assert (E: F.expand [] bs = []).
  { unfold F.data in D. rewrite Zlength_nil, sublist_same in D by reflexivity. exact D. }
  split; [|exact E]. split; [exact N|]. split; [exact B|]. exact (g2_blocks_nil wm wm' bs W E).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The layout of deflate's stream                                                                  *)

Lemma g2_lay_proof : g2_lay_stmt.
Proof.
  intros wbd wb gh O DF HOK W LO.
  destruct DF as (Wd & bs & Wf & Dd & _ & xfl & X & EO).
  exists xfl, bs.
  change (RF.fhdr_of (Some gh) xfl) with (g2_H gh xfl) in EO.
  destruct (g2_H_ok gh xfl HOK X) as (GZ & LN & LC & _).
  destruct (g2_wf_nil (2 ^ wbd) (2 ^ wb) bs Wf Dd) as (Wf' & E).
  assert (XL: forall x, F.gz_extra (g2_H gh xfl) = Some x -> Zlength x <= 65535).
  { destruct GZ as (_ & _ & _ & GE & _). intros x Ex. rewrite Ex in GE. exact (proj1 GE). }
  set (H := g2_H gh xfl) in *.
  set (rest := F.deflate_bytes bs ++ F.le_bytes (Zlib.proof.crc32.Model.ref_crc32 0 (F.data [] bs)) 4 ++
               F.le_bytes (Zlength (F.data [] bs) mod 2 ^ 32) 4).
  assert (OR: O = F.gz_bytes H ++ rest) by (rewrite EO; reflexivity).
  assert (BO: Forall (fun b => 0 <= b < 256) O).
  { rewrite OR. unfold rest. rewrite !Forall_app. repeat split.
    - apply Zlib.proof.roundtrip.RTIGzPassCtx.gpc_gz_bytes, GZ.
    - apply Zlib.proof.roundtrip.RTIGzPassCtx.gpc_pack_ok.
    - apply Zlib.proof.roundtrip.RTIGzPassCtx.gpc_le_ok.
    - apply Zlib.proof.roundtrip.RTIGzPassCtx.gpc_le_ok. }
  assert (BY: is_bytes O).
  { unfold is_bytes. change Byte.max_unsigned with 255. eapply Forall_impl; [|exact BO]. cbv beta. intros; lia. }
  rewrite g2_g_gf. fold H.
  split; [exact X|]. split; [exact EO|]. split; [exact (g2_gf_ok H GZ LN LC)|].
  split; [rewrite OR; apply g2_lay; [exact GZ | exact LN | exact LC | rewrite <- OR; exact BY]|].
  split.
  { rewrite (g2_hdr_bytes H XL), Zlength_app, ihl2_hdr_eq, !Zlength_app.
    pose proof (ihl2_lens (g2_gf H)) as (LA & LX & LN' & LC' & LH & _). lia. }
  assert (SL: Zlib.proof.rfc1951.DecodeDefs.slen (g2_G gh xfl wb bs O) = Zlength O).
  { unfold Zlib.proof.rfc1951.DecodeDefs.slen, g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_w Zlib.proof.rfc1951.DecodeDefs.dc_hist Zlib.proof.rfc1951.DecodeDefs.dc_bs].
    fold H. rewrite <- EO. reflexivity. }
  split.
  - unfold RTIGW.rtigw_ok. rewrite SL. unfold g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_w Zlib.proof.rfc1951.DecodeDefs.dc_wb Zlib.proof.rfc1951.DecodeDefs.dc_hist
         Zlib.proof.rfc1951.DecodeDefs.dc_bs Zlib.proof.rfc1951.DecodeDefs.dc_iw Zlib.proof.rfc1951.DecodeDefs.dc_src].
    fold H. rewrite <- EO.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold F.stream_ok, F.wrapper_ok. split; [lia|]. split; [split; [exact GZ | reflexivity]|].
      split; [exact I | exact Wf'].
    + unfold Zlib.proof.rfc1951.DecodeDefs.accepts. cbn. left. reflexivity.
    + intros ? ? ? Ew. discriminate Ew.
    + lia.
    + unfold max_u64 in LO. lia.
    + exact BY.
    + apply sublist_same; reflexivity.
  - unfold Zlib.proof.rfc1951.DecodeDefs.full, g2_G.
    cbn [Zlib.proof.rfc1951.DecodeDefs.dc_hist Zlib.proof.rfc1951.DecodeDefs.dc_bs]. exact E.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The header reported                                                                             *)

(* the zero-terminated name / comment: its length is the bytes before the zero, plus one *)
Lemma g2_fz (l0: list Z) : Forall (fun b => 0 < b < 256) l0 -> fz (l0 ++ [0]) = Zlength l0.
Proof.
  induction l0 as [|b t IH]; intros G; [reflexivity|].
  inversion G as [|b' t' Hb Ht]; subst. cbn [app fz].
  rewrite (proj2 (Z.eqb_neq b 0)) by lia. rewrite (IH Ht), Zlength_cons. lia.
Qed.

(* a buffer of exactly the field's size holds the field *)
Lemma g2_fbuf (b0 f: list Z) : Zlength b0 = Zlength f -> fbuf b0 f = f.
Proof.
  intros L. unfold fbuf. rewrite L, Z.min_id, sublist_same by reflexivity.
  rewrite sublist_nil, app_nil_r. reflexivity.
Qed.

Lemma g2_out_proof : g2_out_stmt.
Proof.
  intros gh xfl h0 s h HOK HB HX Hhead Hmode Hflags HD Mx Mn Mc.
  destruct (g2_H_ok gh xfl HOK HX) as (_ & _ & _ & EXq).
  rewrite g2_g_gf in Hflags, HD.
  destruct (g2_flags (g2_H gh xfl)) as (_ & _ & _ & F4 & F8 & F16 & FT & FH & FX).
  destruct HD as (D1 & D2 & D3 & _ & D5 & D6 & D7 & D8 & D9).
  destruct HB as (X1 & X2 & X3 & N1 & _ & N3 & N4 & C1 & _ & C3 & C4).
  destruct HOK as (_ & _ & _ & _ & _ & HXB & HN & HC).
  unfold g2_hdr_out.
  split; [exact Hhead|]. split; [exact Hmode|]. split; [exact D1|].
  split; [rewrite D2, FT; unfold g2_H, RF.fhdr_of; cbn [F.gz_text]; destruct (DS.gz_text gh =? 0); reflexivity|].
  split; [rewrite D6, FH; unfold g2_H, RF.fhdr_of; cbn [F.gz_hcrc]; destruct (DS.gz_hcrc gh =? 0); reflexivity|].
  split; [rewrite D5; reflexivity|]. split; [rewrite D3; reflexivity|].
  split; [exact Mx|]. split; [exact Mn|]. split; [exact Mc|].
  split; [|split].
  - (* the extra field *)
    destruct (DS.gz_extra gh) as [x|] eqn:Ex.
    + pose proof (EXq x eq_refl) as E2. destruct (HXB x eq_refl) as (L & _).
      rewrite E2 in F4, FX. cbn [g2_some] in F4, FX. rewrite F4 in D7.
      unfold g2_gf in D7; cbn [g_xf] in D7. rewrite E2 in D7. destruct D7 as (Y1 & Y2 & Y3).
      cbn [set_h_done h_xp h_xbuf] in Y2, Y3.
      assert (XP: h_xp h = true) by (rewrite Y2; exact X1).
      assert (XB: h_xbuf h = x) by (rewrite (Y3 X1); apply g2_fbuf; lia).
      split; [exact XP|]. split; [unfold fextra; rewrite Hflags; exact FX|]. split; [exact Y1|].
      split; [unfold cxa; rewrite XP, Y1, Mx; lia|].
      rewrite XB. apply sublist_same; reflexivity.
    + assert (E2: F.gz_extra (g2_H gh xfl) = None)
        by (unfold g2_H, RF.fhdr_of; cbn [F.gz_extra]; rewrite Ex; reflexivity).
      rewrite E2 in F4. cbn [g2_some] in F4. rewrite F4 in D7. exact D7.
  - (* the name *)
    destruct (DS.gz_name gh) as [l|] eqn:En.
    + destruct (HN l eq_refl) as (l0 & El & _ & B).
      assert (E2: F.gz_name (g2_H gh xfl) = Some l0)
        by (unfold g2_H, RF.fhdr_of; cbn [F.gz_name]; rewrite En, El; cbn [Datatypes.option_map];
            rewrite removelast_last; reflexivity).
      rewrite E2 in F8. cbn [g2_some] in F8. rewrite F8 in D8.
      unfold g2_gf in D8; cbn [g_nf] in D8. rewrite E2 in D8. destruct D8 as (Y2 & Y3).
      cbn [set_h_done h_np h_nbuf] in Y2, Y3.
      assert (NP: h_np h = true) by (rewrite Y2; exact N1).
      pose proof (N4 l eq_refl) as NM.
      assert (NB: h_nbuf h = l) by (rewrite (Y3 N1), El; apply g2_fbuf; rewrite <- El; lia).
      split; [exact NP|]. split.
      * unfold cna. rewrite NP, NB, Mn, NM, El, g2_fz by exact B. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * rewrite NB. apply sublist_same; reflexivity.
    + assert (E2: F.gz_name (g2_H gh xfl) = None)
        by (unfold g2_H, RF.fhdr_of; cbn [F.gz_name]; rewrite En; reflexivity).
      rewrite E2 in F8. cbn [g2_some] in F8. rewrite F8 in D8. exact D8.
  - (* the comment *)
    destruct (DS.gz_comment gh) as [l|] eqn:En.
    + destruct (HC l eq_refl) as (l0 & El & _ & B).
      assert (E2: F.gz_comment (g2_H gh xfl) = Some l0)
        by (unfold g2_H, RF.fhdr_of; cbn [F.gz_comment]; rewrite En, El; cbn [Datatypes.option_map];
            rewrite removelast_last; reflexivity).
      rewrite E2 in F16. cbn [g2_some] in F16. rewrite F16 in D9.
      unfold g2_gf in D9; cbn [g_cf] in D9. rewrite E2 in D9. destruct D9 as (Y2 & Y3).
      cbn [set_h_done h_cp h_cbuf] in Y2, Y3.
      assert (CP: h_cp h = true) by (rewrite Y2; exact C1).
      pose proof (C4 l eq_refl) as CM.
      assert (CB: h_cbuf h = l) by (rewrite (Y3 C1), El; apply g2_fbuf; rewrite <- El; lia).
      split; [exact CP|]. split.
      * unfold cca. rewrite CP, CB, Mc, CM, El, g2_fz by exact B. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      * rewrite CB. apply sublist_same; reflexivity.
    + assert (E2: F.gz_comment (g2_H gh xfl) = None)
        by (unfold g2_H, RF.fhdr_of; cbn [F.gz_comment]; rewrite En; reflexivity).
      rewrite E2 in F16. cbn [g2_some] in F16. rewrite F16 in D9. exact D9.
Qed.

Theorem g2_lay_out : g2_lay_stmt /\ g2_out_stmt.
Proof. exact (conj g2_lay_proof g2_out_proof). Qed.

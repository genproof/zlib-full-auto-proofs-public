(* Law rt_session, sessions with a dictionary and the zlib wrapper: the decode context of the input object.

   The harness's input object is src = O ++ any bytes, O = [CMF; FLG] ++ DICTID ++ T the zlib stream deflate
   wrote with the dictionary (RTFinal.dfinal dict 1).  Its decode context [szd_ctx] is dictionary_w's [dw_ctx]
   (Format's zlib stream with the history dict: FLEVEL 0 in its header, which may differ from O's FLG; inflate
   reads the header only before the dictionary) followed by the bytes of src after O.  From byte 6 on, the
   context's input and src agree, and the calls after inflateSetDictionary start at byte 6.  [szd_set]:
   inflateSetDictionary at DICT gives the decode invariant at position 6 on that context (DWISet.dwi_set on the
   context without the trailing bytes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode7.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.clip_streams.IFacts.
Require Import Zlib.proof.roundtrip.RTIZDictDefs.
Require Import Zlib.proof.roundtrip.RTIZDictKit.
Require Import Zlib.proof.roundtrip.RTIZDictSet.
Require Import Zlib.proof.harness.dictionary_w.DWIFirst.
Require Import Zlib.proof.harness.dictionary_w.DWISet.
Require Import Zlib.proof.harness.dictionary_w.DWIKit.
Import ListNotations.
Local Open Scope Z_scope.

(* the stream's decode context (inflateInit2's windowBits wb) followed by the bytes [tail] *)
Definition szd_ctx (wb: Z) (dict: list Z) (bs: list block) (tail: list Z) : dctx :=
  DCtx (zd_w dict wb) wb dict bs wb (stream_bytes (zd_w dict wb) dict bs ++ tail).

Lemma szd_src6 wb dict bs tail : 6 <= Zlength (dc_src (szd_ctx wb dict bs tail)).
Proof.
  cbn [dc_src szd_ctx]. rewrite Zlength_app. pose proof (Zlength_nonneg tail).
  pose proof (dwi_src6 wb dict bs) as H6. cbn [dc_src dw_ctx] in H6. lia.
Qed.

(* DWISet.dwi_set on the context with the trailing bytes *)
Lemma szd_set : forall wb dict bs tail s,
  9 <= wb <= 15 -> wf (2 ^ wb) dict bs -> dict <> [] ->
  dw_nd wb (Zlib.proof.adler32.Model.ref_adler32 1 dict) s ->
  setdict_check s dict = SDUpdate /\
  dinv (szd_ctx wb dict bs tail) 6 dict (d1_ty (setdict_s s dict)) 0.
Proof.
  intros wb dict bs tail s Wbr Hwf Hne
    (Md & W & Hd & La & Hv & To & Ws & Wh & Wn & Wi & Wd & Wb & Fl & Ho & Bi & Ck).
  split.
  { unfold setdict_check. rewrite Md, Z.eqb_refl. cbn [negb]. rewrite andb_false_r.
    rewrite Zlib.proof.adler32.Model.adler32_z_val_ref by exact rtzs_adler1. rewrite Ck.
    rewrite Z.eqb_refl. reflexivity. }
  destruct (rtzs_sd_fields s dict Ws Wd ltac:(lia)) as
    (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16).
  set (s' := setdict_s s dict) in *.
  rewrite Wb in S13, S14.
  set (t := d1_ty s').
  assert (T: i_mode t = Zlib.proof.inflate.Model.TYPE /\ i_check t = 1 /\ i_last t = i_last s' /\
    i_wrap t = i_wrap s' /\ i_flags t = i_flags s' /\ i_total t = i_total s' /\ i_head t = i_head s' /\
    i_wbits t = i_wbits s' /\ i_hold t = i_hold s' /\ i_bits t = i_bits s' /\ i_win t = i_win s' /\
    i_wsize t = i_wsize s' /\ i_whave t = i_whave s' /\ i_wnext t = i_wnext s' /\ i_wdata t = i_wdata s')
    by (unfold t, d1_ty; cbn; repeat split; reflexivity).
  destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  assert (WAt: forall k, 1 <= k <= i_whave t -> win_at t k = Znth (Zlength dict - k) dict).
  { intros k Hk. unfold win_at. rewrite T12, T14, T15. rewrite T13 in Hk. apply S16 in Hk.
    unfold win_at in Hk. exact Hk. }
  set (G := szd_ctx wb dict bs tail).
  assert (WO: win_ok G t dict).
  { right. split; [rewrite T8, T12, S9, S13, Wb; reflexivity | ].
    split; [rewrite T13, T12, S13, S14; reflexivity | exact WAt]. }
  assert (BP: bpos G 0 = 48) by exact (dwi_bpos0 wb dict bs).
  assert (PR: produced G dict = []) by exact (dwi_produced0 wb dict bs).
  unfold dinv. split; [ | split; [ | split; [ | split]]].
  + unfold at_mode. rewrite T9, T10, S10, S11, Ho, Bi. split.
    * unfold hold_ok. pose proof (szd_src6 wb dict bs tail).
      split; [lia | split; [unfold G; lia | rewrite sublist_nil' by lia; reflexivity]].
    * right; right; left. split; [left; exact T1 | ].
      unfold at_type. exists 0. split; [unfold nblk; pose proof (Zlength_nonneg (dc_bs G)); lia | ].
      split; [rewrite BP; reflexivity | ].
      split; [unfold outk; cbn [dc_hist G szd_ctx]; reflexivity | split; [lia | ]].
      rewrite T3, S2, La. reflexivity.
  + unfold glob_ok. cbn [dc_iw dc_w dc_wb G szd_ctx]. unfold zd_w.
    split; [exists wb; rewrite T4, S3, W; split; [apply dwi_init_wrap_wb; lia | rewrite T1; intros X; discriminate X] | ].
    split; [rewrite T7, S8; exact Hd | ].
    split; [intros _; rewrite T8, S9, Wb; lia | ].
    intros _ _ _. rewrite T5, S5. exact Fl.
  + intros _. exact WO.
  + unfold chk_ok. intros _ _ _ _ _. rewrite T1. cbn [Z.eqb orb].
    change ((Zlib.proof.inflate.Model.TYPE =? LENGTH) || (Zlib.proof.inflate.Model.TYPE =? DONE)) with false.
    cbv iota. rewrite PR, T2, T6, S7, To.
    unfold chkv. cbn [dc_w G szd_ctx]. unfold zd_w.
    split; [reflexivity | split; [reflexivity | exists []; rewrite app_nil_r; reflexivity]].
  + rewrite PR. reflexivity.
Qed.

(* what the theory keeps of the context G of the input object src = O ++ any bytes *)
Definition szd_gok (wb: Z) (dict D O src: list Z) (G: dctx) : Prop :=
  dctx_ok7 G /\ dc_hist G = dict /\ dc_iw G = wb /\ (forall h, dc_w G <> WGzip h) /\
  full G = dict ++ D /\ slen G = Zlength O /\ Zlength (dc_src G) = Zlength src /\
  sublist 6 (Zlength src) (dc_src G) = sublist 6 (Zlength src) src /\ 6 < Zlength O.

Lemma szd_sub6 (A B t: list Z) : Zlength A = Zlength B -> 6 <= Zlength A ->
  sublist 6 (Zlength A) A = sublist 6 (Zlength A) B ->
  sublist 6 (Zlength A + Zlength t) (A ++ t) = sublist 6 (Zlength A + Zlength t) (B ++ t).
Proof.
  intros E L S. pose proof (Zlength_nonneg t).
  rewrite (sublist_split 6 (Zlength A) _ (A ++ t)), (sublist_split 6 (Zlength A) _ (B ++ t))
    by (rewrite ?Zlength_app; lia).
  rewrite (sublist_app1 _ 6 (Zlength A) A t) by lia. rewrite (sublist_app1 _ 6 (Zlength A) B t) by lia.
  rewrite S. f_equal.
  rewrite (sublist_app2 (Zlength A) _ A t) by lia. rewrite (sublist_app2 (Zlength A) _ B t) by lia.
  rewrite E. reflexivity.
Qed.

(* the stream O of D with the dictionary, inside the input object src: its first 6 bytes (CMF, FLG with FDICT,
   the dictionary id) and its context *)
Lemma szd_stream wbits dict D O src :
  dfinal_dict wbits dict D O -> dict <> [] -> Zlength src <= 2 ^ 64 - 1 ->
  Zlength O <= Zlength src -> sublist 0 (Zlength O) src = O -> bytes_ok src ->
  exists flg T, RF.zflg_ok (iwb wbits) true flg /\
    O = [RF.zcmf (iwb wbits); flg] ++ be_bytes (Zlib.proof.adler32.Model.ref_adler32 1 dict) 4 ++ T /\
    exists bs, wf (2 ^ iwb wbits) dict bs /\ 9 <= iwb wbits <= 15 /\
      szd_gok (iwb wbits) dict D O src
        (szd_ctx (iwb wbits) dict bs (sublist (Zlength O) (Zlength src) src)).
Proof.
  intros DF Hne L64 LO PO BY.
  destruct (dwi_stream wbits dict D O DF Hne ltac:(lia)) as (flg & T & FL & EO & HT & bs & WF & GOK).
  exists flg, T. split; [exact FL|]. split; [exact EO|]. exists bs. split; [exact WF|].
  destruct GOK as (OK & HI & IW & IWR & FU & SL & LS & SB & L6).
  split; [exact IWR|].
  set (wb := iwb wbits) in *.
  set (tail := sublist (Zlength O) (Zlength src) src).
  set (G0 := dw_ctx wb dict bs) in *.
  assert (S0: dc_src G0 = stream_bytes (zd_w dict wb) dict bs) by reflexivity.
  assert (TL: Zlength tail = Zlength src - Zlength O) by (unfold tail; rewrite Zlength_sublist; lia).
  assert (ES: dc_src (szd_ctx wb dict bs tail) = dc_src G0 ++ tail) by reflexivity.
  assert (SLE: slen (szd_ctx wb dict bs tail) = slen G0) by reflexivity.
  assert (Esrc: src = O ++ tail).
  { unfold tail. rewrite <- (sublist_same 0 (Zlength src) src) at 1 by lia.
    rewrite (sublist_split 0 (Zlength O) (Zlength src) src) by lia. rewrite PO. reflexivity. }
  destruct OK as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8).
  split; [|split; [exact HI|split; [exact IW|split; [intros h E; discriminate E|]]]].
  - split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
    rewrite SLE, ES, Zlength_app, TL, LS. split; [lia|]. split; [lia|]. split.
    + apply Forall_app. split; [exact O7|]. unfold tail. apply Forall_sublist. exact BY.
    + rewrite sublist_app1 by lia. exact O8.
  - split; [exact FU|]. split; [rewrite SLE; exact SL|].
    rewrite ES, Zlength_app, TL, LS. split; [lia|]. split; [|exact L6].
    replace (Zlength src) with (Zlength (dc_src G0) + Zlength tail) by lia. rewrite Esrc.
    apply szd_sub6; [exact LS | lia | rewrite LS; exact SB].
Qed.

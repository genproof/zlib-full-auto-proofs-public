(* The laws rt_dictionary and api_dict_id: the deflate facts (DWFacts.dict_dfacts) from the deflate side of the
   round trips without size limits (RTK7.kfacts7: what the output is, kf7_dict for the dictionary) and the wide
   deflateBound accounting (LawFactsW2.bound_w_big_stmt: that each model run is defined, with its return codes;
   LawFactsW.bw_dict for deflateSetDictionary), as clip_streams/DTheory.v proves clip_dfacts.

   The invariants are clip_streams' ones with the dictionary: after deflateInit2 its J0c; after
   deflateSetDictionary the deflate laws' invariant with the dictionary set and the round trip's invariant with the
   dictionary; in the loop its Jc with the dictionary, where total_in counts on from the bytes of the dictionary
   deflateSetDictionary counted (at most its length, DWSetdict.setdict_counters). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.harness.clip_streams.DTheory.
Require Zlib.proof.deflate.AdlerKeep.
Require Zlib.proof.harness.dictionary_w.DWSetdict.
Import ListNotations.
Local Open Scope Z_scope.

Module LW := Zlib.proof.deflate.LawFactsW.
Module LF := Zlib.proof.deflate.LawFacts.
Module CT := Zlib.proof.harness.clip_streams.DTheory.

(* deflateSetDictionary right after deflateInit2 with a dictionary of up to 2^32 - 1 bytes: bound_facts_w's
   bw_dict, the one use of it *)
Lemma dw_bw_dict Bpre Brun : LW.bound_facts_w Bpre Brun ->
  forall level wbits mem strategy s tin tout adler d ain aout msg,
    Bpre level wbits mem strategy false s tin tout adler -> wbits <= 15 ->
    LF.bytes d -> Zlength d <= dict_max -> LF.u32r ain -> LF.u32r aout ->
    exists s' z',
      c_deflateSetDictionary s (LF.zcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
      d_gzhead s' = d_gzhead s /\
      Bpre level wbits mem strategy true s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros HB level wbits mem strategy s tin tout adler d ain aout msg Hpre Hw Hd Hl Hai Hao.
  apply (LW.bw_dict _ _ HB); auto; unfold dict_max in Hl; lia.
Qed.

Section Theory.
Variables (K : rinv) (Bpre : LF.bpre_inv) (Brun : LF.brun_inv).
Hypotheses (HK : kfacts7 K) (HB : LW.bound_facts_w Bpre Brun)
           (HBig : Zlib.proof.deflate.LawFactsW2.bw_bound_big Bpre Brun)
           (HClip : Zlib.proof.deflate.LawFactsW2.bw_clip Brun).

(* after deflateInit2: clip_streams' invariant, windowBits 8..15 *)
Definition J0d (wbits : Z) (s : dstate) (tin tout adler : Z) : Prop :=
  8 <= wbits <= 15 /\ CT.J0c K Bpre wbits s tin tout adler.

(* after deflateSetDictionary: the deflate laws' invariant with the dictionary set, the round trip's invariant
   with the dictionary; total_in the bytes of the dictionary deflateSetDictionary counted *)
Definition J1d (wbits : Z) (dict : list Z) (s : dstate) (tin tout adler : Z) : Prop :=
  (exists level mem strategy, Bpre level wbits mem strategy true s tin tout adler) /\
  K dict 1 [] [] None s tin tout adler /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = None /\ 8 <= wbits <= 15 /\
  0 <= tin <= dict_max /\ tout = 0 /\ 0 <= adler <= max_u64.

(* at the head of the loop: clip_streams' Jc with the dictionary; total_in is [t0] (the bytes of the dictionary
   counted) plus the bytes of the data consumed *)
Definition Jd (wbits : Z) (dict data : list Z) (b pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    : Prop :=
  exists fin t0,
  K dict 1 (sublist 0 pos data) O fin s tin tout adler /\
  Brun (Zlength data) b pos (CT.fin_given fin) s tin tout adler /\
  (forall R, fin = Some R -> R = sublist pos (Zlength data) data /\ Zlength data - pos <= umax) /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = None /\ 8 <= wbits <= 15 /\
  0 <= t0 <= dict_max /\ tin = t0 + pos /\ tout = Zlength O /\ 0 <= pos <= Zlength data /\
  Zlength data <= max_size /\ 0 <= Zlength O <= b /\ b <= max_u64 /\ rbytes data /\ rbytes O /\
  0 <= adler <= max_u64.

Lemma rwrap_of_zlib wbits : 8 <= wbits <= 15 -> rwrap_of wbits = 1.
Proof.
  intros H. unfold rwrap_of. destruct (wbits <? 0) eqn:E1; [lia|].
  destruct (wbits >? 15) eqn:E2; [lia|reflexivity].
Qed.

Lemma dw_init_d : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> rs32 mem -> rs32 strategy -> 8 <= wbits <= 15 ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0d wbits s (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros level wbits mem strategy a1 a2 a3 a4 a5 Hl Hm Hs Hw.
  assert (Hw32 : rs32 wbits) by (unfold rs32; lia).
  destruct (CT.cd_init_c K Bpre Brun HK HB level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw32 Hm Hs) as [Hex Hi].
  split; [exact Hex|].
  intros os z' code E Ec. destruct (Hi os z' code E Ec) as (s & Es & HJ).
  exists s. split; [exact Es|]. split; [exact Hw|exact HJ].
Qed.

Lemma dw_range0_d : forall wbits s tin tout adler, J0d wbits s tin tout adler -> dfields_ok s tin tout adler.
Proof.
  intros wbits s tin tout adler (_ & _ & _ & _ & Hgz & _ & Ti & To & Ad).
  unfold dfields_ok, max_u64 in *. subst tin tout. repeat split; auto; lia.
Qed.

Lemma dw_dict_d : forall wbits s tin tout adler dict ain aout msg,
    J0d wbits s tin tout adler -> rbytes dict -> 1 <= Zlength dict <= dict_max ->
    0 <= ain <= umax -> 0 <= aout <= umax ->
    exists s' z',
      c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some dict) = Some (s', z', Z_OK) /\
      J1d wbits dict s' (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros wbits s tin tout adler dict ain aout msg
    (Hw & (Hpre & HK0 & Hwb & Hgz & Hacc & Ti & To & Ad)) Hd Hl Hai Hao.
  destruct Hpre as (level & mem & strategy & Hpre).
  unfold dict_max, umax in *.
  destruct (dw_bw_dict Bpre Brun HB level wbits mem strategy s tin tout adler dict ain aout msg Hpre
              ltac:(lia) Hd ltac:(unfold dict_max; lia) ltac:(unfold LF.u32r; lia) ltac:(unfold LF.u32r; lia))
    as (s' & z' & E & Hgz' & Hpre').
  change (LF.zcall [] 0 ain tin aout tout adler msg) with (rzcall [] 0 ain tin aout tout adler msg) in E.
  rewrite (rwrap_of_zlib wbits Hw) in HK0.
  destruct (kf7_dict _ HK 1 s tin tout adler dict ain aout msg s' z' Z_OK HK0 Hd ltac:(lia) ltac:(lia) ltac:(lia)
              E ltac:(left; reflexivity) ltac:(split; discriminate)) as (Hwb' & _ & HK1).
  change (1 =? 2) with false in HK1. cbv iota in HK1.
  destruct (Zlib.proof.harness.dictionary_w.DWSetdict.setdict_counters s (rzcall [] 0 ain tin aout tout adler msg)
              dict s' z' Z_OK Hd ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; unfold max_u64 in Ad; lia) E)
    as (Hti & Hto & Had).
  cbn in Hti, Hto.
  exists s', z'. split; [exact E|].
  unfold J1d, dict_max, max_u64. split; [eauto|]. split; [exact HK1|]. split; [congruence|].
  split; [congruence|]. split; [exact Hw|]. split; [lia|]. split; [lia|]. exact Had.
Qed.

Lemma dw_range1_d : forall wbits dict s tin tout adler, J1d wbits dict s tin tout adler -> dfields_ok s tin tout adler.
Proof.
  intros wbits dict s tin tout adler (_ & _ & _ & Hgz & _ & Ti & To & Ad).
  unfold dfields_ok, dict_max, max_u64 in *. subst tout. repeat split; auto; lia.
Qed.

Lemma dw_bound_d : forall wbits dict s tin tout adler n,
    J1d wbits dict s tin tout adler -> 0 <= n <= max_size ->
    exists b, c_deflateBound_z (Some s) n = Some b /\ 0 <= b <= max_u64 /\
      forall data, Zlength data = n -> rbytes data -> Jd wbits dict data b 0 [] s tin tout adler.
Proof.
  intros wbits dict s tin tout adler n (Hpre & HK1 & Hwb & Hgz & Hw & Ti & To & Ad) Hn.
  destruct Hpre as (level & mem & strategy & Hpre).
  destruct (HBig _ _ _ _ _ _ _ _ _ n Hpre Hn) as (b & Eb & Hb & Hrun).
  exists b. split; [exact Eb|]. split; [exact Hb|].
  intros data Ld Hd. exists None, tin. subst n.
  rewrite sublist_nil. unfold max_size, max_u64, dict_max in *.
  repeat split; auto; try (rewrite ?Zlength_nil; lia); try discriminate; try constructor.
Qed.

Lemma dw_range_d : forall wbits dict data b pos O s tin tout adler,
    Jd wbits dict data b pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= max_size /\ 0 <= Zlength O <= b /\ b <= max_u64 /\
    rbytes data /\ rbytes O /\ d_gzhead s = None /\
    0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64.
Proof.
  intros wbits dict data b pos O s tin tout adler
    (fin & t0 & _ & _ & _ & _ & Hgz & _ & Ht0 & Ti & To & Hp & Hn & HO & Hb & Hd & HdO & Ad).
  unfold max_size, max_u64, dict_max in *. subst tin tout. repeat split; auto; lia.
Qed.

Lemma dw_call_d : forall wbits dict data b pos O s tin tout adler msg,
    Jd wbits dict data b pos O s tin tout adler ->
    let inb := dpiece data pos in
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) (dflush (Zlength data - pos)) =
        Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = None /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         Jd wbits dict data b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
           (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END ->
         z_avail_in z' = 0 /\ pos + Zlength inb = Zlength data /\ dfinal_dict wbits dict data (O ++ z_out z')).
Proof.
  intros wbits dict data b pos O s tin tout adler msg
    (fin & t0 & HK0 & Hrun & Hfin & Hwb & Hgz & Hw & Ht0 & Ti & To & Hp & Hn & HO & Hb & Hd & HdO & Ad) inb aout.
  set (n := Zlength data) in *. set (flush := dflush (n - pos)).
  assert (Li : Zlength inb = clipz (n - pos)) by (apply CT.dpiece_len; lia).
  assert (Hinb : inb = sublist pos (pos + Zlength inb) data) by (rewrite Li; reflexivity).
  assert (Hai : 0 <= Zlength inb <= umax) by (rewrite Li; unfold clipz, umax; lia).
  assert (Hao : 0 <= aout <= umax) by (unfold aout, clipz, umax in *; lia).
  assert (HOa : Zlength O + aout <= b) by (unfold aout, clipz in *; lia).
  assert (Hfl : (flush = Z_FINISH /\ Zlength inb = n - pos) \/ (flush = Z_NO_FLUSH /\ Zlength inb = umax /\ umax < n - pos)).
  { unfold flush. destruct (CT.dflush_cases (n - pos)) as [[-> L] | [-> L]]; [left | right];
      rewrite Li; unfold clipz; split; auto; lia. }
  assert (Hbi : LF.bytes inb).
  { rewrite Hinb. apply Forall_sublist. exact Hd. }
  assert (Hfg : CT.fin_given fin = true -> n - pos <= 4294967295).
  { intros Hf. destruct fin as [R|]; [|discriminate]. destruct (Hfin R eq_refl) as [_ L]. exact L. }
  assert (Li' : Zlength inb = Z.min (n - pos) 4294967295) by (rewrite Li; reflexivity).
  destruct (HClip n b pos (CT.fin_given fin) s tin tout adler inb msg Hrun Hbi Li' Hfg)
    as (s' & z' & code & E & Hgz' & Hzin & Hav & Hnext & Haout & Hzout & Hzb & Hti & Hto & Htb & Hc &
        Hend & Hrun').
  assert (Ea : Z.min (b - tout) 4294967295 = aout) by (unfold aout, clipz, umax; rewrite To; reflexivity).
  assert (Ef : (if n - pos <=? 4294967295 then Z_FINISH else Z_NO_FLUSH) = flush) by (unfold flush, dflush, umax; reflexivity).
  rewrite Ea, Ef in E. rewrite Ea in Haout, Hzout, Hto. rewrite Ef in Hend, Hrun'. clear Ea Ef.
  assert (Hrc : rcall_ok inb aout tin tout z').
  { unfold rcall_ok. repeat split; auto; lia. }
  exists s', z', code.
  split; [exact E|]. split; [exact Hrc|]. split; [congruence|].
  split; [destruct Hc as [?|[?|?]]; auto|].
  assert (Hfr : 0 <= flush <= 5) by (destruct Hfl as [[-> _] | [-> _]]; cbv; split; discriminate).
  assert (Hkf : code <> Z_BUF_ERROR ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength inb - z_avail_in z' in
     let D' := sublist 0 pos data ++ sublist 0 used inb in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal dict 1 (d_w_bits s) (d_gzhead s) D' O'
     else K dict 1 D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros Nb.
    apply (kf7_deflate _ HK dict 1 (sublist 0 pos data) O fin s tin tout adler inb aout flush msg
             s' z' code HK0 Hfr Hbi).
    + unfold umax in Hai. lia.
    + rewrite Zlength_sublist by lia. unfold max_size in Hn. destruct Hfl as [[_ L] | [_ [L L']]]; lia.
    + unfold umax in Hao. lia.
    + unfold max_u64 in Hb. lia.
    + intros R HR. destruct (Hfin R HR) as [-> L]. unfold flush, dflush.
      destruct (n - pos <=? umax) eqn:X; [|lia]. split; [reflexivity|].
      rewrite Hinb, Li. unfold clipz. f_equal. lia.
    + exact E.
    + exact Hgz'.
    + exact Hrc.
    + destruct Hc as [?|[?|?]]; auto.
    + exact Hend.
    + intros C. contradiction. }
  set (used := Zlength inb - z_avail_in z').
  assert (HD : sublist 0 pos data ++ sublist 0 used inb = sublist 0 (pos + used) data).
  { transitivity (sublist 0 pos data ++ sublist 0 used (sublist pos (pos + Zlength inb) data));
      [f_equal; f_equal; exact Hinb|].
    rewrite sublist_sublist by (unfold used in *; lia).
    rewrite Z.add_0_l, (Z.add_comm used pos). apply sublist_rejoin; unfold used in *; lia. }
  split.
  + intros ->. destruct Hkf as [Hw' HK1]; [discriminate|].
    cbv zeta in HK1. change (Z_OK =? Z_STREAM_END) with false in HK1. cbv iota in HK1. fold used in HK1.
    rewrite HD in HK1.
    exists (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None), t0.
    split; [exact HK1|].
    split.
    { replace (CT.fin_given _) with (flush =? Z_FINISH) by (destruct (flush =? Z_FINISH); reflexivity).
      apply Hrun'. discriminate. }
    split.
    { intros R HR. destruct (flush =? Z_FINISH) eqn:F; [|discriminate]. injection HR as <-.
      apply Z.eqb_eq in F. destruct Hfl as [[_ L] | [F' _]]; [|rewrite F in F'; discriminate].
      split; [|unfold used, umax in *; lia].
      transitivity (sublist used (Zlength inb) (sublist pos (pos + Zlength inb) data)); [f_equal; exact Hinb|].
      rewrite sublist_sublist by (unfold used in *; lia). f_equal; unfold n in *; lia. }
    unfold max_size, max_u64, umax, dict_max in *.
    split; [congruence|]. split; [congruence|]. split; [exact Hw|]. split; [exact Ht0|].
    split; [unfold used in *; lia|].
    split; [rewrite Zlength_app; lia|].
    split; [unfold used in *; lia|]. split; [lia|]. split; [rewrite Zlength_app; lia|].
    split; [lia|]. split; [exact Hd|]. split; [apply Forall_app; split; auto|].
    refine (Zlib.proof.deflate.AdlerKeep.c_deflate_adler_range s _ flush s' z' Z_OK Hgz _ _ E); [exact Hbi | exact Ad].
  + intros ->. destruct (Hend eq_refl) as [F A0].
    destruct Hfl as [[_ L] | [F' _]]; [|rewrite F in F'; discriminate].
    destruct Hkf as [_ HF]; [discriminate|].
    cbv zeta in HF. change (Z_STREAM_END =? Z_STREAM_END) with true in HF. cbv iota in HF. fold used in HF.
    rewrite HD in HF.
    split; [exact A0|]. split; [lia|].
    split; [exact Hw|]. rewrite Hwb, Hgz in HF.
    replace (sublist 0 (pos + used) data) with data in HF; [exact HF|].
    unfold used. rewrite A0, sublist_same; auto; lia.
Qed.

Lemma dict_dfacts_d : dict_dfacts J0d J1d Jd.
Proof.
  constructor.
  - exact dw_init_d.
  - exact dw_range0_d.
  - exact dw_dict_d.
  - exact dw_range1_d.
  - exact dw_bound_d.
  - exact dw_range_d.
  - exact dw_call_d.
Qed.

End Theory.

Lemma dict_dtheory : rt_k7_stmt -> Zlib.proof.deflate.LawFactsW2.bound_w_big_stmt -> dict_dfacts_stmt.
Proof.
  intros [K HK] (Bpre & Brun & HB & HBig & _ & HClip).
  exists (J0d K Bpre), (J1d K Bpre), (Jd K Brun). exact (dict_dfacts_d K Bpre Brun HK HB HBig HClip).
Qed.

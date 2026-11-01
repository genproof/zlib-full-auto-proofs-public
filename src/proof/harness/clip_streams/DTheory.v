(* The deflate facts of the four clip()-stream laws (DFacts.clip_dfacts) from the deflate side of the round trips
   without size limits (RTK7.kfacts7: what the output is) and the wide deflateBound accounting
   (LawFactsW2.bound_w_big_stmt: that each model run is defined, with its return codes). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.DFacts.
Require Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.deflate.InitStrm Zlib.proof.deflate.AdlerKeep Zlib.proof.roundtrip.RTBTheory Zlib.proof.huffman.Lemmas.
Import ListNotations.
Local Open Scope Z_scope.

Module LW := Zlib.proof.deflate.LawFactsW.
Module LF := Zlib.proof.deflate.LawFacts.

(* deflateInit2_ accepted the parameters: its windowBits part *)
Lemma rparams_wbits_acc level wbits mem strategy :
  rparams_ok level 8 wbits mem strategy = true -> wbits_acc wbits = true.
Proof.
  unfold rparams_ok, wbits_acc. intros H.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
  repeat rewrite andb_true_iff. tauto.
Qed.

Lemma rparams_params_ok level wbits mem strategy :
  rparams_ok level 8 wbits mem strategy = true -> LF.params_ok level 8 wbits mem strategy = true.
Proof. intros H. exact H. Qed.

(* Z_FINISH was given *)
Definition fin_given (fin : option (list Z)) : bool := match fin with Some _ => true | None => false end.

Section Theory.
Variables (K : rinv) (Bpre : LF.bpre_inv) (Brun : LF.brun_inv).
Hypotheses (HK : kfacts7 K) (HB : LW.bound_facts_w Bpre Brun)
           (HBig : Zlib.proof.deflate.LawFactsW2.bw_bound_big Bpre Brun)
           (HClip : Zlib.proof.deflate.LawFactsW2.bw_clip Brun).

(* after deflateInit2: the deflate laws' invariant, the round trip's invariant, fresh counters *)
Definition J0c (wbits : Z) (s : dstate) (tin tout adler : Z) : Prop :=
  (exists level mem strategy, Bpre level wbits mem strategy false s tin tout adler) /\
  K [] (rwrap_of wbits) [] [] None s tin tout adler /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = None /\ wbits_acc wbits = true /\
  tin = 0 /\ tout = 0 /\ 0 <= adler <= max_u64.

(* at the head of the loop: [pos] bytes of the data consumed, [O] produced; once Z_FINISH was given, the rest of
   the data is what the round trip's invariant waits for *)
Definition Jc (wbits : Z) (data : list Z) (b pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z) : Prop :=
  exists fin,
  K [] (rwrap_of wbits) (sublist 0 pos data) O fin s tin tout adler /\
  Brun (Zlength data) b pos (fin_given fin) s tin tout adler /\
  (forall R, fin = Some R -> R = sublist pos (Zlength data) data /\ Zlength data - pos <= umax) /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = None /\ wbits_acc wbits = true /\
  tin = pos /\ tout = Zlength O /\ 0 <= pos <= Zlength data /\ Zlength data <= max_size /\
  0 <= Zlength O <= b /\ b <= max_u64 /\ rbytes data /\ rbytes O /\ 0 <= adler <= max_u64.

Lemma cd_init_c : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> rs32 wbits -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0c wbits s (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw Hm Hs.
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hov Hbb].
  destruct (Zlib.proof.roundtrip.RTBTheory.rt_b_facts Hov Hbb) as [Hinit _].
  assert (H8 : rs32 8) by (unfold rs32; lia).
  destruct (Hinit level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 Hl H8 Hw Hm Hs) as [Hex Hcodes].
  split; [exact Hex|].
  intros os z' code E Ecode. subst code.
  destruct (Hcodes os z' Z_OK E) as (_ & Hse & _).
  assert (P : rparams_ok level 8 wbits mem strategy = true).
  { destruct (rparams_ok level 8 wbits mem strategy) eqn:P; [reflexivity|].
    assert (C : Z_OK = Z_STREAM_ERROR) by (apply Hse; reflexivity). discriminate C. }
  destruct (LW.bw_init _ _ HB level wbits mem strategy a1 a2 a3 a4 a5 dz0 (rparams_params_ok _ _ _ _ P))
    as [_ Hbi].
  destruct (Hbi os z' Z_OK E eq_refl) as (s & -> & Hgz & Hpre).
  destruct (kf7_init _ HK level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 s z' Hl H8 Hw Hm Hs E)
    as (Hwb & _ & HK0).
  destruct (Zlib.proof.deflate.InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (Ti & To & Ad & _).
  exists s. split; [reflexivity|].
  unfold J0c. split; [eauto|]. split; [exact HK0|]. split; [exact Hwb|]. split; [exact Hgz|].
  split; [exact (rparams_wbits_acc _ _ _ _ P)|].
  split; [exact Ti|]. split; [exact To|]. unfold max_u64. destruct Ad as [-> | ->]; lia.
Qed.

Lemma cd_bound_c : forall wbits s tin tout adler n,
    J0c wbits s tin tout adler -> 0 <= n <= max_size ->
    exists b, c_deflateBound_z (Some s) n = Some b /\ 0 <= b <= max_u64 /\
      forall data, Zlength data = n -> rbytes data -> Jc wbits data b 0 [] s tin tout adler.
Proof.
  intros wbits s tin tout adler n (Hpre & HK0 & Hwb & Hgz & Hacc & Ti & To & Ad) Hn.
  destruct Hpre as (level & mem & strategy & Hpre).
  destruct (HBig _ _ _ _ _ _ _ _ _ n Hpre Hn) as (b & Eb & Hb & Hrun).
  exists b. split; [exact Eb|]. split; [exact Hb|].
  intros data Ld Hd. exists None. subst n.
  rewrite sublist_nil. unfold max_size, max_u64 in *.
  repeat split; auto; try (rewrite ?Zlength_nil; lia); try discriminate; try constructor.
Qed.

Lemma cd_range_c : forall wbits data b pos O s tin tout adler,
    Jc wbits data b pos O s tin tout adler ->
    0 <= pos <= Zlength data /\ Zlength data <= max_size /\ 0 <= Zlength O <= b /\ b <= max_u64 /\
    rbytes data /\ rbytes O /\ d_gzhead s = None /\
    0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64.
Proof.
  intros wbits data b pos O s tin tout adler
    (fin & _ & _ & _ & _ & Hgz & _ & Ti & To & Hp & Hn & HO & Hb & Hd & HdO & Ad).
  unfold max_size, max_u64 in *. subst tin tout. repeat split; auto; lia.
Qed.

(* the piece of the call made after [pos] bytes: all the rest when the flush is Z_FINISH *)
Lemma dpiece_len data pos : 0 <= pos <= Zlength data ->
  Zlength (dpiece data pos) = clipz (Zlength data - pos).
Proof.
  intros H. unfold dpiece, clipz, umax. rewrite Zlength_sublist; lia.
Qed.

Lemma dflush_cases rest : (dflush rest = Z_FINISH /\ rest <= umax) \/ (dflush rest = Z_NO_FLUSH /\ umax < rest).
Proof. unfold dflush. destruct (rest <=? umax) eqn:E; [left | right]; split; auto; lia. Qed.

Lemma cd_call_c : forall wbits data b pos O s tin tout adler msg,
    Jc wbits data b pos O s tin tout adler ->
    let inb := dpiece data pos in
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) (dflush (Zlength data - pos)) =
        Some (s', z', code) /\
      rcall_ok inb aout tin tout z' /\ d_gzhead s' = None /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         Jc wbits data b (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
           (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END ->
         z_avail_in z' = 0 /\ pos + Zlength inb = Zlength data /\ dfinal_of wbits data (O ++ z_out z')).
Proof.
  intros wbits data b pos O s tin tout adler msg
    (fin & HK0 & Hrun & Hfin & Hwb & Hgz & Hacc & Ti & To & Hp & Hn & HO & Hb & Hd & HdO & Ad) inb aout.
  set (n := Zlength data) in *. set (flush := dflush (n - pos)).
  assert (Li : Zlength inb = clipz (n - pos)) by (apply dpiece_len; lia).
  assert (Hinb : inb = sublist pos (pos + Zlength inb) data) by (rewrite Li; reflexivity).
  assert (Hai : 0 <= Zlength inb <= umax) by (rewrite Li; unfold clipz, umax; lia).
  assert (Hao : 0 <= aout <= umax) by (unfold aout, clipz, umax in *; lia).
  assert (HOa : Zlength O + aout <= b) by (unfold aout, clipz in *; lia).
  assert (Hfl : (flush = Z_FINISH /\ Zlength inb = n - pos) \/ (flush = Z_NO_FLUSH /\ Zlength inb = umax /\ umax < n - pos)).
  { unfold flush. destruct (dflush_cases (n - pos)) as [[-> L] | [-> L]]; [left | right];
      rewrite Li; unfold clipz; split; auto; lia. }
  assert (Hbi : LF.bytes inb).
  { rewrite Hinb. apply Forall_sublist. exact Hd. }
  assert (Hfg : fin_given fin = true -> n - pos <= 4294967295).
  { intros Hf. destruct fin as [R|]; [|discriminate]. destruct (Hfin R eq_refl) as [_ L]. exact L. }
  assert (Li' : Zlength inb = Z.min (n - pos) 4294967295) by (rewrite Li; reflexivity).
  destruct (HClip n b pos (fin_given fin) s tin tout adler inb msg Hrun Hbi Li' Hfg)
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
     if code =? Z_STREAM_END then dfinal [] (rwrap_of wbits) (d_w_bits s) (d_gzhead s) D' O'
     else K [] (rwrap_of wbits) D' O' (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros Nb.
    apply (kf7_deflate _ HK [] (rwrap_of wbits) (sublist 0 pos data) O fin s tin tout adler inb aout flush msg
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
    exists (if flush =? Z_FINISH then Some (sublist used (Zlength inb) inb) else None).
    split; [exact HK1|].
    split.
    { replace (fin_given _) with (flush =? Z_FINISH) by (destruct (flush =? Z_FINISH); reflexivity).
      apply Hrun'. discriminate. }
    split.
    { intros R HR. destruct (flush =? Z_FINISH) eqn:F; [|discriminate]. injection HR as <-.
      apply Z.eqb_eq in F. destruct Hfl as [[_ L] | [F' _]]; [|rewrite F in F'; discriminate].
      split; [|unfold used, umax in *; lia].
      transitivity (sublist used (Zlength inb) (sublist pos (pos + Zlength inb) data)); [f_equal; exact Hinb|].
      rewrite sublist_sublist by (unfold used in *; lia). f_equal; unfold n in *; lia. }
    unfold max_size, max_u64, umax in *.
    split; [congruence|]. split; [congruence|]. split; [exact Hacc|].
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
    split; [exact Hacc|]. rewrite Hwb, Hgz in HF.
    replace (sublist 0 (pos + used) data) with data in HF; [exact HF|].
    unfold used. rewrite A0, sublist_same; auto; lia.
Qed.

Lemma clip_dfacts_c : clip_dfacts J0c Jc.
Proof.
  constructor.
  - exact cd_init_c.
  - exact cd_bound_c.
  - exact cd_range_c.
  - exact cd_call_c.
Qed.

End Theory.

Lemma clip_dtheory : rt_k7_stmt -> Zlib.proof.deflate.LawFactsW2.bound_w_big_stmt -> clip_dfacts_stmt.
Proof.
  intros [K HK] (Bpre & Brun & HB & HBig & _ & HClip).
  exists (J0c K Bpre), (Jc K Brun). exact (clip_dfacts_c K Bpre Brun HK HB HBig HClip).
Qed.

(* Law rt_gzip_header on the round-2 harness: the deflate side of the law (G2DFacts.g2_dfacts), pure Coq over the
   model of deflate.c. *)

(* As clip_streams/DTheory.v (the clip() loop of deflate(Z_FINISH) calls), with no data (n = 0) and a gzip header
   set by deflateSetHeader:
   - what the output is: the deflate side of the round trips, for its own invariant RTK7Defs.K7
     (G2DK7.g2_kfacts7: kf7_init, kf7_head, kf7_deflate gives dfinal at Z_STREAM_END);
   - that each model run is defined and its return codes: the wide deflateBound accounting
     (LawFactsW2.bound_w_big_stmt: bw_init, bw_head, bw_bound_big with n = 0, bw_clip);
   - that strm->adler stays a 64-bit value from one call to the next: G2DAdler.g2_deflate_adler, with the
     pending buffer and the header CRC that K7 gives between the calls (G2DK7.g2_k7_between). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.roundtrip.RTK7Defs.
Require Zlib.proof.deflate.LawFactsW2.
Require Zlib.proof.harness.clip_streams.DTheory.
Require Zlib.proof.huffman.Lemmas.
Require Zlib.proof.deflate.LTWCore.
Require Zlib.proof.deflate.LTWClip.
Require Zlib.proof.deflate.LTWClipCore.
Require Zlib.proof.deflate.LTWHdr.
Require Zlib.proof.harness.rt_gzip_header.G2DAdler.
Require Zlib.proof.harness.rt_gzip_header.G2DK7.
Import ListNotations.
Local Open Scope Z_scope.

Module LW := Zlib.proof.deflate.LawFactsW.
Module LF := Zlib.proof.deflate.LawFacts.
Module DT := Zlib.proof.harness.clip_streams.DTheory.

(* the headers of the harness are those of the round trips' theory and of the wide deflateBound accounting *)
Lemma g2_rhdr gh : g2_hdr_ok gh -> rhdr_ok7 gh.
Proof. intros H. exact H. Qed.

Lemma g2_hdr_w gh : g2_hdr_ok gh -> LW.hdr_ok_w gh.
Proof. intros H. exact H. Qed.

Lemma g2_rwrap wbits : 25 <= wbits <= 31 -> rwrap_of wbits = 2.
Proof.
  intros H. unfold rwrap_of.
  destruct (wbits <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (wbits >? 15) eqn:E2; [reflexivity|]. rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2. lia.
Qed.

Section Theory.
Variables (Bpre : LF.bpre_inv) (Brun : LF.brun_inv).
Hypotheses (HB : LW.bound_facts_w Bpre Brun)
           (HBig : Zlib.proof.deflate.LawFactsW2.bw_bound_big Bpre Brun)
           (HClip : Zlib.proof.deflate.LawFactsW2.bw_clip Brun).

(* after deflateInit2: as for the clip() streams, with a gzip windowBits *)
Definition J0g (wbits : Z) (s : dstate) (tin tout adler : Z) : Prop :=
  DT.J0c K7 Bpre wbits s tin tout adler /\ 25 <= wbits <= 31.

(* at the head of the loop: [O] produced so far, nothing consumed; once Z_FINISH was given (fin = Some []), the
   round trip's invariant waits for no more data *)
Definition Jg (wbits : Z) (gh : DS7.gzh) (b : Z) (O : list Z) (s : dstate) (tin tout adler : Z) : Prop :=
  exists fin,
  K7 [] 2 [] O fin s tin tout adler /\ Brun 0 b 0 (DT.fin_given fin) s tin tout adler /\
  (forall R, fin = Some R -> R = []) /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = Some gh /\ 25 <= wbits <= 31 /\ g2_hdr_ok gh /\
  tin = 0 /\ tout = Zlength O /\ 0 <= Zlength O <= b /\ b <= max_u64 /\ rbytes O /\ 0 <= adler <= max_u64.

Lemma gd_init_g : forall level wbits mem strategy a1 a2 a3 a4 a5,
    rs32 level -> 25 <= wbits <= 31 -> rs32 mem -> rs32 strategy ->
    (exists r, c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some r) /\
    forall os z' code,
      c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 dz0 = Some (os, z', code) ->
      code = Z_OK ->
      exists s, os = Some s /\ J0g wbits s (z_total_in z') (z_total_out z') (z_adler z').
Proof.
  intros level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw Hm Hs.
  assert (Hw' : rs32 wbits) by (unfold rs32; lia).
  destruct (DT.cd_init_c K7 Bpre Brun G2DK7.g2_kfacts7 HB level wbits mem strategy a1 a2 a3 a4 a5 Hl Hw' Hm Hs)
    as [Hex Hc].
  split; [exact Hex|].
  intros os z' code E Ec. destruct (Hc os z' code E Ec) as (s & -> & HJ).
  exists s. split; [reflexivity|]. split; [exact HJ|exact Hw].
Qed.

Lemma gd_head_g : forall wbits s tin tout adler gh z,
    J0g wbits s tin tout adler -> g2_hdr_ok gh ->
    c_deflateSetHeader s z (Some gh) = Some (set_d_gzhead s (Some gh), z, Z_OK).
Proof.
  intros wbits s tin tout adler gh z ((Hpre & _) & Hw) Hh.
  destruct Hpre as (level & mem & strategy & Hpre).
  exact (proj1 (LW.bw_head _ _ HB level wbits mem strategy false s tin tout adler gh z Hpre ltac:(lia) (g2_hdr_w gh Hh))).
Qed.

Lemma gd_bound_g : forall wbits s tin tout adler gh,
    J0g wbits s tin tout adler -> g2_hdr_ok gh ->
    exists b, c_deflateBound_z (Some (set_d_gzhead s (Some gh))) 0 = Some b /\ 0 <= b <= max_u64 /\
      Jg wbits gh b [] (set_d_gzhead s (Some gh)) tin tout adler.
Proof.
  intros wbits s tin tout adler gh ((Hpre & HK0 & Hwb & Hgz & Hacc & Ti & To & Ad) & Hw) Hh.
  destruct Hpre as (level & mem & strategy & Hpre).
  destruct (LW.bw_head _ _ HB level wbits mem strategy false s tin tout adler gh dz0 Hpre ltac:(lia) (g2_hdr_w gh Hh))
    as [_ Hpre'].
  destruct (HBig _ _ _ _ _ _ _ _ _ 0 Hpre' ltac:(lia)) as (b & Eb & Hb & Hrun).
  exists b. split; [exact Eb|]. split; [unfold max_u64; lia|].
  rewrite (g2_rwrap wbits Hw) in HK0.
  pose proof (kf7_head _ G2DK7.g2_kfacts7 [] s tin tout adler gh HK0 (g2_rhdr gh Hh)) as HK1.
  exists None. split; [exact HK1|]. split; [exact Hrun|]. split; [discriminate|].
  split; [destruct s; exact Hwb|]. split; [reflexivity|]. split; [exact Hw|]. split; [exact Hh|].
  rewrite Zlength_nil. unfold max_u64, Zlib.proof.harness.clip_streams.DFacts.max_u64 in *.
  repeat split; auto; try lia. apply Forall_nil.
Qed.

Lemma gd_range_g : forall wbits gh b O s tin tout adler,
    Jg wbits gh b O s tin tout adler ->
    25 <= wbits <= 31 /\ g2_hdr_ok gh /\ 0 <= Zlength O <= b /\ b <= max_u64 /\ rbytes O /\
    d_gzhead s = Some gh /\ 0 <= tin <= max_u64 /\ 0 <= tout <= max_u64 /\ 0 <= adler <= max_u64.
Proof.
  intros wbits gh b O s tin tout adler (fin & _ & _ & _ & _ & Hgz & Hw & Hh & Ti & To & HO & Hb & Hd & Ad).
  unfold max_u64 in *. subst tin tout.
  refine (conj Hw (conj Hh (conj _ (conj _ (conj Hd (conj Hgz _)))))); repeat split; lia.
Qed.

Lemma gd_call_g : forall wbits gh b O s tin tout adler msg,
    Jg wbits gh b O s tin tout adler ->
    let aout := clipz (b - Zlength O) in
    exists s' z' code,
      c_deflate s (rzcall [] 0 0 tin aout tout adler msg) Z_FINISH = Some (s', z', code) /\
      rcall_ok [] aout tin tout z' /\ d_gzhead s' = Some gh /\
      (code = Z_OK \/ code = Z_STREAM_END \/ code = Z_BUF_ERROR) /\
      (code = Z_OK ->
         Jg wbits gh b (O ++ z_out z') s' (z_total_in z') (z_total_out z') (z_adler z')) /\
      (code = Z_STREAM_END -> dfinal [] 2 (rwbe wbits) (Some gh) [] (O ++ z_out z')).
Proof.
  intros wbits gh b O s tin tout adler msg
    (fin & HK0 & Hrun & Hfin & Hwb & Hgz & Hw & Hh & Ti & To & HO & Hb & HdO & Ad) aout.
  assert (Ea0 : aout = Z.min (b - Zlength O) 4294967295) by reflexivity. clearbody aout.
  assert (Hao : 0 <= aout <= 4294967295) by lia.
  assert (HOa : Zlength O + aout <= b) by lia.
  assert (Hfg : DT.fin_given fin = true -> 0 - 0 <= 4294967295) by (intros _; lia).
  destruct (HClip 0 b 0 (DT.fin_given fin) s tin tout adler [] msg Hrun (Forall_nil _) eq_refl Hfg)
    as (s' & z' & code & E & Hgz' & Hzin & Hav & Hnext & Haout & Hzout & Hzb & Hti & Hto & Htb & Hc &
        Hend & Hrun').
  assert (Ea : Z.min (b - tout) 4294967295 = aout) by (rewrite To, Ea0; reflexivity).
  change (if 0 - 0 <=? 4294967295 then Z_FINISH else Z_NO_FLUSH) with Z_FINISH in E, Hend, Hrun'.
  rewrite Ea in E, Haout, Hzout, Hto.
  change (Zlength (@nil Z)) with 0 in *.
  assert (A0 : z_avail_in z' = 0) by lia.
  assert (Hrc : rcall_ok [] aout tin tout z').
  { unfold rcall_ok. change (Zlength (@nil Z)) with 0. repeat split; auto; lia. }
  (* strm->adler after the call *)
  destruct (G2DK7.g2_k7_between O fin s tin tout adler HK0 Hfin) as [Pq Hq].
  assert (Ad' : 0 <= z_adler z' <= max_u64).
  { unfold max_u64 in *.
    refine (G2DAdler.g2_deflate_adler s (rzcall [] 0 0 tin aout tout adler msg) Z_FINISH s' z' code Pq
              (Forall_nil _) Ad _ E).
    intros X. exact (Hq X). }
  exists s', z', code.
  split; [exact E|]. split; [exact Hrc|]. split; [congruence|].
  split; [destruct Hc as [?|[?|?]]; auto|].
  assert (Hkf : code <> Z_BUF_ERROR ->
    d_w_bits s' = d_w_bits s /\
    (let used := Zlength (@nil Z) - z_avail_in z' in
     let D' := [] ++ sublist 0 used (@nil Z) in
     let O' := O ++ z_out z' in
     if code =? Z_STREAM_END then dfinal [] 2 (d_w_bits s) (d_gzhead s) D' O'
     else K7 [] 2 D' O' (if Z_FINISH =? Z_FINISH then Some (sublist used (Zlength (@nil Z)) (@nil Z)) else None)
            s' (z_total_in z') (z_total_out z') (z_adler z'))).
  { intros Nb.
    apply (kf7_deflate _ G2DK7.g2_kfacts7 [] 2 [] O fin s tin tout adler [] aout Z_FINISH msg s' z' code HK0).
    + cbv; split; discriminate.
    + constructor.
    + cbn; lia.
    + cbn; lia.
    + lia.
    + unfold max_u64 in Hb; lia.
    + intros R HR. rewrite (Hfin R HR). auto.
    + exact E.
    + exact Hgz'.
    + exact Hrc.
    + destruct Hc as [?|[?|?]]; auto.
    + exact Hend.
    + intros C. contradiction. }
  rewrite A0 in Hkf. cbv zeta in Hkf.
  change (Zlength (@nil Z) - 0) with 0 in Hkf. change ([] ++ sublist 0 0 (@nil Z)) with (@nil Z) in Hkf.
  change (sublist 0 0 (@nil Z)) with (@nil Z) in Hkf.
  split.
  + intros ->. destruct Hkf as [Hw' HK1]; [discriminate|].
    change (Z_OK =? Z_STREAM_END) with false in HK1. cbv iota in HK1.
    change (Z_FINISH =? Z_FINISH) with true in HK1. cbv iota in HK1.
    exists (Some []). split; [exact HK1|].
    split.
    { replace (0 + (0 - z_avail_in z')) with 0 in Hrun' by lia. exact (Hrun' ltac:(discriminate)). }
    split; [intros R HR; injection HR as <-; reflexivity|].
    unfold max_u64 in *.
    split; [congruence|]. split; [congruence|]. split; [exact Hw|]. split; [exact Hh|].
    split; [lia|]. split; [rewrite Zlength_app; lia|]. split; [rewrite Zlength_app; lia|].
    split; [lia|]. split; [apply Forall_app; split; auto|]. exact Ad'.
  + intros ->. destruct Hkf as [_ HF]; [discriminate|].
    change (Z_STREAM_END =? Z_STREAM_END) with true in HF. cbv iota in HF.
    rewrite Hwb, Hgz in HF. exact HF.
Qed.

Lemma g2_dfacts_g : g2_dfacts J0g Jg.
Proof.
  constructor.
  - exact gd_init_g.
  - exact gd_head_g.
  - exact gd_bound_g.
  - exact gd_range_g.
  - exact gd_call_g.
Qed.

End Theory.

Lemma rtg2_dtheory : g2_dfacts_stmt.
Proof.
  destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hi Hii].
  pose proof (Zlib.proof.deflate.LTWCore.core_facts_w3 Hi) as CF.
  destruct (Zlib.proof.deflate.LTWClip.bound_w_big_thm Hii
              (conj CF (Zlib.proof.deflate.LTWClipCore.core_clip_facts CF)) Zlib.proof.deflate.LTWHdr.hdr_theory_w)
    as (Bpre & Brun & HB & HBig & _ & HClip).
  exists (J0g Bpre), (Jg Brun). exact (g2_dfacts_g Bpre Brun HB HBig HClip).
Qed.

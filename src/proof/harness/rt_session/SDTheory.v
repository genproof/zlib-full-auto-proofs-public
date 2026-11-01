(* Law rt_session: the deflate side's facts for main ([SDFacts.ses_dtheory_stmt]): rt_stream's UDTheory.udj with
   the session's dictionary and gzip header (RTK7Defs.K7 and Iapi7 take both), kept by deflateSetDictionary
   (RTK7Dict) and deflateSetHeader (RTK7Head), deflate() as in UDTheory (RTK7Api.api7_deflate_stmt, proved by
   RTK7Api.rtk7_api_deflate from RTK7Nocut.comp_nocut7). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_stream.UDTheory.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.roundtrip.RTK7Init.
Require Import Zlib.proof.roundtrip.RTK7Core.
Require Import Zlib.proof.roundtrip.RTK7Dict.
Require Import Zlib.proof.roundtrip.RTK7Head.
Require Import Zlib.proof.roundtrip.RTK7Nocut.
Require Zlib.proof.roundtrip.RTDLTApiArith.
Require Zlib.proof.huffman.Lemmas.
Require Zlib.proof.roundtrip.RTBTheory.
Require Zlib.proof.deflate.InitStrm.
Import ListNotations.
Local Open Scope Z_scope.

(** The invariant between main's calls: the round trip's invariant K7 (what the output is) and the wide
    deflate_api invariant Iapi7 (every call is defined), both with the dictionary [dict]; deflate's w_bits and the
    gzip header [gh] (they fix the stream that [RTFinal.dfinal] describes at the end), the output at most
    PTRDIFF_MAX bytes (total_out is its length) and strm->adler 32 bits. *)
Definition sdj : ses_dinv := fun wbits dict gh D O fin s tin tout adler =>
  K7 dict (rwrap_of wbits) D O fin s tin tout adler /\
  Iapi7 W3 hinv7 dict (rwrap_of wbits) D O fin s tin tout adler /\
  d_w_bits s = rwbe wbits /\ d_gzhead s = gh /\ Zlength O <= max_size /\ 0 <= adler < 4294967296.

(** Before any data, without output and before Z_FINISH, a zlib stream's strm->adler is the Adler-32 of its
    dictionary (the phase ph0 of Iapi7; the other phases need output, a gzip stream or Z_FINISH). *)
Lemma sdt_adler1 dict s tin tout adler :
  Iapi7 W3 hinv7 dict 1 [] [] None s tin tout adler -> adler = Zlib.proof.adler32.Model.ref_adler32 1 dict.
Proof.
  intros HI.
  destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Had). exact (Had eq_refl).
  - destruct P1 as (Hw & _). discriminate Hw.
  - destruct P2 as (_ & _ & _ & HOne & _). exfalso. apply (HOne ltac:(discriminate)). reflexivity.
  - destruct P3 as [Hst _]. specialize (Hfin Hst). discriminate.
Qed.

(** Right after deflateInit2 a gzip stream is in GZIP_STATE with d_wrap 2 (phase ph0). *)
Lemma sdt_gzip0 s tin tout adler :
  Iapi7 W3 hinv7 [] 2 [] [] None s tin tout adler -> d_status s = GZIP_STATE /\ d_wrap s = 2.
Proof.
  intros HI.
  destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfin & _ & Hph).
  destruct Hph as [P0 | (_ & [P1 | [P2 | P3]])].
  - destruct P0 as ([[_ Hw] | [Hst _]] & Hdw & _); [lia|]. split; [exact Hst|exact Hdw].
  - destruct P1 as (_ & _ & Hne & _). congruence.
  - destruct P2 as (_ & _ & _ & HOne & _). exfalso. apply (HOne ltac:(discriminate)). reflexivity.
  - destruct P3 as [Hst _]. specialize (Hfin Hst). discriminate.
Qed.

(** deflateSetDictionary right after deflateInit2 on a raw or zlib stream returns Z_OK (the core fact cf7_dict,
    whose conditions on the state are those of the phase of Iapi7 before any data: ph0, or ph2 of a raw stream
    after deflate() calls without data); strm->adler is kept on a raw stream. *)
Lemma sdt_dict_ex wrap s tin tout adler d ain aout msg :
  Iapi7 W3 hinv7 [] wrap [] [] None s tin tout adler -> wrap <> 2 ->
  rbytes d -> Zlength d <= 4294967295 ->
  exists s' z',
    c_deflateSetDictionary s (rzcall [] 0 ain tin aout tout adler msg) (Some d) = Some (s', z', Z_OK) /\
    (wrap = 0 -> z_adler z' = adler).
Proof.
  intros HI0 Hw2 Hd Hdl.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov.
  pose proof (rtk7_core_ok Hov) as HC.
  pose proof HI0 as Hcp. unfold Iapi7 in Hcp.
  destruct Hcp as (HW & Hok & Hwr & _ & Hbd & Hdl0 & Hlfr & Hgz & Hto & HbO & HbD & HDl & Htin & Hfin & Hdz & Hph).
  destruct Htin as (k0 & Hk0 & Htin). rewrite Zlength_nil in Hk0, Htin.
  assert (Hk00 : k0 = 0) by lia. subst k0. change (u64 (0 + 0)) with 0 in Htin. subst tin.
  destruct (Hdz eq_refl) as (Hla & Hsb & Hs00). pose proof (Hs00 eq_refl) as Hss0.
  assert (Hbs0 : d_block_start s = 0) by lia.
  assert (Hcase : (d_status s = INIT_STATE /\ wrap <= 1 /\ d_wrap s = wrap /\ ph0 [] wrap [] [] s 0 adler) \/
                  (d_status s = BUSY_STATE /\ wrap = 0 /\ d_wrap s = 0)).
  { destruct Hph as [P0 | (Hne & [P1 | [P2 | P3]])].
    - pose proof P0 as P0'. destruct P0' as ([[Hst Hw1] | [Hst Hw2']] & Hdw & _).
      + left. auto.
      + contradiction.
    - destruct P1 as (_ & _ & Hne1 & _). congruence.
    - destruct P2 as (Hst & Hdw & _ & HOne & _).
      assert (wrap = 0) by (destruct (Z.eq_dec wrap 0); [auto|exfalso; apply (HOne n); reflexivity]).
      right. subst wrap. auto.
    - destruct P3 as [Hst _]. specialize (Hfin Hst). discriminate. }
  assert (Hb : bad_state s = false).
  { unfold bad_state, c_deflateStateCheck, status_ok.
    destruct Hcase as [(Hst & _)|(Hst & _)]; rewrite Hst; reflexivity. }
  assert (Hx : 0 <= d_wrap s <= 1 /\ d_wrap s = wrap /\ (d_wrap s = 1 -> d_status s = INIT_STATE) /\
               adler_pre (d_wrap s) adler).
  { destruct Hcase as [(Hst & Hw1 & Hdw & P0) | (Hst & -> & Hdw)].
    - destruct P0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Had).
      split; [lia|]. split; [exact Hdw|]. split; [intros; exact Hst|].
      unfold adler_pre. split; [|intros; lia]. intros Hw. rewrite Hdw in Hw. rewrite (Had Hw).
      unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence.
    - split; [lia|]. split; [exact Hdw|]. split; [intros; lia|].
      unfold adler_pre. split; intros; lia. }
  destruct Hx as (Hw1 & Hdw & Hinit & Hadp).
  destruct (cf7_dict W3 HC s (rzcall [] 0 ain 0 aout tout adler msg) d HW Hw1 Hb Hinit Hss0 Hla Hbs0 Hd Hdl
              ltac:(cbn; lia) Hadp)
    as (s2 & z2 & k & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hz').
  exists s2, z2. split; [exact E2|].
  intros Hw0. rewrite Hz'. cbn [z_adler rzcall]. rewrite Hdw, Hw0. reflexivity.
Qed.

(** deflateSetHeader right after deflateInit2 on a gzip stream: Z_OK, the state with the header *)
Lemma sdt_head s z h :
  bad_state s = false -> d_wrap s = 2 ->
  c_deflateSetHeader s z (Some h) = Some (set_d_gzhead s (Some h), z, Z_OK).
Proof. intros Hb Hw. unfold c_deflateSetHeader. rewrite Hb, Hw. reflexivity. Qed.

Theorem ses_dtheory : ses_dtheory_stmt.
Proof.
  pose proof (rtk7_api_deflate comp_nocut7) as AD.
  pose proof (proj1 Zlib.proof.huffman.Lemmas.huffman_lemmas) as Hov0.
  exists sdj. constructor.
  - (* deflateInit2 *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z Hl Hw Hm Hs.
    destruct Zlib.proof.huffman.Lemmas.huffman_lemmas as [Hov Hbb].
    destruct (Zlib.proof.roundtrip.RTBTheory.rt_b_facts Hov Hbb) as [Hinit _].
    assert (H8 : rs32 8) by (unfold rs32; lia).
    destruct (Hinit level 8 wbits mem strategy a1 a2 a3 a4 a5 z Hl H8 Hw Hm Hs) as [Hex Hcodes].
    split; [exact Hex|].
    intros os z' code E Ecode. subst code.
    destruct (Hcodes os z' Z_OK E) as (_ & Hse & Hsome).
    split.
    { destruct (rparams_ok level 8 wbits mem strategy) eqn:P; [reflexivity|].
      assert (C : Z_OK = Z_STREAM_ERROR) by (apply Hse; reflexivity). discriminate C. }
    destruct (Hsome eq_refl) as (s & -> & Hgz).
    destruct (rtk7_init_ok level 8 wbits mem strategy a1 a2 a3 a4 a5 z s z' Hl H8 Hw Hm Hs E)
      as (Hwb & _ & HK0).
    destruct (Zlib.proof.deflate.InitStrm.init_ok_strm _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (Ti & To & Ad & _).
    exists s. split; [reflexivity|].
    split; [exact HK0|].
    split; [destruct HK0 as [[HI _] | (_ & R & HR & _)]; [exact HI | discriminate HR]|].
    split; [exact Hwb|]. split; [exact Hgz|].
    split; [cbn; unfold max_size; lia|]. destruct Ad as [-> | ->]; lia.
  - (* deflateInit2's code *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z os z' code P E.
    exact (udt_init_code _ _ _ _ _ _ _ _ _ _ _ _ _ P E).
  - (* the counters *)
    intros wbits dict gh D O fin s tin tout adler (_ & HI & _ & Hgz & LO & Ha).
    destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & Ht & _ & _ & _ & (k & _ & Htin) & _).
    pose proof (Zlength_nonneg O).
    rewrite Htin. unfold u64.
    pose proof (Z.mod_pos_bound (Zlength D + k) 18446744073709551616 ltac:(lia)).
    unfold max_size in LO. split; [lia|]. split; [lia|]. split; [lia|exact Hgz].
  - (* deflateSetDictionary *)
    intros wbits s tin tout adler d ain aout msg (HK & HI & Hwb & Hgz & LO & Ha) Hw2 Hd Hdl Hain Haout.
    destruct (sdt_dict_ex (rwrap_of wbits) s tin tout adler d ain aout msg HI Hw2 Hd ltac:(lia))
      as (s' & z' & E & Had0).
    destruct (rtk7_dict_ok Hov0 (rtk7_core_ok Hov0) (rwrap_of wbits) s tin tout adler d ain aout msg s' z' Z_OK
                HK Hd ltac:(lia) Hain Haout E ltac:(left; reflexivity) ltac:(split; [discriminate|intros; contradiction]))
      as (Hwb' & Hgz' & HK1).
    rewrite (proj2 (Z.eqb_neq (rwrap_of wbits) 2) Hw2) in HK1.
    assert (HI1 : Iapi7 W3 hinv7 d (rwrap_of wbits) [] [] None s' (z_total_in z') (z_total_out z') (z_adler z')).
    { destruct HK1 as [[HI1 _] | (_ & R & HR & _)]; [exact HI1 | discriminate HR]. }
    exists s', z'. split; [exact E|].
    split; [exact HK1|]. split; [exact HI1|]. split; [congruence|]. split; [congruence|].
    split; [rewrite Zlength_nil; unfold max_size; lia|].
    pose proof HI as (_ & _ & Hwr & _).
    destruct (Z.eq_dec (rwrap_of wbits) 0) as [W0|W0].
    + rewrite (Had0 W0). exact Ha.
    + assert (W1 : rwrap_of wbits = 1) by lia. rewrite W1 in HI1.
      rewrite (sdt_adler1 _ _ _ _ _ HI1). pose proof (Zlib.proof.roundtrip.RTDLTApiArith.radler_range d). lia.
  - (* deflateSetHeader *)
    intros wbits s tin tout adler h z (HK & HI & Hwb & Hgz & LO & Ha) Hw2 Hh.
    rewrite Hw2 in HK, HI.
    destruct (sdt_gzip0 s tin tout adler HI) as [Hst Hdw].
    assert (Hb : bad_state s = false).
    { unfold bad_state, c_deflateStateCheck, status_ok. rewrite Hst. reflexivity. }
    split; [exact (sdt_head s z h Hb Hdw)|].
    unfold sdj. rewrite Hw2.
    split; [exact (rtk7_head_ok [] s tin tout adler h HK Hh)|].
    split; [exact (k7h_iapi [] s tin tout adler h HI Hh)|].
    split; [destruct s; exact Hwb|]. split; [destruct s; reflexivity|].
    split; [exact LO|exact Ha].
  - (* deflate *)
    intros wbits dict gh D O fin s tin tout adler inb aout flush msg (HK & HI & Hwb & Hgz & LO & Ha)
      Hfl Hb Hin Hdin Hao Hout Hfin.
    pose proof HI as (_ & _ & _ & _ & _ & Hdl & _ & _ & Ht & _ & _ & LD & (k & Hk & Htin) & _).
    pose proof (Zlength_nonneg D) as LD0. pose proof (Zlength_nonneg inb) as Li0.
    pose proof (Zlength_nonneg O) as LO0.
    unfold max_size in *.
    assert (Htin' : tin = Zlength D + k).
    { rewrite Htin. unfold u64. apply Z.mod_small. lia. }
    assert (Hfin' : forall R, fin = Some R -> flush = Z_FINISH /\ R = sublist 0 (Zlength inb) inb).
    { intros R ER. destruct (Hfin R ER) as [F1 F2]. split; [exact F1|].
      rewrite sublist_same by lia. symmetry; exact F2. }
    destruct (AD dict (rwrap_of wbits) D O fin s tin tout adler inb 0 aout flush msg HI Hfl Hb
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfin')
      as (s' & z' & code & E & G & Wb & C & A' & Hcode & Hend & Hbuf & Post).
    assert (E' : c_deflate s (rzcall inb 0 (Zlength inb) tin aout tout adler msg) flush = Some (s', z', code)).
    { rewrite <- E. rewrite Z.sub_0_r. reflexivity. }
    destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    assert (Hu : Zlength inb - z_avail_in z' = z_next_in z') by lia.
    assert (Hok : rcall_ok inb aout tin tout z').
    { unfold rcall_ok. split; [exact C1|]. split; [lia|]. split; [lia|]. split.
      { rewrite C4, Z.sub_0_r. unfold u64. rewrite Z.mod_small by lia. lia. }
      split; [lia|]. split; [exact C6|]. split; [exact C7|exact C8]. }
    assert (Hbuf' : code = Z_BUF_ERROR -> z_avail_in z' = Zlength inb /\ z_avail_out z' = aout).
    { intros Hc. destruct (Hbuf Hc) as [N1 N2]. split; [lia|exact N2]. }
    destruct (udt_k7_deflate dict (rwrap_of wbits) D O fin s tin tout adler inb aout flush msg s' z' code HK
                Hfl Hb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hfin E' G Hok Hcode Hend Hbuf')
      as (Hwb' & Fin).
    exists s', z', code. split; [exact E'|]. split; [exact Hok|]. split; [rewrite G; exact Hgz|].
    split.
    { intros A0. subst aout.
      assert (Ns : code <> Z_STREAM_ERROR) by (destruct Hcode as [-> | [-> | ->]]; discriminate).
      destruct (udt_no_out _ _ _ _ _ _ E' eq_refl Ns) as [-> ->]. split; reflexivity. }
    split; [exact Hend|].
    cbv zeta in Fin |- *. rewrite Hu in Fin |- *.
    destruct (code =? Z_STREAM_END) eqn:Ec.
    + rewrite Hwb, Hgz in Fin. exact Fin.
    + assert (Hne : code <> Z_STREAM_END) by (intros X; rewrite X, Z.eqb_refl in Ec; discriminate).
      specialize (Post Hne).
      split; [exact Fin|]. split; [exact Post|]. split; [rewrite Wb; exact Hwb|].
      split; [rewrite G; exact Hgz|].
      split; [rewrite Zlength_app; unfold max_size; lia|]. apply A'; exact Ha.
Qed.

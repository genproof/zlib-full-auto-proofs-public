(** * The deflateBound accounting for compress2_z's loop (LawFactsC2W.c2_facts)

    [BpreC2] / [BrunC2] (LTWC2Defs) with: deflateInit2_ (LTWBInit), the start at compressBound_z(n)
    (LTWC2Defs.c2_start), and one call of the loop: LTWC2Walk.walk_c2 on the bytes offered, cut out of the source
    (InSlice.zslice), moved back to the source by InUnslice.deflate_unslice.  For any core invariant [W] with the
    compression call at every level and flush ([CC], LTWIface.cw_compress) and its progress ([PROG],
    LTWC2Prog.compress_progress). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LawFactsC2W Zlib.proof.deflate.LTWBInit Zlib.proof.deflate.LTWBound.
Require Import Zlib.proof.deflate.LTWC2Walk.
Require Import Zlib.proof.deflate.InSlice Zlib.proof.deflate.InUnslice.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Section C2.
Context (W : dstate -> Prop) (HI : hdr_inv) (CF : core_facts_w W) (HF : hdr_facts_w HI)
  (BB : block_bound_statement).

Hypothesis CC : forall s z flush,
  W s -> outok s -> quiet s -> 0 <= flush <= 5 -> zin_okw z ->
  0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
  exists s' z' bs evs, c_compress_func s z flush = Some (s', z', bs) /\ cpost W s z flush s' z' bs evs.

Hypothesis PROG : forall s z flush s' z' bs,
  W s -> outok s -> quiet s -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> zin_okw z ->
  0 <= d_wrap s <= 2 -> adler_pre (d_wrap s) (z_adler z) ->
  c_compress_func s z flush = Some (s', z', bs) -> bs = need_more ->
  0 < z_avail_out z -> (0 < z_avail_in z \/ flush = Z_FINISH) ->
  z_avail_in z' < z_avail_in z \/ z_avail_out z' < z_avail_out z.

(** A bound above 2^32-1 is that of a stream of at least 2^25 bytes. *)
Lemma c2_big_n : forall n b pos fin s tin tout adler,
  BrunC2 W HI n b pos fin s tin tout adler -> 4294967295 < b -> 33554432 <= n.
Proof.
  intros n b pos fin s tin tout adler (_ & _ & _ & Hbn) Hbig. exact (Hbn Hbig).
Qed.

(** The call of compress2_z's loop on the source [inb] at offset [nin]. *)
Lemma c2_split : forall n b pos fin s tin tout adler inb nin ain aout flush msg,
  BrunC2 W HI n b pos fin s tin tout adler ->
  (flush = Z_NO_FLUSH \/ flush = Z_FINISH) -> (fin = true -> flush = Z_FINISH) ->
  bytes inb -> 0 <= nin -> 0 <= ain <= 4294967295 -> nin + ain <= Zlength inb ->
  pos + ain <= n -> (flush = Z_FINISH -> pos + ain = n) -> 0 <= aout <= 4294967295 ->
  exists s' z' code,
    c_deflate s (mkST inb nin ain tin [] aout tout adler msg) flush = Some (s', z', code) /\
    d_gzhead s' = d_gzhead s /\
    z_in z' = inb /\ 0 <= z_avail_in z' <= ain /\ z_next_in z' = nin + (ain - z_avail_in z') /\
    0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\ bytes (z_out z') /\
    z_total_in z' = tin + (ain - z_avail_in z') /\ z_total_out z' = tout + (aout - z_avail_out z') /\
    z_total_out z' <= b /\
    (code = Z_OK \/ code = Z_BUF_ERROR \/ code = Z_STREAM_END) /\
    (code = Z_BUF_ERROR -> aout = 0 \/ (ain = 0 /\ flush = Z_NO_FLUSH)) /\
    (code = Z_OK -> 0 < aout -> (0 < ain \/ flush = Z_FINISH) ->
     0 < (ain - z_avail_in z') + (aout - z_avail_out z')) /\
    (4294967295 < b -> code = Z_OK -> z_avail_out z' = 0 -> z_total_out z' < b) /\
    (flush = Z_FINISH -> fin = false -> pos = 0 -> b <= tout + aout -> code = Z_STREAM_END) /\
    (code = Z_STREAM_END -> flush = Z_FINISH /\ z_avail_in z' = 0) /\
    (code <> Z_STREAM_END ->
     BrunC2 W HI n b (pos + (ain - z_avail_in z')) (flush =? Z_FINISH) s' (z_total_in z') (z_total_out z')
       (z_adler z')).
Proof.
  intros n b pos fin s tin tout adler inb nin ain aout flush msg HB Hfl Hfin Hinb Hnin Hain Hle Hpn HpF Ha.
  set (sm := sublist nin (nin + ain) inb).
  assert (Hsm : Zlength sm = ain) by (unfold sm; rewrite Zlength_sublist; lia).
  assert (Hbs : bytes sm) by (unfold sm, bytes in *; apply Forall_sublist; exact Hinb).
  destruct (walk_c2 W HI CF HF BB CC PROG n b pos fin s tin tout adler sm aout flush msg HB Hfl Hfin Hbs
              ltac:(lia) ltac:(intros E; specialize (HpF E); lia) Ha ltac:(lia))
    as (s' & z1 & code & E & Hgz & Hcf & Hai0 & Htb & Hcode & Hbuf & Hprog & Hstr & Honce & Hend & Hrun).
  set (z := mkST inb nin ain tin [] aout tout adler msg).
  assert (Ez : zcall sm 0 (Zlength sm) tin aout tout adler msg = zslice nin ain z).
  { rewrite Hsm. unfold zcall, zslice, z, sm. cbn. rewrite Z.sub_diag. reflexivity. }
  rewrite Ez in E.
  destruct (deflate_unslice_in nin ain s z flush s' z1 code ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              ltac:(cbn; lia) E) as (z' & E' & -> & Hzin).
  destruct Hcf as (_ & Hni & Hsum & Hti & Hao & Hol & Hto & Hby).
  unfold zslice in Hai0, Hni, Hsum, Hti, Hao, Hol, Hto, Hby, Htb, Hprog, Hstr, Hend, Hrun.
  cbn [z_in z_next_in z_avail_in z_total_in z_out z_avail_out z_total_out z_adler z_msg] in *.
  rewrite Hsm in Hsum, Hbuf, Hrun, Hprog.
  pose proof (Zlength_nonneg (z_out z')).
  exists s', z', code. split; [exact E'|]. split; [exact Hgz|]. split; [exact Hzin|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hby|].
  split; [lia|]. split; [lia|]. split; [exact Htb|]. split; [exact Hcode|].
  split; [exact Hbuf|].
  split; [intros Hc Hp Hi; specialize (Hprog Hc Hp Hi); lia|].
  split; [intros Hbig; apply Hstr; exact (c2_big_n _ _ _ _ _ _ _ _ HB Hbig)|].
  split; [exact Honce|]. split; [exact Hend|].
  intros Hne. specialize (Hrun Hne).
  replace (pos + (ain - z_avail_in z')) with (pos + ain - z_avail_in z') by lia. exact Hrun.
Qed.

Theorem c2_facts_of : c2_facts (BpreC2 W) (BrunC2 W HI).
Proof.
  constructor.
  - intros level a1 a2 a3 a4 a5 z Hl.
    assert (P : params_ok level 8 15 8 0 = true).
    { unfold params_ok, wb_of, wrap_of; cbn.
      destruct (Z.eqb_spec level (-1)); [reflexivity|].
      destruct (Z.leb_spec 0 level), (Z.leb_spec level 9); cbn; try reflexivity; lia. }
    destruct (bpre_init_w W CF level 15 8 0 a1 a2 a3 a4 a5 z P) as [Hex Hok].
    split; [exact Hex|].
    intros os z' code Ei Ec. destruct (Hok os z' code Ei Ec) as (s & Es & Hgz & HP).
    exists s. split; [exact Es|]. split; [exact Hgz|]. split; [exact HP|exact Hgz].
  - intros level s tin tout adler n HP _ Hn. exact (c2_start W HI CF level s tin tout adler n HP Hn).
  - intros. eapply c2_range; eauto.
  - intros. eapply c2_split; eauto.
Qed.

End C2.

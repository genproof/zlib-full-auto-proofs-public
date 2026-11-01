(** * The deflateBound accounting for compress2_z's loop: the invariant between the calls, and its start

    [BrunC2] is LTWBDefs.BrunW with the margin [mg]: for n >= 2^25, once the last block is out (FINISH_STATE),
    the bytes handed out, the pending bytes and the trailer still to put stay strictly below deflateBound.
    (LTWBEvent.chain_acct_w: the last block leaves a margin of a bit for n >= 2^25, and at the end of the last
    block the bit buffer is empty, so the margin is a byte.)  compress2_z needs it when its output space is cut
    into pieces (a bound above 2^32-1): a call that fills its output space before the end of the stream must
    leave destination bytes for the next one.

    The start of the accounting: deflateBound of compress2_z's stream (zlib wrapper, windowBits 15, memLevel 8,
    the default strategy, no dictionary) is compressBound_z(n) for any n < 2^63. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTWBInit Zlib.proof.deflate.LTWBound Zlib.proof.deflate.LTWBKit.
Require Export Zlib.proof.deflate.LTWBDefs.
Import ListNotations.
Local Open Scope Z_scope.

(** The trailer still to put: none once it is put (wrap < 0). *)
Definition tleft (s : dstate) : Z := if 0 <? d_wrap s then tlen (d_wrap s) else 0.

Definition mg (n b : Z) (s : dstate) (tout : Z) : Prop :=
  33554432 <= n -> d_status s = FINISH_STATE -> tout + d_pending s + tleft s < b.

(** [BrunC2] adds to [BrunW] the margin, that the stream has no gzip header, and that a bound above 2^32-1 is that
    of at least 2^25 bytes (compressBound_z(n) < 2^26 for n < 2^25). *)

(** compress2_z's stream has no gzip header (deflateInit2_ without deflateSetHeader). *)
Definition BpreC2 (W : dstate -> Prop) (level wbits mem strategy : Z) (ds : bool) (s : dstate)
    (tin tout adler : Z) : Prop :=
  BpreW W level wbits mem strategy ds s tin tout adler /\ d_gzhead s = None.

Definition BrunC2 (W : dstate -> Prop) (HI : hdr_inv) (n b pos : Z) (fin : bool) (s : dstate)
    (tin tout adler : Z) : Prop :=
  BrunW W HI n b pos fin s tin tout adler /\ mg n b s tout /\ d_gzhead s = None /\
  (4294967295 < b -> 33554432 <= n).

(** compress2_z's stream after deflateInit2_: the zlib header has 2 bytes, the class is the tight one. *)
Lemma c2_bound_val : forall W level s tin tout adler n,
  BpreW W level 15 8 0 false s tin tout adler -> 0 <= n <= 9223372036854775807 ->
  Zlength (hdr_bytes s adler) + body (bcls_of s) n + tlen (d_wrap s) = compressBound_z n.
Proof.
  intros W level s tin tout adler n HB Hn.
  destruct HB as (HW & Ho & Hpo & Hst & Hwr & Hpd & Hpo0 & Hbi & Hsym & Hla & Hss & Hds & Hlv & Hsg & Hwb & Hhb &
                  Hgz & Hlf & Ht & Hti & Had).
  cbn in Hwr, Hwb. destruct (Hds eq_refl) as [Hs0 _].
  assert (EH : Zlength (hdr_bytes s adler) = 2).
  { unfold hdr_bytes, zlib_hdr_bytes. rewrite Hwr, Hs0. cbn. reflexivity. }
  assert (EC : bcls_of s = BTight).
  { unfold bcls_of, tight_b. rewrite Hwb, Hhb, Hsg. reflexivity. }
  rewrite EH, EC, Hwr. unfold body, tlen, compressBound_z. cbn [Z.eqb Pos.eqb].
  assert (Hs : 0 <= Z.shiftr n 12 /\ 4096 * Z.shiftr n 12 <= n /\ 0 <= Z.shiftr n 14 /\
                16384 * Z.shiftr n 14 <= n /\ 0 <= Z.shiftr n 25 /\ 33554432 * Z.shiftr n 25 <= n).
  { rewrite !Z.shiftr_div_pow2 by lia.
    repeat split; first [apply Z.div_pos; lia | apply Z.mul_div_le; lia]. }
  unfold u64. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (n + Z.shiftr n 12 + Z.shiftr n 14 + Z.shiftr n 25 + 13) n); lia.
Qed.

(** The accounting starts at compressBound_z(n): phase P0, nothing written. *)
Lemma c2_start : forall W HI, core_facts_w W ->
  forall level s tin tout adler n,
  BpreC2 W level 15 8 0 false s tin tout adler -> 0 <= n <= 9223372036854775807 ->
  tout = 0 /\ BrunC2 W HI n (compressBound_z n) 0 false s tin tout adler.
Proof.
  intros W HI CF level s tin tout adler n [HB Hgz] Hn.
  pose proof (c2_bound_val W level s tin tout adler n HB Hn) as Ev.
  destruct (bound_of_bpre_w W HI CF level 15 8 0 false s tin tout adler n HB Hn) as (b & Eb & Hb & HR).
  pose proof HB as (_ & _ & _ & Hst & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  assert (Eb' : b = compressBound_z n).
  { destruct HR as (H & w0 & _ & _ & _ & Hbe & _ & _ & _ & _ & _ & _ & _ & Hph).
    destruct Hph as [P|[P|[P|P]]].
    - destruct P as (_ & Hw & HH & _). rewrite Hbe, HH, <- Hw. exact Ev.
    - exfalso. destruct P as (_ & Hw2 & _). pose proof HB as (_ & _ & _ & _ & Hwr & _). cbn in Hwr. lia.
    - exfalso. destruct P as (Hs & _). rewrite Hst in Hs. cbn in Hs. discriminate.
    - exfalso. destruct P as (Hs & _). rewrite Hst in Hs. cbn in Hs. discriminate. }
  subst b. split; [exact Ht|]. split; [exact HR|]. split; [|split; [exact Hgz|]].
  - intros _ Hs. rewrite Hst in Hs. cbn in Hs. discriminate.
  - intros Hbig. rewrite <- Ev in Hbig.
    pose proof HB as (_ & _ & _ & _ & Hwr & _). cbn in Hwr.
    assert (EH : Zlength (hdr_bytes s adler) <= 2).
    { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hds & _). destruct (Hds eq_refl) as [Hs0 _].
      unfold hdr_bytes, zlib_hdr_bytes. rewrite Hwr, Hs0. cbn. lia. }
    pose proof (body_range_w (bcls_of s) n (proj1 Hn)).
    assert (n / 4 <= n) by (apply Z.div_le_upper_bound; lia).
    rewrite Hwr in Hbig. unfold tlen in Hbig. cbn in Hbig. lia.
Qed.

(** What [BrunC2] says of the position and of the output so far. *)
Lemma c2_range : forall W HI, core_facts_w W -> hdr_facts_w HI ->
  forall n b pos fin s tin tout adler,
  BrunC2 W HI n b pos fin s tin tout adler -> 0 <= pos <= n /\ 0 <= tout <= b.
Proof.
  intros W HI CF HF n b pos fin s tin tout adler [HB _].
  destruct (brunw_facts _ HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & _ & Ht & Htb & _ & Hpos & _). lia.
Qed.

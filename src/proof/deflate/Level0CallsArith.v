(** * Level 0 over several deflate() calls: the counts of blocks and the output space of each call

    The harnesses' loop gives each call [l0_clip (room - |O|)] bytes of output space, where [room >= l0_size] and
    [O] is the output so far.  These lemmas say that the space covers what the call writes: the header (first
    call), [k] blocks of 65540 bytes (a Z_NO_FLUSH call given [k <= 65532] blocks) or the stored blocks of the
    rest (the Z_FINISH call), and the trailer, except in one case: with gzip (10 + 8 wrapper bytes) and all the
    data in the first call, the trailer may not fit in 2^32 - 1 bytes ([l0_cut_gzip]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Calls.
Require Import Zlib.proof.deflate.LTDefs.
Require Import Zlib.proof.deflate.LTCSpecs.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Blocks *)

Lemma l0_blocks_le n k : 1 <= k -> 0 <= n <= 65535 * k -> l0_blocks n <= k.
Proof.
  intros Hk Hn. unfold l0_blocks. destruct (Z.eqb_spec n 0); [lia|].
  assert ((n + 65534) / 65535 < k + 1) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma l0_blocks_split n i : 0 <= i -> 65535 * i < n -> l0_blocks n = i + l0_blocks (n - 65535 * i).
Proof.
  intros Hi Hn. unfold l0_blocks.
  destruct (Z.eqb_spec n 0); [lia|]. destruct (Z.eqb_spec (n - 65535 * i) 0); [lia|].
  replace (n + 65534) with ((n - 65535 * i + 65534) + i * 65535) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

Lemma l0_blocks_gt n j : 0 <= j -> 65535 * j < n -> j + 1 <= l0_blocks n.
Proof.
  intros Hj Hn. rewrite (l0_blocks_split n j) by lia.
  pose proof (l0_blocks_pos (n - 65535 * j)). lia.
Qed.

Lemma l0_clip_ge a b : b <= a -> b <= 4294967295 -> b <= l0_clip a.
Proof. unfold l0_clip. lia. Qed.

(** ** The output space of the calls ([hl], [tl]: the wrapper's header and trailer lengths) *)

(** The first call, Z_NO_FLUSH with [k] blocks (more data follows): the header and the [k] blocks fit. *)
Lemma l0_space_first_nf hl tl n room :
  0 <= hl <= 10 -> 0 <= tl <= 8 -> hl + 5 * l0_blocks n + n + tl <= room ->
  forall k, 1 <= k <= 65532 -> 65535 * k < n -> hl + 65540 * k + 5 <= l0_clip room.
Proof.
  intros Hhl Htl Hroom k Hk Hnk. apply l0_clip_ge; [|lia].
  pose proof (l0_blocks_gt n k ltac:(lia) Hnk). lia.
Qed.

(** The first call, Z_FINISH: the header and the stored blocks fit. *)
Lemma l0_space_first_fin hl tl n room :
  0 <= hl <= 10 -> 0 <= tl <= 8 -> 0 <= n -> hl + 5 * l0_blocks n + n + tl <= room ->
  forall k, 1 <= k <= 65532 -> n <= 65535 * k -> hl + 5 * l0_blocks n + n <= l0_clip room.
Proof.
  intros Hhl Htl Hn Hroom k Hk Hnk. apply l0_clip_ge; [lia|].
  pose proof (l0_blocks_le n k ltac:(lia) ltac:(lia)). lia.
Qed.

(** The trailer of the first Z_FINISH call is cut only with 18 wrapper bytes (gzip) and 2^32 - 1 bytes of space. *)
Lemma l0_cut_gzip hl tl n room :
  0 <= n -> hl + 5 * l0_blocks n + n + tl <= room ->
  forall k, 1 <= k <= 65532 -> n <= 65535 * k ->
  l0_clip room < hl + 5 * l0_blocks n + n + tl -> l0_clip room = 4294967295 /\ 15 < hl + tl.
Proof.
  intros Hn Hroom k Hk Hnk Hlt.
  pose proof (l0_blocks_le n k ltac:(lia) ltac:(lia)). unfold l0_clip in *. lia.
Qed.

(** A later call, after the header and [i] blocks ([|O| = hl + 65540 i]), Z_NO_FLUSH with [k] blocks. *)
Lemma l0_space_busy_nf hl tl n room :
  0 <= tl <= 8 -> hl + 5 * l0_blocks n + n + tl <= room ->
  forall i k, 0 <= i -> 1 <= k <= 65532 -> 65535 * (i + k) < n ->
  65540 * k + 5 <= l0_clip (room - (hl + 65540 * i)).
Proof.
  intros Htl Hroom i k Hi Hk Hnk. apply l0_clip_ge; [|lia].
  pose proof (l0_blocks_gt n (i + k) ltac:(lia) Hnk). lia.
Qed.

(** A later call, Z_FINISH with the rest [n - 65535 i <= 65535 k]: the stored blocks of the rest and the trailer fit. *)
Lemma l0_space_busy_fin hl tl n room :
  0 <= tl <= 8 -> hl + 5 * l0_blocks n + n + tl <= room ->
  forall i k, 0 <= i -> 1 <= k <= 65532 -> 65535 * i < n -> n - 65535 * i <= 65535 * k ->
  5 * l0_blocks (n - 65535 * i) + (n - 65535 * i) + tl <= l0_clip (room - (hl + 65540 * i)).
Proof.
  intros Htl Hroom i k Hi Hk Hn1 Hn2.
  pose proof (l0_blocks_split n i Hi Hn1).
  pose proof (l0_blocks_le (n - 65535 * i) k ltac:(lia) ltac:(lia)).
  apply l0_clip_ge; lia.
Qed.

(** ** strm->adler *)

(** After the header: 1 for zlib, 0 for gzip. *)
Lemma adler_ok_hdr w a : adler_ok w (if w =? 1 then 1 else if w =? 2 then 0 else a).
Proof.
  split; intros ->; cbn.
  - unfold Zlib.proof.adler32.Model.adler_valid. vm_compute. repeat split; congruence.
  - lia.
Qed.

(** strm->adler stays a 64-bit value. *)
Lemma adler_range_zstep w z z' k x :
  0 <= w <= 2 -> zstep w z z' k x -> adler_ok w (z_adler z') -> 0 <= z_adler z <= 18446744073709551615 ->
  0 <= z_adler z' <= 18446744073709551615.
Proof.
  intros Hw (_ & _ & _ & _ & _ & E & _) (A1 & A2) Ha.
  destruct (Z.eq_dec w 1) as [->|N1]; [destruct (A1 eq_refl) as (R & _); lia|].
  destruct (Z.eq_dec w 2) as [->|N2]; [specialize (A2 eq_refl); lia|].
  rewrite E. unfold adler_upd. replace (w =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (w =? 2) with false by (symmetry; apply Z.eqb_neq; lia). exact Ha.
Qed.

(** ** What [Level0Calls.lf_call] says of the stream after a call given [inb], [aout] bytes of output space and
    the counters [tin], [tout] *)
Definition l0_zres (inb : list Z) (tin aout tout : Z) (z' : strm) : Prop :=
  z_in z' = inb /\
  0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
  z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
  0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
  z_total_out z' = tout + (aout - z_avail_out z') /\ bytes (z_out z').

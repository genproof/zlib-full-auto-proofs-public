(** * Level 0 over several deflate() calls: the invariant at the head of the harnesses' loop

    The loop of harness/rfc_level0_size.c and harness/rfc_level0_blocks.c (Level0Calls.v) passes through three
    kinds of states, given the n bytes of [data], the [room] of the output object, the bytes consumed [pos] and the
    bytes produced [O]:
    - [l0_stA]: before the first call, the state deflateInit2_ leaves (nothing consumed, nothing produced);
    - [l0_stB]: after calls with Z_NO_FLUSH, each given whole blocks of 65535 bytes: [j] blocks consumed, some
      data left, [O] is the wrapper header and the [j] non-final stored blocks ([Level0CallsBlocks.nblocks]), the
      stream ready for the next call ([Level0CallsComp.l0_ready]);
    - [l0_stC]: gzip only, after a first call given all the data with Z_FINISH whose trailer did not fit in its
      2^32 - 1 bytes of output space: [O] is the header, the stored blocks of the data and the first bytes of the
      trailer, the others pending ([Level0CallsTrail.l0_pend]).
    [l0_com] holds in all three: the bounds of the data and of room (room covers [l0_size]), total_in = pos,
    total_out = |O|, the bytes, no gzip header, a 32-bit checksum.  [l0_inv] is the invariant; [l0_inv_init]
    starts it after deflateInit2_ and [l0_inv_range] gives the bounds the mains need, in particular |O| < room:
    the output of each state is shorter than the whole output. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Calls.
Require Export Zlib.proof.deflate.Level0CallsTrail.
Require Export Zlib.proof.deflate.Level0CallsArith.
Require Import Zlib.proof.deflate.Level0.
Import ListNotations.
Local Open Scope Z_scope.

(** What holds at the head of the loop in every state. *)
Definition l0_com (wbits : Z) (data : list Z) (room pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    : Prop :=
  bytes data /\ Zlength data <= l0_max_size /\ l0_size wbits (Zlength data) <= room <= l0_max_u64 /\
  tin = pos /\ tout = Zlength O /\ bytes O /\ d_gzhead s = None /\ 0 <= adler <= l0_max_u64.

(** Before the first call: the state of [Level0.l0_init]. *)
Definition l0_stA (wbits pos : Z) (O : list Z) (s : dstate) (adler : Z) : Prop :=
  pos = 0 /\ O = [] /\
  W s /\ outok s /\
  d_status s = (if wrap_of wbits =? 2 then GZIP_STATE else INIT_STATE) /\ d_wrap s = wrap_of wbits /\
  d_last_flush s = -2 /\ d_po s = 0 /\ d_pending s = 0 /\ d_bi_valid s = 0 /\
  d_strstart s = 0 /\ d_block_start s = 0 /\ d_sym_next s = 0 /\ d_level s = 0 /\
  adler = (if wrap_of wbits =? 2 then 0 else 1).

(** After [j >= 1] whole blocks written by Z_NO_FLUSH calls, some data left. *)
Definition l0_stB (wbits : Z) (data : list Z) (pos : Z) (O : list Z) (s : dstate) (adler : Z) : Prop :=
  exists j H,
    l0_ready s /\ d_wrap s = wrap_of wbits /\ adler_ok (d_wrap s) adler /\
    pos = 65535 * Z.of_nat j /\ 0 < pos < Zlength data /\
    O = H ++ nblocks 0 j data /\ Zlength H = l0_hlen wbits /\ bytes H.

(** All the data consumed, the trailer cut: its first bytes [T1] written, the others pending. *)
Definition l0_stC (wbits : Z) (data : list Z) (pos : Z) (O : list Z) (s : dstate) : Prop :=
  exists H T1,
    l0_pend s /\ pos = Zlength data /\
    O = H ++ stored_blocks data ++ T1 /\ Zlength H = l0_hlen wbits /\
    Zlength T1 + d_pending s = l0_tlen wbits /\ Zlength O = 4294967295.

Definition l0_inv (wbits : Z) (data : list Z) (room pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    : Prop :=
  l0_com wbits data room pos O s tin tout adler /\
  (l0_stA wbits pos O s adler \/ l0_stB wbits data pos O s adler \/ l0_stC wbits data pos O s).

(** The output at Z_STREAM_END: the header, the stored blocks of the data, the trailer, total_out = l0_size. *)
Definition l0_done (wbits : Z) (data : list Z) (O : list Z) (tout : Z) : Prop :=
  exists H T, O = H ++ stored_blocks data ++ T /\
    Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\ tout = l0_size wbits (Zlength data).

(** One iteration of the loop from a state of the invariant, with [k] blocks drawn: the run is defined, the
    stream moves as Level0Calls.lf_call says, Z_OK keeps the invariant (and [Pc] when the new state is a cut
    trailer), any other code is Z_STREAM_END with the whole output. *)
Definition l0_call_post (wbits : Z) (data : list Z) (room pos : Z) (O : list Z) (s : dstate) (tin tout adler : Z)
    (msg : option Z) (k : Z) (Pc : Prop) : Prop :=
  let inb := l0_inb data pos k in
  let aout := l0_clip (room - Zlength O) in
  exists s' z' code,
    c_deflate s (zcall inb 0 (Zlength inb) tin aout tout adler msg) (l0_flush (Zlength data) pos k) =
      Some (s', z', code) /\
    z_in z' = inb /\
    0 <= z_avail_in z' <= Zlength inb /\ z_next_in z' = Zlength inb - z_avail_in z' /\
    z_total_in z' = tin + (Zlength inb - z_avail_in z') /\
    0 <= z_avail_out z' <= aout /\ Zlength (z_out z') = aout - z_avail_out z' /\
    z_total_out z' = tout + (aout - z_avail_out z') /\ bytes (z_out z') /\
    d_gzhead s' = None /\
    (code = Z_OK ->
       l0_inv wbits data room (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
         (z_total_in z') (z_total_out z') (z_adler z') /\
       (l0_stC wbits data (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s' -> Pc)) /\
    (code <> Z_OK -> code = Z_STREAM_END /\ l0_done wbits data (O ++ z_out z') (z_total_out z')).

(** ** Arithmetic of the sizes *)

Lemma l0_hlen_range wbits : 0 <= l0_hlen wbits <= 10.
Proof. unfold l0_hlen. destruct (wbits <? 0); [lia|]. destruct (wbits >? 15); lia. Qed.

Lemma l0_tlen_range wbits : 0 <= l0_tlen wbits <= 8.
Proof. unfold l0_tlen. destruct (wbits <? 0); [lia|]. destruct (wbits >? 15); lia. Qed.

Lemma l0_size_eq wbits n : l0_size wbits n = l0_hlen wbits + 5 * l0_blocks n + n + l0_tlen wbits.
Proof. reflexivity. Qed.

(** ** The invariant after deflateInit2_ *)

Lemma l0_inv_init vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room :
  c_deflateInit2_ vok sok snull 0 Z_DEFLATED wbits mem strategy a1 a2 a3 a4 a5 z0 = Some (os, z1, Z_OK) ->
  bytes data -> Zlength data <= l0_max_size ->
  l0_size wbits (Zlength data) <= room <= l0_max_u64 ->
  exists s, os = Some s /\ l0_inv wbits data room 0 [] s (z_total_in z1) (z_total_out z1) (z_adler z1).
Proof.
  intros Hi Hb Hn Hr.
  destruct (l0_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hi)
    as (s & -> & HW & Ho & Hst & Hwr & Hgz & Hlf & Hpo & Hpe & Hbv & Hss & Hbs & Hsn & Hlv & ->).
  exists s. split; [reflexivity|]. cbn [z_total_in z_total_out z_adler].
  assert (Ha : 0 <= (if wrap_of wbits =? 2 then 0 else 1) <= l0_max_u64)
    by (unfold l0_max_u64; destruct (_ =? _); lia).
  split.
  - unfold l0_com. rewrite Zlength_nil. repeat split; auto; try lia. apply Forall_nil.
  - left. unfold l0_stA.
    do 14 (split; [assumption || reflexivity|]). reflexivity.
Qed.

(** ** The bounds at the head of the loop *)

Lemma l0_inv_range wbits data room pos O s tin tout adler :
  l0_inv wbits data room pos O s tin tout adler ->
  0 <= pos <= Zlength data /\ Zlength data <= l0_max_size /\ 0 <= Zlength O < room /\ room <= l0_max_u64 /\
  bytes data /\ bytes O /\ d_gzhead s = None /\
  0 <= tin <= l0_max_u64 /\ 0 <= tout <= l0_max_u64 /\ 0 <= adler <= l0_max_u64.
Proof.
  intros [(Hb & Hn & Hr & -> & -> & HbO & Hgz & Ha) Hst].
  pose proof (Zlength_nonneg data) as L1. pose proof (Zlength_nonneg O) as L2.
  pose proof (l0_hlen_range wbits) as L3. pose proof (l0_tlen_range wbits) as L4.
  pose proof (l0_blocks_pos (Zlength data) ltac:(lia)) as L5.
  unfold l0_max_size, l0_max_u64 in *. rewrite l0_size_eq in Hr.
  assert (pos_ok : 0 <= pos <= Zlength data /\ Zlength O < l0_size wbits (Zlength data)).
  { rewrite l0_size_eq.
    destruct Hst as [(-> & -> & _)|[(j & Hd & _ & _ & _ & -> & Hp & -> & HH & _)|
                                    (Hd & T1 & (_ & _ & _ & _ & _ & _ & _ & Hpd & _) & -> & -> & HH & HT & _)]].
    - rewrite Zlength_nil. lia.
    - rewrite Zlength_app, Zlength_nblocks by lia.
      pose proof (l0_blocks_gt (Zlength data) (Z.of_nat j) ltac:(lia) ltac:(lia)) as L6. lia.
    - rewrite !Zlength_app, Zlength_stored_blocks. lia. }
  rewrite l0_size_eq in pos_ok.
  repeat split; auto; lia.
Qed.

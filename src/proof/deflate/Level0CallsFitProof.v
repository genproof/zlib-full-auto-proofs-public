(** * Level 0 over several deflate() calls when the trailer always fits: the facts of Level0CallsFit.v from
    the model of deflate *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0CallsFit.
Require Import Zlib.proof.deflate.Level0CallsCallA.
Require Import Zlib.proof.deflate.Level0CallsCallB.
Require Import Zlib.proof.deflate.Level0CallsEnd.
Import ListNotations.
Local Open Scope Z_scope.

(** The invariant is [Level0CallsInv.l0_inv] (the state before the first call, after whole blocks, or after a
    first call whose gzip trailer was cut) with room at least size + slack, and a cut trailer only when the
    slack is at least one byte.  The calls: [Level0CallsCallA.l0_callA] (the first), [Level0CallsCallB.l0_callB]
    (after whole blocks), [Level0CallsEnd.l0_callC] (after a cut trailer: the room left is the pending bytes
    plus the slack, more than the pending bytes, so the call flushes them and returns Z_STREAM_END).  A trailer
    is cut only when the first call writes more than 2^32 - 1 bytes, i.e. with gzip and 65532 blocks or more
    ([l0_cut_blocks]); the harness gives at most [kmax] blocks per call, so then [kmax = 65532] and the slack
    is at least one byte. *)

(** [n] bytes fill at most [l0_blocks n] blocks of 65535 bytes. *)
Lemma l0_blocks_cover n : 0 <= n -> n <= 65535 * l0_blocks n.
Proof.
  intros Hn. unfold l0_blocks. destruct (Z.eqb_spec n 0); [lia|].
  pose proof (Z.div_mod (n + 65534) 65535 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 65534) 65535 ltac:(lia)).
  lia.
Qed.

(** A cut trailer means at least 65532 blocks of data: fewer give at most 18 + 65531 * 65540 < 2^32 - 1 bytes. *)
Lemma l0_cut_blocks wbits data pos O s :
  l0_stC wbits data pos O s -> 65532 <= l0_blocks (Zlength data).
Proof.
  intros (H & T1 & Hp & _ & -> & HH & HT & LO).
  pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & Hp0 & _).
  pose proof (l0_hlen_range wbits). pose proof (l0_tlen_range wbits).
  pose proof (Zlength_nonneg data). pose proof (l0_blocks_cover (Zlength data) ltac:(lia)).
  rewrite !Zlength_app, Zlength_stored_blocks in LO. lia.
Qed.

(** The invariant of the loop for [slack]. *)
Definition l0_fit_J (slack : Z) (wbits : Z) (data : list Z) (room pos : Z) (O : list Z) (s : dstate)
    (tin tout adler : Z) : Prop :=
  l0_inv wbits data room pos O s tin tout adler /\ l0_size wbits (Zlength data) + slack <= room /\
  (l0_stC wbits data pos O s -> 1 <= slack).

(** From [l0_call_post] to the facts of one iteration ([ff_call]'s conclusion). *)
Lemma l0_fit_post kmax slack wbits data room pos O s tin tout adler msg k Pc :
  1 <= kmax <= 65532 -> (kmax <= 65531 \/ 1 <= slack) -> l0_size wbits (Zlength data) + slack <= room ->
  (Pc -> l0_blocks (Zlength data) <= kmax) ->
  l0_call_post wbits data room pos O s tin tout adler msg k Pc ->
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
       l0_fit_J slack wbits data room (pos + (Zlength inb - z_avail_in z')) (O ++ z_out z') s'
         (z_total_in z') (z_total_out z') (z_adler z')) /\
    (code <> Z_OK ->
       code = Z_STREAM_END /\
       exists H T, O ++ z_out z' = H ++ stored_blocks data ++ T /\
         Zlength H = l0_hlen wbits /\ Zlength T = l0_tlen wbits /\
         z_total_out z' = l0_size wbits (Zlength data)).
Proof.
  intros Hk Hor Hsl HPc P. unfold l0_call_post in P. cbv zeta in *.
  destruct P as (s' & z' & code & E & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & Fok & Fend).
  exists s', z', code.
  do 10 (split; [assumption|]).
  split; [|exact Fend].
  intros Ec. destruct (Fok Ec) as [Hi Hc].
  split; [exact Hi|]. split; [exact Hsl|].
  intros C. pose proof (l0_cut_blocks _ _ _ _ _ C). pose proof (HPc (Hc C)). lia.
Qed.

Theorem l0_fit_thm : l0_fit_stmt.
Proof.
  intros kmax slack Hk Hs Hor.
  exists (l0_fit_J slack). constructor.
  - intros vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room Hi Hb Hn Hr.
    destruct (l0_inv_init vok sok snull wbits mem strategy a1 a2 a3 a4 a5 z0 os z1 data room Hi Hb Hn
                ltac:(lia)) as (s & Es & HI).
    exists s. split; [exact Es|]. split; [exact HI|]. split; [lia|].
    intros (H & T1 & _ & _ & _ & _ & _ & LO). rewrite Zlength_nil in LO. lia.
  - intros wbits data room pos O s tin tout adler (HI & _ & _). exact (l0_inv_range _ _ _ _ _ _ _ _ _ HI).
  - intros wbits data room pos O s tin tout adler msg k (HI & Hsl & HC) Hkk.
    pose proof HI as [Hcom [HA|[HB|HC']]].
    + apply (l0_fit_post kmax slack _ _ _ _ _ _ _ _ _ _ _ (l0_blocks (Zlength data) <= k) ltac:(lia) Hor Hsl
               ltac:(lia)).
      apply l0_callA; [exact Hcom|exact HA|lia].
    + apply (l0_fit_post kmax slack _ _ _ _ _ _ _ _ _ _ _ False ltac:(lia) Hor Hsl ltac:(intros [])).
      apply l0_callB; [exact Hcom|exact HB|lia].
    + apply (l0_fit_post kmax slack _ _ _ _ _ _ _ _ _ _ _ False ltac:(lia) Hor Hsl ltac:(intros [])).
      apply l0_callC; [exact Hcom|exact HC'|lia|].
      pose proof (HC HC') as Hs1.
      destruct HC' as (H & T1 & Hp & _ & HO & HH & HT & _).
      pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & Hp0 & _).
      pose proof (l0_tlen_range wbits). pose proof (Zlength_nonneg T1).
      assert (LO : Zlength O + d_pending s = l0_size wbits (Zlength data))
        by (rewrite HO, !Zlength_app, Zlength_stored_blocks, l0_size_eq; lia).
      unfold l0_clip. lia.
Qed.

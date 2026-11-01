(** * The deflateBound accounting without the size limits of the deflate laws

    [bound_theory_w]: LawFactsW.bound_facts_w (res_bound, and compress2_z's loop for res_compress_bound) from the
    core and header parts (LTWIface) and lemma (ii) (BlockBound.block_bound_statement: the per-block cost for the
    tight bound).  The accounting is that of LTBound.bound_theory (LTBDefs.v: the classes, [xb], [acct]) for any
    number of bytes, calls of up to 2^32-1 bytes of input and of output space, and any number of calls. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTWIface.
Require Zlib.proof.huffman.BlockBound.
Require Import Zlib.proof.deflate.LTWBInit Zlib.proof.deflate.LTWBDBound Zlib.proof.deflate.LTWBWalk.
Import ListNotations.
Local Open Scope Z_scope.

(** The definitions: LTWBDefs.v ([BpreW], [BrunW], [MidW]). *)

(** bw_bound: deflateBound from [BpreW]; the first [BrunW] (phase P0). *)
Lemma bound_of_bpre_w : forall W HI, core_facts_w W ->
  forall level wbits mem strategy ds s tin tout adler n,
  BpreW W level wbits mem strategy ds s tin tout adler -> 0 <= n <= 9223372036854775807 ->
  exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 18446744073709551615 /\
    BrunW W HI n b 0 false s tin tout adler.
Proof.
  intros W HI CF level wbits mem strategy ds s tin tout adler n HB Hn.
  destruct HB as (HW & Ho & Hpo & Hst & Hwr & Hpd & Hpo0 & Hbi & Hsym & Hla & Hss & Hds & Hlv & Hsg & Hwb & Hhb &
                  Hgz & Hlf & Ht & Hti & Had).
  assert (Hw : 0 <= d_wrap s <= 2) by (rewrite Hwr; unfold wrap_of; destruct (wbits <? 0), (wbits >? 15); lia).
  assert (Hso : status_ok (d_status s) = true).
  { rewrite Hst. destruct (wrap_of wbits =? 2); reflexivity. }
  pose proof (cw_prm W CF s HW) as Hp.
  exists (Zlength (hdr_bytes s adler) + body (bcls_of s) n + tlen (d_wrap s)).
  pose proof (hdr_bytes_len_w s adler Hgz) as HL. pose proof (body_range_w (bcls_of s) n (proj1 Hn)) as HR.
  assert (Hn4 : n / 4 <= 2305843009213693952) by (apply Z.div_le_upper_bound; lia).
  assert (HT : 0 <= tlen (d_wrap s) <= 8) by (unfold tlen; destruct (d_wrap s =? 1), (d_wrap s =? 2); lia).
  split; [apply deflateBound_val_w; auto|].
  split; [lia|].
  exists (hdr_bytes s adler), (d_wrap s).
  split; [exact HW|]. split; [exact Ho|]. split; [exact Hw|]. split; [reflexivity|]. split; [lia|].
  split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hgz|]. split; [exact Hlf|].
  left. split; [rewrite Hst, Hwr; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [exact Ht|]. split; [exact Hpd|]. split; [exact Hbi|]. split; [exact Hsym|].
  split; [unfold ub; lia|]. exact Had.
Qed.

(** At the start of the data nothing is in the window. *)
Lemma brunw_ub0 : forall W HI, core_facts_w W -> forall n b fin s tin tout adler,
  BrunW W HI n b 0 fin s tin tout adler -> ub s = 0.
Proof.
  intros W HI CF n b fin s tin tout adler (H & w0 & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hph).
  destruct Hph as [P|[P|[P|P]]].
  - destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & Hu & _). exact Hu.
  - destruct P as (_ & _ & _ & _ & _ & _ & Hu). exact Hu.
  - destruct P as (_ & _ & _ & _ & E & k & HE & Hk0 & Hmk & _).
    destruct (cw_pos W CF s HW) as (L1 & L2 & L3 & L4). pose proof (minblk_pos (bcls_of s)).
    unfold ub in *. nia.
  - destruct P as (_ & _ & _ & Hu & _). exact Hu.
Qed.

(** bw_once: one deflate(Z_FINISH) offered all the data and b < 2^32 bytes of output space. *)
Lemma once_w : forall W HI, core_facts_w W -> hdr_facts_w HI -> Zlib.proof.huffman.BlockBound.block_bound_statement ->
  forall n b s tin tout adler data msg,
  BrunW W HI n b 0 false s tin tout adler -> b <= 4294967295 -> bytes data -> Zlength data = n ->
  exists s' z',
    c_deflate s (zcall data 0 n tin b tout adler msg) Z_FINISH = Some (s', z', Z_STREAM_END) /\
    d_gzhead s' = d_gzhead s.
Proof.
  intros W HI CF HF BB n b s tin tout adler data msg HB Hb Hd Hn.
  destruct (brunw_facts W HI CF HF _ _ _ _ _ _ _ _ HB) as (Hpd & _ & Ht & Htb & _ & Hpos & _).
  assert (Hnb : n <= b).
  { destruct HB as (H & w0 & _ & _ & _ & Hbe & _ & Hn' & _).
    pose proof (body_range_w (bcls_of s) n (proj1 Hn')). pose proof (Zlength_nonneg H).
    pose proof (tlen_range w0). lia. }
  subst n.
  destruct (deflate_walk_w W HI CF HF BB (Zlength data) b 0 false s tin tout adler data b Z_FINISH msg HB
              ltac:(right; reflexivity) ltac:(intros E; discriminate E) Hd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite (brunw_ub0 W HI CF _ _ _ _ _ _ _ HB); lia))
    as (s' & z' & code & E & G & _ & _ & _ & _ & R).
  destruct (R eq_refl eq_refl eq_refl ltac:(lia)) as [Ec _]. subst code.
  exists s', z'. split; [exact E|exact G].
Qed.

Theorem bound_theory_w : Zlib.proof.huffman.BlockBound.block_bound_statement ->
  core_w_stmt -> hdr_w_stmt -> bound_w_stmt.
Proof.
  intros BB [W CF] [HI HF]. exists (BpreW W), (BrunW W HI). constructor.
  - intros. apply bpre_init_w; auto.
  - intros. eapply bpre_dict_w; eauto.
  - intros. apply bpre_head_w; auto.
  - intros. eapply bound_of_bpre_w; eauto; lia.
  - intros. eapply once_w; eauto.
Qed.

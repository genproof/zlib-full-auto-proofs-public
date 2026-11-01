(** * The model theory of the deflate laws, deflate_bound / deflate_bound_split part.

    [bound_facts Bpre Brun] (LawFacts.v) for invariants chosen here, from the core part's facts ([core_facts W]:
    the compression function's blocks as events [dev] with the count of bits [Gb] before and after each), the
    header part's ([hdr_facts HI]) and lemma (ii) ([BlockBound.block_bound_statement]: the per-block cost at
    memLevel 8 for the tight bound).  What remains here: the costs of the blocks for the conservative bounds
    (fixedlen / storelen), the accounting of all bits against deflateBound, and the walk of deflate() with
    Z_NO_FLUSH / Z_FINISH (entry stage, headers, compression stage, trailer). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface.
Require Import Zlib.proof.deflate.LTBInit Zlib.proof.deflate.LTBDBound Zlib.proof.deflate.LTBWalk.
Import ListNotations.
Local Open Scope Z_scope.

(** The definitions: LTBDefs.v (Bpre, Brun, the classes and the accounting). *)

(** The facts of [cpost_extra] (LTBDefs.v), from [cpost]. *)
Lemma cpost_extra_ok : forall W, core_facts W -> cpost_extra W.
Proof.
  intros W _ s z flush s' z' bs evs (_ & _ & _ & _ & (k & x & Hz & _) & _ & Hev & Hbs).
  split; [|split].
  - eapply Forall_impl; [|exact Hev]. intros [g t syms buf sl last|g len last]; cbn; [tauto|auto].
  - intros ->. destruct Hbs as (_ & Hb & _). exact Hb.
  - destruct Hz as (_ & _ & _ & _ & _ & _ & _ & Hx & Ha & _). pose proof (Zlength_nonneg x). lia.
Qed.

(** bf_bound: deflateBound from [Bpre]; the first [Brun] (phase P0). *)
Lemma bound_of_bpre : forall W HI, core_facts W ->
  forall level wbits mem strategy ds s tin tout adler n,
    Bpre W level wbits mem strategy ds s tin tout adler -> 0 <= n <= 1048576 ->
    exists b, c_deflateBound (Some s) n = Some b /\ 0 <= b <= 4294967295 /\
      (ds = false -> (level = 6 \/ level = -1) -> wbits = 15 -> mem = 8 -> b <= c_compressBound n) /\
      Brun W HI n b 0 false s tin tout adler.
Proof.
  intros W HI CF level wbits mem strategy ds s tin tout adler n HB Hn.
  destruct HB as (HW & Ho & Hpo & Hst & Hwr & Hpd & Hpo0 & Hbi & Hsym & Hla & Hss & Hds & Hlv & Hsg & Hwb & Hhb &
                  Hgz & Hlf & Ht & Hti & Had).
  assert (Hw : 0 <= d_wrap s <= 2) by (rewrite Hwr; unfold wrap_of; destruct (wbits <? 0), (wbits >? 15); lia).
  assert (Hso : status_ok (d_status s) = true).
  { rewrite Hst. destruct (wrap_of wbits =? 2); reflexivity. }
  pose proof (cf_prm W CF s HW) as Hp.
  exists (Zlength (hdr_bytes s adler) + body (bcls_of s) n + tlen (d_wrap s)).
  pose proof (hdr_bytes_len s adler Hgz) as HL. pose proof (body_range (bcls_of s) n Hn) as HR.
  assert (HT : 0 <= tlen (d_wrap s) <= 8) by (unfold tlen; destruct (d_wrap s =? 1), (d_wrap s =? 2); lia).
  split; [apply deflateBound_val; auto|].
  split; [lia|].
  split.
  - intros Hd Hl Hwb15 Hm8. subst wbits mem. destruct (Hds Hd) as [Hs0 _].
    assert (Hw1 : d_wrap s = 1) by (rewrite Hwr; reflexivity).
    rewrite (hdr_bytes_zlib_nodict s adler Hw1 Hs0), Hw1, compressBound_val by exact Hn.
    assert (Hc : bcls_of s = BTight).
    { unfold bcls_of, tight_b. rewrite Hwb, Hhb, Hlv.
      destruct Hl as [-> | ->]; cbn; destruct (d_strategy s =? Z_FIXED); reflexivity. }
    rewrite Hc. unfold tlen. cbn. lia.
  - exists (hdr_bytes s adler), (d_wrap s).
    split; [exact HW|]. split; [exact Ho|]. split; [exact Hw|]. split; [reflexivity|]. split; [lia|].
    split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hgz|]. split; [exact Hlf|].
    left. split; [rewrite Hst, Hwr; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Ht|]. split; [exact Hpd|]. split; [exact Hbi|]. split; [exact Hsym|].
    split; [unfold ub; lia|]. exact Had.
Qed.

Theorem bound_theory : Zlib.proof.huffman.BlockBound.block_bound_statement ->
  forall W HI, core_facts W -> hdr_facts HI -> exists Bpre Brun, bound_facts Bpre Brun.
Proof.
  intros BB W HI CF HF. exists (Bpre W), (Brun W HI). constructor.
  - intros. apply bpre_init; auto.
  - intros. apply bpre_dict; auto.
  - intros. apply bpre_head; auto.
  - intros. eapply bound_of_bpre; eauto.
  - intros n Hn. rewrite compressBound_val by exact Hn. pose proof (body_range BTight n Hn). lia.
  - intros n b s tin tout adler data msg HB Hd Hn.
    assert (Hn' : 0 <= n <= 1048576) by (destruct HB as (H & w0 & _ & _ & _ & _ & _ & Hn' & _); lia).
    assert (Hb : 0 <= b <= 1073741824).
    { destruct HB as (H & w0 & _ & _ & _ & Hb & HH & _ & _ & _ & Ht & _).
      pose proof (body_range (bcls_of s) n Hn'). pose proof (Zlength_nonneg H).
      unfold tlen in Hb. destruct (w0 =? 1), (w0 =? 2); lia. }
    assert (Ht : 0 <= tout) by (destruct HB as (H & w0 & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _); lia).
    destruct (deflate_walk W HI CF HF BB (cpost_extra_ok W CF) n b 0 false s tin tout adler data b Z_FINISH msg HB
                ltac:(right; reflexivity) ltac:(intros H; discriminate) Hd ltac:(lia) ltac:(lia) Hb)
      as (s' & z' & code & E & G & _ & A & T & _ & R).
    destruct (R eq_refl eq_refl eq_refl ltac:(lia)) as [Ec Ea]. subst code.
    exists s', z'. subst n. auto.
  - intros n b pos fin s tin tout adler inb aout flush msg HB Hf Hfin Hd Hp Hfp Ha.
    destruct (deflate_walk W HI CF HF BB (cpost_extra_ok W CF) n b pos fin s tin tout adler inb aout flush msg HB Hf Hfin Hd Hp Hfp
                ltac:(lia)) as (s' & z' & code & E & G & C & A & T & B & _).
    exists s', z', code. repeat split; auto; lia.
Qed.

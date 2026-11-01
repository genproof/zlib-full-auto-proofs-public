(** * The model facts of law api_deterministic on data of any length ([det_theory2_stmt], DetFacts2.v)

    From deflate() on the round trips' wide invariant (RTK7Api.api7_deflate_stmt: every call with the sizes of the
    C types is defined and keeps RTK7Defs.Iapi7), as DetTheory.det_theory does for the data of at most 2^20 bytes
    over LTApiDefs.Iapi: the invariant is Iapi7 with no dictionary and the output kept short (header and trailer,
    DetTheory.Iapi_shrink), total_out only counted (DetShift.tout_shift); deflateParams on Iapi7 (its inner
    deflate(strm, Z_BLOCK) is a call of api7_deflate_stmt; after Z_FINISH it returns Z_STREAM_ERROR at once or
    only the level changes). *)
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DetFacts2.
Require Import Zlib.proof.roundtrip.RTK7Api.
Require Import Zlib.proof.deflate.DetTheory2Params.
Require Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.LTApiInit.
Require Zlib.proof.deflate.DetTheory.
Require Zlib.proof.deflate.DetShift.
Import ListNotations.
Local Open Scope Z_scope.

(** Without a dictionary total_in is the length of the data consumed (below 2^64 in [Iapi7]). *)
Lemma Iapi7_tin : forall wrap D O fin s tin tout adler,
  Iapi7 W3 hinv7 [] wrap D O fin s tin tout adler -> tin = Zlength D.
Proof.
  intros wrap D O fin s tin tout adler HI'.
  destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDl & (k & Hk & Ht) & _).
  cbn in Hk. replace k with 0 in Ht by lia. rewrite Z.add_0_r in Ht. unfold u64 in Ht.
  pose proof (Zlength_nonneg D). rewrite Z.mod_small in Ht by lia. exact Ht.
Qed.

(** The stream of a call as the law's main builds it is the round trips' one. *)
Lemma zcall_r : forall inb nin ain tin aout tout adler msg,
  Zlib.proof.deflate.LawFacts.zcall inb nin ain tin aout tout adler msg = rzcall inb nin ain tin aout tout adler msg.
Proof. reflexivity. Qed.

(** A call run from total_out [t0] (RTK7Api.call_ok7), shifted to the real total_out [tout]: total_in does not
    wrap (the data stay below 2^64 bytes), total_out is counted modulo 2^64. *)
Lemma call_ok7_okw : forall inb nin aout tin t0 tout z,
  call_ok7 inb nin aout tin t0 z -> 0 <= tin -> tin + (Zlength inb - nin) <= 18446744073709551615 ->
  call_okw inb nin aout tin tout (zsh (tout - t0) z).
Proof.
  intros inb nin aout tin t0 tout z (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) H1 H2.
  unfold call_okw, zsh, set_z_total_out; cbn.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [rewrite C4; unfold u64; apply Z.mod_small; lia|].
  split; [exact C5|]. split; [exact C6|]. split; [|exact C8].
  rewrite C7. unfold u64. f_equal. lia.
Qed.

(** The invariant: [Iapi7] of the round trips (RTK7Defs.v) with no dictionary, the output kept short (the
    header and at most the trailer, DetTheory2Inv.Iapi7_shrink; total_out runs from the length of what is kept
    and DetShift.tout_shift moves each call to the real total_out), no gzip header given, strm->adler 32 bits.
    It is named so that law api_deflate_any, whose main drives one stream by such calls, can use more of its
    facts (src/proof/harness/api_deflate_any/AnyTheory.v). *)
Definition det_J2 : det_inv := fun fin s tin adler => exists wrap D O,
  Iapi7 W3 hinv7 [] wrap D O fin s tin (Zlength O) adler /\ Zlength O <= 18 /\ d_gzhead s = None /\
  0 <= adler < 4294967296.

Theorem det_facts2_J2 : api7_deflate_stmt -> det_facts2 det_J2.
Proof.
  intros AD.
  destruct Zlib.proof.deflate.DetShift.tout_shift as [TSD TSP].
  unfold det_J2.
  constructor.
  - (* deflateInit2 *)
    intros level wbits mem strategy a1 a2 a3 a4 a5 z Hl Hw Hm Hs.
    pose proof (Zlib.proof.deflate.LTApiInit.init_shape level 8 wbits mem strategy a1 a2 a3 a4 a5 z) as Sh.
    destruct (Zlib.proof.deflate.LawFacts.params_ok level 8 wbits mem strategy) eqn:P.
    + destruct (Iapi7_init level 8 wbits mem strategy z P) as (s & z0 & E0 & Hgz & Hz0 & HI0).
      split.
      { rewrite Sh. destruct a1; [destruct (a2 && a3 && a4 && a5); [rewrite E0|]|]; eauto. }
      intros os z' code E. rewrite Sh in E.
      destruct a1; [destruct (a2 && a3 && a4 && a5) eqn:Ea|].
      * rewrite E0 in E. injection E as <- <- <-.
        split; [left; reflexivity|].
        split; [split; intros C; [unfold Z_OK, Z_STREAM_ERROR in C; lia|discriminate]|].
        intros _. split.
        -- exists s. subst z0. cbn [z_total_in z_total_out z_adler].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           exists (Zlib.proof.deflate.LawFacts.wrap_of wbits), [], [].
           split; [exact HI0|]. split; [cbn; lia|]. split; [exact Hgz|].
           match goal with |- context [if ?c then _ else _] => destruct c end; lia.
        -- intros b1 b2 b3 b4 b5 os2 z2 code2 E2 Hok2.
           destruct (Zlib.proof.deflate.DetTheory.init_ok level wbits mem strategy b1 b2 b3 b4 b5 z os2 z2 code2
                       E2 Hok2) as [_ E3].
           rewrite E0 in E3. injection E3 as <- <- _. auto.
      * injection E as <- <- <-. split; [right; right; reflexivity|].
        split; [split; intros C; [unfold Z_MEM_ERROR, Z_STREAM_ERROR in C; lia|discriminate]|].
        intros C. unfold Z_MEM_ERROR, Z_OK in C. lia.
      * injection E as <- <- <-. split; [right; right; reflexivity|].
        split; [split; intros C; [unfold Z_MEM_ERROR, Z_STREAM_ERROR in C; lia|discriminate]|].
        intros C. unfold Z_MEM_ERROR, Z_OK in C. lia.
    + split; [rewrite Sh; eauto|].
      intros os z' code E. rewrite Sh in E. injection E as <- <- <-.
      split; [right; left; reflexivity|]. split; [tauto|].
      intros C. unfold Z_STREAM_ERROR, Z_OK in C. lia.
  - (* strm->adler *)
    intros fin s tin adler (wrap & D & O & _ & _ & _ & A). exact A.
  - (* deflate *)
    intros fin s tin adler inb nin aout tout flush msg (wrap & D & O & HI' & LO & Hgz & Ha)
      Hfl Hb Hn Hin Hin2 Hao Ht Hfin.
    pose proof (Iapi7_tin wrap D O fin s tin (Zlength O) adler HI') as Htin.
    pose proof (Zlength_nonneg D) as HD0.
    destruct (AD [] wrap D O fin s tin (Zlength O) adler inb nin aout flush msg HI' Hfl Hb Hn Hin ltac:(lia) Hao
                ltac:(lia) Hfin) as (s' & z' & code & E & G & _ & C & A' & _ & _ & _ & Post).
    rewrite (Zlib.proof.deflate.DetTheory.zcall_shift inb nin (Zlength inb - nin) tin aout (Zlength O) tout adler
               msg Ht), TSD, zcall_r, E.
    cbn [option_map]. exists s', (zsh (tout - Zlength O) z'), code. unfold rsh; cbn [fst snd].
    split; [reflexivity|]. split; [apply call_ok7_okw; [exact C|lia|lia]|].
    intros Hne. specialize (Post Hne).
    destruct (Iapi7_shrink wrap _ _ _ s' _ _ _ Post) as (O' & HO' & LO'); [rewrite G; exact Hgz|].
    unfold zsh, set_z_total_out; cbn [z_total_in z_adler z_next_in].
    exists wrap, (D ++ sublist nin (z_next_in z') inb), O'.
    split; [exact HO'|]. split; [exact LO'|]. split; [rewrite G; exact Hgz|]. apply A'; exact Ha.
  - (* deflateParams *)
    intros fin s tin adler inb nin aout tout level strategy msg (wrap & D & O & HI' & LO & Hgz & Ha)
      Hl Hs Hb Hn Hin Hin2 Hao Ht Hfin.
    pose proof (Iapi7_tin wrap D O fin s tin (Zlength O) adler HI') as Htin.
    pose proof (Zlength_nonneg D) as HD0.
    destruct (Z.eq_dec (d_status s) FINISH_STATE) as [Hst | Hst].
    + pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _).
      specialize (Hf Hst). subst fin. pose proof (Hfin [] eq_refl) as Hr.
      destruct (params_in_finish7 [] wrap D O (Some []) s tin (Zlength O) adler
                  (Zlib.proof.deflate.LawFacts.zcall inb nin (Zlength inb - nin) tin aout tout adler msg)
                  level strategy HI' Hst)
        as (s' & z' & code & E & Ez & G & HI2).
      destruct (Zlib.proof.deflate.DetTheory.call_okw_none inb nin aout tin tout adler msg (Some Z_STREAM_ERROR)
                  Hn (proj1 Hao) Ht) as [K1 K2].
      exists s', z', code. split; [exact E|].
      assert (Hz : z_next_in z' = nin /\ z_total_in z' = tin /\ z_adler z' = adler)
        by (destruct Ez as [-> | ->]; cbn; auto).
      destruct Hz as (Z1 & Z2 & Z3).
      split; [destruct Ez as [-> | ->]; assumption|].
      rewrite Z1, Z2, Z3, <- Hr. exists wrap, D, O.
      split; [exact HI2|]. split; [exact LO|]. split; [rewrite G; exact Hgz|exact Ha].
    + assert (HI0 : Iapi7 W3 hinv7 [] wrap D O None s tin (Zlength O) adler)
        by (apply (Iapi7_fin [] wrap D O fin None s tin (Zlength O) adler HI'); intros E; contradiction).
      destruct (api7_params AD [] wrap D O s tin (Zlength O) adler inb nin aout level strategy msg HI0 Hb Hn Hin
                  ltac:(lia) Hao ltac:(lia)) as (s' & z' & code & E & G & C & A' & Post).
      rewrite (Zlib.proof.deflate.DetTheory.zcall_shift inb nin (Zlength inb - nin) tin aout (Zlength O) tout adler
                 msg Ht), TSP, zcall_r, E.
      cbn [option_map]. exists s', (zsh (tout - Zlength O) z'), code. unfold rsh; cbn [fst snd].
      split; [reflexivity|]. split; [apply call_ok7_okw; [exact C|lia|lia]|].
      pose proof Post as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf' & _).
      apply (Iapi7_fin [] wrap _ _ None
               (match fin with None => None | Some _ => Some (sublist (z_next_in z') (Zlength inb) inb) end))
        in Post; [|intros E'; specialize (Hf' E'); discriminate].
      destruct (Iapi7_shrink wrap _ _ _ s' _ _ _ Post) as (O' & HO' & LO'); [rewrite G; exact Hgz|].
      unfold zsh, set_z_total_out; cbn [z_total_in z_adler z_next_in].
      exists wrap, (D ++ sublist nin (z_next_in z') inb), O'.
      split; [exact HO'|]. split; [exact LO'|]. split; [rewrite G; exact Hgz|]. apply A'; exact Ha.
Qed.

Theorem det_theory2 : api7_deflate_stmt -> det_theory2_stmt.
Proof. intros AD. exists det_J2. exact (det_facts2_J2 AD). Qed.

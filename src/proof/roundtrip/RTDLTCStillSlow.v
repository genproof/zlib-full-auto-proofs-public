(** * Core part of the deflate law theory: cf_still, part slow.  Definitions: RTDLTCStill.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Import Zlib.proof.roundtrip.RTDLTCSlowInv Zlib.proof.roundtrip.RTDLTCSlowRefill Zlib.proof.roundtrip.RTDLTCSlow2 Zlib.proof.roundtrip.RTDLTCStillSlowKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem still_slow_ok : fill_idem_spec -> fill_spec -> ins_spec -> lm_spec -> tally_spec2 -> fbo_spec ->
  fpend_spec2 -> slow_spec2 ->
  forall s z flush, compress_pre2 s z flush -> still_at s -> fn_of s = 2 -> still_concl c_deflate_slow s z flush.
Proof.
  intros _ Hfill Hins Hlm Htally Hfbo _ _ s z flush Hpre Hst Hfn s' z' bs E Enx.
  pose proof (SI_init s z flush Hpre Hfn) as HI.
  apply ss_slow_inv in E. destruct E as (s2 & z2 & o & EL & E).
  apply loop_runs in EL.
  apply ss_loop_end in E. destruct E as (Fn & Fs & Fo).
  destruct (ss_fill0 s z flush Hfill HI Hst) as (s1 & z1 & k & Ec & ES1 & Hma & EL1 & Hn & Hk0).
  pose proof (ss_first s z s1 z1 flush (proj2 (proj2 Hst)) Ec) as Eb.
  apply runs_inv in EL. destruct EL as [EL|(a' & EL & Hr)].
  - rewrite Eb in EL.
    destruct ((d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)).
    + injection EL as <- <- <-. rewrite (Fo ltac:(discriminate)). exact ES1.
    + destruct (Z.eqb_spec (d_lookahead s1) 0) as [E0|E0].
      * injection EL as <- <- <-. rewrite (Fs eq_refl Hma). exact ES1.
      * apply ss_step in EL. simpl ss_z in EL. lia.
  - pose proof (ss_runs s z flush Hfill Hins Hlm Htally Hfbo a' _ Hr) as Hmono.
    destruct (slow_body_ok Hfill Hins Hlm Htally Hfbo s z flush (s, z) (ex_intro _ [] HI)) as (_ & r & E' & Hr').
    rewrite EL in E'. injection E' as <-. destruct Hr' as [HP' _]. specialize (Hmono HP').
    rewrite Eb in EL. simpl ss_z in Hmono.
    destruct ((d_lookahead s1 <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); [discriminate|].
    destruct (Z.eqb_spec (d_lookahead s1) 0) as [E0|E0]; [discriminate|].
    apply ss_step in EL. destruct a' as [sa za]. simpl ss_z in EL. simpl snd in Hmono. lia.
Qed.

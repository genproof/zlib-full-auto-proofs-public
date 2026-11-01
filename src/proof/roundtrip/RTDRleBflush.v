(* RT-D part RLE: if (bflush) FLUSH_BLOCK(s, 0) (statement: RTDRleKit.v; model on RTDLTCRleBflush.rbflush_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDRleKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem rfbflush_ok : fbo_spec -> rffbo_stmt -> rfbflush_stmt.
Proof.
  intros Hfbo Hffbo s z flush syms bf r dict D BS p [HT0 Hbf] Hz Ha Hfl Hd HD Hk Hp Hpm Hr.
  destruct bf.
  - symmetry in Hbf. apply Z.eqb_eq in Hbf.
    destruct (rfbw_ok Hfbo s z flush syms 0 HT0 Hz Ha Hfl ltac:(lia) ltac:(intros; discriminate)
                ltac:(intros; left; exact Hbf))
      as (s' & z' & e & Hfb & _ & _ & Hz' & _).
    destruct (Hffbo s z syms 0 s' z' dict D BS p HT0 Hz ltac:(lia) Hd HD Hk Hp Hpm Hfb)
      as (x & blk & Hzo & Hwt & Hk' & Hbits).
    assert (Hrst : rst r = (s', z')).
    { unfold c_bflush, c_flush_block in Hr. rewrite Hfb in Hr. cbn [bind] in Hr.
      destruct ((z_avail_out z' =? 0) && _); inversion Hr; subst; reflexivity. }
    rewrite Hrst. cbn [fst snd].
    exists x, [blk], []. split.
    { apply zout_only_zstep; [exact Hz|exact Ha|exact Hzo|].
      destruct Hz' as (_ & Ho & _). exact Ho. }
    split; [exact Hwt|]. split; [exact Hk'|].
    rewrite Hbits. reflexivity.
  - assert (HL2 : Zlength syms <= d_L s - 2).
    { destruct HT0 as (_ & _ & _ & _ & _ & _ & _ & HL & _).
      symmetry in Hbf. apply Z.eqb_neq in Hbf. lia. }
    unfold c_bflush in Hr. inversion Hr; subst r. cbn [rst fst snd].
    exists [], [], syms. split.
    { apply zout_only_zstep; [exact Hz|exact Ha| |destruct Hz as (_ & Ho & _); exact Ho].
      unfold zout_only. rewrite app_nil_r, Zlength_nil, Z.sub_0_r, Z.add_0_r. tauto. }
    pose proof HT0 as (Hpr & _ & _ & _ & _ & Hm & Ht & _ & Hf & Hb & _ & Hq & Hfn & _).
    split.
    { destruct (fn_of_rle s Hpr Hfn) as [Hlev _].
      pose proof (wmatch_avail0 s Hm Hfn) as Hav.
      unfold wtrees. split; [exact Ht|]. split; [exact HL2|]. split; [exact Hf|].
      split; [intros; lia|]. intros _. rewrite Hav, Z.sub_0_r. exact Hb. }
    rewrite app_nil_r. split; [exact Hk|]. rewrite (rk_quiet_pend s Hq). cbn. rewrite !app_nil_r. reflexivity.
Qed.

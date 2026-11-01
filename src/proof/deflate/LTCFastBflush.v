(** * deflate_fast, part: if (bflush) FLUSH_BLOCK(s, 0) (c_bflush).  Statement and definitions: LTCFastKit.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Theorem bflush_ok : fbw_stmt -> bflush_stmt.
Proof.
  intros Hfbw s z flush syms bf [HT0 Hbf] Hz Ha Hfl.
  destruct bf.
  - symmetry in Hbf. apply Z.eqb_eq in Hbf.
    destruct (Hfbw s z flush syms 0 HT0 Hz Ha Hfl ltac:(lia) ltac:(intros; discriminate) ltac:(intros; left; exact Hbf))
      as (s' & z' & e & Hfb & Hcr & Hlast & Hz' & Had & Hai & Hla & Hss & Hbs & Hsn & Hbv & _ & Hpo).
    unfold c_bflush, c_flush_block. rewrite Hfb. cbn [bind].
    destruct (Z.eqb_spec (z_avail_out z') 0) as [E|E]; cbn [andb orb negb Z.eqb Pos.eqb].
    + eexists. split; [reflexivity|]. split; [reflexivity|]. exists [e]. split; [exact Hcr|].
      cbn [bpost]. split; [constructor; [exact Hlast|constructor]|]. split; [exact Hbv|]. right; left; exact E.
    + eexists. split; [reflexivity|]. cbn beta iota.
      split; [|split; [exact Hla|exact Hai]]. exists [e].
      assert (Hcr' := Hcr). destruct Hcr' as (_ & Ho & _ & Hapi & _).
      assert (Hp0 : d_pending s' = 0) by (destruct Hpo as [P|P]; [exact P|contradiction]).
      unfold FI. split; [exact Hcr|]. split.
      { unfold quiet. split; [exact Hp0|]. split; [|exact Hbv].
        destruct Ho as (_ & _ & _ & _ & _ & Ho). apply Ho; exact Hp0. }
      split; [exact Hz'|]. split.
      { destruct Hapi as (_ & Hw & _). rewrite Hw, Had. exact Ha. }
      constructor; [exact Hlast|constructor].
  - assert (HL2 : Zlength syms <= d_L s - 2).
    { destruct HT0 as (_ & _ & _ & _ & _ & _ & _ & HL & _).
      symmetry in Hbf. apply Z.eqb_neq in Hbf. lia. }
    assert (HW := TS0_W s syms HT0 HL2).
    destruct HT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & Hq & _).
    unfold c_bflush. eexists. split; [reflexivity|].
    split; [exists []; apply FI_refl; assumption|]. split; reflexivity.
Qed.

(* RT-D part FILL: fill_window appends the bytes read to the history, keeps the chains hash-consistent (specs: RTDSpecs.v / RTDK.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDSpecs.
Require Import Zlib.proof.roundtrip.RTDFillKit.
Import ListNotations.
Local Open Scope Z_scope.
Local Strategy opaque [loop loop2].

Theorem rtd_fill_ok : fill_fspec.
Proof.
  intros s z s' z' H Hf Hz Ha E Hk.
  unfold c_fill_window in E.
  destruct (loop FUEL fw_body (s, z)) as [[s1 z1]|] eqn:El; [|discriminate]. cbn [bind] in E.
  destruct (c_fw_high_water s1) as [s2|] eqn:Eh; [|discriminate]. cbn [bind] in E.
  injection E as <- <-.
  apply loop_runs in El.
  assert (I0 : fwI s z H (s, z)).
  { split; [exact Hf|]. split; [exact Hz|]. split; [exact Ha|]. exists 0, 0. cbn [fst snd].
    split; [unfold fwstep; split; [reflexivity|]; split; [apply zstep_refl; auto|]; lia|].
    split; [intros K; rewrite Z.add_0_r, sublist_nil, app_nil_r; exact K|].
    split; [intros C; apply hok_chk2; [apply Hf|exact C]|].
    intros [C|(C1 & C2)]; [lia|]. intros _. split; [exact C1|exact C2]. }
  destruct (fw_runs s z H _ _ Hf Hz Ha El I0) as (Hf1 & Hz1 & Ha1 & d & k & Hs & Ik & Ic & Ip).
  cbn [fst snd] in *.
  destruct (hw_vals s1 s2 Hf1 Eh) as (Eq & Hv).
  pose proof Hf1 as (_ & _ & (_ & P2 & _) & _).
  exists k. split; [destruct Hs as (_ & Zs & _); exact Zs|]. split; [|split].
  - assert (Kw := kwin_win _ s1 (d_window s2) (Ik Hk) Hv). rewrite Eq. exact Kw.
  - intros C. assert (C2 := chk2_hok _ (chk2_win s1 (d_window s2) (d_lookahead s1) (Ic C) ltac:(lia) Hv)).
    rewrite Eq. exact C2.
  - intros Hla Hc. assert (P := Pr_win s1 (d_window s2) (Ip Hc) P2 Hv).
    rewrite Eq. apply P. rewrite Eq in Hla. exact Hla.
Qed.

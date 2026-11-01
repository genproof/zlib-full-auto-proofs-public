(** * Core part of the deflate law theory: cf_still, part fill.  Definitions: LTCStill.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCStill.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma fill_idem_loop2 {A B : Type} (body : A -> option (A + B)) a r d :
  body a = Some (inr r) -> loop2 d body a = Some (inr r).
Proof.
  intros H. induction d as [|d IH]; cbn [loop2]; [exact H|]. rewrite IH. reflexivity.
Qed.

Theorem fill_idem_ok : fill_idem_spec.
Proof.
  intros s z Hpre Hz Had Hav Hss Hhw.
  destruct Hpre as (Hprm & Hws & Hwp & _ & _).
  destruct Hprm as (Hwb & Hwsz & _).
  destruct Hws as (_ & _ & Hwin & _).
  destruct Hwp as (Hla & Hst & Hsl & _).
  assert (Hw1 : 512 <= d_w_size s <= 32768).
  { rewrite Hwsz. split.
    - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
    - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hbody : fw_body (s, z) = Some (inr (s, z))).
  { unfold fw_body, c_fw_slide.
    unfold MAX_DIST, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *.
    assert (Hu : u32 (d_w_size s + u32 (d_w_size s - (258 + 3 + 1))) =
                 d_w_size s + (d_w_size s - (258 + 3 + 1))).
    { unfold u32. rewrite (Z.mod_small (d_w_size s - _)) by lia. apply Z.mod_small; lia. }
    rewrite Hu.
    destruct (d_strstart s >=? _) eqn:E; [rewrite Z.geb_le in E; lia|].
    cbn [bind]. rewrite Hav. reflexivity. }
  unfold c_fill_window, loop. rewrite (fill_idem_loop2 _ _ _ FUEL Hbody).
  cbn [bind].
  assert (Hh : c_fw_high_water s = Some s).
  { unfold c_fw_high_water.
    destruct (d_high_water s <? d_window_size s) eqn:E1; [|reflexivity].
    rewrite Z.ltb_lt in E1.
    assert (Hm : d_strstart s + d_lookahead s + WIN_INIT <= d_high_water s) by lia.
    unfold WIN_INIT, MAX_MATCH in *.
    destruct (d_high_water s <? d_strstart s + d_lookahead s) eqn:E2; [rewrite Z.ltb_lt in E2; lia|].
    destruct (d_high_water s <? d_strstart s + d_lookahead s + 258) eqn:E3; [rewrite Z.ltb_lt in E3; lia|].
    reflexivity. }
  rewrite Hh. reflexivity.
Qed.

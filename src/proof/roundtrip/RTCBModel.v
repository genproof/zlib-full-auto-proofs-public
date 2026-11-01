(* Round-trip laws, part RT-CB: compress2_z's loop over the model (RTDIface.c2_give / c2_loop). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTDIface.
Import ListNotations.
Local Open Scope Z_scope.

(* with the destination and the source each given in one piece (the loop's invariant: what is left to give is
   0 or the stream's space / input is exhausted), an iteration offers all the rest, with Z_FINISH *)
Lemma give_eq src z left srcleft :
  0 <= left <= umax -> 0 <= srcleft <= umax ->
  (left = 0 \/ z_avail_out z = 0) -> (srcleft = 0 \/ z_avail_in z = 0) ->
  c2_give src z left srcleft =
  (mkST src (z_next_in z) (z_avail_in z + srcleft) (z_total_in z) [] (z_avail_out z + left) (z_total_out z)
     (z_adler z) (z_msg z), 0, 0, Z_FINISH).
Proof.
  intros Hl Hs Hlo Hso. unfold c2_give.
  destruct (z_avail_out z =? 0) eqn:Eo; [apply Z.eqb_eq in Eo | apply Z.eqb_neq in Eo];
  destruct (z_avail_in z =? 0) eqn:Ei; [apply Z.eqb_eq in Ei | apply Z.eqb_neq in Ei | apply Z.eqb_eq in Ei | apply Z.eqb_neq in Ei];
  rewrite ?Z.min_l by lia; cbv zeta; rewrite ?Z.sub_diag.
  - rewrite Eo, Ei. reflexivity.
  - destruct Hso as [-> | ?]; [|contradiction]. rewrite Eo, Z.add_0_r. reflexivity.
  - destruct Hlo as [-> | ?]; [|contradiction]. rewrite Ei, Z.add_0_r. reflexivity.
  - destruct Hlo as [-> | ?]; [|contradiction]. destruct Hso as [-> | ?]; [|contradiction].
    rewrite !Z.add_0_r. reflexivity.
Qed.

Require Import Zlib.proof.roundtrip.RTC2.

(* one iteration of the loop over a run: the deflate call's result, and either the rest of the run (Z_OK) or the
   run's end *)
Lemma c2_run_inv src s z left srcleft out E O SF ZF z1 l' sl' fl :
  c2_run src s z left srcleft out E O SF ZF -> c2_give src z left srcleft = (z1, l', sl', fl) ->
  exists s' z' e, c_deflate s z1 fl = Some (s', z', e) /\ d_gzhead s' = d_gzhead s /\ c2_step z1 z' /\
    ((e = Z_OK /\ c2_run src s' z' l' sl' (out ++ z_out z') E O SF ZF) \/
     (e <> Z_OK /\ E = e /\ O = out ++ z_out z' /\ SF = s' /\ ZF = z')).
Proof.
  intros H G. inversion H; subst.
  - rewrite G in H0. injection H0 as <- <- <- <-.
    exists s', z', Z_OK. split; [auto | split; [auto | split; [auto | left; auto]]].
  - rewrite G in H0. injection H0 as <- <- <- <-.
    exists SF, ZF, E. split; [auto | split; [auto | split; [auto | right; auto]]].
Qed.

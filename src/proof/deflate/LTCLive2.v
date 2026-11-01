(** * Core part of the deflate law theory: deflate_stored with Z_FINISH and room finishes, against the corrected specs of LTCSpecs2.v.
    With LTCSpecs2.tally_spec_2 / fpend_spec_2 it also holds under the original specifications of
    LTCSpecs.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTCSpecs2.
Require Import Zlib.proof.deflate.LTCLiveKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The kernel must never compute the loop fuel (2^40 iterations). *)
Local Strategy opaque [loop loop2].

Lemma bind_inv {A B : Type} (c : option A) (f : A -> option B) y :
  bind c f = Some y -> exists x, c = Some x /\ f x = Some y.
Proof. destruct c as [x|]; cbn; [intros H; exists x; split; [reflexivity|exact H]|discriminate]. Qed.

Lemma tail_last (x : dstate) (z1 : strm) (last : Z) (K : option (dstate * strm * bstate)) y :
  last <> 0 -> (if negb (last =? 0) then Some (x, z1, finish_done) else K) = Some y -> snd y = finish_done.
Proof.
  intros N H. destruct (Z.eqb_spec last 0) as [E|E]; [contradiction|]. cbn in H. inversion H. reflexivity.
Qed.

Theorem live_ok2 : fpend_spec2 -> live_spec.
Proof.
  intros _ s z s' z' bs HW Ho Hq Hzin Hwrap Had Hlev Hroom H.
  destruct HW as (Hprm & _ & Hwpos & _ & _ & _ & Hl0 & _).
  destruct (Hl0 Hlev) as [Hla Hbs].
  pose proof (prm_pbsize s Hprm) as [Hps1 Hps2].
  destruct Hprm as (Hwb & Hws & _).
  destruct Hwpos as (_ & _ & _ & Hbs2 & Hl & _).
  assert (Hwsz : d_w_size s <= 32768).
  { rewrite Hws. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  assert (Hwsz0 : 0 <= d_w_size s) by (rewrite Hws; apply Z.pow_nonneg; lia).
  destruct Hzin as (_ & _ & Hai & _ & Hao & _ & Hto).
  assert (Hmb : u32 (let a := u64 (d_pending_buf_size s - 5) in if a >? d_w_size s then d_w_size s else a)
                < MAX_STORED).
  { cbv zeta. unfold MAX_STORED.
    set (a := u64 (d_pending_buf_size s - 5)).
    assert (0 <= a < 18446744073709551616) by (subst a; unfold u64; apply Z.mod_pos_bound; lia).
    rewrite Z.gtb_ltb. destruct (Z.ltb_spec (d_w_size s) a).
    - rewrite u32_id by lia. lia.
    - rewrite u32_id by lia. lia. }
  unfold c_deflate_stored in H.
  apply bind_inv in H. destruct H as ([[s1 z1] last] & EL & H).
  assert (Hlast : last <> 0).
  { apply (ds_loop _ s z s1 z1 last Hmb); [|exact EL].
    unfold linv, lrest, zout_ok. unfold ub in Hroom. rewrite Hla, !Z.add_0_r in Hroom.
    split; [lia|]. split; [lia|]. split; [exact Ho|]. split; [exact Hq|]. lia. }
  apply bind_inv in H. destruct H as (s2 & EW & H).
  exact (tail_last _ _ _ _ _ Hlast H).
Qed.

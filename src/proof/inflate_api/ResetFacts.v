(* Facts about the reset models of ApiModel.v with patch F8 (bit 3 of wrap): the state after inflateInit2_ /
   inflateReset2 in terms of the plain reset reset_s, and its fields.  With wrap from reset2_wb (0..7), bit 3 is
   set exactly when wb = 0, and then inflateReset's extra step (window freed, wbits = 0) changes nothing that
   wb = 0 and the freed window have not already fixed. *)
From Coq Require Import ZArith List Lia Bool.
Require Export Zlib.proof.inflate_api.ApiModel.
Import ListNotations.
Local Open Scope Z_scope.

Lemma reset2_wrap_land8 (wrap wb: Z) : 0 <= wrap <= 7 ->
  (Z.land (reset2_wrap wrap wb) 8 =? 0) = negb (wb =? 0).
Proof.
  intros H. unfold reset2_wrap. destruct (Z.eqb_spec wb 0) as [E | E]; cbn [negb].
  - assert (C: wrap = 0 \/ wrap = 1 \/ wrap = 2 \/ wrap = 3 \/ wrap = 4 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
  - assert (C: wrap = 0 \/ wrap = 1 \/ wrap = 2 \/ wrap = 3 \/ wrap = 4 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.

(* inflateReset2 on an accepted windowBits: the plain reset of the state with the new wrap and wbits, the window
   freed when its size changes or the header gives it (wb = 0) *)
Lemma reset2_s_eq (wrap wb: Z) (s: istate) : 0 <= wrap <= 7 ->
  reset2_s wrap wb s =
  reset_s (set_i_wbits (set_i_wrap (if (i_win s && negb (i_wbits s =? wb)) || (wb =? 0) then set_i_win s false else s)
                         (reset2_wrap wrap wb)) wb).
Proof.
  intros H. unfold reset2_s, reset_full_s, reset_hdr_s.
  cbn [i_wrap set_i_wbits set_i_wrap].
  rewrite (reset2_wrap_land8 wrap wb H).
  destruct (Z.eqb_spec wb 0) as [E | E].
  - subst wb. rewrite orb_true_r. cbn [negb].
    destruct (i_win s && negb (i_wbits s =? 0))%bool; destruct s; reflexivity.
  - rewrite orb_false_r. cbn [negb]. reflexivity.
Qed.

(* the state after inflateInit2_ *)
Lemma init_s_eq (wrap wb: Z) : 0 <= wrap <= 7 ->
  init_s wrap wb = reset_s (set_i_wbits (set_i_wrap zero_s (reset2_wrap wrap wb)) wb).
Proof.
  intros H. unfold init_s. rewrite (reset2_s_eq wrap wb zero_s H).
  cbn [zero_s i_win i_wbits andb orb]. destruct (wb =? 0); reflexivity.
Qed.

Lemma init_s_fields (wrap wb: Z) : 0 <= wrap <= 7 ->
  i_wrap (init_s wrap wb) = reset2_wrap wrap wb /\ i_wbits (init_s wrap wb) = wb /\
  i_win (init_s wrap wb) = false /\ i_mode (init_s wrap wb) = HEAD /\ i_flags (init_s wrap wb) = -1 /\
  i_wsize (init_s wrap wb) = 0 /\ i_whave (init_s wrap wb) = 0 /\ i_wnext (init_s wrap wb) = 0 /\
  i_wdata (init_s wrap wb) = [] /\ i_havedict (init_s wrap wb) = 0 /\ i_head (init_s wrap wb) = false /\
  i_hold (init_s wrap wb) = 0 /\ i_bits (init_s wrap wb) = 0 /\ i_total (init_s wrap wb) = 0 /\
  i_check (init_s wrap wb) = 0 /\ i_last (init_s wrap wb) = 0.
Proof. intros H. rewrite (init_s_eq wrap wb H). cbn. repeat split. Qed.

(* the wrap after inflateInit2_ / inflateReset2 on windowBits w: bits 0-2 those of reset2_wb, bit 3 when wb = 0 *)
Lemma init_s_wrap (w wrap wb: Z) : reset2_wb w = Some (wrap, wb) ->
  i_wrap (init_s wrap wb) = reset2_wrap wrap wb /\
  (0 <= reset2_wrap wrap wb <= 7 \/ 9 <= reset2_wrap wrap wb <= 11 \/ 13 <= reset2_wrap wrap wb <= 15) /\
  Z.land (reset2_wrap wrap wb) 7 = wrap /\ (reset2_wrap wrap wb = 0 <-> wrap = 0) /\
  (Z.land (reset2_wrap wrap wb) 8 =? 0) = negb (wb =? 0).
Proof.
  intros E. destruct (reset2_wrap_ok w wrap wb E) as (A & B & C & D).
  assert (R: 0 <= wrap <= 7) by (destruct (reset2_wb_cases w wrap wb E); lia).
  split; [exact (proj1 (init_s_fields wrap wb R)) | auto].
Qed.

(* inflateReset: the window freed and wbits = 0 with bit 3 of wrap, then the plain reset *)
Lemma reset_full_fields (s: istate) :
  i_wrap (reset_full_s s) = i_wrap s /\
  i_wbits (reset_full_s s) = (if Z.land (i_wrap s) 8 =? 0 then i_wbits s else 0) /\
  i_win (reset_full_s s) = (if Z.land (i_wrap s) 8 =? 0 then i_win s else false) /\
  i_mode (reset_full_s s) = HEAD /\ i_wsize (reset_full_s s) = 0 /\ i_whave (reset_full_s s) = 0 /\
  i_wnext (reset_full_s s) = 0 /\ i_wdata (reset_full_s s) = [] /\ i_flags (reset_full_s s) = -1.
Proof.
  unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); destruct s; cbn; repeat split.
Qed.

(* without bit 3, inflateReset is the plain reset *)
Lemma reset_full_plain (s: istate) : Z.land (i_wrap s) 8 = 0 -> reset_full_s s = reset_s s.
Proof. intros H. unfold reset_full_s, reset_hdr_s. rewrite H. reflexivity. Qed.

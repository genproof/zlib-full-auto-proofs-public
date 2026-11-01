(* Law res_memory_deflate: the arithmetic of the bound.  A successful deflateInit2_ makes exactly the five
   allocations [dinit_events s] (src/proof/za/deflate/ZSpec.v): the deflate_state (5968 bytes), the window and
   prev (2 * w_size each), head (2 * hash_size) and pending_buf (4 * lit_bufsize), with w_size = 2^w', w' the
   window bits (windowBits without the raw sign or the gzip 16, raised from 8 to 9), hash_size = 2^(memLevel+7)
   and lit_bufsize = 2^(memLevel+6).  So the counting allocator's peak, in its size_t counters [cnt], is
   5968 + 2^(w'+2) + 2^(memLevel+9), within the harness's (1 << (w + 2)) + (1 << (memLevel + 9)) + 7 * 1024
   (w' = 9 when w = 8 costs 2^10 = 1024 bytes more: 5968 + 1024 <= 7168). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
#[local] Existing Instance DCS.CS.

(* the counters after five allocations that fit in size_t: both the sum *)
Lemma cnt_five (a b c d e : Z) :
  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d -> 0 <= e -> a + b + c + d + e < 2 ^ 64 ->
  cnt [ZAlloc a; ZAlloc b; ZAlloc c; ZAlloc d; ZAlloc e] = (a + b + c + d + e, a + b + c + d + e).
Proof.
  intros. unfold cnt. cbn [fold_left cnt_step fst snd].
  rewrite (Z.mod_small (0 + a)) by lia.
  rewrite (Z.mod_small (0 + a + b)) by lia.
  rewrite (Z.mod_small (0 + a + b + c)) by lia.
  rewrite (Z.mod_small (0 + a + b + c + d)) by lia.
  rewrite (Z.mod_small (0 + a + b + c + d + e)) by lia.
  repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end;
  f_equal; lia.
Qed.

(* the window bits as the harness computes them: w = windowBits, w = -w when negative, w - 16 when above 15 *)
Lemma harness_w_eq (wbits : Z) :
  -15 <= wbits ->
  wb_of wbits = (let w := if wbits <? 0 then - wbits else wbits in if w >? 15 then w - 16 else w).
Proof.
  intros H. unfold wb_of.
  destruct (Z.ltb_spec wbits 0); [destruct (Z.gtb_spec (- wbits) 15); lia | reflexivity].
Qed.

Lemma sizeof_t_ds : sizeof t_ds = 5968.
Proof. reflexivity. Qed.

(* The peak bound: after a successful deflateInit2_ the counters (both now and peak) are
   5968 + 2^(w'+2) + 2^(memLevel+9), within the harness's bound; the window bits w are 8..15 and memLevel
   1..9 (the shifts of the harness's check are defined). *)
Lemma init_peak level method wbits mem strategy a1 a2 a3 a4 a5 z s z' r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', r) ->
  8 <= wb_of wbits <= 15 /\ 1 <= mem <= 9 /\ -15 <= wbits /\
  fst (cnt (dinit_events s)) = snd (cnt (dinit_events s)) /\
  snd (cnt (dinit_events s)) <= 2 ^ (wb_of wbits + 2) + 2 ^ (mem + 9) + 7 * 1024 /\
  snd (cnt (dinit_events s)) <= dinit_max /\ 0 <= snd (cnt (dinit_events s)).
Proof.
  intros H. destruct (init_sizes _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (P & Ew & Eh & El).
  unfold params_ok in P. rewrite !andb_true_iff in P.
  destruct P as [[[[[[[[[[P1 P2] P3] P4] P5] P6] P7] P8] P9] P10] P11].
  rewrite negb_true_iff, Z.ltb_ge in P1. rewrite Z.leb_le in P2, P3, P5, P6.
  unfold dinit_events. rewrite sizeof_t_ds, Ew, Eh, El.
  set (k := Z.max 9 (wb_of wbits)).
  assert (Hk : 9 <= k <= 15) by (unfold k; lia).
  assert (Pk : 2 ^ 9 <= 2 ^ k <= 2 ^ 15) by (split; apply Z.pow_le_mono_r; lia).
  assert (Pm : 2 ^ 1 <= 2 ^ mem <= 2 ^ 9) by (split; apply Z.pow_le_mono_r; lia).
  assert (E7 : 2 ^ (mem + 7) = 2 ^ mem * 128) by (rewrite Z.pow_add_r by lia; reflexivity).
  assert (E6 : 2 ^ (mem + 6) = 2 ^ mem * 64) by (rewrite Z.pow_add_r by lia; reflexivity).
  assert (E9 : 2 ^ (mem + 9) = 2 ^ mem * 512) by (rewrite Z.pow_add_r by lia; reflexivity).
  rewrite E7, E6.
  rewrite cnt_five by (simpl in *; lia). cbn [fst snd].
  split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [reflexivity | ]. split.
  - rewrite E9.
    assert (Ek : wb_of wbits = 8 /\ k = 9 \/ k = wb_of wbits) by (unfold k; lia).
    destruct Ek as [[E8 E9'] | Ek].
    + rewrite E8, E9'. simpl. lia.
    + rewrite <- Ek. rewrite Z.pow_add_r by lia. simpl in *. lia.
  - split; [unfold dinit_max; simpl in *; lia | simpl in *; lia].
Qed.

(* the harness's check, as main evaluates it: count.peak <= (1ul << (w + 2)) + (1ul << (mem_level + 9)) + 7 * 1024
   in unsigned long arithmetic (the shifts are below 64, the sum does not wrap) *)
Lemma check_true (P W M : Z) :
  0 <= P -> 8 <= W <= 15 -> 1 <= M <= 9 -> P <= 2 ^ (W + 2) + 2 ^ (M + 9) + 7 * 1024 ->
  negb (Int64.ltu
    (Int64.add
       (Int64.add (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.add (Int.repr W) (Int.repr 2)))))
                  (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.add (Int.repr M) (Int.repr 9))))))
       (Int64.repr (Int.signed (Int.mul (Int.repr 7) (Int.repr 1024)))))
    (Int64.repr P)) = true.
Proof.
  intros HP HW HM Hb.
  assert (Pw : 1024 <= 2 ^ (W + 2) <= 131072)
    by (split; [change 1024 with (2 ^ 10) | change 131072 with (2 ^ 17)]; apply Z.pow_le_mono_r; lia).
  assert (Pm : 1024 <= 2 ^ (M + 9) <= 262144)
    by (split; [change 1024 with (2 ^ 10) | change 262144 with (2 ^ 18)]; apply Z.pow_le_mono_r; lia).
  rewrite !add_repr. rewrite !Int.unsigned_repr by rep_lia.
  unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite !Z.shiftl_1_l.
  change (Int.signed (Int.mul (Int.repr 7) (Int.repr 1024))) with 7168.
  rewrite !add64_repr.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt _ _); [lia | reflexivity].
Qed.

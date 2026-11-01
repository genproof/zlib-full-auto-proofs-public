(* Law res_memory_deflate: the exact bound of round 3's harness.  After a successful deflateInit2_ the peak of
   its five allocations (Peak.v) is exactly 5968 + 2^(w'+2) + 2^(memLevel+9), w' = max 9 (wb_of windowBits),
   which is the harness's (1 << (w + 2)) + (1 << (memLevel + 9)) + 5968 with w = 9 for 8 as main computes it. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.deflate.LawFacts.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
#[local] Existing Instance DCS.CS.

(* the harness's `if (w == 8) w = 9` on the window bits 8..15: deflateInit2_'s max 9 *)
Lemma harness_w9 (x : Z) : 8 <= x <= 15 -> (if x =? 8 then 9 else x) = Z.max 9 x.
Proof. intros H. destruct (Z.eqb_spec x 8); lia. Qed.

(* After a successful deflateInit2_ the peak of its five allocations is exactly
   5968 + 2^(w'+2) + 2^(memLevel+9), w' = max 9 (wb_of windowBits): the state (5968 bytes), window and prev
   (2 * 2^w' each), head (2 * 2^(memLevel+7)) and pending_buf (4 * 2^(memLevel+6)). *)
Lemma init_peak_exact level method wbits mem strategy a1 a2 a3 a4 a5 z s z' r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', r) ->
  8 <= wb_of wbits <= 15 /\ 1 <= mem <= 9 /\ -15 <= wbits /\
  snd (cnt (dinit_events s)) = 2 ^ (Z.max 9 (wb_of wbits) + 2) + 2 ^ (mem + 9) + 5968.
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
  assert (Ek2 : 2 ^ (k + 2) = 2 ^ k * 4) by (rewrite Z.pow_add_r by lia; reflexivity).
  rewrite E7, E6.
  rewrite cnt_five by (simpl in *; lia). cbn [fst snd].
  split; [lia | ]. split; [lia | ]. split; [lia | ].
  rewrite E9, Ek2. lia.
Qed.

(* the harness's check after every deflate() call, as main evaluates it:
   count.peak <= (1ul << (w + 2)) + (1ul << (mem_level + 9)) + 5968 in unsigned long arithmetic (the shifts are
   below 64, the sum does not wrap) *)
Lemma check_true_exact (P W M : Z) :
  0 <= P -> 9 <= W <= 15 -> 1 <= M <= 9 -> P <= 2 ^ (W + 2) + 2 ^ (M + 9) + 5968 ->
  negb (Int64.ltu
    (Int64.add
       (Int64.add (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.add (Int.repr W) (Int.repr 2)))))
                  (Int64.shl (Int64.repr 1) (Int64.repr (Int.unsigned (Int.add (Int.repr M) (Int.repr 9))))))
       (Int64.repr (Int.signed (Int.repr 5968))))
    (Int64.repr P)) = true.
Proof.
  intros HP HW HM Hb.
  assert (Pw : 2048 <= 2 ^ (W + 2) <= 131072)
    by (split; [change 2048 with (2 ^ 11) | change 131072 with (2 ^ 17)]; apply Z.pow_le_mono_r; lia).
  assert (Pm : 1024 <= 2 ^ (M + 9) <= 262144)
    by (split; [change 1024 with (2 ^ 10) | change 262144 with (2 ^ 18)]; apply Z.pow_le_mono_r; lia).
  rewrite !add_repr. rewrite !Int.unsigned_repr by rep_lia.
  unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite !Z.shiftl_1_l.
  change (Int.signed (Int.repr 5968)) with 5968.
  rewrite !add64_repr.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt _ _); [lia | reflexivity].
Qed.

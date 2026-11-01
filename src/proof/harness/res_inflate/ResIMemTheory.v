(* Law res_memory_inflate: the counters of struct count between two inflate() calls of main's loop.

   The allocator has seen inflateInit2_'s state (7160 bytes), perhaps failed allocations of the window, and at
   most one window, of 2^wbits bytes with wbits at most the harness's w (res_inv); nothing is freed.  So
   count.now = count.peak = N, with N = 7160 while there is no window and N <= 7160 + 2^w; and a state in mode
   MEM (the window could not be allocated) comes with count.failed set.  [mem_ok hw s tr] says this of the
   state s and the events tr; inflateInit2_'s state satisfies it ([mem_init]) and one inflate() call keeps it
   and gives both assertions of the loop (ResIMemStep.mem_call). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Zlib.proof.harness.res_inflate.ResITheory.

Definition mem_ok (hw : Z) (s : istate) (tr : list zev) : Prop :=
  exists N, za_now tr = N /\ cnt tr = (N, N) /\ (i_win s = false -> N = state_size) /\
            state_size <= N <= state_size + 2 ^ hw /\
            (i_mode s = MEM -> za_failed tr = true).

(* after inflateInit2_: the state allocated, no window, mode HEAD *)
Lemma mem_init (hw : Z) (sp : val) (w : Z) :
  0 <= hw -> mem_ok hw (l_s (init_live sp w)) [ZAlloc state_size].
Proof.
  intros Hh. pose proof (ResITheory.init_mode sp w) as M.
  pose proof (Z.pow_pos_nonneg 2 hw ltac:(lia) Hh).
  exists state_size. rewrite M. unfold za_now, za_count, cnt, state_size.
  repeat split; try lia; try (intros E; discriminate E).
Qed.

(* the allocator can serve inflate(): what it holds leaves room for one more window *)
Lemma mem_cap (hw : Z) (s : istate) (tr : list zev) :
  hw <= 15 -> mem_ok hw s tr -> za_now tr + 2 ^ 23 <= Int64.max_unsigned.
Proof.
  intros Hh (N & E & _ & _ & B & _). rewrite E.
  assert (2 ^ hw <= 2 ^ 15).
  { destruct (Z.ltb_spec hw 0).
    - rewrite Z.pow_neg_r by lia. lia.
    - apply Z.pow_le_mono_r; lia. }
  unfold state_size in B. rep_lia.
Qed.

(* Invariants of the main loop of the model of inflate_table (model.v), as the VST proof of the body
   (verif_inflate_table.v) needs them: every state the for(;;) loop reaches from the initial state of
   an accepted code keeps every array access in bounds, every value in its C range, and the loop
   ends (Break) before running out of symbols.  Plain Coq.
   The facts are stated as Props (`*_stmt`), bundled in `loop_facts`; the segments of the body
   proof take `loop_facts` as a hypothesis, and part_loop_facts.v proves it (loop_facts_ok). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inftrees.model.
Import ListNotations.
Local Open Scope Z_scope.

(* The code passed the Kraft tests of inflate_table (no return -1). *)
Definition acc_test (type: Z) (lens: list Z) : Prop :=
  exists lft, left_final (counts lens) = Some lft /\
    ((0 <? lft) && ((type =? CODES) || negb (maxlen lens =? 1))) = false.

(* The hypotheses under which the main loop runs: inputs of the spec, at least one symbol, the code
   accepted, the root table fits (no return 1 before the loop). *)
Definition acc_ok (type: Z) (lens: list Z) (req cap: Z) : Prop :=
  inputs_ok type lens req /\ cap_ok type lens req cap /\ 1 <= maxlen lens /\ acc_test type lens /\
  over type (Z.shiftl 1 (root_of req lens)) = false.

(* s is the state at the top of the loop after k iterations, all of which continued. *)
Definition reach (type: Z) (lens: list Z) (req: Z) (old: list entry) (k: nat) (s: state) : Prop :=
  run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) k
      (init_state lens (root_of req lens) old) = Continue s.

(* What one iteration from s needs: the bounds of every access and value of the C loop body. *)
Definition iter_ok (lens: list Z) (cap: Z) (s: state) : Prop :=
  0 <= s_sym s < Zlength (sorted_syms lens) /\
  1 <= s_len s <= 15 /\
  0 <= s_drop s <= s_len s /\
  s_len s - s_drop s <= s_curr s <= 15 /\
  0 <= s_huff s < Z.shiftl 1 (s_len s) /\
  0 <= s_next s /\ s_next s + Z.shiftl 1 (s_curr s) <= s_used s /\ s_used s <= cap /\
  s_used s <= 32768 /\
  0 <= s_low s <= 4294967295 /\
  Zlength (s_cnt s) = 16 /\ Forall (fun c => 0 <= c <= 288) (s_cnt s) /\
  1 <= Znth (s_len s) (s_cnt s) /\
  Zlength (s_tab s) = cap.

(* The values one iteration (model.v, step) computes from s. *)
Definition st_huff' (s: state) : Z := next_huff (s_huff s) (s_len s).
Definition st_c (s: state) : Z := Znth (s_len s) (s_cnt s) - 1.
Definition st_cnt' (s: state) : list Z := upd_Znth (s_len s) (s_cnt s) (st_c s).
Definition st_len' (lens: list Z) (s: state) : Z :=
  if st_c s =? 0 then Znth (Znth (s_sym s + 1) (sorted_syms lens)) lens else s_len s.
Definition st_drop' (root: Z) (s: state) : Z := if s_drop s =? 0 then root else s_drop s.

(* The sorted symbols: used symbols, each once. *)
Definition sorted_syms_ok_stmt : Prop := forall lens,
  Forall (fun l => 0 <= l <= MAXBITS) lens ->
  Zlength (sorted_syms lens) <= Zlength lens /\
  Forall (fun x => 0 <= x < Zlength lens /\ 1 <= Znth x lens <= 15) (sorted_syms lens).

(* Root, min, max of an accepted code. *)
Definition root_ok_stmt : Prop := forall type lens req cap,
  acc_ok type lens req cap ->
  1 <= minlen lens <= root_of req lens /\ root_of req lens <= maxlen lens <= 15 /\
  (type = CODES -> root_of req lens = maxlen lens).

(* Every reached state satisfies iter_ok, and its symbol index is the number of iterations. *)
Definition reach_ok_stmt : Prop := forall type lens req old k s,
  acc_ok type lens req (Zlength old) -> reach type lens req old k s ->
  iter_ok lens (Zlength old) s /\ s_sym s = Z.of_nat k.

(* `len = lens[work[sym]]` after `sym++` reads inside the sorted symbols. *)
Definition reach_read_ok_stmt : Prop := forall type lens req old k s,
  acc_ok type lens req (Zlength old) -> reach type lens req old k s ->
  st_c s = 0 -> s_len s <> maxlen lens ->
  s_sym s + 1 < Zlength (sorted_syms lens).

(* A new sub-table: never for CODES, its index bits are in range (curr = len - drop >= 0, the
   sub_bits loop ends at most at 15). *)
Definition reach_sub_ok_stmt : Prop := forall type lens req old k s,
  acc_ok type lens req (Zlength old) -> reach type lens req old k s ->
  ~ (st_c s = 0 /\ s_len s = maxlen lens) ->
  root_of req lens < st_len' lens s ->
  Z.land (st_huff' s) (Z.shiftl 1 (root_of req lens) - 1) <> s_low s ->
  type <> CODES /\
  st_drop' (root_of req lens) s <= st_len' lens s /\
  sub_bits (st_len' lens s) (st_drop' (root_of req lens) s) (maxlen lens) (st_cnt' s) <= 15.

(* After the loop: the entry `next[huff]` of an incomplete code is inside the table. *)
Definition reach_break_ok_stmt : Prop := forall type lens req old k s s',
  acc_ok type lens req (Zlength old) -> reach type lens req old k s ->
  step type lens (sorted_syms lens) (root_of req lens) (maxlen lens) s = Break s' ->
  s_huff s' <> 0 -> 0 <= s_next s' + s_huff s' < s_used s'.

(* One more iteration. *)
Definition reach_step_stmt : Prop := forall type lens req old k s s',
  reach type lens req old k s ->
  step type lens (sorted_syms lens) (root_of req lens) (maxlen lens) s = Continue s' ->
  reach type lens req old (S k) s'.

(* The loop of the model (fuel = number of symbols) ends where the C loop ends. *)
Definition reach_final_stmt : Prop := forall type lens req old k s,
  acc_ok type lens req (Zlength old) -> reach type lens req old k s ->
  forall o, step type lens (sorted_syms lens) (root_of req lens) (maxlen lens) s = o ->
  (match o with Continue _ => False | _ => True end) ->
  run type lens (sorted_syms lens) (root_of req lens) (maxlen lens) (length (sorted_syms lens))
      (init_state lens (root_of req lens) old) = o.

Definition loop_facts : Prop :=
  sorted_syms_ok_stmt /\ root_ok_stmt /\ reach_ok_stmt /\ reach_read_ok_stmt /\
  reach_sub_ok_stmt /\ reach_break_ok_stmt /\ reach_step_stmt /\ reach_final_stmt.

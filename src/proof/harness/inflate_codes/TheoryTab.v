(* Law inflate_codes, theory part: the table cases TABLE, LENLENS, CODELENS *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Require Import Zlib.proof.inflate.MwfLemmas.
Require Zlib.proof.inftrees.facts Zlib.proof.inftrees.part_result Zlib.proof.inftrees.part_sorted
  Zlib.proof.inftrees.part_rfc Zlib.proof.inftrees.part_bits Zlib.proof.inftrees.part_subbits
  Zlib.proof.inftrees.part_size.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The pass from TABLE / LENLENS / CODELENS up to LEN_: its result does not depend on flush, which   *)
(* is read only at CODELENS's end (`if flush == Z_TREES`).                                          *)

Inductive ttab_res := TTDone (o: iout) | TTLen (m: mst).

Definition ttab_run (flush: Z) (p: ttab_res) : iout :=
  match p with
  | TTDone o => o
  | TTLen m => if flush =? Z_TREES then IBrk (set_leave m)
               else c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) m
  end.

Definition ttab_clpost (m: mst) : ttab_res :=
  let s := m_s m in
  if Znth 256 (i_lens s) =? 0 then TTDone (IBrk (set_bad m M_eob)) else
  let s := set_i_lenbits (set_i_lencode (set_i_next s 0) (TCodes 0)) 9 in
  let '(r, codes, nxt, lb) := call_table LENS 0 (i_nlen s) 9 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_ll_set)) else
  let s := set_i_distbits (set_i_distcode s (TCodes (i_next s))) 6 in
  let '(r, codes, nxt, db) := call_table DISTS (i_nlen s) (i_ndist s) 6 s in
  let s := set_i_distbits (set_i_next (set_i_codes s codes) nxt) db in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_d_set)) else
  TTLen (set_mode m LEN_).

Definition ttab_cl (m: mst) : ttab_res :=
  match codelens_loop lenfix_list distfix_list 320 m with
  | CLleave m => TTDone (IBrk m)
  | CLbad m => TTDone (IBrk m)
  | CLnext m => ttab_clpost m
  end.

Definition ttab_llpost (m: mst) : ttab_res :=
  let s := lenlens_zero 19 (m_s m) in
  let s := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next s 0) (TCodes 0)) (TCodes 0)) 7 in
  let '(r, codes, nxt, lb) := call_table CODES 0 19 7 s in
  let s := set_i_lenbits (set_i_next (set_i_codes s codes) nxt) lb in
  let m := set_m_ret (set_m_s m s) r in
  if negb (r =? 0) then TTDone (IBrk (set_bad m M_cl_set)) else
  ttab_cl (set_mode (upd_s m (fun s => set_i_have s 0)) CODELENS).

Definition ttab_ll (m: mst) : ttab_res :=
  let m := lenlens_loop 19 m in
  if m_leave m =? 1 then TTDone (IBrk m) else ttab_llpost m.

Definition ttab_tab (m: mst) : ttab_res :=
  let m := needbits 14 m in
  if m_leave m =? 1 then TTDone (IBrk m) else
  let nlen := bitsn m 5 + 257 in let m := dropbits 5 m in
  let ndist := bitsn m 5 + 1 in let m := dropbits 5 m in
  let ncode := bitsn m 4 + 4 in let m := dropbits 4 m in
  let m := upd_s m (fun s => set_i_ncode (set_i_ndist (set_i_nlen s nlen) ndist) ncode) in
  if orb (286 <? nlen) (30 <? ndist) then TTDone (IBrk (set_bad m M_toomany)) else
  ttab_ll (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS).

Ltac ttab_split :=
  repeat match goal with
  | |- context [if ?c then _ else _] => destruct c
  | |- context [match ?x with (_, _) => _ end] => destruct x as [[[? ?] ?] ?]
  end.

Lemma ttab_cl_eq flush m :
  c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_cl m).
Proof.
  unfold c_CODELENS, ttab_cl. destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1];
    try reflexivity.
  unfold ttab_clpost. cbv zeta.
  destruct (Znth 256 (i_lens (m_s m1)) =? 0); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|].
  destruct (call_table _ _ _ _ _) as [[[r2 c2] n2] b2].
  destruct (negb (r2 =? 0)); reflexivity.
Qed.

Lemma ttab_ll_eq flush m :
  c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_ll m).
Proof.
  unfold c_LENLENS, ttab_ll. cbv zeta.
  destruct (m_leave (lenlens_loop 19 m) =? 1); [reflexivity|].
  unfold ttab_llpost. cbv zeta.
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  destruct (negb (r =? 0)); [reflexivity|]. apply ttab_cl_eq.
Qed.

Lemma ttab_tab_eq flush m :
  c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list) m = ttab_run flush (ttab_tab m).
Proof.
  unfold c_TABLE, ttab_tab. cbv zeta.
  destruct (m_leave (needbits 14 m) =? 1); [reflexivity|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [reflexivity|].
  apply ttab_ll_eq.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts kept along the pass (the call's frame) and what the pass gives                       *)

Record ttab_fr (wrap: Z) (inp: list Z) (aout: Z) (m: mst) : Prop := {
  tf_inp : m_inp m = inp;
  tf_aout : m_aout m = aout;
  tf_wrap : i_wrap (m_s m) = wrap;
  tf_head : i_head (m_s m) = false;
  tf_out : m_out m = m_aout m;
  tf_nx : 0 <= m_nx m <= Zlength (m_inp m);
  tf_hold : lrange (m_hold m);
  tf_bits : 0 <= m_bits m <= 31 }.

Definition ttab_ok (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (p: ttab_res) : Prop :=
  match p with
  | TTDone (IBrk m') => Kc wrap src pos inp aout m' /\ (m_leave m' = 0 -> m_mode m' <> DICT)
  | TTDone (IRet _ _) => False
  | TTLen m' => ttab_fr wrap inp aout m' /\ m_leave m' = 0 /\ m_ret m' = Z_OK /\ m_mode m' = LEN_
  end.

(* Kc of a frame state in one of the modes of the pass *)
Lemma ttab_Kc wrap src pos inp aout m :
  ttab_fr wrap inp aout m ->
  (m_mode m = TABLE \/ m_mode m = LENLENS \/ m_mode m = CODELENS \/ m_mode m = LEN_) ->
  m_ret m = Z_OK -> (m_leave m = 0 \/ m_leave m = 1) ->
  Kc wrap src pos inp aout m.
Proof.
  intros F Hmd Hr Hl. destruct F.
  assert (N: m_mode m <> SYNC /\ m_mode m <> BAD /\ m_mode m <> DONE /\ m_mode m <> HEAD /\
             m_mode m <> DICTID /\ m_mode m <> DICT /\ m_mode m <> MEM).
  { unfold TABLE, LENLENS, CODELENS, LEN_, SYNC, BAD, DONE, HEAD, DICTID, DICT, MEM in *. lia. }
  destruct N as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  constructor; auto; intros; try contradiction; try lia.
Qed.

Lemma ttab_Kc_bad wrap src pos inp aout m e :
  ttab_fr wrap inp aout m -> m_leave m = 0 ->
  Kc wrap src pos inp aout (set_bad m e).
Proof.
  intros F Hl. destruct F.
  unfold set_bad, set_mode, upd_s.
  constructor; unfold m_mode;
    cbn [m_s m_inp m_aout m_nx m_out m_leave m_msg m_bits m_hold set_m_s set_m_msg
         i_mode i_wrap i_head set_i_mode]; auto;
    unfold BAD, SYNC, DONE, HEAD, DICTID, DICT, MEM; intros; try congruence; try lia.
Qed.

Lemma ttab_ok_bad wrap src pos inp aout m e :
  ttab_fr wrap inp aout m -> m_leave m = 0 ->
  ttab_ok wrap src pos inp aout (TTDone (IBrk (set_bad m e))).
Proof.
  intros F Hl. cbn [ttab_ok]. split; [apply ttab_Kc_bad; auto|].
  intros _. unfold set_bad, set_mode, upd_s, m_mode. cbn. unfold BAD, DICT. lia.
Qed.

Lemma ttab_ok_brk wrap src pos inp aout m :
  ttab_fr wrap inp aout m ->
  (m_mode m = TABLE \/ m_mode m = LENLENS \/ m_mode m = CODELENS) ->
  m_ret m = Z_OK -> (m_leave m = 0 \/ m_leave m = 1) ->
  ttab_ok wrap src pos inp aout (TTDone (IBrk m)).
Proof.
  intros F Hmd Hr Hl. cbn [ttab_ok]. split; [apply ttab_Kc; auto; tauto|].
  intros _. unfold TABLE, LENLENS, CODELENS, DICT in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts                                                                                      *)

(* CODELENS: the frame under the bit buffer operations *)
Lemma ttcl_fr_pull wrap inp aout m :
  ttab_fr wrap inp aout m -> m_have m <> 0 -> m_bits m <= 23 ->
  ttab_fr wrap inp aout (pull m) /\ m_bits (pull m) = m_bits m + 8.
Proof.
  intros [I A W H O N L B] Hh Hb. unfold m_have in Hh.
  assert (Bp: u32 (m_bits m + 8) = m_bits m + 8) by (unfold u32; rewrite Z.mod_small; lia).
  unfold pull. split; [constructor|];
    cbn [m_inp m_aout m_s m_out m_nx m_hold m_bits set_m_bits set_m_hold set_m_nx]; auto; try lia.
  unfold lrange, u64.
  pose proof (Z.mod_pos_bound (m_hold m + Znth (m_nx m) (m_inp m) * 2 ^ m_bits m) (2^64)). rep_lia.
Qed.

Lemma ttcl_fr_drop wrap inp aout m n :
  ttab_fr wrap inp aout m -> 0 <= n <= m_bits m ->
  ttab_fr wrap inp aout (dropbits n m) /\ m_bits (dropbits n m) = m_bits m - n.
Proof.
  intros [I A W H O N L B] Hn.
  assert (Bp: u32 (m_bits m - n) = m_bits m - n) by (unfold u32; rewrite Z.mod_small; lia).
  unfold dropbits. split; [constructor|];
    cbn [m_inp m_aout m_s m_out m_nx m_hold m_bits set_m_bits set_m_hold]; auto; try lia.
  apply Zshiftr_range; [exact L | lia].
Qed.

Lemma ttcl_fr_leave wrap inp aout m : ttab_fr wrap inp aout m -> ttab_fr wrap inp aout (set_leave m).
Proof. intros []. constructor; auto. Qed.

Lemma ttcl_fr_s wrap inp aout m s :
  ttab_fr wrap inp aout m -> i_wrap s = i_wrap (m_s m) -> i_head s = i_head (m_s m) ->
  ttab_fr wrap inp aout (set_m_s m s).
Proof. intros [] E1 E2. constructor; cbn [m_s set_m_s m_inp m_aout m_out m_nx m_hold m_bits]; auto; congruence. Qed.

Lemma ttcl_fr_ret wrap inp aout m r : ttab_fr wrap inp aout m -> ttab_fr wrap inp aout (set_m_ret m r).
Proof. intros []. constructor; auto. Qed.

(* NEEDBITS(n), n <= 24, from a frame state *)
Lemma ttcl_needbits : forall k n wrap inp aout m,
  ttab_fr wrap inp aout m -> m_leave m = 0 -> n <= 24 -> n <= m_bits m + 8 * Z.of_nat k ->
  ttab_fr wrap inp aout (needbits_f k n m) /\ m_s (needbits_f k n m) = m_s m /\
  m_ret (needbits_f k n m) = m_ret m /\
  (m_leave (needbits_f k n m) = 1 \/ (m_leave (needbits_f k n m) = 0 /\ n <= m_bits (needbits_f k n m))).
Proof.
  induction k; intros n wrap inp aout m F L Hn K; cbn [needbits_f].
  - split; [exact F|]. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact L|]. simpl in K. lia.
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (Z.eqb_spec (m_have m) 0).
      * split; [apply ttcl_fr_leave; auto|]. split; [reflexivity|]. split; [reflexivity|]. left; reflexivity.
      * destruct (ttcl_fr_pull wrap inp aout m F ltac:(assumption) ltac:(lia)) as [F' B'].
        destruct (IHk n wrap inp aout (pull m) F' L Hn ltac:(rewrite B'; lia)) as (A & B & C & D).
        split; [exact A|]. split; [rewrite B; reflexivity|]. split; [rewrite C; reflexivity|]. exact D.
    + split; [exact F|]. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact L|]. lia.
Qed.

(* the root lookup of a table whose entries (at any hold) have 0..15 bits *)
Lemma ttcl_lookup : forall k t nb wrap inp aout m,
  ttab_fr wrap inp aout m -> m_leave m = 0 ->
  (forall h, lrange h -> 0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) t (h mod 2 ^ nb)) <= 15) ->
  15 <= m_bits m + 8 * (Z.of_nat k - 1) ->
  forall here m1 ok, lookup1_f k lenfix_list distfix_list t nb m = (here, m1, ok) ->
  ttab_fr wrap inp aout m1 /\ m_s m1 = m_s m /\ m_ret m1 = m_ret m /\
  (ok = true -> m_leave m1 = 0 /\ 0 <= e_bits here <= m_bits m1 /\ e_bits here <= 15) /\
  (ok = false -> m_leave m1 = 1).
Proof.
  induction k; intros t nb wrap inp aout m F L Hb K here m1 ok E; cbn [lookup1_f] in E;
    pose proof (Hb (m_hold m) (tf_hold _ _ _ _ F)) as HB;
    change (m_hold m mod 2 ^ nb) with (bitsn m nb) in HB.
  - injection E as <- <- <-. split; [exact F|]. split; [reflexivity|]. split; [reflexivity|].
    split; [|discriminate]. intros _. split; [exact L|]. simpl in K. lia.
  - destruct (Z.leb_spec (e_bits (tab_entry lenfix_list distfix_list (m_s m) t (bitsn m nb))) (m_bits m)).
    + injection E as <- <- <-. split; [exact F|]. split; [reflexivity|]. split; [reflexivity|].
      split; [|discriminate]. intros _. split; [exact L|]. lia.
    + destruct (Z.eqb_spec (m_have m) 0).
      * injection E as <- <- <-. split; [apply ttcl_fr_leave; auto|]. split; [reflexivity|].
        split; [reflexivity|]. split; [discriminate|]. intros _; reflexivity.
      * destruct (ttcl_fr_pull wrap inp aout m F ltac:(assumption) ltac:(lia)) as [F' B'].
        destruct (IHk t nb wrap inp aout (pull m) F' L Hb ltac:(rewrite B'; lia) here m1 ok E)
          as (A & B & C & D).
        split; [exact A|]. split; [rewrite B; reflexivity|]. split; [rewrite C; reflexivity|]. exact D.
Qed.

(* the loop's invariant and the result of a pass *)
Definition ttcl_inv wrap inp aout m : Prop :=
  ttab_fr wrap inp aout m /\ m_leave m = 0 /\ m_ret m = Z_OK /\ m_mode m = CODELENS /\
  (forall h, lrange h ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m))
                   (h mod 2 ^ i_lenbits (m_s m))) <= 15).

Definition ttcl_res wrap src pos inp aout (o: clout) : Prop :=
  match o with
  | CLnext m => ttcl_inv wrap inp aout m
  | CLleave m => ttab_ok wrap src pos inp aout (TTDone (IBrk m))
  | CLbad m => ttab_ok wrap src pos inp aout (TTDone (IBrk m))
  end.

Lemma ttcl_inv_ms wrap inp aout m m' :
  ttcl_inv wrap inp aout m -> ttab_fr wrap inp aout m' -> m_leave m' = 0 -> m_ret m' = Z_OK ->
  m_s m' = m_s m -> ttcl_inv wrap inp aout m'.
Proof.
  intros (F & L & R & Md & Hb) F' L' R' E. split; [exact F'|]. split; [exact L'|]. split; [exact R'|].
  unfold m_mode. rewrite E. split; [exact Md | exact Hb].
Qed.

Lemma ttcl_inv_upd wrap inp aout m f :
  ttcl_inv wrap inp aout m ->
  i_mode (f (m_s m)) = i_mode (m_s m) -> i_wrap (f (m_s m)) = i_wrap (m_s m) ->
  i_head (f (m_s m)) = i_head (m_s m) -> i_codes (f (m_s m)) = i_codes (m_s m) ->
  i_lencode (f (m_s m)) = i_lencode (m_s m) -> i_lenbits (f (m_s m)) = i_lenbits (m_s m) ->
  ttcl_inv wrap inp aout (upd_s m f).
Proof.
  intros (F & L & R & Md & Hb) E1 E2 E3 E4 E5 E6. unfold upd_s.
  split; [apply ttcl_fr_s; auto|]. split; [exact L|]. split; [exact R|].
  unfold m_mode in *. cbn [m_s set_m_s]. split; [congruence|].
  intros h Hh. rewrite E5, E6.
  replace (tab_entry lenfix_list distfix_list (f (m_s m)) (i_lencode (m_s m)) (h mod 2 ^ i_lenbits (m_s m)))
    with (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (h mod 2 ^ i_lenbits (m_s m)))
    by (unfold tab_entry; destruct (i_lencode (m_s m)); auto; rewrite E4; reflexivity).
  apply Hb; auto.
Qed.

Lemma ttcl_lens_fill : forall k len s,
  i_mode (lens_fill k len s) = i_mode s /\ i_wrap (lens_fill k len s) = i_wrap s /\
  i_head (lens_fill k len s) = i_head s /\ i_codes (lens_fill k len s) = i_codes s /\
  i_lencode (lens_fill k len s) = i_lencode s /\ i_lenbits (lens_fill k len s) = i_lenbits s.
Proof.
  induction k; intros len s; cbn [lens_fill]; [tauto|].
  destruct (IHk len (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1)))
    as (A & B & C & D & E & G).
  rewrite A, B, C, D, E, G. cbn. tauto.
Qed.

(* the end of a pass with a repeat code *)
Lemma ttcl_tail wrap src pos inp aout m len copy :
  ttcl_inv wrap inp aout m ->
  ttcl_res wrap src pos inp aout
    (if m_mode m =? BAD then CLbad m else
     if i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + copy then CLbad (set_bad m M_repeat) else
     CLnext (upd_s m (lens_fill (Z.to_nat copy) len))).
Proof.
  intros I. pose proof I as (F & L & R & Md & Hb). rewrite Md.
  replace (CODELENS =? BAD) with false by reflexivity.
  destruct (i_nlen (m_s m) + i_ndist (m_s m) <? i_have (m_s m) + copy).
  - cbn [ttcl_res]. apply ttab_ok_bad; auto.
  - cbn [ttcl_res]. destruct (ttcl_lens_fill (Z.to_nat copy) len (m_s m)) as (A & B & C & D & E & G).
    apply ttcl_inv_upd; auto.
Qed.

Lemma ttcl_iter wrap src pos inp aout m :
  ttcl_inv wrap inp aout m -> ttcl_res wrap src pos inp aout (codelens_iter lenfix_list distfix_list m).
Proof.
  intros I. pose proof I as (F & L & R & Md & Hb).
  unfold codelens_iter.
  destruct (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m) as [[here m1] ok] eqn:E.
  destruct (ttcl_lookup 3 _ _ wrap inp aout m F L Hb ltac:(pose proof (tf_bits _ _ _ _ F); simpl; lia)
              here m1 ok E) as (F1 & S1 & R1 & OKt & OKf).
  destruct ok; cbn [negb].
  2:{ cbn [ttcl_res]. apply ttab_ok_brk;
        [exact F1 | right; right; unfold m_mode; rewrite S1; exact Md | congruence | right; auto]. }
  destruct (OKt eq_refl) as (L1 & Bh & Bh15).
  assert (I1: ttcl_inv wrap inp aout m1) by (apply ttcl_inv_ms with m; auto; congruence).
  destruct (Z.ltb_spec (e_val here) 16).
  - cbn [ttcl_res]. destruct (ttcl_fr_drop wrap inp aout m1 (e_bits here) F1 ltac:(lia)) as [F2 B2].
    assert (I2: ttcl_inv wrap inp aout (dropbits (e_bits here) m1))
      by (apply ttcl_inv_ms with m1; [exact I1 | assumption | ..]; unfold dropbits;
              cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence).
    apply ttcl_inv_upd; auto.
  - unfold needbits.
    destruct (Z.eqb_spec (e_val here) 16); [|destruct (Z.eqb_spec (e_val here) 17)].
    + destruct (ttcl_needbits 4 (e_bits here + 2) wrap inp aout m1 F1 L1 ltac:(lia)
                  ltac:(pose proof (tf_bits _ _ _ _ F1); simpl; lia)) as (F2 & S2 & R2 & LL).
      set (m2 := needbits_f 4 (e_bits here + 2) m1) in *. clearbody m2.
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ttcl_res]. apply ttab_ok_brk;
          [exact F2 | right; right; unfold m_mode; rewrite S2, S1; exact Md | congruence | right; exact LL].
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ttcl_fr_drop wrap inp aout m2 (e_bits here) F2 ltac:(lia)) as [F3 B3].
        assert (I3: ttcl_inv wrap inp aout (dropbits (e_bits here) m2))
          by (apply ttcl_inv_ms with m1; [exact I1 | assumption | ..]; unfold dropbits;
              cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence).
        change (m_s (dropbits (e_bits here) m2)) with (m_s m2).
        destruct (i_have (m_s m2) =? 0).
        -- cbv beta iota. cbn [negb]. change (m_mode (set_bad (dropbits (e_bits here) m2) M_repeat)) with BAD.
           rewrite Z.eqb_refl. cbn [ttcl_res]. apply ttab_ok_bad; auto.
        -- cbv beta iota. cbn [negb]. apply ttcl_tail.
           destruct (ttcl_fr_drop wrap inp aout _ 2 F3 ltac:(lia)) as [F4 B4].
           apply ttcl_inv_ms with (dropbits (e_bits here) m2); [exact I3 | exact F4 | ..]; unfold dropbits;
             cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence.
    + destruct (ttcl_needbits 4 (e_bits here + 3) wrap inp aout m1 F1 L1 ltac:(lia)
                  ltac:(pose proof (tf_bits _ _ _ _ F1); simpl; lia)) as (F2 & S2 & R2 & LL).
      set (m2 := needbits_f 4 (e_bits here + 3) m1) in *. clearbody m2.
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ttcl_res]. apply ttab_ok_brk;
          [exact F2 | right; right; unfold m_mode; rewrite S2, S1; exact Md | congruence | right; exact LL].
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ttcl_fr_drop wrap inp aout m2 (e_bits here) F2 ltac:(lia)) as [F3 B3].
        assert (I3: ttcl_inv wrap inp aout (dropbits (e_bits here) m2))
          by (apply ttcl_inv_ms with m1; [exact I1 | assumption | ..]; unfold dropbits;
              cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence).
        cbn [negb]. apply ttcl_tail.
        destruct (ttcl_fr_drop wrap inp aout _ 3 F3 ltac:(lia)) as [F4 B4].
        apply ttcl_inv_ms with (dropbits (e_bits here) m2); [exact I3 | exact F4 | ..]; unfold dropbits;
          cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence.
    + destruct (ttcl_needbits 4 (e_bits here + 7) wrap inp aout m1 F1 L1 ltac:(lia)
                  ltac:(pose proof (tf_bits _ _ _ _ F1); simpl; lia)) as (F2 & S2 & R2 & LL).
      set (m2 := needbits_f 4 (e_bits here + 7) m1) in *. clearbody m2.
      destruct LL as [LL | (LL & NB)].
      * rewrite LL, Z.eqb_refl. cbv beta iota. cbn [negb ttcl_res]. apply ttab_ok_brk;
          [exact F2 | right; right; unfold m_mode; rewrite S2, S1; exact Md | congruence | right; exact LL].
      * rewrite LL. change (0 =? 1) with false. cbv beta iota zeta.
        destruct (ttcl_fr_drop wrap inp aout m2 (e_bits here) F2 ltac:(lia)) as [F3 B3].
        assert (I3: ttcl_inv wrap inp aout (dropbits (e_bits here) m2))
          by (apply ttcl_inv_ms with m1; [exact I1 | assumption | ..]; unfold dropbits;
              cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence).
        cbn [negb]. apply ttcl_tail.
        destruct (ttcl_fr_drop wrap inp aout _ 7 F3 ltac:(lia)) as [F4 B4].
        apply ttcl_inv_ms with (dropbits (e_bits here) m2); [exact I3 | exact F4 | ..]; unfold dropbits;
          cbn [m_leave m_ret m_s set_m_bits set_m_hold]; congruence.
Qed.

Lemma ttcl_loop : forall k wrap src pos inp aout m, ttcl_inv wrap inp aout m ->
  ttcl_res wrap src pos inp aout (codelens_loop lenfix_list distfix_list k m).
Proof.
  induction k; intros wrap src pos inp aout m I; cbn [codelens_loop]; [exact I|].
  destruct (i_have (m_s m) <? i_nlen (m_s m) + i_ndist (m_s m)); [|exact I].
  pose proof (ttcl_iter wrap src pos inp aout m I) as IT.
  destruct (codelens_iter lenfix_list distfix_list m) as [m'|m'|m']; [apply IHk; exact IT | exact IT | exact IT].
Qed.

Ltac ttcl_wh := cbn [i_wrap i_head m_s set_m_s set_m_ret set_i_lenbits set_i_next set_i_codes set_i_lencode
                     set_i_distbits set_i_distcode]; reflexivity.

Lemma ttcl_post wrap src pos inp aout m :
  ttab_fr wrap inp aout m -> m_leave m = 0 -> ttab_ok wrap src pos inp aout (ttab_clpost m).
Proof.
  intros F L. unfold ttab_clpost. cbv zeta.
  destruct (Znth 256 (i_lens (m_s m)) =? 0); [apply ttab_ok_bad; auto|].
  destruct (call_table _ _ _ _ _) as [[[r c] n] b].
  match goal with |- context [set_m_ret (set_m_s m ?s1) r] =>
    assert (F1: ttab_fr wrap inp aout (set_m_ret (set_m_s m s1) r))
      by (apply ttcl_fr_ret, ttcl_fr_s; [exact F | ttcl_wh | ttcl_wh]);
    assert (L1: m_leave (set_m_ret (set_m_s m s1) r) = 0) by exact L;
    assert (S1: m_s (set_m_ret (set_m_s m s1) r) = s1) by reflexivity;
    generalize dependent (set_m_ret (set_m_s m s1) r) end.
  intros m1 F1 L1 S1.
  destruct (negb (r =? 0)) eqn:R1.
  { apply ttab_ok_bad; [exact F1 | exact L1]. }
  destruct (call_table _ _ _ _ _) as [[[r2 c2] n2] b2].
  match goal with |- context [set_m_ret (set_m_s m1 ?s2) r2] =>
    assert (F2: ttab_fr wrap inp aout (set_m_ret (set_m_s m1 s2) r2))
      by (apply ttcl_fr_ret, ttcl_fr_s; [exact F1 | rewrite S1; ttcl_wh | rewrite S1; ttcl_wh]);
    assert (L2: m_leave (set_m_ret (set_m_s m1 s2) r2) = 0) by exact L1;
    assert (Q2: m_ret (set_m_ret (set_m_s m1 s2) r2) = r2) by reflexivity;
    generalize dependent (set_m_ret (set_m_s m1 s2) r2) end.
  intros m2 F2 L2 Q2.
  destruct (negb (r2 =? 0)) eqn:R2.
  { apply ttab_ok_bad; [exact F2 | exact L2]. }
  cbn [ttab_ok]. apply negb_false_iff, Z.eqb_eq in R2.
  split; [|split; [exact L2 | split; [exact (eq_trans Q2 R2) | reflexivity]]].
  unfold set_mode, upd_s. apply ttcl_fr_s; [exact F2 | reflexivity | reflexivity].
Qed.

(* CODELENS: the code length loop with a code length code whose root entries (read at any hold) have
   0..15 bits, then the LENS / DISTS tables *)
Lemma ttab_cl_ok wrap src pos inp aout m :
  ttab_fr wrap inp aout m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = CODELENS ->
  (forall h, lrange h ->
     0 <= e_bits (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m))
                   (h mod 2 ^ i_lenbits (m_s m))) <= 15) ->
  ttab_ok wrap src pos inp aout (ttab_cl m).
Proof.
  intros F L R Md Hb. unfold ttab_cl.
  pose proof (ttcl_loop 320 wrap src pos inp aout m (conj F (conj L (conj R (conj Md Hb))))) as LP.
  destruct (codelens_loop lenfix_list distfix_list 320 m) as [m1|m1|m1]; cbn [ttcl_res] in LP; auto.
  destruct LP as (F1 & L1 & _). apply ttcl_post; auto.
Qed.

(* helpers of ttab_llloop *)
Lemma ttll_nb_f : forall k n m,
  let m2 := needbits_f k n m in
  m_s m2 = m_s m /\ m_inp m2 = m_inp m /\ m_aout m2 = m_aout m /\ m_out m2 = m_out m /\
  m_ret m2 = m_ret m /\ (m_leave m2 = m_leave m \/ m_leave m2 = 1) /\
  (0 <= m_bits m <= 31 -> n <= 24 -> 0 <= m_bits m2 <= 31).
Proof.
  induction k; intros n m; cbn [needbits_f]; cbv zeta.
  - repeat split; auto; lia.
  - destruct (Z.ltb_spec (m_bits m) n) as [Hb|Hb].
    + destruct (m_have m =? 0).
      * unfold set_leave, set_m_leave. cbn [m_s m_inp m_aout m_out m_ret m_leave m_bits].
        repeat split; auto; lia.
      * assert (P: m_s (pull m) = m_s m /\ m_inp (pull m) = m_inp m /\ m_aout (pull m) = m_aout m /\
                   m_out (pull m) = m_out m /\ m_ret (pull m) = m_ret m /\ m_leave (pull m) = m_leave m /\
                   m_bits (pull m) = u32 (m_bits m + 8)) by (repeat split; reflexivity).
        destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
        destruct (IHk n (pull m)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
        repeat split; try congruence.
        all: try (destruct E6; [left; congruence | right; auto]).
        all: first [refine (proj1 (E7 _ _)) | refine (proj2 (E7 _ _))]; auto;
          rewrite P7; unfold u32; rewrite Z.mod_small; lia.
    + repeat split; auto; lia.
Qed.

Lemma ttll_nb_ok: forall k n m,
  m_leave m = 0 -> 0 <= m_bits m -> n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  m_leave (needbits_f k n m) <> 1 -> n <= m_bits (needbits_f k n m).
Proof.
  induction k; intros n m L B N32 N E; cbn [needbits_f] in *.
  - lia.
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (m_have m =? 0).
      * unfold set_leave, set_m_leave in E. cbn [m_leave] in E. lia.
      * apply IHk; auto; unfold pull, set_m_bits, set_m_hold, set_m_nx;
          cbn [m_leave m_bits]; unfold u32; rewrite ?Z.mod_small; lia.
    + lia.
Qed.

Lemma ttll_upd : forall m L h,
  mwf3 m -> m_mode m = LENLENS -> 0 <= h <= i_ncode (m_s m) -> Zlength L = 320 ->
  Forall (fun x => 0 <= x <= 65535) L -> (forall k, 0 <= k < h -> Znth (Znth k order) L <= 7) ->
  mwf3 (set_m_s m (set_i_have (set_i_lens (m_s m) L) h)).
Proof.
  intros m L h [W X] Md H ZL FL LE. unfold m_mode in Md.
  pose proof (mw_md _ W) as MD. pose proof (mw_s _ W) as S.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & _).
  split.
  - destruct W. constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
      m_adler m_msg m_tin m_tout m_snx m_sow set_m_s]; auto.
    all: try (constructor; cbn [i_mode i_ncode i_have i_nlen i_ndist i_lens set_i_have set_i_lens]; rewrite ?Md;
        intros; try (unfold decode_mode in *);
        unfold LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; try lia;
        repeat split; auto; lia).
    + destruct S; constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_wbits
        i_wsize i_whave i_wnext i_wdata i_hold i_bits i_length i_offset i_extra i_lencode
        i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back
        i_was i_win set_i_have set_i_lens]; auto; lia.
  - constructor; cbn [m_s set_m_s i_mode set_i_have set_i_lens]; rewrite Md;
      intros; try (unfold decode_mode in *);
      unfold HEAD, LENLENS, CODELENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT in *; lia.
Qed.

Lemma ttll_fr : forall wrap inp aout m m',
  ttab_fr wrap inp aout m -> mwf m' -> m_inp m' = m_inp m -> m_aout m' = m_aout m -> m_out m' = m_out m ->
  i_wrap (m_s m') = i_wrap (m_s m) -> i_head (m_s m') = i_head (m_s m) -> 0 <= m_bits m' <= 31 ->
  ttab_fr wrap inp aout m'.
Proof.
  intros wrap inp aout m m' F W E1 E2 E3 E4 E5 B. destruct F.
  constructor; try congruence; auto; [apply (mw_nx _ W) | apply (mw_hold _ W)].
Qed.

Lemma ttll_mwf3 : forall m m', mwf3 m -> mwf m' -> m_s m' = m_s m -> mwf3 m'.
Proof. intros m m' [_ X] W E. split; auto. rewrite E. exact X. Qed.

Lemma ttll_order_nodup: NoDup order.
Proof. unfold order. repeat constructor; simpl; intuition lia. Qed.

Lemma ttll_order_range: forall k, 0 <= k < 19 -> 0 <= Znth k order < 19.
Proof.
  intros k Hk. assert (F: Forall (fun x => 0 <= x < 19) order) by (unfold order; repeat constructor; lia).
  rewrite Forall_forall in F. apply F. apply Znth_In. change (Zlength order) with 19. lia.
Qed.

Lemma ttll_order_inj: forall i j, 0 <= i < 19 -> 0 <= j < 19 -> Znth i order = Znth j order -> i = j.
Proof.
  intros i j Hi Hj E. apply (NoDup_Znth_inj order i j ttll_order_nodup); change (Zlength order) with 19; auto.
Qed.

(* LENLENS's loop *)
Lemma ttab_llloop : forall k wrap inp aout m,
  ttab_fr wrap inp aout m -> mwf3 m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = LENLENS ->
  i_ncode (m_s m) - i_have (m_s m) <= Z.of_nat k ->
  let m1 := lenlens_loop k m in
  ttab_fr wrap inp aout m1 /\ mwf3 m1 /\ m_ret m1 = Z_OK /\ m_mode m1 = LENLENS /\
  (m_leave m1 = 1 \/ (m_leave m1 = 0 /\ i_have (m_s m1) = i_ncode (m_s m1))).
Proof.
  induction k; intros wrap inp aout m F W L R Md K; cbv zeta.
  - pose proof (md_lenlens _ (mw_md _ (mwf3_mwf _ W)) Md) as (_ & H0 & _).
    cbn [lenlens_loop]. refine (conj F (conj W (conj R (conj Md _)))). right. split; auto. simpl in K. lia.
  - pose proof (md_lenlens _ (mw_md _ (mwf3_mwf _ W)) Md) as (Hc & H0 & Hnl & Hnd & LE).
    cbn [lenlens_loop].
    destruct (Z.ltb_spec (i_have (m_s m)) (i_ncode (m_s m))) as [Hh|Hh];
      [| refine (conj F (conj W (conj R (conj Md _)))); right; split; auto; lia].
    pose proof (mwf3_mwf _ W) as W0.
    destruct (ttll_nb_f 4 3 m) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbv zeta in E1, E2, E3, E4, E5, E6, E7.
    change (needbits_f 4 3 m) with (needbits 3 m) in E1, E2, E3, E4, E5, E6, E7.
    assert (W2: mwf (needbits 3 m)) by (apply mwf_needbits; auto; lia).
    assert (B2: 0 <= m_bits (needbits 3 m) <= 31) by (apply E7; [apply (tf_bits _ _ _ _ F) | lia]).
    assert (F2: ttab_fr wrap inp aout (needbits 3 m)) by (apply ttll_fr with m; rewrite ?E1; auto).
    assert (X2: mwf3 (needbits 3 m)) by (apply ttll_mwf3 with m; auto).
    assert (Md2: m_mode (needbits 3 m) = LENLENS) by (unfold m_mode; rewrite E1; exact Md).
    destruct (Z.eqb_spec (m_leave (needbits 3 m)) 1) as [EL|EL].
    { refine (conj F2 (conj X2 (conj _ (conj Md2 (or_introl EL))))). congruence. }
    assert (L2: m_leave (needbits 3 m) = 0) by lia.
    assert (NB: 3 <= m_bits (needbits 3 m)).
    { apply (ttll_nb_ok 4 3 m); auto; try lia; [apply (tf_bits _ _ _ _ F) | pose proof (tf_bits _ _ _ _ F); simpl; lia]. }
    generalize dependent (needbits 3 m). intros m2 E1 E2 E3 E4 E5 E6 E7 W2 B2 F2 X2 Md2 EL L2 NB.
    rewrite E1.
    pose proof (sw_lens _ (mw_s _ W0)) as [ZL FL].
    pose proof (ttll_order_range (i_have (m_s m)) ltac:(lia)) as OR.
    assert (BR: 0 <= bitsn m2 3 < 2 ^ 3) by (unfold bitsn; apply Z.mod_pos_bound; lia).
    set (L' := upd_Znth (Znth (i_have (m_s m)) order) (i_lens (m_s m)) (bitsn m2 3)).
    assert (X3: mwf3 (set_m_s m2 (set_i_have (set_i_lens (m_s m2) L') (i_have (m_s m) + 1)))).
    { apply ttll_upd; rewrite ?E1; auto; try lia.
      - unfold L'. rewrite upd_Znth_Zlength; lia.
      - unfold L'. apply Forall_upd_Znth; auto. lia.
      - intros k' Hk'. unfold L'. destruct (Z.eq_dec k' (i_have (m_s m))).
        + subst k'. rewrite upd_Znth_same by lia. lia.
        + pose proof (ttll_order_range k' ltac:(lia)).
          rewrite upd_Znth_diff by (try lia; intros E; apply n; apply ttll_order_inj; auto; lia).
          apply LE; lia. }
    rewrite E1 in X3. unfold upd_s. cbv beta.
    set (s3 := set_i_have (set_i_lens (m_s m) L') (i_have (m_s m) + 1)) in X3 |- *.
    set (m3 := set_m_s m2 s3) in X3 |- *.
    assert (D1: m_s (dropbits 3 m3) = s3) by reflexivity.
    assert (D2: m_inp (dropbits 3 m3) = m_inp m2) by reflexivity.
    assert (D3: m_aout (dropbits 3 m3) = m_aout m2) by reflexivity.
    assert (D4: m_out (dropbits 3 m3) = m_out m2) by reflexivity.
    assert (D5: m_ret (dropbits 3 m3) = m_ret m2) by reflexivity.
    assert (D6: m_leave (dropbits 3 m3) = m_leave m2) by reflexivity.
    assert (D7: m_bits (dropbits 3 m3) = u32 (m_bits m2 - 3)) by reflexivity.
    assert (D8: m_bits m3 = m_bits m2) by reflexivity.
    assert (S1: i_wrap s3 = i_wrap (m_s m) /\ i_head s3 = i_head (m_s m) /\ i_mode s3 = i_mode (m_s m) /\
                i_ncode s3 = i_ncode (m_s m) /\ i_have s3 = i_have (m_s m) + 1) by (repeat split; reflexivity).
    destruct S1 as (S1 & S2 & S3 & S4 & S5).
    unfold u32 in D7. rewrite Z.mod_small in D7 by lia.
    assert (W4: mwf (dropbits 3 m3)) by (apply mwf_dropbits; [apply (mwf3_mwf _ X3) | lia]).
    apply IHk.
    + apply ttll_fr with m2; auto; try congruence;
        try (rewrite D1, S1, E1; reflexivity); try (rewrite D1, S2, E1; reflexivity); lia.
    + apply ttll_mwf3 with m3; auto.
    + congruence.
    + congruence.
    + unfold m_mode. rewrite D1, S3. exact Md.
    + rewrite D1, S4, S5. lia.
Qed.

(* LENLENS: from a loop head *)

Lemma ttab_fact_result : Zlib.proof.inftrees.facts.fact_result.
Proof.
  exact (part_result.fact_result_ok part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2
           part_subbits.subbits_ok2
           (part_size.size_ok2 part_sorted.sorted_ok2 part_rfc.rfc_ok2 part_bits.bits_ok2)).
Qed.

Lemma ttab_order_nodup: NoDup order.
Proof. unfold order. repeat constructor; simpl; intuition lia. Qed.

Lemma ttab_order_range: forall k, 0 <= k < 19 -> 0 <= Znth k order < 19.
Proof.
  intros k Hk. assert (F: Forall (fun x => 0 <= x < 19) order) by (unfold order; repeat constructor; lia).
  rewrite Forall_forall in F. apply F. apply Znth_In. change (Zlength order) with 19. lia.
Qed.

Lemma ttab_order_inj: forall i j, 0 <= i < 19 -> 0 <= j < 19 -> Znth i order = Znth j order -> i = j.
Proof.
  intros i j Hi Hj E. apply (NoDup_Znth_inj order i j ttab_order_nodup); change (Zlength order) with 19; auto.
Qed.

Lemma ttab_order_surj: forall x, 0 <= x < 19 -> exists k, 0 <= k < 19 /\ Znth k order = x.
Proof.
  intros x Hx. assert (IN: In x order) by (unfold order; simpl; lia).
  apply In_Znth in IN. destruct IN as (k & Hk & E). change (Zlength order) with 19 in Hk. eauto.
Qed.

Lemma ttab_maxlen_le: forall l, Forall (fun x => 0 <= x <= 7) l -> 0 <= maxlen l <= 7.
Proof.
  induction l; intros F; simpl; [unfold maxlen; simpl; lia|]. inversion F; subst.
  specialize (IHl H2). unfold maxlen in *. simpl. lia.
Qed.

Lemma ttab_lenlens_zero: forall n s, 0 <= i_have s <= 19 -> 19 <= i_have s + Z.of_nat n ->
  Zlength (i_lens s) = 320 -> Forall (fun x => 0 <= x <= 65535) (i_lens s) ->
  (forall k, 0 <= k < i_have s -> Znth (Znth k order) (i_lens s) <= 7) ->
  exists L, lenlens_zero n s = set_i_have (set_i_lens s L) 19 /\ Zlength L = 320 /\
    Forall (fun x => 0 <= x <= 65535) L /\ (forall k, 0 <= k < 19 -> Znth (Znth k order) L <= 7).
Proof.
  induction n; intros s H0 Hn ZL FL LE.
  - exists (i_lens s). simpl in Hn. assert (i_have s = 19) by lia.
    split; [destruct s; simpl in *; subst; reflexivity|]. split; [auto|]. split; [auto|].
    intros k Hk. apply LE. lia.
  - cbn [lenlens_zero]. destruct (Z.ltb_spec (i_have s) 19).
    + pose proof (ttab_order_range (i_have s) ltac:(lia)) as OR.
      destruct (IHn (set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) 0)) (i_have s + 1)))
        as (L & E & ZL1 & FL1 & LE1); simpl; try lia.
      * rewrite upd_Znth_Zlength; lia.
      * apply Forall_upd_Znth; auto; lia.
      * intros k Hk. destruct (Z.eq_dec k (i_have s)).
        -- subst k. rewrite upd_Znth_same by lia. lia.
        -- pose proof (ttab_order_range k ltac:(lia)).
           rewrite upd_Znth_diff by (try lia; intros E; apply n0; apply ttab_order_inj; auto; lia).
           apply LE; lia.
      * exists L. rewrite E. split; [reflexivity | auto].
    + exists (i_lens s). assert (i_have s = 19) by lia.
      split; [destruct s; simpl in *; subst; reflexivity|]. split; [auto|]. split; [auto|].
      intros k Hk. apply LE. lia.
Qed.

Lemma ttab_forall_sublist: forall (P: Z -> Prop) lo hi l, 0 <= lo <= hi -> hi <= Zlength l ->
  (forall k, lo <= k < hi -> P (Znth k l)) -> Forall P (sublist lo hi l).
Proof.
  intros P lo hi l H1 H2 H. rewrite Forall_forall. intros x IN.
  apply In_Znth in IN. destruct IN as (i & Hi & E). subst x.
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma ttab_entry_bits_nonneg (l: list entry) i : Forall entry_ok l -> 0 <= e_bits (Znth i l).
Proof.
  intros F. destruct (zlt i 0) as [H|H]; [rewrite Znth_outofbounds by lia; simpl; lia|].
  destruct (zlt i (Zlength l)) as [H'|H']; [|rewrite Znth_outofbounds by lia; simpl; lia].
  rewrite Forall_Znth in F. destruct (F i ltac:(lia)) as (_ & B & _). lia.
Qed.

(* the code length code table of a successful call: entries with bits >= 0 *)
Lemma ttab_codes_ok s r codes nxt lb :
  swf s -> i_next s = 0 ->
  (forall x, 0 <= x < 19 -> 0 <= Znth x (i_lens s) <= 7) ->
  call_table CODES 0 19 7 s = (r, codes, nxt, lb) -> r = 0 ->
  Forall entry_ok codes.
Proof.
  intros S N0 LE CT R0.
  set (L := sublist 0 (0 + 19) (i_lens s)).
  set (old := sublist (i_next s) ENOUGH_CODES (i_codes s)).
  destruct (sw_codes _ S) as [ZC FC]. destruct (sw_lens _ S) as [ZL FL].
  assert (F07: Forall (fun x => 0 <= x <= 7) L).
  { apply ttab_forall_sublist; try lia. intros k Hk. apply LE; lia. }
  assert (IN: inputs_ok CODES L 7).
  { unfold inputs_ok. unfold L. rewrite Zlength_sublist by lia. split; [unfold CODES; lia|].
    split; [unfold max_codes; simpl; lia|]. split; [|lia].
    eapply Forall_impl; [|exact F07]. unfold MAXBITS; simpl; intros; lia. }
  assert (ZO: Zlength old = 1444).
  { unfold old. rewrite N0. rewrite Zlength_sublist; unfold ENOUGH_CODES in *; lia. }
  assert (CAP: cap_ok CODES L 7 (Zlength old)).
  { pose proof (ttab_maxlen_le _ F07) as ML. rewrite ZO.
    unfold cap_ok. unfold LENS, CODES, DISTS. split; [|split; intros; discriminate].
    intros _. split; [lia|]. split; [lia|]. rewrite Z.shiftl_1_l.
    assert (2 ^ maxlen L <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 7) with 128 in *. lia. }
  assert (FO: Forall entry_ok old) by (apply Forall_sublist; auto).
  pose proof (ttab_fact_result CODES L 7 old IN CAP FO) as FR.
  unfold call_table in CT. fold old in CT. fold L in CT.
  destruct (Zlib.proof.inftrees.ref.expected_call CODES L 7) as [[want root] size].
  destruct (inflate_table_model CODES L 7 old) as [ | t | root' used t];
    cbn [it_ret it_tab it_adv it_bits] in CT; injection CT as E1 E2 E3 E4.
  - rewrite <- E1 in R0. discriminate.
  - rewrite <- E1 in R0. discriminate.
  - destruct FR as (_ & _ & _ & _ & _ & _ & FT & _).
    rewrite <- E2. rewrite N0. rewrite sublist_nil. exact FT.
Qed.

Lemma ttab_mwf3_override m h :
  mwf3 m -> lrange h -> mwf3 (set_m_nx (set_m_bits (set_m_hold m h) 0) (Zlength (m_inp m))).
Proof.
  intros [W S] Hh. split; [|exact S].
  destruct W; constructor; cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
    m_adler m_msg m_tin m_tout m_snx m_sow set_m_nx set_m_bits set_m_hold]; auto; try lia.
Qed.

Lemma ttab_cl_step k m : codelens_loop lenfix_list distfix_list (S k) m =
  (if i_have (m_s m) <? i_nlen (m_s m) + i_ndist (m_s m) then
     match codelens_iter lenfix_list distfix_list m with
     | CLnext m' => codelens_loop lenfix_list distfix_list k m'
     | o => o
     end
   else CLnext m).
Proof. reflexivity. Qed.

Lemma ttab_lk_step k fx dx t nb m : lookup1_f (S k) fx dx t nb m =
  (let here := tab_entry fx dx (m_s m) t (bitsn m nb) in
   if e_bits here <=? m_bits m then (here, m, true)
   else if m_have m =? 0 then (here, set_leave m, false)
   else lookup1_f k fx dx t nb (pull m)).
Proof. reflexivity. Qed.

Lemma ttab_ll_step k m : lenlens_loop (S k) m =
  (if i_have (m_s m) <? i_ncode (m_s m) then
     let m := needbits 3 m in
     if m_leave m =? 1 then m else
     let s := m_s m in
     let m := upd_s m (fun _ => set_i_have (set_i_lens s (upd_Znth (Znth (i_have s) order) (i_lens s) (bitsn m 3)))
                                            (i_have s + 1)) in
     lenlens_loop k (dropbits 3 m)
   else m).
Proof. reflexivity. Qed.

(* a CODELENS head whose first lookup needs a bit more and has no input: the pass leaves at once *)
Lemma ttab_cl_leave mc :
  i_have (m_s mc) < i_nlen (m_s mc) + i_ndist (m_s mc) -> m_have mc = 0 ->
  m_bits mc < e_bits (tab_entry lenfix_list distfix_list (m_s mc) (i_lencode (m_s mc))
                        (bitsn mc (i_lenbits (m_s mc)))) ->
  ttab_cl mc = TTDone (IBrk (set_leave mc)).
Proof.
  intros H1 H2 H3. unfold ttab_cl. change 320%nat with (S 319). rewrite ttab_cl_step.
  rewrite (proj2 (Z.ltb_lt _ _) H1).
  unfold codelens_iter. unfold lookup1. change 3%nat with (S 2). rewrite ttab_lk_step. cbv zeta.
  rewrite (proj2 (Z.leb_gt _ _) H3). rewrite H2, Z.eqb_refl. reflexivity.
Qed.

Lemma ttab_fr_s wrap inp aout m s r :
  ttab_fr wrap inp aout m -> i_wrap s = i_wrap (m_s m) -> i_head s = i_head (m_s m) ->
  ttab_fr wrap inp aout (set_m_ret (set_m_s m s) r).
Proof. intros [] E1 E2. constructor; cbn [m_s m_inp m_aout m_out m_nx m_hold m_bits set_m_ret set_m_s]; congruence. Qed.

(* the root entries of a valid table have 0..15 bits *)
Lemma ttab_tv_bits kind fx dx s t rb h :
  tvalid kind fx dx s t rb -> 0 <= e_bits (tab_entry fx dx s t (h mod 2 ^ rb)) <= 15.
Proof.
  intros (sz & _ & [R _ T]).
  assert (Hi: 0 <= h mod 2 ^ rb < 2 ^ rb) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (T _ Hi) as [E F]. cbv zeta in F. destruct E as (_ & E & _).
  destruct (islink kind (e_op (tab_entry fx dx s t (h mod 2 ^ rb)))).
  - destruct F as (F & _). lia.
  - lia.
Qed.

Lemma ttab_llpost_ok (SM: stepf2_mwf3_stmt) wrap src pos inp aout m1 :
  ttab_fr wrap inp aout m1 -> mwf3 m1 -> m_leave m1 = 0 -> m_ret m1 = Z_OK -> m_mode m1 = LENLENS ->
  i_have (m_s m1) = i_ncode (m_s m1) ->
  ttab_ok wrap src pos inp aout (ttab_llpost m1).
Proof.
  intros F W L R Md HH.
  pose proof (mw_s _ (mwf3_mwf _ W)) as SW. pose proof (mw_md _ (mwf3_mwf _ W)) as MD.
  destruct (md_lenlens _ MD Md) as (Hc & H0 & Hnl & Hnd & LE).
  destruct (sw_lens _ SW) as [ZL FL].
  destruct (ttab_lenlens_zero 19 (m_s m1) ltac:(lia) ltac:(simpl; lia) ZL FL LE) as (L0 & EZ & ZL0 & FL0 & LE0).
  assert (LE7: forall x, 0 <= x < 19 -> 0 <= Znth x L0 <= 7).
  { intros x Hx. destruct (ttab_order_surj x Hx) as (k & Hk & <-). split; [|apply LE0; auto].
    rewrite Forall_forall in FL0. apply FL0. apply Znth_In. pose proof (ttab_order_range k Hk). lia. }
  unfold ttab_llpost. cbv zeta. rewrite EZ.
  set (s0 := set_i_lenbits (set_i_distcode (set_i_lencode (set_i_next (set_i_have (set_i_lens (m_s m1) L0) 19) 0)
                (TCodes 0)) (TCodes 0)) 7).
  assert (S0: swf s0) by (destruct SW; constructor; simpl; auto; unfold tref_ok, ENOUGH_CODES; lia).
  destruct (call_table CODES 0 19 7 s0) as [[[r codes] nxt] lb] eqn:CT.
  destruct (Z.eqb_spec r 0) as [R0|R0].
  2:{ cbn [negb]. apply ttab_ok_bad; [apply ttab_fr_s; auto | exact L]. }
  subst r. cbn [negb].
  pose proof (ttab_codes_ok s0 0 codes nxt lb S0 eq_refl LE7 CT eq_refl) as FC.
  set (s1 := set_i_lenbits (set_i_next (set_i_codes s0 codes) nxt) lb).
  set (mc := set_mode (upd_s (set_m_ret (set_m_s m1 s1) 0) (fun s => set_i_have s 0)) CODELENS).
  apply ttab_cl_ok.
  - unfold mc, set_mode, upd_s. destruct F. constructor; cbn [m_s m_inp m_aout m_out m_nx m_hold m_bits
      set_m_ret set_m_s i_wrap i_head set_i_mode set_i_have]; auto.
  - exact L.
  - reflexivity.
  - reflexivity.
  - intros h Hh. change (m_s mc) with (set_i_mode (set_i_have s1 0) CODELENS).
    cbn [i_lencode i_lenbits i_codes set_i_mode set_i_have s1 s0 set_i_lenbits set_i_next set_i_codes
         set_i_distcode set_i_lencode set_i_lens tab_entry].
    split; [apply ttab_entry_bits_nonneg; exact FC|].
    destruct (Z.le_gt_cases (e_bits (Znth (0 + h mod 2 ^ lb) codes)) 15) as [B|B]; [exact B|exfalso].
    (* the hold-override trick: a LENLENS head with hold h, no bits, no input *)
    set (m' := set_m_nx (set_m_bits (set_m_hold m1 h) 0) (Zlength (m_inp m1))).
    assert (W': mwf3 m') by (apply ttab_mwf3_override; auto).
    assert (Ms: m_s m' = m_s m1) by reflexivity.
    assert (Md': m_mode m' = LENLENS) by exact Md.
    set (mc' := set_mode (upd_s (set_m_ret (set_m_s m' s1) 0) (fun s => set_i_have s 0)) CODELENS).
    assert (EP: ttab_ll m' = TTDone (IBrk (set_leave mc'))).
    { unfold ttab_ll. cbv zeta.
      replace (lenlens_loop 19 m') with m'
        by (change 19%nat with (S 18); rewrite ttab_ll_step, Ms, HH, Z.ltb_irrefl; reflexivity).
      replace (m_leave m' =? 1) with false by (cbn; rewrite L; reflexivity).
      unfold ttab_llpost. cbv zeta. rewrite Ms, EZ. fold s0. rewrite CT. cbn [negb Z.eqb].
      fold s1. fold mc'.
      apply ttab_cl_leave.
      - change (m_s mc') with (set_i_mode (set_i_have s1 0) CODELENS).
        unfold s1, s0. cbn [i_have i_nlen i_ndist set_i_mode set_i_have set_i_lenbits set_i_next set_i_codes
          set_i_distcode set_i_lencode set_i_lens]. lia.
      - unfold mc', m', set_mode, upd_s, m_have.
        cbn [m_inp m_nx set_m_s set_m_ret set_m_nx set_m_bits set_m_hold]. lia.
      - change (m_bits mc') with 0.
        change (tab_entry lenfix_list distfix_list (m_s mc') (i_lencode (m_s mc'))
                  (bitsn mc' (i_lenbits (m_s mc')))) with (Znth (0 + h mod 2 ^ lb) codes).
        lia. }
    pose proof (SM 0 m' W' ltac:(cbn; exact L)) as WE.
    assert (E0: stepf2 0 lenfix_list distfix_list m' = ttab_run 0 (ttab_ll m')).
    { rewrite <- (ttab_ll_eq 0 m'). unfold stepf2, step2. rewrite Md'. reflexivity. }
    rewrite E0, EP in WE. cbn [ttab_run] in WE.
    assert (MC: i_mode (m_s (set_leave mc')) = CODELENS) by reflexivity.
    destruct (md_codelens _ (mw_md _ (mwf3_mwf _ WE)) MC) as (_ & _ & _ & _ & TV & _).
    pose proof (ttab_tv_bits _ _ _ _ _ _ h TV) as TB.
    change (tab_entry lenfix_list distfix_list (m_s (set_leave mc')) (i_lencode (m_s (set_leave mc')))
              (h mod 2 ^ i_lenbits (m_s (set_leave mc')))) with (Znth (0 + h mod 2 ^ lb) codes) in TB.
    lia.
Qed.

Lemma ttab_ll_ok wrap src pos inp aout m :
  stepf2_mwf3_stmt ->
  ttab_fr wrap inp aout m -> mwf3 m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = LENLENS ->
  ttab_ok wrap src pos inp aout (ttab_ll m).
Proof.
  intros SM F W L R Md.
  destruct (md_lenlens _ (mw_md _ (mwf3_mwf _ W)) Md) as (Hc & H0 & _).
  destruct (ttab_llloop 19 wrap inp aout m F W L R Md ltac:(simpl; lia)) as (F1 & W1 & R1 & M1 & LV).
  unfold ttab_ll. cbv zeta. revert F1 W1 R1 M1 LV. generalize (lenlens_loop 19 m) as m1.
  intros m1 F1 W1 R1 M1 LV.
  destruct LV as [L1|[L1 HH]].
  - rewrite L1, Z.eqb_refl. apply ttab_ok_brk; auto.
  - rewrite L1. change (0 =? 1) with false. cbv iota.
    apply ttab_llpost_ok; auto.
Qed.

(* TABLE's helpers *)
Lemma tttb_nb : forall k n m, n <= 24 -> 0 <= m_bits m ->
  m_inp (needbits_f k n m) = m_inp m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_out (needbits_f k n m) = m_out m /\ m_s (needbits_f k n m) = m_s m /\
  m_ret (needbits_f k n m) = m_ret m /\ m_bits (needbits_f k n m) <= Z.max (m_bits m) (n + 7).
Proof.
  induction k; intros n m N B; cbn [needbits_f]; [repeat split; auto; lia|].
  destruct (Z.ltb_spec (m_bits m) n); [|repeat split; auto; lia].
  destruct (m_have m =? 0); [unfold set_leave; cbn; repeat split; auto; lia|].
  assert (PB: m_bits (pull m) = m_bits m + 8)
    by (unfold pull, u32; cbn [m_bits set_m_bits]; rewrite Z.mod_small; lia).
  destruct (IHk n (pull m) N ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6).
  rewrite A1, A2, A3, A4, A5. rewrite PB in A6. repeat split; try reflexivity. lia.
Qed.

Lemma tttb_nb_ok : forall k n m,
  m_leave m = 0 -> 0 <= m_bits m -> n <= 32 -> n <= m_bits m + 8 * Z.of_nat k ->
  m_leave (needbits_f k n m) <> 1 -> n <= m_bits (needbits_f k n m) /\ m_leave (needbits_f k n m) = 0.
Proof.
  induction k; intros n m L B N F E; cbn [needbits_f] in *.
  - split; [lia | auto].
  - destruct (Z.ltb_spec (m_bits m) n).
    + destruct (m_have m =? 0).
      * unfold set_leave in E. cbn in E. lia.
      * apply IHk; auto; unfold pull, u32; cbn [m_bits m_leave set_m_bits set_m_hold set_m_nx];
          rewrite ?Z.mod_small; lia.
    + split; [lia | auto].
Qed.

Lemma tttb_drop wrap inp aout m n : ttab_fr wrap inp aout m -> 0 <= n <= m_bits m ->
  ttab_fr wrap inp aout (dropbits n m) /\ m_bits (dropbits n m) = m_bits m - n.
Proof.
  intros [] H.
  assert (E: m_bits (dropbits n m) = m_bits m - n)
    by (unfold dropbits, u32; cbn [m_bits set_m_bits]; rewrite Z.mod_small; lia).
  split; [|exact E].
  constructor; rewrite ?E; unfold dropbits; cbn [m_inp m_aout m_s m_out m_nx m_hold set_m_bits set_m_hold];
    auto; try lia.
  unfold lrange in *. apply Zshiftr_range; lia.
Qed.

Lemma tttb_fr_s wrap inp aout m s' : ttab_fr wrap inp aout m ->
  i_wrap s' = i_wrap (m_s m) -> i_head s' = i_head (m_s m) -> ttab_fr wrap inp aout (set_m_s m s').
Proof. intros [] A B. constructor; cbn [m_inp m_aout m_s m_out m_nx m_hold m_bits set_m_s]; auto; congruence. Qed.

Lemma tttb_mwf_s m s' : mwf m -> swf s' -> modewf s' -> m_out m = m_aout m -> mwf (set_m_s m s').
Proof.
  intros [] S M O. constructor; unfold m_mode, m_have, m_left in *;
    cbn [m_inp m_aout m_s m_h m_out m_nx m_ow m_hold m_bits m_in m_ret m_leave m_adler m_tin m_tout m_snx m_sow
         set_m_s]; auto.
Qed.

Lemma tttb_s1 s a b c : swf s -> 0 <= a <= 288 -> 0 <= b <= 32 -> 0 <= c <= 19 ->
  swf (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) /\
  i_wrap (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) = i_wrap s /\
  i_head (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) = i_head s /\
  i_nlen (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) = a /\
  i_ndist (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) = b /\
  i_ncode (set_i_ncode (set_i_ndist (set_i_nlen s a) b) c) = c.
Proof.
  intros [] A B C. split; [|repeat split; reflexivity].
  constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
           i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits
           i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
           set_i_mode set_i_have set_i_ncode set_i_ndist set_i_nlen]; auto.
Qed.

Lemma tttb_s2 s : swf s ->
  swf (set_i_mode (set_i_have s 0) LENLENS) /\ i_mode (set_i_mode (set_i_have s 0) LENLENS) = LENLENS /\
  i_have (set_i_mode (set_i_have s 0) LENLENS) = 0 /\
  i_wrap (set_i_mode (set_i_have s 0) LENLENS) = i_wrap s /\
  i_head (set_i_mode (set_i_have s 0) LENLENS) = i_head s /\
  i_nlen (set_i_mode (set_i_have s 0) LENLENS) = i_nlen s /\
  i_ndist (set_i_mode (set_i_have s 0) LENLENS) = i_ndist s /\
  i_ncode (set_i_mode (set_i_have s 0) LENLENS) = i_ncode s.
Proof.
  intros []. split; [|repeat split; reflexivity].
  constructor; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
           i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits
           i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
           set_i_mode set_i_have set_i_ncode set_i_ndist set_i_nlen]; auto; unfold LENLENS, HEAD, SYNC; lia.
Qed.

Lemma tttb_E m s :
  set_mode (set_m_s (set_m_s m s) (set_i_have (m_s (set_m_s m s)) 0)) LENLENS =
  set_m_s m (set_i_mode (set_i_have s 0) LENLENS).
Proof. reflexivity. Qed.

(* after NEEDBITS(14) and the three DROPBITS *)
Lemma tttb_post wrap src pos inp aout (LL: mst -> ttab_res) m5 a1 a2 a3 :
  (forall m', ttab_fr wrap inp aout m' -> mwf3 m' -> m_leave m' = 0 -> m_ret m' = Z_OK ->
     m_mode m' = LENLENS -> ttab_ok wrap src pos inp aout (LL m')) ->
  ttab_fr wrap inp aout m5 -> mwf m5 -> m_leave m5 = 0 -> m_ret m5 = Z_OK -> m_out m5 = m_aout m5 ->
  0 <= a1 < 32 -> 0 <= a2 < 32 -> 0 <= a3 < 16 ->
  ttab_ok wrap src pos inp aout
    (let m := upd_s m5 (fun s => set_i_ncode (set_i_ndist (set_i_nlen s (a1 + 257)) (a2 + 1)) (a3 + 4)) in
     if orb (286 <? a1 + 257) (30 <? a2 + 1) then TTDone (IBrk (set_bad m M_toomany)) else
     LL (set_mode (upd_s m (fun s => set_i_have s 0)) LENLENS)).
Proof.
  intros HLL F5 W5 L5 R5 O5 X1 X2 X3. cbv zeta.
  unfold upd_s. cbv beta.
  set (s' := set_i_ncode (set_i_ndist (set_i_nlen (m_s m5) (a1 + 257)) (a2 + 1)) (a3 + 4)).
  destruct (tttb_s1 (m_s m5) (a1 + 257) (a2 + 1) (a3 + 4) (mw_s _ W5) ltac:(lia) ltac:(lia) ltac:(lia))
    as (SW' & Wr' & Hd' & Ls' & Ds' & Cs').
  fold s' in SW', Wr', Hd', Ls', Ds', Cs'. clearbody s'.
  assert (F6: ttab_fr wrap inp aout (set_m_s m5 s')) by (apply tttb_fr_s; auto).
  destruct (orb (286 <? a1 + 257) (30 <? a2 + 1)) eqn:TM.
  { apply ttab_ok_bad; auto. }
  apply orb_false_iff in TM. destruct TM as [T1 T2]. apply Z.ltb_ge in T1. apply Z.ltb_ge in T2.
  rewrite tttb_E.
  destruct (tttb_s2 s' SW') as (SW'' & Ms'' & Hs'' & Wr'' & Hd'' & Ls'' & Ds'' & Cs'').
  set (s'' := set_i_mode (set_i_have s' 0) LENLENS) in *. clearbody s''.
  assert (ND: ~ decode_mode (i_mode s'')) by (rewrite Ms''; unfold decode_mode, LENLENS, LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT; lia).
  assert (MW: modewf s'').
  { constructor; rewrite ?Ms''; unfold LENLENS, CODELENS, LENEXT, DISTEXT, MATCH, DIST; try (intros; lia).
    - intros _. rewrite Hs'', Cs'', Ls'', Ds'', Cs', Ls', Ds'. repeat split; intros; lia.
    - intros D; exfalso; apply ND; rewrite Ms''; exact D. }
  apply HLL.
  - apply tttb_fr_s; auto; congruence.
  - split; [apply tttb_mwf_s; auto|].
    constructor; cbn [m_s set_m_s]; rewrite ?Ms''; unfold LENLENS, HEAD, LENEXT, DISTEXT; try (intros; lia).
    intros D; exfalso; apply ND; rewrite Ms''; exact D.
  - exact L5.
  - exact R5.
  - exact Ms''.
Qed.

(* TABLE: from a loop head, given the LENLENS part *)
Lemma ttab_tab_ok wrap src pos inp aout m :
  (forall m', ttab_fr wrap inp aout m' -> mwf3 m' -> m_leave m' = 0 -> m_ret m' = Z_OK ->
     m_mode m' = LENLENS -> ttab_ok wrap src pos inp aout (ttab_ll m')) ->
  ttab_fr wrap inp aout m -> mwf3 m -> m_leave m = 0 -> m_ret m = Z_OK -> m_mode m = TABLE ->
  ttab_ok wrap src pos inp aout (ttab_tab m).
Proof.
  intros HLL F W L R Md.
  pose proof (mwf3_mwf _ W) as W1.
  pose proof (tf_bits _ _ _ _ F) as B0.
  unfold ttab_tab. cbv zeta.
  pose proof (tttb_nb 4 14 m ltac:(lia) ltac:(lia)) as (N1 & N2 & N3 & N4 & N5 & N6).
  change (needbits_f 4 14 m) with (needbits 14 m) in *.
  assert (W2: mwf (needbits 14 m)) by (apply mwf_needbits; auto; lia).
  assert (F2: ttab_fr wrap inp aout (needbits 14 m)).
  { destruct F. constructor; try congruence.
    - pose proof (mw_nx _ W2). congruence.
    - apply (mw_hold _ W2).
    - pose proof (mw_bits _ W2). lia. }
  assert (OK2: m_leave (needbits 14 m) <> 1 -> 14 <= m_bits (needbits 14 m) /\ m_leave (needbits 14 m) = 0)
    by (intros E; apply tttb_nb_ok; auto; lia).
  set (m2 := needbits 14 m) in *. clearbody m2.
  destruct (Z.eqb_spec (m_leave m2) 1) as [EL|EL].
  { apply ttab_ok_brk; auto.
    - left. unfold m_mode. rewrite N4. exact Md.
    - congruence. }
  destruct (OK2 EL) as [B2 L2]. clear OK2 EL.
  destruct (tttb_drop _ _ _ m2 5 F2 ltac:(lia)) as [F3 B3].
  destruct (tttb_drop _ _ _ (dropbits 5 m2) 5 F3 ltac:(lia)) as [F4 B4].
  destruct (tttb_drop _ _ _ (dropbits 5 (dropbits 5 m2)) 4 F4 ltac:(lia)) as [F5 B5].
  assert (W5: mwf (dropbits 4 (dropbits 5 (dropbits 5 m2)))).
  { apply mwf_dropbits; [|lia]. apply mwf_dropbits; [|lia]. apply mwf_dropbits; auto; lia. }
  assert (S5: m_s (dropbits 4 (dropbits 5 (dropbits 5 m2))) = m_s m2) by reflexivity.
  assert (L5: m_leave (dropbits 4 (dropbits 5 (dropbits 5 m2))) = 0) by exact L2.
  assert (R5: m_ret (dropbits 4 (dropbits 5 (dropbits 5 m2))) = Z_OK) by (cbn; congruence).
  assert (O5: m_out (dropbits 4 (dropbits 5 (dropbits 5 m2))) = m_aout (dropbits 4 (dropbits 5 (dropbits 5 m2))))
    by (apply (tf_out _ _ _ _ F5)).
  pose proof (Z.mod_pos_bound (m_hold m2) (2 ^ 5) ltac:(lia)) as X1.
  pose proof (Z.mod_pos_bound (m_hold (dropbits 5 m2)) (2 ^ 5) ltac:(lia)) as X2.
  pose proof (Z.mod_pos_bound (m_hold (dropbits 5 (dropbits 5 m2))) (2 ^ 4) ltac:(lia)) as X3.
  unfold bitsn in *.
  set (a1 := m_hold m2 mod 2 ^ 5) in *. set (a2 := m_hold (dropbits 5 m2) mod 2 ^ 5) in *.
  set (a3 := m_hold (dropbits 5 (dropbits 5 m2)) mod 2 ^ 4) in *.
  clearbody a1 a2 a3.
  set (m5 := dropbits 4 (dropbits 5 (dropbits 5 m2))) in *. clearbody m5.
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  exact (tttb_post wrap src pos inp aout ttab_ll m5 a1 a2 a3 HLL F5 W5 L5 R5 O5 X1 X2 X3).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Assembly                                                                                        *)

Lemma ttab_mwf3_unleave m : mwf3 (set_leave m) -> m_leave m = 0 -> mwf3 m.
Proof.
  intros [W S] L. split; [|exact S].
  destruct W; constructor; auto; lia.
Qed.

Lemma ttab_fr_leave wrap inp aout m : ttab_fr wrap inp aout m -> ttab_fr wrap inp aout (set_leave m).
Proof. intros []. constructor; auto. Qed.

Lemma ttab_fr_head wrap src pos inp aout m :
  Kc wrap src pos inp aout m -> mwf3 m -> m_mode m <> BAD -> m_mode m <> MEM -> m_mode m <> LENGTH ->
  m_mode m <> DONE -> ttab_fr wrap inp aout m.
Proof.
  intros K W H1 H2 H3 H4. pose proof (mwf3_mwf _ W) as W1.
  constructor.
  - apply (kc_inp _ _ _ _ _ _ K).
  - apply (kc_aout _ _ _ _ _ _ K).
  - apply (kc_wrap _ _ _ _ _ _ K).
  - apply (kc_head _ _ _ _ _ _ K).
  - apply mwf_out_eq; auto.
  - apply (mw_nx _ W1).
  - apply (mw_hold _ W1).
  - apply (kc_bits _ _ _ _ _ _ K); auto.
Qed.

Lemma ttab_final (SM: stepf2_mwf3_stmt) (DEC: group_ok decode_mode) wrap src pos inp aout flush m P :
  ctx_ok src pos inp -> mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->
  ttab_ok wrap src pos inp aout P ->
  step_post wrap src pos inp aout m (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros CX W L E O.
  rewrite E. destruct P as [o|mX].
  - destruct o as [m'|r m']; [exact O | destruct O].
  - destruct O as (FX & LX & RX & MX).
    pose proof (SM Z_TREES m W L) as WT. rewrite E in WT. cbn [ttab_run] in WT.
    rewrite Z.eqb_refl in WT.
    pose proof (ttab_mwf3_unleave mX WT LX) as WX.
    cbn [ttab_run]. destruct (flush =? Z_TREES).
    + cbn [step_post]. split.
      * apply ttab_Kc; [apply ttab_fr_leave; auto | | |].
        -- unfold set_leave, m_mode in *. cbn [m_s set_m_leave]. tauto.
        -- exact RX.
        -- right; reflexivity.
      * unfold set_leave. cbn [m_leave set_m_leave]. discriminate.
    + assert (EE: stepf2 flush lenfix_list distfix_list mX =
                  c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) mX)
        by (unfold stepf2, step2; rewrite MX; reflexivity).
      assert (D: step_post wrap src pos inp aout mX (stepf2 flush lenfix_list distfix_list mX)).
      { apply DEC; auto.
        - apply ttab_Kc; auto.
        - rewrite MX. left; reflexivity. }
      rewrite <- EE. destruct (stepf2 flush lenfix_list distfix_list mX) as [m'|r m']; [exact D|].
      exfalso. cbn [step_post] in D. rewrite MX in D.
      unfold LEN_, MEM, DICTID, DICT in D. lia.
Qed.

Lemma th_tab : tab_stmt.
Proof.
  intros SM DEC wrap src pos inp aout flush m CX K W L Md.
  assert (N: m_mode m <> BAD /\ m_mode m <> MEM /\ m_mode m <> LENGTH /\ m_mode m <> DONE /\
             m_mode m <> DICT).
  { unfold md_tab in Md. unfold TABLE, LENLENS, CODELENS, BAD, MEM, LENGTH, DONE, DICT in *. lia. }
  destruct N as (N1 & N2 & N3 & N4 & N5).
  pose proof (ttab_fr_head wrap src pos inp aout m K W N1 N2 N3 N4) as F.
  pose proof (kc_ret _ _ _ _ _ _ K N1 N4) as R.
  unfold md_tab in Md. destruct Md as [H|[H|H]].
  - apply (ttab_final SM DEC wrap src pos inp aout flush m (ttab_tab m) CX W L).
    + intros fl. rewrite <- (ttab_tab_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply ttab_tab_ok; auto. intros m' F' W' L' R' H'. apply ttab_ll_ok; auto.
  - apply (ttab_final SM DEC wrap src pos inp aout flush m (ttab_ll m) CX W L).
    + intros fl. rewrite <- (ttab_ll_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply ttab_ll_ok; auto.
  - apply (ttab_final SM DEC wrap src pos inp aout flush m (ttab_cl m) CX W L).
    + intros fl. rewrite <- (ttab_cl_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply ttab_cl_ok; auto. intros h _.
      destruct (md_codelens _ (mw_md _ (mwf3_mwf _ W)) H) as (_ & _ & _ & _ & TV & _).
      apply (ttab_tv_bits _ _ _ _ _ _ h TV).
Qed.

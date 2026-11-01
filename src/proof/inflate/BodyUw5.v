(* The body of updatewindow (inflate.c) against Callees3.v's updatewindow_spec3 (the spec of the v5 layer:
   LibStmt5.inflate_lib5_stmt), in Vprog_inflate (Callees5.v: CaseCommon's globals). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.Callees5.
Require Import Zlib.proof.inflate.BodyUpdatewindow.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* helper lemmas                                                                                  *)
(* the state without the window fields                                                            *)

Definition st_rest (gv: globals) (sp strmp headp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

Lemma state_rep_split gv sp strmp headp winp s:
  state_rep gv sp strmp headp winp s =
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  st_rest gv sp strmp headp s.
Proof. unfold state_rep, st_rest. apply pred_ext; cancel. Qed.

Lemma st_rest_same gv sp strmp headp s s':
  i_mode s' = i_mode s -> i_last s' = i_last s -> i_wrap s' = i_wrap s -> i_havedict s' = i_havedict s ->
  i_flags s' = i_flags s -> i_dmax s' = i_dmax s -> i_check s' = i_check s -> i_total s' = i_total s ->
  i_head s' = i_head s -> i_hold s' = i_hold s -> i_bits s' = i_bits s -> i_length s' = i_length s ->
  i_offset s' = i_offset s -> i_extra s' = i_extra s -> i_lencode s' = i_lencode s ->
  i_distcode s' = i_distcode s -> i_lenbits s' = i_lenbits s -> i_distbits s' = i_distbits s ->
  i_ncode s' = i_ncode s -> i_nlen s' = i_nlen s -> i_ndist s' = i_ndist s -> i_have s' = i_have s ->
  i_next s' = i_next s -> i_lens s' = i_lens s -> i_codes s' = i_codes s -> i_sane s' = i_sane s ->
  i_back s' = i_back s -> i_was s' = i_was s ->
  st_rest gv sp strmp headp s' = st_rest gv sp strmp headp s.
Proof.
  intros. unfold st_rest.
  repeat match goal with H: _ s' = _ s |- _ => rewrite H; clear H end. reflexivity.
Qed.

(* the model's updatewindow in two steps: the window initialisation, then the copy *)
Definition uw_init (s: istate) : istate :=
  if i_wsize s =? 0 then set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0 else s.

Definition uw_core (s: istate) (data: list Z) : istate :=
  let copy := Zlength data in
  let ws := i_wsize s in
  let w := i_wdata s in
  if ws <=? copy then
    set_i_wdata (set_i_whave (set_i_wnext s 0) ws) (sublist (copy - ws) copy data)
  else
    let dist := Z.min (ws - i_wnext s) copy in
    let src1 := sublist 0 dist data in
    let full := sublist 0 (i_wnext s) w ++ src1 ++ sublist (i_wnext s + dist) (Zlength w) w in
    let copy' := copy - dist in
    if negb (copy' =? 0) then
      let src2 := sublist dist copy data in
      set_i_wdata (set_i_whave (set_i_wnext s copy') ws) (src2 ++ sublist copy' (Zlength full) full)
    else
      let wn := i_wnext s + dist in
      let wh := if i_whave s <? ws then i_whave s + dist else i_whave s in
      set_i_wdata (set_i_whave (set_i_wnext s (if wn =? ws then 0 else wn)) wh) full.

Lemma updatewindow_split s data: updatewindow s data = uw_core (uw_init s) data.
Proof. reflexivity. Qed.

Lemma st_rest_upd gv sp strmp headp s data:
  st_rest gv sp strmp headp (set_i_win (updatewindow s data) true) = st_rest gv sp strmp headp s.
Proof.
  rewrite updatewindow_split. unfold uw_core, uw_init.
  destruct (i_wsize s =? 0); [mnorm_goal |];
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  apply st_rest_same; reflexivity.
Qed.

Lemma updatewindow_wbits s data: i_wbits (updatewindow s data) = i_wbits s.
Proof.
  rewrite updatewindow_split. unfold uw_core, uw_init.
  destruct (i_wsize s =? 0);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* byte arrays in three slices                                                                    *)

Lemma data_at_tuchar_slice sh n (l: list val) p lo hi:
  field_compatible (tarray tuchar n) [] p ->
  0 <= lo <= hi -> hi <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p =
  data_at sh (tarray tuchar lo) (sublist 0 lo l) p *
  data_at sh (tarray tuchar (hi - lo)) (sublist lo hi l) (offset_val lo p) *
  data_at sh (tarray tuchar (n - hi)) (sublist hi n l) (offset_val hi p).
Proof.
  intros FC B1 B2 L.
  rewrite (split3_data_at_Tarray_tuchar sh n lo hi l p) by (auto; lia).
  replace (field_address0 (Tarray tuchar n noattr) (ArraySubsc lo :: nil) p) with (offset_val lo p)
    by (apply offset_val_field_address0_tuchar; auto; lia).
  replace (field_address0 (Tarray tuchar n noattr) (ArraySubsc hi :: nil) p) with (offset_val hi p)
    by (apply offset_val_field_address0_tuchar; auto; lia).
  reflexivity.
Qed.

(* the rest of an array around the slice [a, b) *)
Definition slice_frame (sh: share) (p: val) (n: Z) (l: list val) (a b: Z) : mpred :=
  data_at sh (tarray tuchar a) (sublist 0 a l) p *
  data_at sh (tarray tuchar (n - b)) (sublist b n l) (offset_val b p).

Lemma slice_split sh n (l: list val) p a b:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p |--
  data_at sh (tarray tuchar (b - a)) (sublist a b l) (offset_val a p) * slice_frame sh p n l a b.
Proof.
  intros. rewrite (data_at_tuchar_slice sh n l p a b) by auto. unfold slice_frame. cancel.
Qed.

Lemma slice_join sh n (l: list val) p a b (x: list val):
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength l = n -> Zlength x = b - a ->
  data_at sh (tarray tuchar (b - a)) x (offset_val a p) * slice_frame sh p n l a b |--
  data_at sh (tarray tuchar n) (sublist 0 a l ++ x ++ sublist b n l) p.
Proof.
  intros. rewrite (data_at_tuchar_slice sh n _ p a b) by (auto; list_solve). unfold slice_frame.
  replace (sublist 0 a (sublist 0 a l ++ x ++ sublist b n l)) with (sublist 0 a l) by list_solve.
  replace (sublist a b (sublist 0 a l ++ x ++ sublist b n l)) with x by list_solve.
  replace (sublist b n (sublist 0 a l ++ x ++ sublist b n l)) with (sublist b n l) by list_solve.
  cancel.
Qed.

Lemma slice_join_same sh n (l: list val) p a b:
  field_compatible (tarray tuchar n) [] p -> 0 <= a <= b -> b <= n -> Zlength l = n ->
  data_at sh (tarray tuchar (b - a)) (sublist a b l) (offset_val a p) * slice_frame sh p n l a b |--
  data_at sh (tarray tuchar n) l p.
Proof.
  intros. sep_apply (slice_join sh n l p a b (sublist a b l)); auto. { list_solve. }
  replace (sublist 0 a l ++ sublist a b l ++ sublist b n l) with l by list_solve. auto.
Qed.

(* the slices of the source *)
Lemma src_slice (c: list val) (data: list Z) e a b:
  sublist (e - Zlength data) e c = byte_vals data -> e - Zlength data <= a <= b -> b <= e ->
  e <= Zlength c -> 0 <= Zlength data <= e ->
  sublist a b c = byte_vals (sublist (a - (e - Zlength data)) (b - (e - Zlength data)) data).
Proof.
  intros H B1 B2 B3 B4. rewrite <- sublist_byte_vals, <- H.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma shl_one k: 0 <= k < 32 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
  intros. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. rewrite Int.mul_commut, Int.mul_one. reflexivity.
Qed.

(* the window after the first copy of the non-full case *)
Lemma win_list_B (W h wn dist: Z) (w src1: list Z):
  0 <= h <= W -> 0 <= wn < W -> (h < W -> wn = h) -> Zlength w = h -> 0 <= dist -> wn + dist <= W ->
  Zlength src1 = dist ->
  sublist 0 wn (byte_vals w ++ Zrepeat Vundef (W - h)) ++ byte_vals src1 ++
  sublist (wn + dist) W (byte_vals w ++ Zrepeat Vundef (W - h)) =
  byte_vals (sublist 0 wn w ++ src1 ++ sublist (wn + dist) h w) ++
  Zrepeat Vundef (W - Zlength (sublist 0 wn w ++ src1 ++ sublist (wn + dist) h w)).
Proof.
  intros. unfold byte_vals.
  destruct (Z.eq_dec h W).
  - subst h. list_solve.
  - assert (wn = h) by lia. subst wn.
    rewrite (sublist_nil_gen w (h + dist) h) by lia. rewrite (sublist_same 0 h w) by lia. list_solve.
Qed.


Lemma slice_split_k sh n (l: list val) p a k:
  field_compatible (tarray tuchar n) [] p -> 0 <= a -> 0 <= k -> a + k <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p |--
  data_at sh (tarray tuchar k) (sublist a (a + k) l) (offset_val a p) * slice_frame sh p n l a (a + k).
Proof.
  intros. pose proof (slice_split sh n l p a (a + k)) as S.
  replace (a + k - a) with k in S by lia. apply S; auto; lia.
Qed.

Lemma slice_join_k sh n (l: list val) p a k (x: list val):
  field_compatible (tarray tuchar n) [] p -> 0 <= a -> 0 <= k -> a + k <= n -> Zlength l = n ->
  Zlength x = k ->
  data_at sh (tarray tuchar k) x (offset_val a p) * slice_frame sh p n l a (a + k) |--
  data_at sh (tarray tuchar n) (sublist 0 a l ++ x ++ sublist (a + k) n l) p.
Proof.
  intros. pose proof (slice_join sh n l p a (a + k) x) as S.
  replace (a + k - a) with k in S by lia. apply S; auto; lia.
Qed.

Lemma slice_join_same_k sh n (l: list val) p a k:
  field_compatible (tarray tuchar n) [] p -> 0 <= a -> 0 <= k -> a + k <= n -> Zlength l = n ->
  data_at sh (tarray tuchar k) (sublist a (a + k) l) (offset_val a p) * slice_frame sh p n l a (a + k) |--
  data_at sh (tarray tuchar n) l p.
Proof.
  intros. pose proof (slice_join_same sh n l p a (a + k)) as S.
  replace (a + k - a) with k in S by lia. apply S; auto; lia.
Qed.

(* the window fields after the initialisation *)
Lemma uw_init_ok s: swf s ->
  i_wsize (uw_init s) = 2 ^ i_wbits s /\
  0 <= i_whave (uw_init s) <= i_wsize (uw_init s) /\
  0 <= i_wnext (uw_init s) < i_wsize (uw_init s) /\
  (i_whave (uw_init s) < i_wsize (uw_init s) -> i_wnext (uw_init s) = i_whave (uw_init s)) /\
  i_wdata (uw_init s) = i_wdata s /\
  Zlength (i_wdata s) = i_whave (uw_init s) /\
  i_wbits (uw_init s) = i_wbits s /\ i_win (uw_init s) = i_win s.
Proof.
  intros H. pose proof (sw_wbits _ H). pose proof (sw_wsize _ H). pose proof (sw_whave _ H).
  pose proof (sw_wnext _ H). pose proof (sw_wvalid _ H). pose proof (sw_wdata _ H).
  assert (0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  unfold uw_init. destruct (Z.eqb_spec (i_wsize s) 0) as [E | E].
  - mnorm_goal. rewrite E in *. repeat split; lia.
  - destruct H1 as [H1 | [_ H1]]; [contradiction |]. rewrite H1 in *. repeat split; try lia; auto.
Qed.

Lemma uw_init_eq0 s: i_wsize s = 0 ->
  uw_init s = set_i_whave (set_i_wnext (set_i_wsize s (2 ^ i_wbits s)) 0) 0.
Proof. intros E. unfold uw_init. rewrite E. reflexivity. Qed.

Lemma uw_init_neq0 s: i_wsize s <> 0 -> uw_init s = s.
Proof. intros E. unfold uw_init. rewrite (proj2 (Z.eqb_neq _ _) E). reflexivity. Qed.

Lemma uw_core_wbits s data: i_wbits (uw_core s data) = i_wbits s.
Proof.
  unfold uw_core. repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

(* the final state and window *)
Lemma finish_rep gv sp strmp headp s data winp' wh wn (L: list val):
  i_wsize (uw_core (uw_init s) data) = 2 ^ i_wbits s ->
  i_whave (uw_core (uw_init s) data) = wh ->
  i_wnext (uw_core (uw_init s) data) = wn ->
  L = byte_vals (i_wdata (uw_core (uw_init s) data)) ++
      Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata (uw_core (uw_init s) data))) ->
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (2 ^ i_wbits s)) sp *
  field_at Ews t_state (DOT _whave) (zv wh) sp *
  field_at Ews t_state (DOT _wnext) (zv wn) sp *
  field_at Ews t_state (DOT _window) winp' sp *
  st_rest gv sp strmp headp s *
  malloc_token Ews (tarray tuchar (2 ^ i_wbits s)) winp' *
  data_at Ews (tarray tuchar (2 ^ i_wbits s)) L winp'
  |-- state_rep gv sp strmp headp winp' (set_i_win (updatewindow s data) true) *
      win_rep winp' (set_i_win (updatewindow s data) true).
Proof.
  intros E1 E2 E3 E4. rewrite state_rep_split, st_rest_upd. unfold win_rep.
  rewrite updatewindow_split. cbn [i_win i_wbits i_wsize i_whave i_wnext i_wdata set_i_win].
  rewrite uw_core_wbits.
  assert (W: i_wbits (uw_init s) = i_wbits s).
  { unfold uw_init. destruct (i_wsize s =? 0); reflexivity. }
  rewrite W, E1, E2, E3, <- E4. cancel.
Qed.

(* end - k for an unsigned k *)
Lemma sem_sub_pu_offset: forall s off n, isptr s -> 0 <= n <= Int.max_unsigned ->
  force_val (sem_sub_pi tuchar Unsigned (offset_val off s) (Vint (Int.repr n))) = offset_val (off - n) s.
Proof.
  intros s off n Hptr Hn.
  replace (off - n) with (off + (- n)) by lia. rewrite <- offset_offset_val.
  assert (Hptr' : isptr (offset_val off s)) by (rewrite isptr_offset_val; auto).
  destruct (offset_val off s) eqn:Hoff; inversion Hptr'. simpl.
  unfold sem_sub_pi. simpl. f_equal.
  assert (E: Ptrofs.of_intu (Int.repr n) = Ptrofs.repr n).
  { unfold Ptrofs.of_intu, Ptrofs.of_int. f_equal. apply Int.unsigned_repr; auto. }
  rewrite E. rewrite ptrofs_mul_repr. rewrite Ptrofs.sub_add_opp. f_equal.
  rewrite Ptrofs.neg_repr. f_equal. simpl. lia.
Qed.

Lemma sem_add_pu_offset: forall s off n, isptr s -> 0 <= n <= Int.max_unsigned ->
  force_val (sem_add_ptr_int tuchar Unsigned (offset_val off s) (Vint (Int.repr n))) = offset_val (off + n) s.
Proof.
  intros s off n Hptr Hn. rewrite <- offset_offset_val.
  assert (Hptr' : isptr (offset_val off s)) by (rewrite isptr_offset_val; auto).
  destruct (offset_val off s) eqn:Hoff; inversion Hptr'. simpl.
  unfold sem_add_ptr_int. simpl. f_equal.
  assert (E: Ptrofs.of_intu (Int.repr n) = Ptrofs.repr n).
  { unfold Ptrofs.of_intu, Ptrofs.of_int. f_equal. apply Int.unsigned_repr; auto. }
  rewrite E. rewrite ptrofs_mul_repr. f_equal. f_equal. simpl. lia.
Qed.

(* the three outcomes of the copy, against the memory the C code leaves *)
Section Core.
Variables (s1: istate) (data: list Z) (W: Z).
Hypotheses (HS: i_wsize s1 = W) (HH: 0 <= i_whave s1 <= W) (HN: 0 <= i_wnext s1 < W)
  (HV: i_whave s1 < W -> i_wnext s1 = i_whave s1) (HL: Zlength (i_wdata s1) = i_whave s1).

Lemma core_A (L: list val): W <= Zlength data -> Zlength L = W ->
  i_wsize (uw_core s1 data) = W /\ i_whave (uw_core s1 data) = W /\ i_wnext (uw_core s1 data) = 0 /\
  sublist 0 0 L ++ byte_vals (sublist (Zlength data - W) (Zlength data) data) ++ sublist (0 + W) W L =
  byte_vals (i_wdata (uw_core s1 data)) ++ Zrepeat Vundef (W - Zlength (i_wdata (uw_core s1 data))).
Proof.
  intros HW HLL. unfold uw_core. rewrite HS. rewrite (proj2 (Z.leb_le _ _) HW). mnorm_goal.
  split; [auto | split; [auto | split; [auto |]]].
  unfold byte_vals. list_solve.
Qed.

Lemma core_B1: Zlength data < W ->
  Zlength data - Z.min (W - i_wnext s1) (Zlength data) <> 0 ->
  let wn := i_wnext s1 in
  let dist := Z.min (W - wn) (Zlength data) in
  let L0 := byte_vals (i_wdata s1) ++ Zrepeat Vundef (W - Zlength (i_wdata s1)) in
  let L1 := sublist 0 wn L0 ++ byte_vals (sublist 0 dist data) ++ sublist (wn + dist) W L0 in
  i_wsize (uw_core s1 data) = W /\ i_whave (uw_core s1 data) = W /\
  i_wnext (uw_core s1 data) = Zlength data - dist /\
  sublist 0 0 L1 ++ byte_vals (sublist dist (Zlength data) data) ++
    sublist (0 + (Zlength data - dist)) W L1 =
  byte_vals (i_wdata (uw_core s1 data)) ++ Zrepeat Vundef (W - Zlength (i_wdata (uw_core s1 data))).
Proof.
  intros HW HC wn dist L0 L1.
  assert (Ewn: wn = i_wnext s1) by reflexivity.
  assert (Edist: dist = Z.min (W - wn) (Zlength data)) by reflexivity.
  unfold L1, L0. clear L1 L0. clearbody dist wn.
  pose proof (Zlength_nonneg data).
  assert (HD: dist = W - wn) by lia.
  unfold uw_core. rewrite HS. rewrite (proj2 (Z.leb_gt _ _) HW).
  rewrite <- Ewn, <- Edist. rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbn [negb]. cbn zeta. mnorm_goal.
  try rewrite <- Ewn; try rewrite <- Edist.
  split; [auto | split; [auto | split; [auto |]]].
  rewrite !HL.
  rewrite (win_list_B W (i_whave s1) wn dist (i_wdata s1) (sublist 0 dist data)) by (lia || list_solve).
  assert (HF: Zlength (sublist 0 wn (i_wdata s1) ++ sublist 0 dist data ++
                       sublist (wn + dist) (i_whave s1) (i_wdata s1)) = W).
  { destruct (Z.eq_dec (i_whave s1) W).
    - rewrite !Zlength_app, !Zlength_sublist by lia. lia.
    - assert (Hwn: wn = i_whave s1) by (rewrite Ewn; apply HV; lia). rewrite Hwn.
      rewrite (sublist_nil_gen _ (i_whave s1 + dist)) by lia.
      rewrite !Zlength_app, !Zlength_sublist by lia. rewrite Zlength_nil. lia. }
  set (full := sublist 0 wn (i_wdata s1) ++ sublist 0 dist data ++
                sublist (wn + dist) (i_whave s1) (i_wdata s1)) in *.
  clearbody full. rewrite HF.
  assert (0 < Zlength data - dist < W) by lia.
  unfold byte_vals. list_solve.
Qed.

Lemma core_B2: Zlength data < W ->
  Zlength data - Z.min (W - i_wnext s1) (Zlength data) = 0 ->
  let wn := i_wnext s1 in
  let dist := Z.min (W - wn) (Zlength data) in
  let L0 := byte_vals (i_wdata s1) ++ Zrepeat Vundef (W - Zlength (i_wdata s1)) in
  i_wsize (uw_core s1 data) = W /\
  i_wnext (uw_core s1 data) = (if wn + dist =? W then 0 else wn + dist) /\
  i_whave (uw_core s1 data) = (if i_whave s1 <? W then i_whave s1 + dist else i_whave s1) /\
  sublist 0 wn L0 ++ byte_vals (sublist 0 dist data) ++ sublist (wn + dist) W L0 =
  byte_vals (i_wdata (uw_core s1 data)) ++ Zrepeat Vundef (W - Zlength (i_wdata (uw_core s1 data))).
Proof.
  intros HW HC wn dist L0.
  assert (Ewn: wn = i_wnext s1) by reflexivity.
  assert (Edist: dist = Z.min (W - wn) (Zlength data)) by reflexivity.
  unfold L0. clear L0. clearbody dist wn.
  pose proof (Zlength_nonneg data).
  unfold uw_core. rewrite HS. rewrite (proj2 (Z.leb_gt _ _) HW).
  rewrite <- Ewn, <- Edist. rewrite (proj2 (Z.eqb_eq _ _)) by lia. cbn [negb]. cbn zeta. mnorm_goal.
  try rewrite <- Ewn; try rewrite <- Edist.
  split; [auto | split; [auto | split; [auto |]]].
  rewrite !HL.
  apply win_list_B; try lia. { list_solve. }
Qed.

End Core.

(* the slice at the start of an array *)
Lemma slice_split0 sh n (l: list val) p k:
  field_compatible (tarray tuchar n) [] p -> 0 <= k -> k <= n -> Zlength l = n ->
  data_at sh (tarray tuchar n) l p |--
  data_at sh (tarray tuchar k) (sublist 0 (0 + k) l) p * slice_frame sh p n l 0 (0 + k).
Proof.
  intros FC H1 H2 H3. sep_apply (slice_split_k sh n l p 0 k FC); try lia; auto.
  rewrite isptr_offset_val_zero by (destruct FC; auto). auto.
Qed.

Lemma slice_join0 sh n (l: list val) p k (x: list val):
  field_compatible (tarray tuchar n) [] p -> 0 <= k -> k <= n -> Zlength l = n -> Zlength x = k ->
  data_at sh (tarray tuchar k) x p * slice_frame sh p n l 0 (0 + k) |--
  data_at sh (tarray tuchar n) (sublist 0 0 l ++ x ++ sublist (0 + k) n l) p.
Proof.
  intros FC H1 H2 H3 H4. rewrite <- (isptr_offset_val_zero p) at 1 by (destruct FC; auto).
  apply slice_join_k; auto; lia.
Qed.

Lemma Zlength_win (w: list Z) W: Zlength w <= W ->
  Zlength (byte_vals w ++ Zrepeat Vundef (W - Zlength w)) = W.
Proof. intros. rewrite Zlength_app, Zlength_byte_vals, Zlength_Zrepeat by lia. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the state after the window allocation *)
Definition P1 (gv: globals) (shs: share) (strmp: val) (sv: reptype t_strm) (sp headp winp: val) (s: istate)
    (ssh: share) (p: val) (n: Z) (c: list val) (e: Z) (data: list Z) (zfp: val) : environ -> mpred :=
  (EX winp': val,
    PROP (i_win s = true -> winp' = winp)
    LOCAL (temp _state sp; gvars gv; temp _strm strmp; temp _end (offset_val e p);
           temp _copy (Vint (Int.repr (Zlength data))))
    SEP (data_at shs t_strm sv strmp;
         field_at Ews t_state (DOT _wbits) (Vint (Int.repr (i_wbits s))) sp;
         field_at Ews t_state (DOT _wsize) (Vint (Int.repr (i_wsize s))) sp;
         field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave s))) sp;
         field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext s))) sp;
         field_at Ews t_state (DOT _window) winp' sp;
         st_rest gv sp strmp headp s;
         malloc_token Ews (tarray tuchar (2 ^ i_wbits s)) winp';
         data_at Ews (tarray tuchar (2 ^ i_wbits s))
           (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))) winp';
         data_at ssh (tarray tuchar n) c p; mem_mgr gv;
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc);
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) zfp))%assert.

(* the state after the initialisation of an empty window *)
Definition P2 (gv: globals) (shs: share) (strmp: val) (sv: reptype t_strm) (sp headp winp': val) (s: istate)
    (ssh: share) (p: val) (n: Z) (c: list val) (e: Z) (data: list Z) (zfp: val) : environ -> mpred :=
  (PROP ()
    LOCAL (temp _state sp; gvars gv; temp _strm strmp; temp _end (offset_val e p);
           temp _copy (Vint (Int.repr (Zlength data))))
    SEP (data_at shs t_strm sv strmp;
         field_at Ews t_state (DOT _wbits) (Vint (Int.repr (i_wbits s))) sp;
         field_at Ews t_state (DOT _wsize) (Vint (Int.repr (i_wsize (uw_init s)))) sp;
         field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (uw_init s)))) sp;
         field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (uw_init s)))) sp;
         field_at Ews t_state (DOT _window) winp' sp;
         st_rest gv sp strmp headp s;
         malloc_token Ews (tarray tuchar (2 ^ i_wbits s)) winp';
         data_at Ews (tarray tuchar (2 ^ i_wbits s))
           (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))) winp';
         data_at ssh (tarray tuchar n) c p; mem_mgr gv;
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc);
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) zfp))%assert.

(* forward on `return e;` without floyd's final entailer (it unfolds the model in the postcondition) *)
Ltac return_noent :=
  try fold_frame_function_body;
  match goal with
  | |- @semax ?CS _ ?Delta ?Pre (Sreturn (Some ?ret)) _ =>
        let v := fresh "v" in
        let H := fresh "HRE" in
        do_compute_expr1 CS Delta Pre constr:(Ecast ret (ret_type Delta));
        match goal with v' := _, H':_ |- _ => rename H' into H; rename v' into v end;
        subst v;
        eapply semax_return_Some;
        [ exact H
        | entailer_for_return
        | (solve_return_outer_gen || fail 1000 "unexpected failure in forward_return")
        | (solve_canon_derives_stackframe || fail 1000 "stackframe is unfolded or modified.")
        | try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end;
          try change_compspecs CS;
          solve_return_inner_gen
        | idtac];
        clear H
  end.

Ltac uint_hyp :=
  repeat match goal with
  | H: context [Int.unsigned (Int.repr ?x)] |- _ => rewrite (Int.unsigned_repr x) in H by rep_lia
  | H: context [Int.ltu (Int.repr ?x) (Int.repr ?y)] |- _ => unfold Int.ltu in H
  | H: context [zlt ?a ?b] |- _ => destruct (zlt a b); try discriminate; try contradiction
  end.

Ltac forward_if_temp id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    match Q with context C [temp id _] =>
      let Q' := context C [temp id v] in forward_if (PROPx P (LOCALx Q' (SEPx R))) end end.

Ltac forward_if_field fld v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    match R with context C [field_at Ews t_state (StructField fld :: nil) _ ?sp] =>
      let R' := context C [field_at Ews t_state (StructField fld :: nil) v sp] in
      forward_if (PROPx P (LOCALx Q (SEPx R'))) end end.

(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)
(* the copy phase as separate lemmas (one Qed for the whole body exceeds the time budget)        *)

Definition uw_copy_if : statement :=
  match fn_body f_updatewindow with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ x) _))) => x
  | _ => Sskip end.
Definition uw_DA : statement := match uw_copy_if with Sifthenelse _ a _ => a | _ => Sskip end.
Definition uw_DB : statement := match uw_copy_if with Sifthenelse _ _ b => b | _ => Sskip end.
Definition uw_ret : statement := Sreturn (Some (Econst_int (Int.repr 0) tint)).

Definition uw_post (gv: globals) (shs: share) (strmp: val) (sv: reptype t_strm) (sp headp winp: val)
    (s: istate) (ssh: share) (p: val) (n: Z) (c: list val) (data: list Z) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint
    (EX r: Z, EX winp': val,
     PROP ((r = 0 /\ (i_win s = true -> winp' = winp)) \/ (r = 1 /\ i_win s = false /\ winp' = nullval))
     RETURN (Vint (Int.repr r))
     SEP (data_at shs t_strm sv strmp;
          state_rep gv sp strmp headp winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
          win_rep winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
          data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv))%assert)
   (stackframe_of f_updatewindow).

(* the state at the test copy >= wsize *)
Definition PC (gv: globals) (shs: share) (strmp: val) (sv: reptype t_strm) (sp headp winp': val) (s: istate)
    (ssh: share) (p: val) (n: Z) (c: list val) (e: Z) (data: list Z) (zfp: val) : environ -> mpred :=
  (PROP ()
    LOCAL (temp _t'2 (Vint (Int.repr (2 ^ i_wbits s))); temp _state sp; gvars gv; temp _strm strmp;
           temp _end (offset_val e p); temp _copy (Vint (Int.repr (Zlength data))))
    SEP (data_at shs t_strm sv strmp;
         field_at Ews t_state (DOT _wbits) (Vint (Int.repr (i_wbits s))) sp;
         field_at Ews t_state (DOT _wsize) (Vint (Int.repr (2 ^ i_wbits s))) sp;
         field_at Ews t_state (DOT _whave) (Vint (Int.repr (i_whave (uw_init s)))) sp;
         field_at Ews t_state (DOT _wnext) (Vint (Int.repr (i_wnext (uw_init s)))) sp;
         field_at Ews t_state (DOT _window) winp' sp;
         st_rest gv sp strmp headp s;
         malloc_token Ews (tarray tuchar (2 ^ i_wbits s)) winp';
         data_at Ews (tarray tuchar (2 ^ i_wbits s))
           (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))) winp';
         data_at ssh (tarray tuchar n) c p; mem_mgr gv;
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcalloc_spec Zlib.units.Inflate.CS)) (gv _zcalloc);
         func_ptr' (snd (@Zlib.proof.zutil.Spec.zcfree_spec Zlib.units.Inflate.CS)) zfp))%assert.



Section Copy.
Context {Espec: OracleKind}.
Variables (gv: globals) (shs: share) (strmp ni ai ti no ao tout msg dt adl res sp headp winp winp': val)
  (s: istate) (ssh: share) (p: val) (n: Z) (c: list val) (e: Z) (data: list Z) (zfp: val).
Hypotheses (SH: readable_share shs) (SH0: readable_share ssh) (H1: 0 <= Zlength data <= e)
  (H2: Zlength data <= Int.max_unsigned) (H3: e <= n) (H4: Zlength c = n) (H5: n <= Ptrofs.max_unsigned)
  (Hsrc: sublist (e - Zlength data) e c = byte_vals data) (Hbok: bytes_ok data) (Hzfp: zfp = gv _zcfree)
  (Hwb: 0 <= i_wbits s <= 23) (HW1: 0 < 2 ^ i_wbits s) (HW2: 2 ^ i_wbits s <= 2 ^ 23)
  (Hwin': i_win s = true -> winp' = winp) (Hs1: i_wsize (uw_init s) = 2 ^ i_wbits s)
  (Hh1: 0 <= i_whave (uw_init s) <= 2 ^ i_wbits s) (Hn1: 0 <= i_wnext (uw_init s) < 2 ^ i_wbits s)
  (Hv1: i_whave (uw_init s) < 2 ^ i_wbits s -> i_wnext (uw_init s) = i_whave (uw_init s))
  (Hd1: i_wdata (uw_init s) = i_wdata s) (Hl1: Zlength (i_wdata s) = i_whave (uw_init s))
  (HW3: 2 ^ i_wbits s <= 8388608) (HL1: Zlength (i_wdata (uw_init s)) = i_whave (uw_init s))
  (FCp: field_compatible (tarray tuchar n) [] p)
  (FCw: field_compatible (tarray tuchar (2 ^ i_wbits s)) [] winp') (Pp: isptr p) (Pw: isptr winp').

Ltac uw_start :=
  match goal with |- semax _ _ (Ssequence ?d _) _ =>
    let x := eval cbv beta iota delta [uw_DA uw_DB uw_copy_if f_updatewindow fn_body] in d in
    change d with x end;
  unfold uw_ret, PC, uw_post; simplify_func_tycontext; abbreviate_semax.

Lemma uw_caseA (H: Zlength data >= 2 ^ i_wbits s) :
  semax (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil)
    (PC gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp' s ssh p n c e data zfp)
    (Ssequence uw_DA uw_ret)
    (uw_post gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp s ssh p n c data).
Proof.
  uw_start.
  assert (HA: 2 ^ i_wbits s <= Zlength data) by lia.
  forward. forward. forward.
  assert (HlA: Zlength (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data) = 2 ^ i_wbits s)
    by (rewrite Zlength_sublist; lia).
  assert (HcA: sublist (e - 2 ^ i_wbits s) (e - 2 ^ i_wbits s + 2 ^ i_wbits s) c =
               byte_vals (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data)).
  { rewrite (src_slice c data e) by (exact Hsrc || lia). f_equal; f_equal; lia. }
  sep_apply (slice_split_k ssh n c p (e - 2 ^ i_wbits s) (2 ^ i_wbits s) FCp ltac:(lia) ltac:(lia)
               ltac:(lia) H4).
  rewrite HcA.
  sep_apply (data_at_data_at_ Ews (tarray tuchar (2 ^ i_wbits s))
    (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))) winp').
  replace (data_at_ Ews (tarray tuchar (2 ^ i_wbits s)) winp')
    with (data_at_ Ews (tarray tuchar (Zlength (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data))) winp')
    by (rewrite HlA; reflexivity).
  replace (data_at ssh (tarray tuchar (2 ^ i_wbits s))
             (byte_vals (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data))
             (offset_val (e - 2 ^ i_wbits s) p))
    with (data_at ssh (tarray tuchar (Zlength (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data)))
             (byte_vals (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data))
             (offset_val (e - 2 ^ i_wbits s) p))
    by (rewrite HlA; reflexivity).
  forward_call (Ews, winp', ssh, offset_val (e - 2 ^ i_wbits s) p,
                sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data).
  { entailer!. all: try rewrite sem_sub_pu_offset by (auto; rep_lia). all: try rewrite HlA.
    all: try rewrite Int.unsigned_repr by rep_lia. all: auto.
    clear - Pp Pw HW1 HW3. destruct p; try contradiction; destruct winp'; try contradiction; simpl.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { repeat split; auto with share; try (apply Forall_sublist; auto); try rep_lia. }
  rewrite HlA. rewrite <- HcA.
  sep_apply (slice_join_same_k ssh n c p (e - 2 ^ i_wbits s) (2 ^ i_wbits s) FCp ltac:(lia) ltac:(lia)
               ltac:(lia) H4).
  forward. forward. forward.
  destruct (core_A (uw_init s) data (2 ^ i_wbits s) Hs1 Hn1 HL1 (Zrepeat Vundef (2 ^ i_wbits s)) HA
              ltac:(list_solve)) as (C1 & C2 & C3 & C4).
  sep_apply (finish_rep gv sp strmp headp s data winp' (2 ^ i_wbits s) 0
               (byte_vals (sublist (Zlength data - 2 ^ i_wbits s) (Zlength data) data)) C1 C2 C3
               ltac:(rewrite <- C4; list_solve)).
  return_noent.
  Exists 0 winp'. change (0 =? 0) with true. cbv iota. unfold zfuncs. rewrite <- Hzfp. entailer!.
Qed.

Lemma uw_caseB (H: Zlength data < 2 ^ i_wbits s) :
  semax (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil)
    (PC gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp' s ssh p n c e data zfp)
    (Ssequence uw_DB uw_ret)
    (uw_post gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp s ssh p n c data).
Proof.
  uw_start.
  assert (HB: Zlength data < 2 ^ i_wbits s) by lia.
  forward. forward. forward.
  forward_if_temp _dist (Vint (Int.repr (Z.min (2 ^ i_wbits s - i_wnext (uw_init s)) (Zlength data)))).
  { forward. rewrite Z.min_r by (uint_hyp; lia). entailer!. }
  { forward. rewrite Z.min_l by (uint_hyp; lia). entailer!. }
  remember (Z.min (2 ^ i_wbits s - i_wnext (uw_init s)) (Zlength data)) as dist eqn:Hdist.
  assert (Hd0: 0 <= dist <= Zlength data /\ dist <= 2 ^ i_wbits s - i_wnext (uw_init s)) by lia.
  forward. forward.
  assert (HlB1: Zlength (sublist 0 dist data) = dist) by (rewrite Zlength_sublist; lia).
  assert (HcB1: sublist (e - Zlength data) (e - Zlength data + dist) c = byte_vals (sublist 0 dist data)).
  { rewrite (src_slice c data e) by (exact Hsrc || lia). f_equal; f_equal; lia. }
  sep_apply (slice_split_k ssh n c p (e - Zlength data) dist FCp ltac:(lia) ltac:(lia) ltac:(lia) H4).
  rewrite HcB1.
  assert (HL0: Zlength (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))) =
               2 ^ i_wbits s) by (apply Zlength_win; lia).
  sep_apply (slice_split_k Ews (2 ^ i_wbits s)
               (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s)))
               winp' (i_wnext (uw_init s)) dist FCw ltac:(lia) ltac:(lia) ltac:(lia) HL0).
  sep_apply (data_at_data_at_ Ews (tarray tuchar dist)
    (sublist (i_wnext (uw_init s)) (i_wnext (uw_init s) + dist)
       (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s))))
    (offset_val (i_wnext (uw_init s)) winp')).
  replace (data_at_ Ews (tarray tuchar dist) (offset_val (i_wnext (uw_init s)) winp'))
    with (data_at_ Ews (tarray tuchar (Zlength (sublist 0 dist data))) (offset_val (i_wnext (uw_init s)) winp'))
    by (rewrite HlB1; reflexivity).
  replace (data_at ssh (tarray tuchar dist) (byte_vals (sublist 0 dist data)) (offset_val (e - Zlength data) p))
    with (data_at ssh (tarray tuchar (Zlength (sublist 0 dist data))) (byte_vals (sublist 0 dist data))
            (offset_val (e - Zlength data) p))
    by (rewrite HlB1; reflexivity).
  forward_call (Ews, offset_val (i_wnext (uw_init s)) winp', ssh, offset_val (e - Zlength data) p,
                sublist 0 dist data).
  { entailer!. all: try rewrite sem_sub_pu_offset by (auto; rep_lia). all: try rewrite HlB1.
    all: try rewrite Int.unsigned_repr by rep_lia. all: auto.
    clear - Pp Pw Hd0 Hn1 H2 HW3. destruct p; try contradiction; destruct winp'; try contradiction; simpl.
    rewrite Int.unsigned_repr by rep_lia. reflexivity. }
  { repeat split; auto with share; try (apply Forall_sublist; auto); try rep_lia. }
  rewrite HlB1.
  sep_apply (slice_join_k Ews (2 ^ i_wbits s)
               (byte_vals (i_wdata s) ++ Zrepeat Vundef (2 ^ i_wbits s - Zlength (i_wdata s)))
               winp' (i_wnext (uw_init s)) dist (byte_vals (sublist 0 dist data)) FCw ltac:(lia) ltac:(lia)
               ltac:(lia) HL0 ltac:(rewrite Zlength_byte_vals; auto)).
  sep_apply (slice_join_k ssh n c p (e - Zlength data) dist (byte_vals (sublist 0 dist data)) FCp
               ltac:(lia) ltac:(lia) ltac:(lia) H4 ltac:(rewrite Zlength_byte_vals; auto)).
  replace (sublist 0 (e - Zlength data) c ++ byte_vals (sublist 0 dist data) ++
           sublist (e - Zlength data + dist) n c) with c by (rewrite <- HcB1; list_solve).
  forward.
  apply semax_if_seq.
  forward_if.
  + (* a second piece at the start of the window *)
    assert (HC: Zlength data - dist <> 0)
      by (rewrite !Int.unsigned_repr in H0' by rep_lia; exact H0').
    rewrite sub_repr.
    forward.
    assert (HlB2: Zlength (sublist dist (Zlength data) data) = Zlength data - dist)
      by (rewrite Zlength_sublist; lia).
    assert (HcB2: sublist (e - (Zlength data - dist)) (e - (Zlength data - dist) + (Zlength data - dist)) c =
                  byte_vals (sublist dist (Zlength data) data)).
    { rewrite (src_slice c data e) by (exact Hsrc || lia). f_equal; f_equal; lia. }
    sep_apply (slice_split_k ssh n c p (e - (Zlength data - dist)) (Zlength data - dist) FCp ltac:(lia)
                 ltac:(lia) ltac:(lia) H4).
    rewrite HcB2.
    match goal with |- context [data_at Ews (tarray tuchar (2 ^ i_wbits s)) ?L winp'] =>
      remember L as L1 eqn:EL1 end.
    assert (HLL1: Zlength L1 = 2 ^ i_wbits s).
    { rewrite EL1, !Zlength_app, Zlength_byte_vals, !Zlength_sublist; lia. }
    sep_apply (slice_split0 Ews (2 ^ i_wbits s) L1 winp' (Zlength data - dist) FCw ltac:(lia) ltac:(lia) HLL1).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength data - dist))
                 (sublist 0 (0 + (Zlength data - dist)) L1) winp').
    replace (data_at_ Ews (tarray tuchar (Zlength data - dist)) winp')
      with (data_at_ Ews (tarray tuchar (Zlength (sublist dist (Zlength data) data))) winp')
      by (rewrite HlB2; reflexivity).
    replace (data_at ssh (tarray tuchar (Zlength data - dist)) (byte_vals (sublist dist (Zlength data) data))
               (offset_val (e - (Zlength data - dist)) p))
      with (data_at ssh (tarray tuchar (Zlength (sublist dist (Zlength data) data)))
              (byte_vals (sublist dist (Zlength data) data)) (offset_val (e - (Zlength data - dist)) p))
      by (rewrite HlB2; reflexivity).
    forward_call (Ews, winp', ssh, offset_val (e - (Zlength data - dist)) p, sublist dist (Zlength data) data).
    { entailer!. all: try rewrite sem_sub_pu_offset by (auto; rep_lia). all: try rewrite HlB2.
      all: try rewrite Int.unsigned_repr by rep_lia. all: auto.
      clear - Pp Pw Hd0 H2 HW3 HB. destruct p; try contradiction; destruct winp'; try contradiction; simpl.
      rewrite Int.unsigned_repr by rep_lia. reflexivity. }
    { repeat split; auto with share; try (apply Forall_sublist; auto); try rep_lia. }
    rewrite HlB2.
    sep_apply (slice_join0 Ews (2 ^ i_wbits s) L1 winp' (Zlength data - dist)
                 (byte_vals (sublist dist (Zlength data) data)) FCw ltac:(lia) ltac:(lia) HLL1
                 ltac:(rewrite Zlength_byte_vals; auto)).
    sep_apply (slice_join_k ssh n c p (e - (Zlength data - dist)) (Zlength data - dist)
                 (byte_vals (sublist dist (Zlength data) data)) FCp ltac:(lia) ltac:(lia) ltac:(lia) H4
                 ltac:(rewrite Zlength_byte_vals; auto)).
    replace (sublist 0 (e - (Zlength data - dist)) c ++ byte_vals (sublist dist (Zlength data) data) ++
             sublist (e - (Zlength data - dist) + (Zlength data - dist)) n c) with c
      by (rewrite <- HcB2; list_solve).
    forward. forward. forward.
    destruct (core_B1 (uw_init s) data (2 ^ i_wbits s) Hs1 Hh1 Hn1 Hv1 HL1 HB
                ltac:(rewrite <- Hdist; exact HC)) as (C1 & C2 & C3 & C4).
    rewrite <- Hdist in C3, C4. rewrite Hd1 in C4. rewrite <- EL1 in C4.
    sep_apply (finish_rep gv sp strmp headp s data winp' (2 ^ i_wbits s) (Zlength data - dist)
                 (sublist 0 0 L1 ++ byte_vals (sublist dist (Zlength data) data) ++
                  sublist (0 + (Zlength data - dist)) (2 ^ i_wbits s) L1) C1 C2 C3 C4).
    return_noent.
    Exists 0 winp'. change (0 =? 0) with true. cbv iota. unfold zfuncs. rewrite <- Hzfp. entailer!.
  + (* the first piece was all of it *)
    assert (HC: Zlength data - dist = 0).
    { rewrite sub_repr in H0. change Int.zero with (Int.repr 0) in H0.
      apply repr_inj_unsigned in H0; [lia | rep_lia | rep_lia]. }
    forward. forward. rewrite add_repr. forward. forward.
    forward_if_field _wnext (Vint (Int.repr (if i_wnext (uw_init s) + dist =? 2 ^ i_wbits s then 0
                                            else i_wnext (uw_init s) + dist))).
    { forward. rewrite (proj2 (Z.eqb_eq _ _)) by lia. entailer!. }
    { forward. rewrite (proj2 (Z.eqb_neq _ _)) by lia. entailer!. }
    forward. forward.
    forward_if_field _whave (Vint (Int.repr (if i_whave (uw_init s) <? 2 ^ i_wbits s
                                            then i_whave (uw_init s) + dist else i_whave (uw_init s)))).
    { forward. forward. rewrite (proj2 (Z.ltb_lt _ _)) by lia. try rewrite add_repr. entailer!. }
    { forward. rewrite (proj2 (Z.ltb_ge _ _)) by lia. entailer!. }
    destruct (core_B2 (uw_init s) data (2 ^ i_wbits s) Hs1 Hh1 Hn1 Hv1 HL1 HB
                ltac:(rewrite <- Hdist; exact HC)) as (C1 & C2 & C3 & C4).
    rewrite <- Hdist in C2, C3, C4. rewrite Hd1 in C4.
    sep_apply (finish_rep gv sp strmp headp s data winp'
                 (if i_whave (uw_init s) <? 2 ^ i_wbits s then i_whave (uw_init s) + dist else i_whave (uw_init s))
                 (if i_wnext (uw_init s) + dist =? 2 ^ i_wbits s then 0 else i_wnext (uw_init s) + dist)
                 _ C1 C3 C2 C4).
    return_noent.
    Exists 0 winp'. change (0 =? 0) with true. cbv iota. unfold zfuncs. rewrite <- Hzfp. entailer!.
Qed.

End Copy.

Lemma body_updatewindow5 {Espec: OracleKind} :
  semax_body Vprog_inflate Gprog_updatewindow f_updatewindow updatewindow_spec3.
Proof.
  clear Espec. start_function.
  destruct sv as [ni [ai [ti [no [ao [tout [msg [st [za [zf [op [dt [adl res]]]]]]]]]]]]].
  change val in ni, ai, ti, no, ao, tout, msg, st, za, zf, op, dt, adl, res.
  match goal with H: stream_ok_val2 _ _ _ |- _ =>
    assert (Hsv: st = sp /\ za = gv _zcalloc /\ zf = gv _zcfree /\ op = nullval) by exact H; clear H end.
  destruct Hsv as (? & ? & ? & ?). subst st za zf op.
  match goal with H: swf s |- _ => rename H into Hswf end.
  match goal with H: i_win s = false -> winp = nullval |- _ => rename H into Hwinp end.
  match goal with H: sublist _ _ c = byte_vals data |- _ => rename H into Hsrc end.
  match goal with H: bytes_ok data |- _ => rename H into Hbok end.
  pose proof (sw_wbits _ Hswf) as Hwb. pose proof (sw_wsize _ Hswf) as Hws.
  pose proof (sw_whave _ Hswf) as Hwh. pose proof (sw_wnext _ Hswf) as Hwn.
  pose proof (sw_wvalid _ Hswf) as Hwv. pose proof (sw_wdata _ Hswf) as Hwd.
  rewrite state_rep_split. unfold zfuncs. Intros.
  remember (gv _zcfree) as zfp eqn:Hzfp.
  assert (HW1: 0 < 2 ^ i_wbits s) by (apply Z.pow_pos_nonneg; lia).
  assert (HW2: 2 ^ i_wbits s <= 2 ^ 23) by (apply Z.pow_le_mono_r; lia).
  assert_PROP (i_win s = true -> isptr winp) as Hwp.
  { unfold win_rep. destruct (i_win s); entailer!. }
  forward.
  forward.
  match goal with |- context [data_at shs t_strm ?sv strmp] =>
    apply semax_seq with (Q := P1 gv shs strmp sv sp headp winp s ssh p n c e data zfp) end.
  unfold P1.
  { unfold win_rep. destruct (i_win s) eqn:Hw.
    - specialize (Hwp eq_refl). Intros.
      forward.
      forward_if.
      + exfalso. match goal with H: winp = nullval |- _ => rewrite H in Hwp; exact Hwp end.
      + forward. Exists winp. entailer!.
    - Intros.
      forward.
      forward_if; [ | ].
      + forward. forward. forward.
        forward_call (tarray tuchar (2 ^ i_wbits s), gv, nullval, 2 ^ i_wbits s, 1).
        { change (Int.unsigned Int.iwordsize) with 32. lia. }
        { entailer!. simpl. rewrite shl_one by lia. reflexivity. }
        { simpl. lia. }
        assert (Hwd0: i_wdata s = []).
        { apply Zlength_nil_inv. destruct Hws as [Hws | [Hws _]]; [lia | discriminate]. }
        Intros vret.
        destruct (eq_dec vret nullval) as [Hv | Hv].
        * subst vret. forward. forward.
          forward_if; [ | ].
          -- return_noent.
             Exists 1 nullval. change (1 =? 0) with false. cbv iota. rewrite state_rep_split. unfold win_rep.
             rewrite Hw. unfold zfuncs. rewrite <- Hzfp. entailer!.
          -- exfalso. match goal with H: ?a <> ?a |- _ => apply H; reflexivity end.
        * Intros. forward. forward.
          forward_if; [ | ].
          -- exfalso. apply Hv. assumption.
          -- forward. Exists vret. rewrite Hwd0. simpl byte_vals. rewrite app_nil_l.
             sep_apply (data_at__data_at Ews (tarray tuchar (2 ^ i_wbits s)) (Zrepeat Vundef (2 ^ i_wbits s))
                          vret ltac:(reflexivity)).
             replace (2 ^ i_wbits s - Zlength (@nil Z)) with (2 ^ i_wbits s) by (rewrite Zlength_nil; lia).
             entailer!.
      + exfalso. match goal with H: ?a <> ?a |- _ => apply H; reflexivity end. }
  unfold P1. Intros winp'.
  match goal with H: i_win s = true -> winp' = winp |- _ => rename H into Hwin' end.
  destruct (uw_init_ok s Hswf) as (Hs1 & Hh1 & Hn1 & Hv1 & Hd1 & Hl1 & Hb1 & Hwi1).
  subst MORE_COMMANDS. unfold abbreviate.
  forward.
  match goal with |- context [data_at shs t_strm ?sv strmp] =>
    let Q := eval unfold P2 in (P2 gv shs strmp sv sp headp winp' s ssh p n c e data zfp) in
    forward_if Q end.
  { assert (Hz: i_wsize s = 0).
    { destruct Hws as [? | [_ Hws]]; auto;
      match goal with H: Int.repr (i_wsize s) = Int.repr 0 |- _ => rewrite Hws in H;
        apply repr_inj_unsigned in H; rep_lia end. }
    forward. forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    forward. forward.
    rewrite (uw_init_eq0 s Hz). mnorm_goal. rewrite shl_one by lia. entailer!. }
  { assert (Hz: i_wsize s <> 0).
    { intro Hz. match goal with
      | H: i_wsize s <> 0 |- _ => contradiction
      | H: Int.repr (i_wsize s) <> Int.repr 0 |- _ => apply H; rewrite Hz; reflexivity end. }
    forward. rewrite (uw_init_neq0 s Hz). entailer!. }
  (* the copy *)
  assert (HW3: 2 ^ i_wbits s <= 8388608) by (change 8388608 with (2 ^ 23); auto).
  rewrite Hs1 in Hh1, Hn1, Hv1.
  assert (HL1: Zlength (i_wdata (uw_init s)) = i_whave (uw_init s)) by (rewrite Hd1; auto).
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FCp by entailer!.
  assert_PROP (field_compatible (tarray tuchar (2 ^ i_wbits s)) [] winp') as FCw by entailer!.
  assert (Pp: isptr p) by (destruct FCp; auto).
  assert (Pw: isptr winp') by (destruct FCw; auto).
  rewrite Hs1.
  forward.
  apply semax_if_seq.
  forward_if.
  - assert (HA: Zlength data >= 2 ^ i_wbits s) by (uint_hyp; lia).
    match goal with |- semax ?D _ _ _ =>
      change D with (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil) end.
    change (semax (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil)
      (PC gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp' s ssh p n c e data zfp)
      (Ssequence uw_DA uw_ret)
      (uw_post gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp s ssh p n c data)).
    apply uw_caseA; assumption.
  - assert (HB: Zlength data < 2 ^ i_wbits s) by (uint_hyp; lia).
    match goal with |- semax ?D _ _ _ =>
      change D with (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil) end.
    change (semax (func_tycontext f_updatewindow Vprog_inflate Gprog_updatewindow nil)
      (PC gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp' s ssh p n c e data zfp)
      (Ssequence uw_DB uw_ret)
      (uw_post gv shs strmp (ni, (ai, (ti, (no, (ao, (tout, (msg, (sp, (gv _zcalloc, (zfp, (nullval, (dt, (adl, res))))))))))))) sp headp winp s ssh p n c data)).
    apply uw_caseB; assumption.
Qed.
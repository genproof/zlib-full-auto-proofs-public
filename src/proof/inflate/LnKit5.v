(* The case LEN (20) of inflate()'s switch (Cases5_LEN.v), cut into parts:
   - the Clight cut into its statements (ln_cond: the F4 test; ln_fast: RESTORE, inflate_fast, LOAD, back;
     ln_loop1: the root lookup loop; ln_ltest / ln_link: the link test and the sub-table part (ln_copy: last = here;
     ln_loop2: the sub-table lookup loop; ln_dropl: DROPBITS(last.bits); ln_backl); ln_tail: DROPBITS(here.bits),
     back, length and the four outcomes LIT / TYPE / BAD / LENEXT);
   - the model's tail (ln_tail_m) and the equation of c_LEN's slow path in these pieces (c_LEN_slow_eq);
   - the state with the locals `here` and `last` holding values (ls_hl);
   - the decoding table as an array (tab_arr) and the statements of the parts (ln_*_stmt), proved in Ln<Part>5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseHyps5.
Require Export Zlib.proof.inflate.Model2.
Require Export Zlib.proof.inflate.Steps2.
Require Export Zlib.proof.inflate.StepKit.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight                                                                                     *)

Definition ln_body : statement := case_body 20.
Definition ln_head : statement := match ln_body with Ssequence h _ => h | _ => Sskip end.
Definition ln_slow : statement := match ln_body with Ssequence _ s => s | _ => Sskip end.
(* the test have >= 6 && left >= 258 && bits < 8 into _t'73 *)
Definition ln_cond : statement := match ln_head with Ssequence c _ => c | _ => Sskip end.
(* RESTORE(); inflate_fast(strm, out); LOAD(); if (state->mode == TYPE) state->back = -1; break; *)
Definition ln_fast : statement :=
  match ln_head with Ssequence _ (Sifthenelse _ f _) => f | _ => Sskip end.
(* state->back = 0; *)
Definition ln_back0 : statement := match ln_slow with Ssequence b _ => b | _ => Sskip end.
Definition ln_s1 : statement := match ln_slow with Ssequence _ r => r | _ => Sskip end.
(* for (;;) { here = lencode[BITS(lenbits)]; if (here.bits <= bits) break; PULLBYTE(); } *)
Definition ln_loop1 : statement := match ln_s1 with Ssequence l _ => l | _ => Sskip end.
Definition ln_s2 : statement := match ln_s1 with Ssequence _ r => r | _ => Sskip end.
(* if (leave) break; *)
Definition ln_ifleave1 : statement := match ln_s2 with Ssequence l _ => l | _ => Sskip end.
Definition ln_s3 : statement := match ln_s2 with Ssequence _ r => r | _ => Sskip end.
Definition ln_lif : statement := match ln_s3 with Ssequence l _ => l | _ => Sskip end.
(* DROPBITS(here.bits); state->back += here.bits; state->length = here.val; the outcomes *)
Definition ln_tail : statement := match ln_s3 with Ssequence _ t => t | _ => Sskip end.
(* the test here.op && (here.op & 0xf0) == 0 into _t'76 *)
Definition ln_ltest : statement := match ln_lif with Ssequence t _ => t | _ => Sskip end.
Definition ln_link : statement := match ln_lif with Ssequence _ (Sifthenelse _ l _) => l | _ => Sskip end.
(* last = here; (field by field: op, bits, val) *)
Definition ln_c1 : statement := match ln_link with Ssequence c _ => c | _ => Sskip end.
Definition ln_c2 : statement := match ln_link with Ssequence _ (Ssequence c _) => c | _ => Sskip end.
Definition ln_c3 : statement := match ln_link with Ssequence _ (Ssequence _ (Ssequence c _)) => c | _ => Sskip end.
Definition ln_l1 : statement :=
  match ln_link with Ssequence _ (Ssequence _ (Ssequence _ r)) => r | _ => Sskip end.
(* for (;;) { here = lencode[last.val + (BITS(last.bits + last.op) >> last.bits)]; ... PULLBYTE(); } *)
Definition ln_loop2 : statement := match ln_l1 with Ssequence l _ => l | _ => Sskip end.
Definition ln_l2 : statement := match ln_l1 with Ssequence _ r => r | _ => Sskip end.
Definition ln_ifleave2 : statement := match ln_l2 with Ssequence l _ => l | _ => Sskip end.
Definition ln_l3 : statement := match ln_l2 with Ssequence _ r => r | _ => Sskip end.
(* DROPBITS(last.bits) (a do-while(0)) *)
Definition ln_dropl : statement := match ln_l3 with Ssequence d _ => d | _ => Sskip end.
(* state->back += last.bits; *)
Definition ln_backl : statement := match ln_l3 with Ssequence _ b => b | _ => Sskip end.

Definition ifleave_stmt : statement := Sifthenelse (Etempvar _leave tint) Sbreak Sskip.

Lemma ln_body_eq: ln_body =
  Ssequence (Ssequence ln_cond (Sifthenelse (Etempvar _t'73 tint) ln_fast Sskip))
    (Ssequence ln_back0 (Ssequence ln_loop1 (Ssequence ifleave_stmt
      (Ssequence (Ssequence ln_ltest (Sifthenelse (Etempvar _t'76 tint) ln_link Sskip)) ln_tail)))).
Proof. reflexivity. Qed.

Lemma ln_link_eq: ln_link =
  Ssequence ln_c1 (Ssequence ln_c2 (Ssequence ln_c3 (Ssequence ln_loop2 (Ssequence ifleave_stmt (Ssequence ln_dropl ln_backl))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* DROPBITS(here.bits); back += here.bits; length = here.val; then LIT / TYPE / BAD / LENEXT *)
Definition ln_tail_m (h: entry) (m: mst) : iout :=
  let m := dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))) in
  let m := upd_s m (fun s => set_i_length s (e_val h)) in
  if e_op h =? 0 then IBrk (set_mode m LIT) else
  if negb (Z.land (e_op h) 32 =? 0) then IBrk (set_mode (upd_s m (fun s => set_i_back s (-1))) Model.TYPE) else
  if negb (Z.land (e_op h) 64 =? 0) then IBrk (set_bad m M_ll_code) else
  c_LENEXT lenfix_list distfix_list (set_mode (upd_s m (fun s => set_i_extra s (Z.land (e_op h) 15))) LENEXT).

(* the slow path of c_LEN, with the machine after state->back = 0 *)
Definition ln_slow_m (m: mst) : iout :=
  let s := m_s m in
  match lookup1 lenfix_list distfix_list (i_lencode s) (i_lenbits s) m with
  | (here, m1, false) => IBrk m1
  | (here, m1, true) =>
      if andb (negb (e_op here =? 0)) (Z.land (e_op here) 240 =? 0) then
        match lookup2 lenfix_list distfix_list (i_lencode s) here m1 with
        | (h2, m2, false) => IBrk m2
        | (h2, m2, true) =>
            ln_tail_m h2 (dropbits (e_bits here) (upd_s m2 (fun s => set_i_back s (i_back s + e_bits here))))
        end
      else ln_tail_m here m1
  end.

Definition ln_fastc (m: mst) : bool := andb (andb (6 <=? m_have m) (258 <=? m_left m)) (m_bits m <? 8).

Lemma c_LEN_slow_eq: forall fst m, ln_fastc m = false ->
  c_LEN lenfix_list distfix_list fst m = ln_slow_m (upd_s m (fun s => set_i_back s 0)).
Proof.
  intros fst m E. unfold c_LEN. unfold ln_fastc in E. rewrite E. unfold ln_slow_m.
  destruct (lookup1 _ _ _ _ _) as [[here m1] ok]. destruct ok; [ | reflexivity].
  destruct (andb (negb (e_op here =? 0)) (Z.land (e_op here) 240 =? 0)); [ | reflexivity].
  destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2]. destruct ok2; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the states                                                                                     *)

(* loop_state's temps *)
Definition ln_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

(* loop_state with the locals here and last holding hv and lv *)
Definition ls_hl (F: frame) (m: mst) (hv lv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ln_locals F m)
  (SEPx [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma loop_state_hl: forall F m, loop_state F m = ls_hl F m (default_val t_code) (default_val t_code).
Proof.
  intros. unfold loop_state, ls_hl, locals_rep, ln_locals. f_equal. f_equal.
  unfold SEPx. extensionality rho. simpl. rewrite !sepcon_emp.
  unfold data_at_, field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma ls_hl_loop_state: forall F m hv lv, ls_hl F m hv lv |-- loop_state F m.
Proof.
  intros. rewrite loop_state_hl. unfold ls_hl, PROPx, LOCALx, SEPx.
  repeat (apply andp_derives; [apply derives_refl|]). intro rho. cbn [fold_right_sepcon].
  apply sepcon_derives; [apply derives_refl|].
  apply sepcon_derives; [apply data_at_data_at_|].
  apply sepcon_derives; [apply data_at_data_at_|]. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the decoding table as an array, and the memory a lookup loop reads                             *)

Definition tab_sh (F: frame) (t: tref) : share := match t with TCodes _ => Ews | _ => f_gsh F end.
Definition tab_list (s: istate) (t: tref) : list entry :=
  match t with
  | TLenfix => lenfix_list
  | TDistfix => distfix_list
  | TCodes k => sublist k ENOUGH_CODES (i_codes s)
  end.
(* tab_entry s t i is Znth i (tab_list s t) for 0 <= i *)
Definition tab_arr (F: frame) (s: istate) (t: tref) : mpred :=
  data_at (tab_sh F t) (tarray t_code (tab_size t)) (map ent (tab_list s t)) (tref_val (f_gv F) (f_sp F) t).

(* state->lencode, state->lenbits, the table lencode points to, the input *)
Definition ln_view (F: frame) (m: mst) : mpred :=
  field_at Ews t_state (DOT _lencode) (tref_val (f_gv F) (f_sp F) (i_lencode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits (m_s m))) (f_sp F) *
  tab_arr F (m_s m) (i_lencode (m_s m)) *
  in_rep (f_ib F).

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the parts                                                                    *)

(* the memory of a lookup apart (LnTab5.v) *)
Definition ln_tab_stmt : Prop :=
  (forall s t i, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> 0 <= i ->
     tab_entry lenfix_list distfix_list s t i = Znth i (tab_list s t)) /\
  (forall s t, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> Zlength (tab_list s t) = tab_size t) /\
  (forall F m, tref_ok (i_lencode (m_s m)) -> Zlength (i_codes (m_s m)) = ENOUGH_CODES ->
     mem_rep F m |-- ln_view F m * (ln_view F m -* mem_rep F m)).

(* the fast path (LnFast5.v) *)
Definition ln_fast_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (R: ret_assert),
  frame_ok5 F -> mwf3 m -> m_mode m = LEN -> m_leave m = 0 ->
  6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
  RA_break R = RA_normal (case_post2 F m) ->
  semax Delta_cases5 (loop_state F m) ln_fast R.

(* the root lookup loop (LnLoop1_5.v) *)
Definition ln_loop1_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (hv lv: reptype t_code),
  frame_ok5 F -> mwf m -> m_mode m = LEN -> m_leave m = 0 ->
  semax Delta_cases5 (ls_hl F m hv lv) ln_loop1
    (normal_ret_assert (EX here: entry, EX m1: mst, EX ok: bool,
       !! (lookup1 lenfix_list distfix_list (i_lencode (m_s m)) (i_lenbits (m_s m)) m = (here, m1, ok)) &&
       ls_hl F m1 (ent here) lv)).

(* the sub-table lookup loop (LnLoop2_5.v) *)
Definition ln_loop2_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (last: entry) (hv: reptype t_code) (sz: Z),
  frame_ok5 F -> mwf m -> m_mode m = LEN -> m_leave m = 0 ->
  sz <= tab_size (i_lencode (m_s m)) ->
  sub_ok LENS (tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m))) (i_lenbits (m_s m)) sz last ->
  entry_ok last -> e_bits last <= m_bits m ->
  semax Delta_cases5 (ls_hl F m hv (ent last)) ln_loop2
    (normal_ret_assert (EX here: entry, EX m1: mst, EX ok: bool,
       !! (lookup2 lenfix_list distfix_list (i_lencode (m_s m)) last m = (here, m1, ok)) &&
       ls_hl F m1 (ent here) (ent last))).

(* the tail: DROPBITS(here.bits), back, length, LIT / TYPE / BAD (break) or LENEXT (fall through) (LnTail5.v) *)
Definition ln_tail_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m0 m: mst) (h: entry) (lv: reptype t_code) (R: ret_assert),
  frame_ok5 F -> mwf3 m -> m_mode m = LEN -> m_leave m = 0 ->
  entry_ok h -> final_ok LENS h -> 0 <= i_back (m_s m) -> i_back (m_s m) + e_bits h <= 15 ->
  e_bits h <= m_bits m ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = ln_tail_m h m ->
  RA_break R = RA_normal (case_post2 F m0) ->
  RA_normal R = fall_post5 F m0 LENEXT ->
  semax Delta_cases5 (ls_hl F m (ent h) lv) ln_tail R.

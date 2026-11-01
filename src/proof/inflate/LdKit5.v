(* The cases LENEXT (21) and DIST (22) of inflate()'s switch (Cases5_LD.v), cut into parts:
   - LENEXT: the Clight cut into its statements (le_nb: NEEDBITS(state->extra), a loop that re-reads its bound
     state->extra; le_rest: length += BITS(extra), DROPBITS(extra), back += extra; le_fin: was = length,
     mode = DIST); the NEEDBITS part statement ld_nb_stmt;
   - DIST: the Clight cut into its statements (ds_loop1: the root lookup loop over distcode; ds_ltest / ds_link:
     the link test and the sub-table part (ds_c1..c3: last = here; ds_loop2: the sub-table lookup loop;
     ds_dropl: DROPBITS(last.bits); ds_backl: back += last.bits); ds_tail: DROPBITS(here.bits), back, the
     invalid-code test (BAD), offset, extra, mode DISTEXT);
   - the model's tail (ds_tail_m) and the equation of c_DIST in these pieces (c_DIST_eq);
   - the state with the locals `here` and `last` holding values (ld_hl);
   - the decoding table as an array (ld_tab_arr), the view of what a lookup reads (ds_view) and the statements
     of the parts (ds_*_stmt, ld_*_stmt), proved in Ld<Part>5.v / Ds<Part>5.v.
   The same design as LnKit5.v of the case LEN. *)
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
(* the Clight of LENEXT                                                                           *)

Definition le_body : statement := case_body 21.
(* if (state->extra) { NEEDBITS(state->extra); length += BITS(extra); DROPBITS(extra); back += extra; } *)
Definition le_head : statement := match le_body with Ssequence h _ => h | _ => Sskip end.
(* state->was = state->length; state->mode = DIST; *)
Definition le_fin : statement := match le_body with Ssequence _ f => f | _ => Sskip end.
Definition le_ext : statement :=
  match le_head with Ssequence _ (Sifthenelse _ e _) => e | _ => Sskip end.
(* NEEDBITS(state->extra): for (;;) { if (!(bits < state->extra)) break; PULLBYTE(); } *)
Definition le_nb : statement := match le_ext with Ssequence (Ssequence nb _) _ => nb | _ => Sskip end.
(* state->length += BITS(state->extra); DROPBITS(state->extra); state->back += state->extra; *)
Definition le_rest : statement := match le_ext with Ssequence _ r => r | _ => Sskip end.

Definition ld_ifleave : statement := Sifthenelse (Etempvar _leave tint) Sbreak Sskip.

Lemma le_body_eq: le_body =
  Ssequence
    (Ssequence
       (Sset _t'223 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                               (Tstruct _inflate_state noattr)) _extra tuint))
       (Sifthenelse (Etempvar _t'223 tuint) (Ssequence (Ssequence le_nb ld_ifleave) le_rest) Sskip))
    le_fin.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight of DIST                                                                             *)

Definition ds_body : statement := case_body 22.
(* for (;;) { here = distcode[BITS(distbits)]; if (here.bits <= bits) break; PULLBYTE(); } *)
Definition ds_loop1 : statement := match ds_body with Ssequence l _ => l | _ => Sskip end.
Definition ds_s1 : statement := match ds_body with Ssequence _ r => r | _ => Sskip end.
Definition ds_s2 : statement := match ds_s1 with Ssequence _ r => r | _ => Sskip end.
Definition ds_lif : statement := match ds_s2 with Ssequence l _ => l | _ => Sskip end.
(* DROPBITS(here.bits); back += here.bits; if (here.op & 64) BAD; offset = here.val; extra = here.op & 15;
   mode = DISTEXT *)
Definition ds_tail : statement := match ds_s2 with Ssequence _ t => t | _ => Sskip end.
(* _t'182 = here.op *)
Definition ds_ltest : statement := match ds_lif with Ssequence t _ => t | _ => Sskip end.
(* (_t'182 & 0xf0) == 0 *)
Definition ds_lcond : expr :=
  match ds_lif with Ssequence _ (Sifthenelse c _ _) => c | _ => Etempvar _leave tint end.
Definition ds_link : statement :=
  match ds_lif with Ssequence _ (Sifthenelse _ l _) => l | _ => Sskip end.
(* last = here; (field by field: op, bits, val) *)
Definition ds_c1 : statement := match ds_link with Ssequence c _ => c | _ => Sskip end.
Definition ds_c2 : statement := match ds_link with Ssequence _ (Ssequence c _) => c | _ => Sskip end.
Definition ds_c3 : statement := match ds_link with Ssequence _ (Ssequence _ (Ssequence c _)) => c | _ => Sskip end.
Definition ds_l1 : statement :=
  match ds_link with Ssequence _ (Ssequence _ (Ssequence _ r)) => r | _ => Sskip end.
(* for (;;) { here = distcode[last.val + (BITS(last.bits + last.op) >> last.bits)]; ... PULLBYTE(); } *)
Definition ds_loop2 : statement := match ds_l1 with Ssequence l _ => l | _ => Sskip end.
Definition ds_l2 : statement := match ds_l1 with Ssequence _ r => r | _ => Sskip end.
Definition ds_l3 : statement := match ds_l2 with Ssequence _ r => r | _ => Sskip end.
(* DROPBITS(last.bits) (a do-while(0)) *)
Definition ds_dropl : statement := match ds_l3 with Ssequence d _ => d | _ => Sskip end.
(* state->back += last.bits; *)
Definition ds_backl : statement := match ds_l3 with Ssequence _ b => b | _ => Sskip end.

Lemma ds_body_eq: ds_body =
  Ssequence ds_loop1 (Ssequence ld_ifleave
    (Ssequence (Ssequence ds_ltest (Sifthenelse ds_lcond ds_link Sskip)) ds_tail)).
Proof. reflexivity. Qed.

Lemma ds_ltest_eq: ds_ltest = Sset _t'182 (Efield (Evar _here t_code) _op tuchar).
Proof. reflexivity. Qed.

Lemma ds_lcond_eq: ds_lcond =
  Ebinop Oeq (Ebinop Oand (Etempvar _t'182 tuchar) (Econst_int (Int.repr 240) tint) tint)
    (Econst_int (Int.repr 0) tint) tint.
Proof. reflexivity. Qed.

Lemma ds_link_eq: ds_link =
  Ssequence ds_c1 (Ssequence ds_c2 (Ssequence ds_c3 (Ssequence ds_loop2 (Ssequence ld_ifleave
    (Ssequence ds_dropl ds_backl))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the model                                                                                      *)

(* DROPBITS(h.bits); back += h.bits; BAD on an invalid code; offset, extra; DISTEXT *)
Definition ds_tail_m (h: entry) (m: mst) : iout :=
  let m := dropbits (e_bits h) (upd_s m (fun s => set_i_back s (i_back s + e_bits h))) in
  if negb (Z.land (e_op h) 64 =? 0) then IBrk (set_bad m M_d_code) else
  let m := upd_s m (fun s => set_i_extra (set_i_offset s (e_val h)) (Z.land (e_op h) 15)) in
  c_DISTEXT (set_mode m DISTEXT).

(* the machine after the sub-table part: DROPBITS(last.bits); back += last.bits *)
Definition ds_drop (b: Z) (m: mst) : mst := dropbits b (upd_s m (fun s => set_i_back s (i_back s + b))).

Definition ds_m (m: mst) : iout :=
  let s := m_s m in
  match lookup1 lenfix_list distfix_list (i_distcode s) (i_distbits s) m with
  | (here, m1, false) => IBrk m1
  | (here, m1, true) =>
      if Z.land (e_op here) 240 =? 0 then
        match lookup2 lenfix_list distfix_list (i_distcode s) here m1 with
        | (h2, m2, false) => IBrk m2
        | (h2, m2, true) => ds_tail_m h2 (ds_drop (e_bits here) m2)
        end
      else ds_tail_m here m1
  end.

Lemma c_DIST_eq: forall m, c_DIST lenfix_list distfix_list m = ds_m m.
Proof.
  intros m. unfold c_DIST, ds_m, ds_drop.
  destruct (lookup1 _ _ _ _ _) as [[here m1] ok]. destruct ok; [ | reflexivity].
  destruct (Z.land (e_op here) 240 =? 0); [ | reflexivity].
  destruct (lookup2 _ _ _ _ _) as [[h2 m2] ok2]. destruct ok2; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the states                                                                                     *)

(* loop_state's temps *)
Definition ld_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _flush (zv (f_flush F)); temp _state (f_sp F);
   temp _next (in_ptr (f_ib F) (m_nx m)); temp _put (out_ptr (f_ob F) (Zlength (m_ow m)));
   temp _have (zv (m_have m)); temp _left (zv (m_left m)); temp _hold (lv (m_hold m));
   temp _bits (zv (m_bits m)); temp _in (zv (m_in m)); temp _out (zv (m_out m));
   temp _ret (zv (m_ret m)); temp _leave (zv (m_leave m));
   lvar _here t_code (f_vhere F); lvar _last t_code (f_vlast F);
   lvar _hbuf (tarray tuchar 4) (f_vhbuf F); gvars (f_gv F)].

(* loop_state with the locals here and last holding hv and lv *)
Definition ld_hl (F: frame) (m: mst) (hv lv: reptype t_code) : environ -> mpred :=
  PROPx [in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m)]
  (LOCALx (ld_locals F m)
  (SEPx [mem_rep F m; data_at Tsh t_code hv (f_vhere F); data_at Tsh t_code lv (f_vlast F);
         data_at_ Tsh (tarray tuchar 4) (f_vhbuf F)])).

Lemma loop_state_ld_hl: forall F m, loop_state F m = ld_hl F m (default_val t_code) (default_val t_code).
Proof.
  intros. unfold loop_state, ld_hl, locals_rep, ld_locals. f_equal. f_equal.
  unfold SEPx. extensionality rho. simpl. rewrite !sepcon_emp.
  unfold data_at_, field_at_. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma ld_hl_loop_state: forall F m hv lv, ld_hl F m hv lv |-- loop_state F m.
Proof.
  intros. rewrite loop_state_ld_hl. unfold ld_hl, PROPx, LOCALx, SEPx.
  repeat (apply andp_derives; [apply derives_refl|]). intro rho. cbn [fold_right_sepcon].
  apply sepcon_derives; [apply derives_refl|].
  apply sepcon_derives; [apply data_at_data_at_|].
  apply sepcon_derives; [apply data_at_data_at_|]. apply derives_refl.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the decoding table as an array, and the memory a lookup loop reads                             *)

Definition ld_tab_sh (F: frame) (t: tref) : share := match t with TCodes _ => Ews | _ => f_gsh F end.
Definition ld_tab_list (s: istate) (t: tref) : list entry :=
  match t with
  | TLenfix => lenfix_list
  | TDistfix => distfix_list
  | TCodes k => sublist k ENOUGH_CODES (i_codes s)
  end.
(* tab_entry s t i is Znth i (ld_tab_list s t) for 0 <= i *)
Definition ld_tab_arr (F: frame) (s: istate) (t: tref) : mpred :=
  data_at (ld_tab_sh F t) (tarray t_code (tab_size t)) (map ent (ld_tab_list s t)) (tref_val (f_gv F) (f_sp F) t).

(* state->distcode, state->distbits, the table distcode points to, the input *)
Definition ds_view (F: frame) (m: mst) : mpred :=
  field_at Ews t_state (DOT _distcode) (tref_val (f_gv F) (f_sp F) (i_distcode (m_s m))) (f_sp F) *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits (m_s m))) (f_sp F) *
  ld_tab_arr F (m_s m) (i_distcode (m_s m)) *
  in_rep (f_ib F).

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the parts                                                                    *)

(* LENEXT: NEEDBITS(state->extra) (LdNb5.v) *)
Definition ld_nb_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst),
  mwf m -> m_mode m = LENEXT -> m_leave m = 0 ->
  semax Delta_cases5 (loop_state F m) le_nb
    (normal_ret_assert (loop_state F (needbits (i_extra (m_s m)) m))).

(* LENEXT: the whole case, from its NEEDBITS (LdLenext5.v) *)
Definition ld_lenext_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok5 F DIST 22 -> case_ok5 F LENEXT 21.

(* DIST: the memory of a lookup apart (DsTab5.v) *)
Definition ds_tab_stmt : Prop :=
  (forall s t i, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> 0 <= i ->
     tab_entry lenfix_list distfix_list s t i = Znth i (ld_tab_list s t)) /\
  (forall s t, tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> Zlength (ld_tab_list s t) = tab_size t) /\
  (forall F m, tref_ok (i_distcode (m_s m)) -> Zlength (i_codes (m_s m)) = ENOUGH_CODES ->
     mem_rep F m |-- ds_view F m * (ds_view F m -* mem_rep F m)).

(* DIST: the root lookup loop (DsLoop1_5.v) *)
Definition ds_loop1_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (hv lv: reptype t_code),
  frame_ok5 F -> mwf m -> m_mode m = DIST -> m_leave m = 0 ->
  semax Delta_cases5 (ld_hl F m hv lv) ds_loop1
    (normal_ret_assert (EX here: entry, EX m1: mst, EX ok: bool,
       !! (lookup1 lenfix_list distfix_list (i_distcode (m_s m)) (i_distbits (m_s m)) m = (here, m1, ok)) &&
       ld_hl F m1 (ent here) lv)).

(* DIST: the sub-table lookup loop (DsLoop2_5.v) *)
Definition ds_loop2_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst) (last: entry) (hv: reptype t_code) (sz: Z),
  frame_ok5 F -> mwf m -> m_mode m = DIST -> m_leave m = 0 ->
  sz <= tab_size (i_distcode (m_s m)) ->
  sub_ok DISTS (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m))) (i_distbits (m_s m)) sz last ->
  entry_ok last -> e_bits last <= m_bits m ->
  semax Delta_cases5 (ld_hl F m hv (ent last)) ds_loop2
    (normal_ret_assert (EX here: entry, EX m1: mst, EX ok: bool,
       !! (lookup2 lenfix_list distfix_list (i_distcode (m_s m)) last m = (here, m1, ok)) &&
       ld_hl F m1 (ent here) (ent last))).

(* DIST: the sub-table part: last = here; the sub-table loop; if (leave) break; DROPBITS(last.bits);
   back += last.bits (DsLink5.v) *)
Definition ds_link_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m0 m: mst) (here: entry) (lv: reptype t_code) (sz: Z) (R: ret_assert),
  frame_ok5 F -> mwf m -> m_mode m = DIST -> m_leave m = 0 ->
  sz <= tab_size (i_distcode (m_s m)) ->
  sub_ok DISTS (tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m))) (i_distbits (m_s m)) sz here ->
  entry_ok here -> e_bits here <= m_bits m ->
  RA_break R = RA_normal (case_post2 F m0) ->
  (forall h2 m2, lookup2 lenfix_list distfix_list (i_distcode (m_s m)) here m = (h2, m2, false) ->
     stepf2 (f_flush F) lenfix_list distfix_list m0 = IBrk m2) ->
  semax Delta_cases5 (ld_hl F m (ent here) lv) ds_link
    (overridePost
       (EX h2: entry, EX m2: mst,
          !! (lookup2 lenfix_list distfix_list (i_distcode (m_s m)) here m = (h2, m2, true)) &&
          ld_hl F (ds_drop (e_bits here) m2) (ent h2) (ent here))
       R).

(* DIST: the tail, from the machine M after the lookups and the sub-table's b1 dropped bits (b1 = 0 without a
   sub-table): DROPBITS(here.bits), back, BAD (break) or offset, extra, DISTEXT (fall through) (DsTail5.v) *)
Definition ds_tail_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m0 M: mst) (b1: Z) (h: entry) (lv: reptype t_code) (R: ret_assert),
  frame_ok5 F -> mwf3 M -> m_mode M = DIST -> m_leave M = 0 ->
  0 <= b1 -> entry_ok h -> final_ok DISTS h -> b1 + e_bits h <= 15 -> b1 + e_bits h <= m_bits M ->
  stepf2 (f_flush F) lenfix_list distfix_list m0 = ds_tail_m h (ds_drop b1 M) ->
  RA_break R = RA_normal (case_post2 F m0) ->
  RA_normal R = fall_post5 F m0 DISTEXT ->
  semax Delta_cases5 (ld_hl F (ds_drop b1 M) (ent h) lv) ds_tail R.

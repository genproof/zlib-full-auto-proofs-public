(* The main for(;;) loop of inflate_table (segment seg_loop of verif_it_defs.v), cut into five
   consecutive parts of its body, with the assertions between them and the triple of each part.
   (Each part is proved in its own file seg_loop_<part>.v, the loop is assembled in part_seg_loop.v.)

   The body of the loop is `Ssequence Sskip B` with B the right-nested sequence of 12 statements
     a1 a2 | a3 a4 a5 r | i2 w f y | c | u
   cut into
     sl_here = a1;a2         here.bits = len - drop; here.op/here.val by type
     sl_rep  = a3;a4;a5;r    incr = 1 << (len - drop); fill = 1 << curr; min = fill; do {...} while (fill != 0)
     sl_huff = i2;w;f;y      incr = 1 << (len - 1); while (huff & incr) incr >>= 1; huff update; sym++
     sl_cnt  = c             if (--(count[len]) == 0) { if (len == max) break; len = lens[work[sym]]; }
     sl_sub  = u             if (len > root && (huff & mask) != low) { ... return 1 ...; root link entry }
   All the assertions are about the model state s at the top of the iteration (model.v step):
     A_loop X s  --sl_here-->  SL_here X s  --sl_rep-->  SL_rep X s  --sl_huff-->  SL_huff X s
                 --sl_cnt-->   SL_cnt X s (break: EX s', A_brk X s')
                 --sl_sub-->   EX s', A_loop X s' (return 1: POST_it X). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Export Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts of the body. *)

Definition sl_parts : statement * statement * statement * statement * statement :=
  match seg_loop with
  | Sloop (Ssequence Sskip (Ssequence a1 (Ssequence a2 (Ssequence a3 (Ssequence a4 (Ssequence a5
      (Ssequence r (Ssequence i2 (Ssequence w (Ssequence f (Ssequence y (Ssequence c u)))))))))))) _ =>
      (Ssequence a1 a2, Ssequence a3 (Ssequence a4 (Ssequence a5 r)),
       Ssequence i2 (Ssequence w (Ssequence f y)), c, u)
  | _ => (Sskip, Sskip, Sskip, Sskip, Sskip)
  end.

Definition sl_here : statement :=
  ltac:(let x := eval cbv [sl_parts seg_loop fst snd] in (fst (fst (fst (fst sl_parts)))) in exact x).
Definition sl_rep : statement :=
  ltac:(let x := eval cbv [sl_parts seg_loop fst snd] in (snd (fst (fst (fst sl_parts)))) in exact x).
Definition sl_huff : statement :=
  ltac:(let x := eval cbv [sl_parts seg_loop fst snd] in (snd (fst (fst sl_parts))) in exact x).
Definition sl_cnt : statement :=
  ltac:(let x := eval cbv [sl_parts seg_loop fst snd] in (snd (fst sl_parts)) in exact x).
Definition sl_sub : statement :=
  ltac:(let x := eval cbv [sl_parts seg_loop fst snd] in (snd sl_parts) in exact x).

(* ---------------------------------------------------------------------------------------------- *)
(* The model's values of one iteration from s (model.v step; see also the st_ functions of model_inv.v) *)

(* here: the entry of the current symbol. *)
Definition sl_here_e (X: itctx) (s: state) : entry :=
  sym_entry (c_type X) (Znth (s_sym s) (sorted_syms (c_lens X))) (s_len s - s_drop s).

(* The table after the replicate loop. *)
Definition sl_t1 (X: itctx) (s: state) : list entry :=
  rep_fill (s_tab s) (s_next s + Z.shiftr (s_huff s) (s_drop s)) (Z.shiftl 1 (s_len s - s_drop s))
           (Z.to_nat (Z.shiftl 1 (s_curr s) / Z.shiftl 1 (s_len s - s_drop s))) (sl_here_e X s).

(* The model's Break state (count[len] reaches 0 at len == max). *)
Definition sl_brk (X: itctx) (s: state) : state :=
  mkSt (st_huff' s) (s_sym s + 1) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s)
       (st_cnt' s) (sl_t1 X s).

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions.  Same PROP as A_loop X s (s is the state at the top of the iteration), the
   loop's locals, the constant locals, and it_sep with `here` and count/table as given. *)

Definition sl_props (X: itctx) (s: state) : list Prop :=
  [1 <= it_mx X; acc_test (c_type X) (c_lens X);
   over (c_type X) (Z.shiftl 1 (it_root X)) = false;
   reach (c_type X) (c_lens X) (c_req X) (c_old X) (Z.to_nat (s_sym s)) s].

Definition sl_K (X: itctx) : list localdef :=
  temp _root (Vint (Int.repr (it_root X))) ::
  temp _max (Vint (Int.repr (it_mx X))) ::
  temp _mask (Vint (Int.repr (Z.shiftl 1 (it_root X) - 1))) ::
  temp _match (Vint (Int.repr (match_of (c_type X)))) ::
  temp _base (base_v X) :: temp _extra (extra_v X) :: params_locs X.

Definition sl_locs (X: itctx) (huff sym len curr drop low used next: Z) : list localdef :=
  temp _huff (Vint (Int.repr huff)) ::
  temp _sym (Vint (Int.repr sym)) ::
  temp _len (Vint (Int.repr len)) ::
  temp _curr (Vint (Int.repr curr)) ::
  temp _drop (Vint (Int.repr drop)) ::
  temp _low (Vint (Int.repr low)) ::
  temp _used (Vint (Int.repr used)) ::
  temp _next (offset_val (4 * next) (c_pt X)) :: sl_K X.

(* it_sep X (count_at X cnt) (work_sorted X) tab, with `here` given by hv. *)
Definition sl_sep (X: itctx) (hv: mpred) (cnt: list Z) (tab: list entry) : list mpred :=
  [data_at_ Tsh (tarray tushort 16) (c_offs X);
   count_at X cnt;
   hv;
   itables (c_shg X) (c_gv X);
   data_at (c_shl X) (tarray tushort (Zlength (c_lens X))) (zs_rep (c_lens X)) (c_pl X);
   work_sorted X;
   data_at (c_sh X) (tarray code_t (Zlength (c_old X))) (map entry_rep tab) (c_pt X);
   data_at (c_sh X) (tptr code_t) (c_pt X) (c_ptab X);
   data_at (c_sh X) tuint (Vint (Int.repr (c_req X))) (c_pb X)].

Definition here_ (X: itctx) : mpred := data_at_ Tsh (Tstruct ___gp_code noattr) (c_here X).

(* After sl_here: `here` holds the model's entry. *)
Definition SL_here (X: itctx) (s: state) : environ -> mpred :=
  PROPx (sl_props X s)
   (LOCALx (sl_locs X (s_huff s) (s_sym s) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s))
    (SEPx (sl_sep X (data_at Tsh (Tstruct ___gp_code noattr) (entry_rep (sl_here_e X s)) (c_here X))
                  (s_cnt s) (s_tab s)))).

(* After sl_rep: the table is sl_t1, min = 1 << curr (here holds anything again). *)
Definition SL_rep (X: itctx) (s: state) : environ -> mpred :=
  PROPx (sl_props X s)
   (LOCALx (temp _min (Vint (Int.repr (Z.shiftl 1 (s_curr s)))) ::
            sl_locs X (s_huff s) (s_sym s) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s))
    (SEPx (sl_sep X (here_ X) (s_cnt s) (sl_t1 X s)))).

(* After sl_huff: huff is incremented, sym++. *)
Definition SL_huff (X: itctx) (s: state) : environ -> mpred :=
  PROPx (sl_props X s)
   (LOCALx (temp _min (Vint (Int.repr (Z.shiftl 1 (s_curr s)))) ::
            sl_locs X (st_huff' s) (s_sym s + 1) (s_len s) (s_curr s) (s_drop s) (s_low s) (s_used s) (s_next s))
    (SEPx (sl_sep X (here_ X) (s_cnt s) (sl_t1 X s)))).

(* After sl_cnt (no break): count[len] decremented, len the next symbol's length. *)
Definition SL_cnt (X: itctx) (s: state) : environ -> mpred :=
  PROPx ((~ (st_c s = 0 /\ s_len s = it_mx X)) :: sl_props X s)
   (LOCALx (temp _min (Vint (Int.repr (Z.shiftl 1 (s_curr s)))) ::
            sl_locs X (st_huff' s) (s_sym s + 1) (st_len' (c_lens X) s) (s_curr s) (s_drop s) (s_low s)
                    (s_used s) (s_next s))
    (SEPx (sl_sep X (here_ X) (st_cnt' s) (sl_t1 X s)))).

(* The loop's ret_assert (semax_loop with invariant EX s, A_loop X s; break: EX s, A_brk X s;
   return: the function's postcondition). *)
Definition sl_R (X: itctx) : ret_assert :=
  loop1_ret_assert (EX s: state, A_loop X s)%argsassert
                   (overridePost (EX s: state, A_brk X s)%argsassert (POST_it X)).

(* ---------------------------------------------------------------------------------------------- *)
(* The triples of the parts. *)

Definition sl_here_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (A_loop X s) sl_here (overridePost (SL_here X s) (sl_R X)).

Definition sl_rep_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (SL_here X s) sl_rep (overridePost (SL_rep X s) (sl_R X)).

Definition sl_huff_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (SL_rep X s) sl_huff (overridePost (SL_huff X s) (sl_R X)).

(* break: A_brk X (sl_brk X s) is the break post (RA_break (sl_R X) = EX s, A_brk X s). *)
Definition sl_cnt_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (SL_huff X s) sl_cnt (overridePost (SL_cnt X s) (sl_R X)).

(* normal: the next state (step = Continue s'); return 1 (step = Full _): POST_it X. *)
Definition sl_sub_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (SL_cnt X s) sl_sub (overridePost (EX s': state, A_loop X s')%argsassert (sl_R X)).

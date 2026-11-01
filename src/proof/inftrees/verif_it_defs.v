(* The body proof of inflate_table, cut into segments: the statements of the segments (consecutive
   top-level statements of f_inflate_table's body, left-nested), the assertions between them, and
   the Hoare triple of each segment (a Prop; proved in part_seg_<segment>.v, assembled by
   body_from_segs in verif_inflate_table.v).

   Program points (the A_ assertions), all with the locals of the parameters (params_locs) and the separation
   facts of it_sep (offs, count, here, static tables, lens, work, table, *table, *bits):
     A_start   function entry (count, offs, here, work uninitialised)
     A_max     after the counting loops, `root = *bits`, the max loop, `if (root > max) root = max`
     A_max1    after `if (max == 0) {... return 0;}`: max >= 1
     A_acc     after the min loop, `if (root < min) root = min`, the left loop and the incomplete test
     A_sorted  after the offs and sort loops: work = sorted symbols
     A_loop s  top of for(;;) in model state s (reached from init_state by `reach`)
     A_brk s   after the loop (break) in the model's Break state s
   Returns (-1, 1, 0 for max == 0) go to POST_it, the function's postcondition. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Export Zlib.proof.inftrees.spec.
Require Export Zlib.proof.inftrees.model_inv.

#[local] Existing Instance Inftrees.CS.

(* The parameters of the spec (WITH) and the addresses of the three addressable locals. *)
Record itctx := mkCtx {
  c_type: Z; c_lens: list Z; c_req: Z; c_old: list entry; c_gv: globals;
  c_shg: share; c_shl: share; c_sh: share;
  c_pl: val; c_pw: val; c_ptab: val; c_pt: val; c_pb: val;
  c_here: val; c_count: val; c_offs: val }.

(* The PROP part of the precondition. *)
Definition it_wf (X: itctx) : Prop :=
  readable_share (c_shg X) /\ readable_share (c_shl X) /\ writable_share (c_sh X) /\
  inputs_ok (c_type X) (c_lens X) (c_req X) /\ Forall entry_ok (c_old X) /\
  cap_ok (c_type X) (c_lens X) (c_req X) (Zlength (c_old X)).

Definition Delta_it : tycontext := func_tycontext f_inflate_table Vprog nil nil.

Definition it_model (X: itctx) : result :=
  inflate_table_model (c_type X) (c_lens X) (c_req X) (c_old X).

(* The function's postcondition (as start_function leaves it). *)
Definition POST_it (X: itctx) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
      (PROP ()
       RETURN (Vint (Int.repr (it_ret (it_model X))))
       SEP (itables (c_shg X) (c_gv X);
            data_at (c_shl X) (tarray tushort (Zlength (c_lens X))) (zs_rep (c_lens X)) (c_pl X);
            data_at_ (c_sh X) (tarray tushort (Zlength (c_lens X))) (c_pw X);
            data_at (c_sh X) (tarray code_t (Zlength (c_old X)))
                    (map entry_rep (it_tab (c_old X) (it_model X))) (c_pt X);
            data_at (c_sh X) (tptr code_t) (offset_val (4 * it_adv (it_model X)) (c_pt X)) (c_ptab X);
            data_at (c_sh X) tuint (Vint (Int.repr (it_bits (c_req X) (it_model X)))) (c_pb X))))
    (stackframe_of f_inflate_table).

(* The locals that never change: the three addressable locals, the globals, the parameters. *)
Definition params_locs (X: itctx) : list localdef :=
  [lvar _offs (tarray tushort 16) (c_offs X);
   lvar _count (tarray tushort 16) (c_count X);
   lvar _here (Tstruct ___gp_code noattr) (c_here X);
   gvars (c_gv X);
   temp _type (Vint (Int.repr (c_type X)));
   temp _lens (c_pl X);
   temp _codes (Vint (Int.repr (Zlength (c_lens X))));
   temp _table (c_ptab X);
   temp _bits (c_pb X);
   temp _work (c_pw X)].

(* The memory between two segments: offs and here hold anything, count is `cnt`, work is `work`,
   the table holds `tab`, *table and *bits are unchanged. *)
Definition it_sep (X: itctx) (cnt work: mpred) (tab: list entry) : list mpred :=
  [data_at_ Tsh (tarray tushort 16) (c_offs X);
   cnt;
   data_at_ Tsh (Tstruct ___gp_code noattr) (c_here X);
   itables (c_shg X) (c_gv X);
   data_at (c_shl X) (tarray tushort (Zlength (c_lens X))) (zs_rep (c_lens X)) (c_pl X);
   work;
   data_at (c_sh X) (tarray code_t (Zlength (c_old X))) (map entry_rep tab) (c_pt X);
   data_at (c_sh X) (tptr code_t) (c_pt X) (c_ptab X);
   data_at (c_sh X) tuint (Vint (Int.repr (c_req X))) (c_pb X)].

Definition count_at (X: itctx) (cnt: list Z) : mpred :=
  data_at Tsh (tarray tushort 16) (zs_rep cnt) (c_count X).
Definition count_ (X: itctx) : mpred := data_at_ Tsh (tarray tushort 16) (c_count X).
Definition work_ (X: itctx) : mpred :=
  data_at_ (c_sh X) (tarray tushort (Zlength (c_lens X))) (c_pw X).
(* work[0..n) = the sorted symbols, the rest uninitialised. *)
Definition work_sorted (X: itctx) : mpred :=
  data_at (c_sh X) (tarray tushort (Zlength (c_lens X)))
          (zs_rep (sorted_syms (c_lens X)) ++
           Zrepeat Vundef (Zlength (c_lens X) - Zlength (sorted_syms (c_lens X)))) (c_pw X).

Definition it_mx (X: itctx) : Z := maxlen (c_lens X).
Definition it_root (X: itctx) : Z := root_of (c_req X) (c_lens X).

(* base, extra (NULL for CODES) and match after the switch. *)
Definition base_v (X: itctx) : val :=
  if c_type X =? LENS then c_gv X _lbase else if c_type X =? DISTS then c_gv X _dbase else nullval.
Definition extra_v (X: itctx) : val :=
  if c_type X =? LENS then c_gv X _lext else if c_type X =? DISTS then c_gv X _dext else nullval.

Definition A_start (X: itctx) : environ -> mpred :=
  PROPx [] (LOCALx (params_locs X)
    (SEPx (it_sep X (count_ X) (work_ X) (c_old X)))).

Definition A_max (X: itctx) : environ -> mpred :=
  PROPx [] (LOCALx (temp _max (Vint (Int.repr (it_mx X))) ::
                    temp _root (Vint (Int.repr (Z.min (c_req X) (it_mx X)))) ::
                    temp _base nullval :: temp _extra nullval ::
                    temp _match (Vint (Int.repr 0)) :: params_locs X)
    (SEPx (it_sep X (count_at X (counts (c_lens X))) (work_ X) (c_old X)))).

Definition A_max1 (X: itctx) : environ -> mpred :=
  PROPx [1 <= it_mx X] (LOCALx (temp _max (Vint (Int.repr (it_mx X))) ::
                    temp _root (Vint (Int.repr (Z.min (c_req X) (it_mx X)))) ::
                    temp _base nullval :: temp _extra nullval ::
                    temp _match (Vint (Int.repr 0)) :: params_locs X)
    (SEPx (it_sep X (count_at X (counts (c_lens X))) (work_ X) (c_old X)))).

Definition A_acc (X: itctx) : environ -> mpred :=
  PROPx [1 <= it_mx X; acc_test (c_type X) (c_lens X)]
   (LOCALx (temp _min (Vint (Int.repr (minlen (c_lens X)))) ::
            temp _max (Vint (Int.repr (it_mx X))) ::
            temp _root (Vint (Int.repr (it_root X))) ::
            temp _base nullval :: temp _extra nullval ::
            temp _match (Vint (Int.repr 0)) :: params_locs X)
    (SEPx (it_sep X (count_at X (counts (c_lens X))) (work_ X) (c_old X)))).

Definition A_sorted (X: itctx) : environ -> mpred :=
  PROPx [1 <= it_mx X; acc_test (c_type X) (c_lens X)]
   (LOCALx (temp _min (Vint (Int.repr (minlen (c_lens X)))) ::
            temp _max (Vint (Int.repr (it_mx X))) ::
            temp _root (Vint (Int.repr (it_root X))) ::
            temp _base nullval :: temp _extra nullval ::
            temp _match (Vint (Int.repr 0)) :: params_locs X)
    (SEPx (it_sep X (count_at X (counts (c_lens X))) (work_sorted X) (c_old X)))).

(* The loop invariant: the C variables are those of the model state s, reached after s_sym s
   iterations; count = s_cnt s, the table = s_tab s. *)
Definition A_loop (X: itctx) (s: state) : environ -> mpred :=
  PROPx [1 <= it_mx X; acc_test (c_type X) (c_lens X);
         over (c_type X) (Z.shiftl 1 (it_root X)) = false;
         reach (c_type X) (c_lens X) (c_req X) (c_old X) (Z.to_nat (s_sym s)) s]
   (LOCALx (temp _huff (Vint (Int.repr (s_huff s))) ::
            temp _sym (Vint (Int.repr (s_sym s))) ::
            temp _len (Vint (Int.repr (s_len s))) ::
            temp _curr (Vint (Int.repr (s_curr s))) ::
            temp _drop (Vint (Int.repr (s_drop s))) ::
            temp _low (Vint (Int.repr (s_low s))) ::
            temp _used (Vint (Int.repr (s_used s))) ::
            temp _next (offset_val (4 * s_next s) (c_pt X)) ::
            temp _root (Vint (Int.repr (it_root X))) ::
            temp _max (Vint (Int.repr (it_mx X))) ::
            temp _mask (Vint (Int.repr (Z.shiftl 1 (it_root X) - 1))) ::
            temp _match (Vint (Int.repr (match_of (c_type X)))) ::
            temp _base (base_v X) :: temp _extra (extra_v X) :: params_locs X)
    (SEPx (it_sep X (count_at X (s_cnt s)) (work_sorted X) (s_tab s)))).

(* After the loop: s is the model's Break state, the loop's result. *)
Definition A_brk (X: itctx) (s: state) : environ -> mpred :=
  PROPx [1 <= it_mx X; acc_test (c_type X) (c_lens X);
         over (c_type X) (Z.shiftl 1 (it_root X)) = false;
         run (c_type X) (c_lens X) (sorted_syms (c_lens X)) (it_root X) (it_mx X)
             (length (sorted_syms (c_lens X))) (init_state (c_lens X) (it_root X) (c_old X))
           = Break s]
   (LOCALx (temp _huff (Vint (Int.repr (s_huff s))) ::
            temp _len (Vint (Int.repr (s_len s))) ::
            temp _drop (Vint (Int.repr (s_drop s))) ::
            temp _used (Vint (Int.repr (s_used s))) ::
            temp _next (offset_val (4 * s_next s) (c_pt X)) ::
            temp _root (Vint (Int.repr (it_root X))) :: params_locs X)
    (SEPx (it_sep X (count_at X (s_cnt s)) (work_sorted X) (s_tab s)))).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments: consecutive top-level statements of the body of f_inflate_table (left-nested).  *)

Definition seg_counts : statement :=
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Sset _base (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
(Sset _extra (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
(Sset _match (Econst_int (Int.repr 0) tint)))
(Ssequence
          (Sset _len (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _len tuint)
                             (Econst_int (Int.repr 15) tint) tint)
                Sskip
                Sbreak)
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _count (tarray tushort 16))
                    (Etempvar _len tuint) (tptr tushort)) tushort)
                (Econst_int (Int.repr 0) tint)))
            (Sset _len
              (Ebinop Oadd (Etempvar _len tuint)
                (Econst_int (Int.repr 1) tint) tuint)))))
(Ssequence
            (Sset _sym (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _sym tuint)
                               (Etempvar _codes tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'52
                    (Ederef
                      (Ebinop Oadd (Etempvar _lens (tptr tushort))
                        (Etempvar _sym tuint) (tptr tushort)) tushort))
                  (Ssequence
                    (Sset _t'53
                      (Ederef
                        (Ebinop Oadd (Etempvar _lens (tptr tushort))
                          (Etempvar _sym tuint) (tptr tushort)) tushort))
                    (Ssequence
                      (Sset _t'54
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _t'53 tushort) (tptr tushort)) tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _t'52 tushort) (tptr tushort)) tushort)
                        (Ebinop Oadd (Etempvar _t'54 tushort)
                          (Econst_int (Int.repr 1) tint) tint))))))
              (Sset _sym
                (Ebinop Oadd (Etempvar _sym tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))))
(Sset _root (Ederef (Etempvar _bits (tptr tuint)) tuint)))
(Ssequence
                (Sset _max (Econst_int (Int.repr 15) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _max tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'51
                        (Ederef
                          (Ebinop Oadd (Evar _count (tarray tushort 16))
                            (Etempvar _max tuint) (tptr tushort)) tushort))
                      (Sifthenelse (Ebinop Cop.One (Etempvar _t'51 tushort)
                                     (Econst_int (Int.repr 0) tint) tint)
                        Sbreak
                        Sskip)))
                  (Sset _max
                    (Ebinop Osub (Etempvar _max tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))))
(Sifthenelse (Ebinop Ogt (Etempvar _root tuint)
                               (Etempvar _max tuint) tint)
                  (Sset _root (Etempvar _max tuint))
                  Sskip)).

Definition seg_max0 : statement :=
(Sifthenelse (Ebinop Oeq (Etempvar _max tuint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield (Evar _here (Tstruct ___gp_code noattr)) _op
                          tuchar)
                        (Ecast (Econst_int (Int.repr 64) tint) tuchar))
                      (Ssequence
                        (Sassign
                          (Efield (Evar _here (Tstruct ___gp_code noattr))
                            _bits tuchar)
                          (Ecast (Econst_int (Int.repr 1) tint) tuchar))
                        (Ssequence
                          (Sassign
                            (Efield (Evar _here (Tstruct ___gp_code noattr))
                              _val tushort)
                            (Ecast (Econst_int (Int.repr 0) tint) tushort))
                          (Ssequence
                            (Ssequence
                              (Sset _t'49
                                (Ederef
                                  (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                  (tptr (Tstruct ___gp_code noattr))))
                              (Ssequence
                                (Sset _t'50
                                  (Efield
                                    (Evar _here (Tstruct ___gp_code noattr))
                                    _op tuchar))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'49 (tptr (Tstruct ___gp_code noattr)))
                                      (Tstruct ___gp_code noattr)) _op
                                    tuchar) (Etempvar _t'50 tuchar))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'47
                                  (Ederef
                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                    (tptr (Tstruct ___gp_code noattr))))
                                (Ssequence
                                  (Sset _t'48
                                    (Efield
                                      (Evar _here (Tstruct ___gp_code noattr))
                                      _bits tuchar))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'47 (tptr (Tstruct ___gp_code noattr)))
                                        (Tstruct ___gp_code noattr)) _bits
                                      tuchar) (Etempvar _t'48 tuchar))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'45
                                    (Ederef
                                      (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                      (tptr (Tstruct ___gp_code noattr))))
                                  (Ssequence
                                    (Sset _t'46
                                      (Efield
                                        (Evar _here (Tstruct ___gp_code noattr))
                                        _val tushort))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'45 (tptr (Tstruct ___gp_code noattr)))
                                          (Tstruct ___gp_code noattr)) _val
                                        tushort) (Etempvar _t'46 tushort))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'44
                                      (Ederef
                                        (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                        (tptr (Tstruct ___gp_code noattr))))
                                    (Sassign
                                      (Ederef
                                        (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                        (tptr (Tstruct ___gp_code noattr)))
                                      (Ebinop Oadd
                                        (Etempvar _t'44 (tptr (Tstruct ___gp_code noattr)))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (Tstruct ___gp_code noattr)))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'42
                                        (Ederef
                                          (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                          (tptr (Tstruct ___gp_code noattr))))
                                      (Ssequence
                                        (Sset _t'43
                                          (Efield
                                            (Evar _here (Tstruct ___gp_code noattr))
                                            _op tuchar))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'42 (tptr (Tstruct ___gp_code noattr)))
                                              (Tstruct ___gp_code noattr))
                                            _op tuchar)
                                          (Etempvar _t'43 tuchar))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'40
                                          (Ederef
                                            (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                            (tptr (Tstruct ___gp_code noattr))))
                                        (Ssequence
                                          (Sset _t'41
                                            (Efield
                                              (Evar _here (Tstruct ___gp_code noattr))
                                              _bits tuchar))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _t'40 (tptr (Tstruct ___gp_code noattr)))
                                                (Tstruct ___gp_code noattr))
                                              _bits tuchar)
                                            (Etempvar _t'41 tuchar))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'38
                                            (Ederef
                                              (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                              (tptr (Tstruct ___gp_code noattr))))
                                          (Ssequence
                                            (Sset _t'39
                                              (Efield
                                                (Evar _here (Tstruct ___gp_code noattr))
                                                _val tushort))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'38 (tptr (Tstruct ___gp_code noattr)))
                                                  (Tstruct ___gp_code noattr))
                                                _val tushort)
                                              (Etempvar _t'39 tushort))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'37
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr))))
                                            (Sassign
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr)))
                                              (Ebinop Oadd
                                                (Etempvar _t'37 (tptr (Tstruct ___gp_code noattr)))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr (Tstruct ___gp_code noattr)))))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Etempvar _bits (tptr tuint))
                                                tuint)
                                              (Econst_int (Int.repr 1) tint))
                                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))
                    Sskip).

Definition seg_check : statement :=
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
                      (Sset _min (Econst_int (Int.repr 1) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _min tuint)
                                         (Etempvar _max tuint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _t'36
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _count (tarray tushort 16))
                                  (Etempvar _min tuint) (tptr tushort))
                                tushort))
                            (Sifthenelse (Ebinop Cop.One (Etempvar _t'36 tushort)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              Sbreak
                              Sskip)))
                        (Sset _min
                          (Ebinop Oadd (Etempvar _min tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
(Sifthenelse (Ebinop Olt (Etempvar _root tuint)
                                     (Etempvar _min tuint) tint)
                        (Sset _root (Etempvar _min tuint))
                        Sskip))
(Sset _left (Econst_int (Int.repr 1) tint)))
(Ssequence
                            (Sset _len (Econst_int (Int.repr 1) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Ole
                                               (Etempvar _len tuint)
                                               (Econst_int (Int.repr 15) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _left
                                    (Ebinop Oshl (Etempvar _left tint)
                                      (Econst_int (Int.repr 1) tint) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'35
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _count (tarray tushort 16))
                                            (Etempvar _len tuint)
                                            (tptr tushort)) tushort))
                                      (Sset _left
                                        (Ebinop Osub (Etempvar _left tint)
                                          (Etempvar _t'35 tushort) tint)))
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _left tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sreturn (Some (Eunop Oneg
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)))
                                      Sskip))))
                              (Sset _len
                                (Ebinop Oadd (Etempvar _len tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)))))
(Ssequence
                              (Sifthenelse (Ebinop Ogt (Etempvar _left tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _type tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Sset _t'1
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Sset _t'1
                                      (Ecast
                                        (Ebinop Cop.One (Etempvar _max tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tbool))
                                    (Sset _t'1
                                      (Ecast (Etempvar _t'1 tint) tbool))))
                                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'1 tint)
                                (Sreturn (Some (Eunop Oneg
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)))
                                Sskip))).

Definition seg_sort : statement :=
(Ssequence
(Ssequence
(Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _offs (tarray tushort 16))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tushort)) tushort)
                                (Econst_int (Int.repr 0) tint))
(Ssequence
                                  (Sset _len (Econst_int (Int.repr 1) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _len tuint)
                                                     (Econst_int (Int.repr 15) tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _t'33
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _offs (tarray tushort 16))
                                              (Etempvar _len tuint)
                                              (tptr tushort)) tushort))
                                        (Ssequence
                                          (Sset _t'34
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _count (tarray tushort 16))
                                                (Etempvar _len tuint)
                                                (tptr tushort)) tushort))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _offs (tarray tushort 16))
                                                (Ebinop Oadd
                                                  (Etempvar _len tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint) (tptr tushort))
                                              tushort)
                                            (Ebinop Oadd
                                              (Etempvar _t'33 tushort)
                                              (Etempvar _t'34 tushort) tint)))))
                                    (Sset _len
                                      (Ebinop Oadd (Etempvar _len tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))))
(Ssequence
                                    (Sset _sym
                                      (Econst_int (Int.repr 0) tint))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _sym tuint)
                                                       (Etempvar _codes tuint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _t'30
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _lens (tptr tushort))
                                                (Etempvar _sym tuint)
                                                (tptr tushort)) tushort))
                                          (Sifthenelse (Ebinop Cop.One
                                                         (Etempvar _t'30 tushort)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'32
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _lens (tptr tushort))
                                                        (Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Sset _t'2
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _offs (tarray tushort 16))
                                                        (Etempvar _t'32 tushort)
                                                        (tptr tushort))
                                                      tushort)))
                                                (Ssequence
                                                  (Sset _t'31
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _lens (tptr tushort))
                                                        (Etempvar _sym tuint)
                                                        (tptr tushort))
                                                      tushort))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _offs (tarray tushort 16))
                                                        (Etempvar _t'31 tushort)
                                                        (tptr tushort))
                                                      tushort)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'2 tushort)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint))))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _work (tptr tushort))
                                                    (Etempvar _t'2 tushort)
                                                    (tptr tushort)) tushort)
                                                (Ecast (Etempvar _sym tuint)
                                                  tushort)))
                                            Sskip)))
                                      (Sset _sym
                                        (Ebinop Oadd (Etempvar _sym tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint))))).

Definition seg_init : statement :=
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Ssequence
(Sswitch (Etempvar _type tint)
                                      (LScons (Some 0)
                                        (Ssequence
                                          (Sset _match
                                            (Econst_int (Int.repr 20) tint))
                                          Sbreak)
                                        (LScons (Some 1)
                                          (Ssequence
                                            (Sset _base
                                              (Evar _lbase (tarray tushort 31)))
                                            (Ssequence
                                              (Sset _extra
                                                (Evar _lext (tarray tushort 31)))
                                              (Ssequence
                                                (Sset _match
                                                  (Econst_int (Int.repr 257) tint))
                                                Sbreak)))
                                          (LScons (Some 2)
                                            (Ssequence
                                              (Sset _base
                                                (Evar _dbase (tarray tushort 32)))
                                              (Ssequence
                                                (Sset _extra
                                                  (Evar _dext (tarray tushort 32)))
                                                Sbreak))
                                            LSnil))))
(Sset _huff
                                        (Econst_int (Int.repr 0) tint)))
(Sset _sym
                                          (Econst_int (Int.repr 0) tint)))
(Sset _len (Etempvar _min tuint)))
(Sset _next
                                              (Ederef
                                                (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                (tptr (Tstruct ___gp_code noattr)))))
(Sset _curr
                                                (Etempvar _root tuint)))
(Sset _drop
                                                  (Econst_int (Int.repr 0) tint)))
(Sset _low
                                                    (Ecast
                                                      (Eunop Oneg
                                                        (Econst_int (Int.repr 1) tint)
                                                        tint) tuint)))
(Sset _used
                                                      (Ebinop Oshl
                                                        (Econst_int (Int.repr 1) tuint)
                                                        (Etempvar _root tuint)
                                                        tuint)))
(Sset _mask
                                                        (Ebinop Osub
                                                          (Etempvar _used tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint)))
(Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _type tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 852) tint)
                                                                    tint)
                                                                  tbool))
                                                              (Sset _t'3
                                                                (Econst_int (Int.repr 0) tint)))
                                                            (Sifthenelse (Etempvar _t'3 tint)
                                                              (Sset _t'4
                                                                (Econst_int (Int.repr 1) tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _type tint)
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 592) tint)
                                                                    tint)
                                                                    tbool))
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Etempvar _t'4 tint)
                                                                    tbool)))
                                                                (Sset _t'4
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tbool)))))
                                                          (Sifthenelse (Etempvar _t'4 tint)
                                                            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                            Sskip))).

Definition seg_loop : statement :=
(Sloop
                                                            (Ssequence
                                                              Sskip
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                  (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'23
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'23 tushort)
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    tuint)
                                                                    (Etempvar _match tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'29 tushort))))
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _t'24 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _extra (tptr tushort))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'27 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _t'28 tushort)
                                                                    tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _base (tptr tushort))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'25 tushort)
                                                                    (Etempvar _match tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'26 tushort)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Econst_int (Int.repr 0) tint)))))))
                                                                  (Ssequence
                                                                    (Sset _incr
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _fill
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _curr tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _min
                                                                    (Etempvar _fill tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _fill
                                                                    (Ebinop Osub
                                                                    (Etempvar _fill tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'22 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'21 tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oshr
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _fill tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'20 tushort))))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Cop.One
                                                                    (Etempvar _fill tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sset _incr
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint)
                                                                    (Sset _incr
                                                                    (Ebinop Oshr
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Cop.One
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _huff
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _incr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _huff
                                                                    (Ebinop Oadd
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _incr tuint)
                                                                    tuint)))
                                                                    (Sset _huff
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Ssequence
                                                                    (Sset _sym
                                                                    (Ebinop Oadd
                                                                    (Etempvar _sym tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _t'5
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'19 tushort)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tushort)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Etempvar _t'5 tushort)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'5 tushort)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _max tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _t'18
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _work (tptr tushort))
                                                                    (Etempvar _sym tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _len
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _lens (tptr tushort))
                                                                    (Etempvar _t'18 tushort)
                                                                    (tptr tushort))
                                                                    tushort))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _root tuint)
                                                                    tint)
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop Cop.One
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint)
                                                                    (Etempvar _low tuint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'8
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'8 tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _drop tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _drop
                                                                    (Etempvar _root tuint))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _min tuint)
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _curr
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ecast
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Etempvar _curr tuint)
                                                                    tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Olt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (Etempvar _max tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _count (tarray tushort 16))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tint)
                                                                    (Etempvar _t'17 tushort)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Etempvar _left tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _curr
                                                                    (Ebinop Oadd
                                                                    (Etempvar _curr tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Sset _left
                                                                    (Ebinop Oshl
                                                                    (Etempvar _left tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))))
                                                                    (Ssequence
                                                                    (Sset _used
                                                                    (Ebinop Oadd
                                                                    (Etempvar _used tuint)
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _curr tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'6
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 852) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'6
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'6 tint)
                                                                    (Sset _t'7
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _type tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _used tuint)
                                                                    (Econst_int (Int.repr 592) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Etempvar _t'7 tint)
                                                                    tbool)))
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'7 tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sset _low
                                                                    (Ebinop Oand
                                                                    (Etempvar _huff tuint)
                                                                    (Etempvar _mask tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'16 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _curr tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'15 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _root tuint)
                                                                    tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'13 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _low tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _t'14 (tptr (Tstruct ___gp_code noattr)))
                                                                    tlong)
                                                                    tushort))))))))))))))
                                                                    Sskip))))))))))))))
                                                            Sskip).

Definition seg_fin : statement :=
(Ssequence
(Ssequence
(Ssequence
(Sifthenelse 
                                                              (Ebinop Cop.One
                                                                (Etempvar _huff tuint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _drop tuint)
                                                                    tuint)
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'12 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'11
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'11 tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'10
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _huff tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'10 tushort))))))))
                                                              Sskip)
(Ssequence
                                                                (Sset _t'9
                                                                  (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Etempvar _table (tptr (tptr (Tstruct ___gp_code noattr))))
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'9 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _used tuint)
                                                                    (tptr (Tstruct ___gp_code noattr))))))
(Sassign
                                                                  (Ederef
                                                                    (Etempvar _bits (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _root tuint)))
(Sreturn (Some (Econst_int (Int.repr 0) tint)))).

(* ---------------------------------------------------------------------------------------------- *)
(* The Hoare triples of the segments. *)

Definition seg_counts_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_start X) seg_counts (overridePost (A_max X) (POST_it X)).

Definition seg_max0_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_max X) seg_max0 (overridePost (A_max1 X) (POST_it X)).

Definition seg_check_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_max1 X) seg_check (overridePost (A_acc X) (POST_it X)).

Definition seg_sort_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_acc X) seg_sort (overridePost (A_sorted X) (POST_it X)).

Definition seg_init_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_sorted X) seg_init
    (overridePost (A_loop X (init_state (c_lens X) (it_root X) (c_old X))) (POST_it X)).

Definition seg_loop_stmt : Prop := forall {Espec: OracleKind} (X: itctx), it_wf X ->
  semax Delta_it (A_loop X (init_state (c_lens X) (it_root X) (c_old X))) seg_loop
    (overridePost (EX s: state, A_brk X s) (POST_it X)).

Definition seg_fin_stmt : Prop := forall {Espec: OracleKind} (X: itctx) (s: state), it_wf X ->
  semax Delta_it (A_brk X s) seg_fin (POST_it X).

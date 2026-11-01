(* THE specification of inflate_table (zlib 1.3.2 inftrees.c), shared by every law, and the
   (False-precondition) specification of inflate_fixed, which no harness calls.

   Stated in the compspecs of the inftrees unit (Zlib.units.Inftrees.CS); a harness proof in
   its own compspecs calls it through VST's change_compspecs cancel hints (field_at.v), as the
   struct `code` (___gp_code) is the same in every unit.

   PRE: the inputs of model.v's inputs_ok (type 0..2, at most max_codes symbols, lengths 0..15, any
   32-bit requested root), the table region of cap = Zlength old entries holding any (defined)
   entries, with cap_ok (LENS >= 852, DISTS >= 592, CODES: A5 and >= 2^max, >= 2), work uninitialised.
   POST: exactly what the model says: the result, the table contents, *table advanced by `used` on 0,
   *bits the root on 0; lens and the static tables unchanged; work holds anything. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Export Zlib.proof.inftrees.model.

#[local] Existing Instance Inftrees.CS.

Definition code_t : type := Tstruct ___gp_code noattr.

Definition entry_rep (e: entry) : reptype code_t :=
  (Vint (Int.repr (e_op e)), (Vint (Int.repr (e_bits e)), Vint (Int.repr (e_val e)))).

Definition zs_rep (l: list Z) : list val := map (fun x => Vint (Int.repr x)) l.

(* The static constant tables of inflate_table (read for LENS and DISTS). *)
Definition itables (sh: share) (gv: globals) : mpred :=
  (data_at sh (tarray tushort 31) (zs_rep lbase) (gv _lbase) *
  data_at sh (tarray tushort 31) (zs_rep lext) (gv _lext) *
  data_at sh (tarray tushort 32) (zs_rep dbase) (gv _dbase) *
  data_at sh (tarray tushort 32) (zs_rep dext) (gv _dext))%logic.

Definition inflate_table_spec :=
 DECLARE _inflate_table
 WITH type: Z, lens: list Z, req: Z, old: list entry, gv: globals,
      shg: share, shl: share, sh: share, pl: val, pw: val, ptab: val, pt: val, pb: val
 PRE [ tint, tptr tushort, tuint, tptr (tptr code_t), tptr tuint, tptr tushort ]
   PROP (readable_share shg; readable_share shl; writable_share sh;
         inputs_ok type lens req; Forall entry_ok old; cap_ok type lens req (Zlength old))
   PARAMS (Vint (Int.repr type); pl; Vint (Int.repr (Zlength lens)); ptab; pb; pw)
   GLOBALS (gv)
   SEP (itables shg gv;
        data_at shl (tarray tushort (Zlength lens)) (zs_rep lens) pl;
        data_at_ sh (tarray tushort (Zlength lens)) pw;
        data_at sh (tarray code_t (Zlength old)) (map entry_rep old) pt;
        data_at sh (tptr code_t) pt ptab;
        data_at sh tuint (Vint (Int.repr req)) pb)
 POST [ tint ]
   PROP ()
   RETURN (Vint (Int.repr (it_ret (inflate_table_model type lens req old))))
   SEP (itables shg gv;
        data_at shl (tarray tushort (Zlength lens)) (zs_rep lens) pl;
        data_at_ sh (tarray tushort (Zlength lens)) pw;
        data_at sh (tarray code_t (Zlength old))
                (map entry_rep (it_tab old (inflate_table_model type lens req old))) pt;
        data_at sh (tptr code_t) (offset_val (4 * it_adv (inflate_table_model type lens req old)) pt) ptab;
        data_at sh tuint (Vint (Int.repr (it_bits req (inflate_table_model type lens req old)))) pb).

(* inflate_fixed: never called by any harness. *)
Definition inflate_fixed_spec :=
 DECLARE _inflate_fixed
 WITH p: val
 PRE [ tptr (Tstruct _inflate_state noattr) ]
   PROP (False) PARAMS (p) SEP ()
 POST [ tvoid ]
   PROP () RETURN () SEP ().

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog : funspecs := [inflate_table_spec; inflate_fixed_spec].

(* The body obligations of the unit (proved in verif_inflate_table.v). *)
Definition body_inflate_table_stmt : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog Gprog f_inflate_table inflate_table_spec.
Definition body_inflate_fixed_stmt : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog Gprog f_inflate_fixed inflate_fixed_spec.

(* No struct-copy rule is needed: VST 2.15's floyd logic has none (`mapsto` of a struct type is FF; the
   deep semax's only Sassign rule needs a By_value or numeric type), so the code under test copies the
   local `here` into the table member by member (DEVIATIONS.md, edit 3).  Every table write is a plain
   uchar/ushort field store that `forward` handles. *)

Lemma body_inflate_fixed : body_inflate_fixed_stmt.
Proof. unfold body_inflate_fixed_stmt. intros Es. start_function. contradiction. Qed.

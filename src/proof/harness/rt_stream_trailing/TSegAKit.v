(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's setup segment (TMainKit.segA_t, proved in TSegA.v,
   TSegANull.v, TSegAInit.v and TSegAStores.v).  Statements 0-20 of this main are rt_stream's (the same temporaries)
   except for the ZLIB_VERSION literal, so the objects, the NULL tests' tactics and the compspecs conversions are
   rt_stream's (rt_stream/USegAKit.v, reused); this file holds what depends on this program: the version literal,
   and the statements and states at which the proof of segA_t is cut. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.harness.rt_stream_trailing.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac st_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in st_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := st_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* this harness's ZLIB_VERSION literal as deflateInit2_'s version argument *)
Lemma st_version_cs gv :
  hversion_at_t gv =
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0]))
    (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_stream_trailing_1).
Proof.
  unfold hversion_at_t. change (Zlength [49; 46; 51; 46; 50; 0]) with 6. symmetry.
  apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

(** ** The cut points of segA_t *)

(* segA_t from its thirteenth statement on (the NULL tests of expected, compressed and out, then new_stream,
   deflateInit2_, its return code's tests and the stores), from its fourteenth on (new_stream onwards) and from its
   eighteenth on (the four stores) *)
Definition segA_tests_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA_t] in (suf 12 segA_t) in exact x).
Definition segA_init_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA_t] in (suf 13 segA_t) in exact x).
Definition segA_stores_t : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA_t] in (suf 17 segA_t) in exact x).

(* the state before the NULL test of out: the draws are done, data, expected (its copy) and compressed are
   objects, out (op) is what malloc returned *)
Definition PRE_tests_t (gv : globals) (vc vd va : val) (lv wv mv sv : Z) (data : list Z) (cap : Z) (bd : block)
    (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (op : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out op; temp _compressed (Vptr bc oc); temp _expected (Vptr be oe); temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (Vint (Int.repr sv)); temp _mem_level (Vint (Int.repr mv));
         temp _window_bits (Vint (Int.repr wv)); temp _level (Vint (Int.repr lv));
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec op nullval then emp
       else malloc_token Ews (tarray tuchar (Zlength data)) op * data_at_ Ews (tarray tuchar (Zlength data)) op;
       sa_buf cap (Vptr bc oc); sa_dobj (Vptr be oe) data; sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd;
       data_at_ Tsh t_z vc; Rm_t gv; data_at_ Tsh t_p va).

(* the state after the NULL tests, none of the three pointers NULL *)
Definition PRE_init_t (gv : globals) (vc vd va : val) (lv wv mv sv : Z) (data : list Z) (cap : Z) (bd : block)
    (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (bout : block) (oout : ptrofs)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'13 (Vint Int.zero); temp _t'12 (Vint Int.zero);
         temp _out (Vptr bout oout); temp _compressed (Vptr bc oc); temp _expected (Vptr be oe);
         temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (Vint (Int.repr sv)); temp _mem_level (Vint (Int.repr mv));
         temp _window_bits (Vint (Int.repr wv)); temp _level (Vint (Int.repr lv));
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (mem_mgr gv; sa_buf (Zlength data) (Vptr bout oout); sa_buf cap (Vptr bc oc); sa_dobj (Vptr be oe) data;
       sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd; data_at_ Tsh t_z vc; Rm_t gv;
       data_at_ Tsh t_p va).

(* the state after deflateInit2_ returned Z_OK with the state s and the stream fields z' *)
Definition PRE_stores_t (gv : globals) (vc vd va : val) (lvl wb mem str : Z) (data : list Z) (cap : Z)
    (bd : block) (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (bout : block)
    (oout : ptrofs) (s : dstate) (z' : strm) (msgv' : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out (Vptr bout oout); temp _compressed (Vptr bc oc); temp _expected (Vptr be oe);
         temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (vi str); temp _mem_level (vi mem); temp _window_bits (vi wb); temp _level (vi lvl);
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) nullval vc;
       reset_fields vc (rfv (Z_OK =? Z_OK) (z_total_in z') Vundef) (rfv (Z_OK =? Z_OK) (z_total_out z') Vundef)
         msgv' (rfv (Z_OK =? Z_OK) (z_adler z') Vundef);
       @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0]))
         (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_stream_trailing_1);
       mem_mgr gv; deflate_globals gv;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_in) (vi 0) vc;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) nullval vc;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_out) (vi 0) vc;
       BoundKit.strm_pad vc; sa_buf (Zlength data) (Vptr bout oout); sa_buf cap (Vptr bc oc);
       sa_dobj (Vptr be oe) data; sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd; data_at_ BoundKit.Ecomp t_z vc;
       Zlib.proof.inflate.Rep.tables_rep Ers gv; Zlib.proof.inflate_api.Spec5.version_lit gv; data_at_ Tsh t_p va).

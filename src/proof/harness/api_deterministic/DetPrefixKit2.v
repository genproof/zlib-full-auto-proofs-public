(* Law api_deterministic (data of any length): the cuts of main's body before its loop (DetKit2.det_prefix_stmt),
   so that the proof is split into parts that each check quickly.  As in DetKit2.v, each part is in
   continuation-passing style:
     det_prefix (DetPrefix2.v):      main_body (PRE0) -> msuf10 (the deflateInit2_ calls), P10
     det_init   (DetPrefixInit2.v):  msuf10 (P10)     -> msuf12 (the Z_MEM_ERROR test), P12
     det_codes  (DetPrefixCodes2.v): msuf12 (P12)     -> msuf14 (offered = 0), P14
     det_enter  (DetPrefixEnter2.v): msuf14 (P14)     -> msuf17 (the loop), DetKit2.J_at *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which can take minutes on main's
   LOCAL list; the same list is built syntactically by [rlt_list], comparing the identifiers by vm_compute *)
Ltac rlt_list i L :=
  lazymatch L with
  | temp ?j ?v :: ?L' =>
      let r := rlt_list i L' in
      let b := eval vm_compute in (Pos.eqb i j) in
      lazymatch b with true => r | false => constr:(temp j v :: r) end
  | ?d :: ?L' => let r := rlt_list i L' in constr:(d :: r)
  | nil => constr:(@nil localdef)
  end.
(* each part file sets [Local Ltac simplify_remove_localdef_temp ::=] to use it *)

(* main_body from deflateInit2_(&first, ...) on (statement 10), from the Z_MEM_ERROR test on (statement 12), and
   from offered = 0 on (statement 14) *)
Definition msuf10 : statement := ltac:(get_msuf 10%nat).
Definition msuf12 : statement := ltac:(get_msuf 12%nat).
Definition msuf14 : statement := ltac:(get_msuf 14%nat).

Section Cuts.
Context (v1 v2 : val) (gv : globals).
Context (level wbits mem strategy n : Z) (bs : list Z) (datap : val).

(* the parameters drawn (the signed values of the four u32), the data's length and bytes *)
Definition pre_ok : Prop :=
  Int.min_signed <= level <= Int.max_signed /\ Int.min_signed <= wbits <= Int.max_signed /\
  Int.min_signed <= mem <= Int.max_signed /\ Int.min_signed <= strategy <= Int.max_signed /\
  0 <= n <= 9223372036854775807 /\ Zlength bs = n /\ is_bytes bs /\ isptr datap.

Definition P_loc : list localdef :=
  [temp _data datap; temp _data_len (vl n); temp _strategy (vi strategy); temp _mem_level (vi mem);
   temp _window_bits (vi wbits); temp _level (vi level); lvar _first t_strm v1; lvar _second t_strm v2;
   gvars gv].

(* new_stream's postcondition: the Ews half of a local *)
Definition new_strm (p : val) : mpred :=
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nullval (vi 0) Vundef nullval (vi 0) Vundef Vundef Vundef nullval nullval nullval Vundef Vundef Vundef) p.

(* before the deflateInit2_ calls: both streams just made by new_stream; the parameters passed
   gp_assume(deflate_params_ok(...)): they are in zlib.h's ranges (laws_session/Facts.deflate_params_valid_ok) *)
Definition P10 : environ -> mpred :=
  PROPx [pre_ok; params_ok level 8 wbits mem strategy = true] (LOCALx P_loc (SEPx
    [new_strm v2; new_strm v1; mem_mgr gv; malloc_token Ews (tarray tuchar n) datap;
     data_at Ews (tarray tuchar n) (bytes_rep bs) datap;
     data_at_ BoundKit.Ecomp t_strm v1; data_at_ BoundKit.Ecomp t_strm v2;
     deflate_globals gv; version_at gv vlit])).

(* the state part of deflateInit2__spec_v9's postcondition at the stream [p], for the outcome [os], [code] *)
Definition init_res (p : val) (os : option dstate) (code : Z) : mpred :=
  match os with
  | Some _ => dstream 2 os p nullval gv
  | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
            !! (code = Z_VERSION_ERROR -> st = Vundef) &&
            (zfuncs gv * field_at_ Ews t_strm (DOT Zlib.deflate.code._reserved) p *
             field_at Ews t_strm (DOT Zlib.deflate.code._state) st p *
             field_at Ews t_strm (DOT Zlib.deflate.code._zalloc) za p *
             field_at Ews t_strm (DOT Zlib.deflate.code._zfree) zf p *
             field_at Ews t_strm (DOT Zlib.deflate.code._opaque) op' p *
             field_at Ews t_strm (DOT Zlib.deflate.code._data_type) dt' p)
  end.

Definition init_run (os : option dstate) (z : strm) (code : Z) : Prop :=
  exists a1 a2 a3 a4 a5,
    c_deflateInit2_ true true false level 8 wbits mem strategy a1 a2 a3 a4 a5 zrst0 = Some (os, z, code).

Definition init_msg (z : strm) (code : Z) (msgv : val) : Prop :=
  if code =? Z_VERSION_ERROR then msgv = Vundef else msg_ok (z_msg z) msgv.

(* after both deflateInit2_ calls: the outcomes [os], [z'], [code] (first) and [os2], [z2], [code2] (second) *)
Definition P12 (os : option dstate) (z' : strm) (code : Z) (msgv1 : val)
    (os2 : option dstate) (z2 : strm) (code2 : Z) (msgv2 : val) : environ -> mpred :=
  PROPx [pre_ok; params_ok level 8 wbits mem strategy = true; init_run os z' code; init_run os2 z2 code2;
         init_msg z' code msgv1; init_msg z2 code2 msgv2]
  (LOCALx (temp _code_second (vi code2) :: temp _code_first (vi code) :: P_loc) (SEPx
    [init_res v2 os2 code2; field_at Ews t_strm (DOT Zlib.deflate.code._next_in) nullval v2;
     reset_fields v2 (rfv (code2 =? Z_OK) (z_total_in z2) Vundef)
       (rfv (code2 =? Z_OK) (z_total_out z2) Vundef) msgv2 (rfv (code2 =? Z_OK) (z_adler z2) Vundef);
     version_at gv vlit; mem_mgr gv; deflate_globals gv;
     init_res v1 os code; field_at Ews t_strm (DOT Zlib.deflate.code._next_in) nullval v1;
     reset_fields v1 (rfv (code =? Z_OK) (z_total_in z') Vundef)
       (rfv (code =? Z_OK) (z_total_out z') Vundef) msgv1 (rfv (code =? Z_OK) (z_adler z') Vundef);
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._next_out) nullval v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) v2; BoundKit.strm_pad v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) v1;
     field_at Ews t_strm (DOT Zlib.deflate.code._next_out) nullval v1;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) v1; BoundKit.strm_pad v1;
     malloc_token Ews (tarray tuchar n) datap; data_at Ews (tarray tuchar n) (bytes_rep bs) datap;
     data_at_ BoundKit.Ecomp t_strm v1; data_at_ BoundKit.Ecomp t_strm v2])).

(* both deflateInit2_ calls returned Z_OK with the same state [s] and stream [z'] (DetFacts2.df2_init): the
   streams' states are at [sp1] and [sp2] *)
Definition P14 (J : det_inv) (s : dstate) (z' : strm) (msgv1 msgv2 sp1 sp2 : val) : environ -> mpred :=
  PROPx [pre_ok; J None s 0 (z_adler z'); d_gzhead s = None; 0 <= z_adler z' < 4294967296;
         msg_ok (z_msg z') msgv1; msg_ok (z_msg z') msgv2]
  (LOCALx (temp _code_second (vi Z_OK) :: temp _code_first (vi Z_OK) :: P_loc) (SEPx
    [dstream_sp 2 (Some s) v2 nullval sp2 gv; field_at Ews t_strm (DOT Zlib.deflate.code._next_in) nullval v2;
     reset_fields v2 (vl 0) (vl 0) msgv2 (vl (z_adler z'));
     version_at gv vlit; mem_mgr gv; deflate_globals gv;
     dstream_sp 2 (Some s) v1 nullval sp1 gv; field_at Ews t_strm (DOT Zlib.deflate.code._next_in) nullval v1;
     reset_fields v1 (vl 0) (vl 0) msgv1 (vl (z_adler z'));
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._next_out) nullval v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) v2; BoundKit.strm_pad v2;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi 0) v1;
     field_at Ews t_strm (DOT Zlib.deflate.code._next_out) nullval v1;
     field_at Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi 0) v1; BoundKit.strm_pad v1;
     malloc_token Ews (tarray tuchar n) datap; data_at Ews (tarray tuchar n) (bytes_rep bs) datap;
     data_at_ BoundKit.Ecomp t_strm v1; data_at_ BoundKit.Ecomp t_strm v2])).

End Cuts.

(** ** The parts' statements *)
Definition det_init_stmt : Prop := forall {Espec : OracleKind} v1 v2 gv J,
  det_facts2 J -> forall level wbits mem strategy n bs datap,
  (forall os z' code msgv1 os2 z2 code2 msgv2,
     semax Delta_m (P12 v1 v2 gv level wbits mem strategy n bs datap os z' code msgv1 os2 z2 code2 msgv2)
       msuf12 POST_m) ->
  semax Delta_m (P10 v1 v2 gv level wbits mem strategy n bs datap) msuf10 POST_m.

Definition det_codes_stmt : Prop := forall {Espec : OracleKind} v1 v2 gv J,
  det_facts2 J -> forall level wbits mem strategy n bs datap os z' code msgv1 os2 z2 code2 msgv2,
  (forall s z' msgv1 msgv2 sp1 sp2,
     semax Delta_m (P14 v1 v2 gv level wbits mem strategy n bs datap J s z' msgv1 msgv2 sp1 sp2) msuf14 POST_m) ->
  semax Delta_m (P12 v1 v2 gv level wbits mem strategy n bs datap os z' code msgv1 os2 z2 code2 msgv2)
    msuf12 POST_m.

Definition det_enter_stmt : Prop := forall {Espec : OracleKind} v1 v2 gv J,
  det_facts2 J -> forall level wbits mem strategy n bs datap s z' msgv1 msgv2 sp1 sp2,
  (forall J n data datap sp1 sp2 ls,
     semax Delta_m (J_at J n data datap v1 v2 sp1 sp2 gv ls) msuf17 POST_m) ->
  semax Delta_m (P14 v1 v2 gv level wbits mem strategy n bs datap J s z' msgv1 msgv2 sp1 sp2) msuf14 POST_m.

(* Law deflate_roundtrip (port of deflate_api9/RunSpec.v to the program of deflate_roundtrip):
   THE specification of deflate_common.h's deflate_run for this law (any [api], any invariants I Iend with the
   facts of LawFacts.v and RTXFacts.rt_extra; rf_ok also gives RTFinal.dfinal of the output with deflate's
   window bits), the representation of struct drun and of the run's objects, and the context of the body of
   deflate_run.

   The memory of main's locals R and s is Tsh; main splits it (join Ews (comp Ews) Tsh) and gives the Ews half
   to deflate_run (the API specifications are on Ews fields), keeping the other half until its return.

   deflate_run's run, in the representation:
   - [rs : rsetup]: what the run drew (the parameters, the selectors, the data, dictionary and header fields and
     their objects);
   - [drun_rest rs init wrap wb nf dset hset clen ended Rp]: the 25 fields of *R other than h ([init], [wrap],
     [wb] as vals: Vundef before deflateInit2);
   - [hdr_of rs]: the gzip header the run gives to deflateSetHeader; R->h is owned by the stream's [hdr_at] once
     deflateSetHeader returned Z_OK ([hset = 1]), else by [hpart];
   - the objects data, dict (and xf, nf_, cf before the loop) [obj], and comp ([comp_at]: the output O so far,
     the rest undefined). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTRCS.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Definition t_drun := Tstruct _drun noattr.
Definition t_strmL := Tstruct _z_stream_s noattr.

(* the harness's "1.3.2" (deflateInit2's version argument) *)
Definition vlit : ident := ___stringlit_x_deflate_roundtrip_1.

(** ** What the run drew *)
Record rsetup := mkRS {
  rs_level : Z; rs_method : Z; rs_wbits : Z; rs_mem : Z; rs_strategy : Z;
  rs_t1 : Z; rs_t2 : Z; rs_t3 : Z; rs_t4 : Z;          (* deflateTune's arguments *)
  rs_mtime : Z;                                         (* the header's time *)
  rs_tsel : Z; rs_dsel : Z; rs_hsel : Z;                (* tune / dictionary / header selectors (bytes) *)
  rs_text : Z; rs_os : Z; rs_hcrc : Z;                  (* bytes *)
  rs_data : list Z; rs_dict : list Z;                   (* n = Zlength rs_data, dlen = Zlength rs_dict *)
  rs_xf : list Z; rs_nm : list Z; rs_cm : list Z;       (* the extra field, the name and the comment (without 0) *)
  rs_datap : val; rs_dictp : val; rs_xfp : val; rs_nfp : val; rs_cfp : val; rs_compp : val }.

Definition rs_ok (rs : rsetup) : Prop :=
  s32 (rs_level rs) /\ s32 (rs_method rs) /\ s32 (rs_wbits rs) /\ s32 (rs_mem rs) /\ s32 (rs_strategy rs) /\
  s32 (rs_t1 rs) /\ s32 (rs_t2 rs) /\ s32 (rs_t3 rs) /\ s32 (rs_t4 rs) /\ u32r (rs_mtime rs) /\
  0 <= rs_tsel rs < 256 /\ 0 <= rs_dsel rs < 256 /\ 0 <= rs_hsel rs < 256 /\
  0 <= rs_text rs < 256 /\ 0 <= rs_os rs < 256 /\ 0 <= rs_hcrc rs < 256 /\
  Zlength (rs_data rs) <= 1048576 /\ Zlength (rs_dict rs) <= 32768 /\ Zlength (rs_xf rs) <= 4096 /\
  Zlength (rs_nm rs) <= 4096 /\ Zlength (rs_cm rs) <= 4096 /\
  bytes (rs_data rs) /\ bytes (rs_dict rs) /\ bytes (rs_xf rs) /\
  Forall (fun b => 0 < b < 256) (rs_nm rs) /\ Forall (fun b => 0 < b < 256) (rs_cm rs) /\
  isptr (rs_datap rs) /\ isptr (rs_dictp rs) /\ isptr (rs_xfp rs) /\ isptr (rs_nfp rs) /\ isptr (rs_cfp rs) /\
  isptr (rs_compp rs).

(* the header of deflateSetHeader (R->h) *)
Definition hdr_of (rs : rsetup) : gzh :=
  mkGZ (Z.land (rs_text rs) 1) (rs_mtime rs) (rs_os rs) (Some (rs_xf rs)) (Zlength (rs_xf rs))
       (Some (rs_nm rs ++ [0])) (Some (rs_cm rs ++ [0])) (Z.land (rs_hcrc rs) 1).

(* &R->h *)
Definition hp_of (Rp : val) : val := field_address t_drun (DOT _h) Rp.

(* the header's objects as hdr_at holds them *)
Definition hx_of (rs : rsetup) : share * val * val * val := (Ews, rs_xfp rs, rs_nfp rs, rs_cfp rs).

(** ** The structs' padding (v2 of the kit): data_at_ of a struct owns its padding bytes (VST spacers), the
    field-wise predicates do not, so the padding is carried explicitly (layouts at RTRCS.CS / DCS.CS:
    drun 216 bytes, holes 68-72 and 188-192; z_stream 112 bytes, holes 12-16, 36-40, 92-96; gz_header 80 bytes,
    holes 4-8, 52-56, 76-80). *)
Definition drun_pad (Rp : val) : mpred := spacer Ews 68 72 Rp * spacer Ews 188 192 Rp.
Definition strm_pad (sp : val) : mpred := spacer Ews 12 16 sp * spacer Ews 36 40 sp * spacer Ews 92 96 sp.
Definition gzh_pad (hp : val) : mpred := spacer Ews 4 8 hp * spacer Ews 52 56 hp * spacer Ews 76 80 hp.

(** ** struct drun *)
Definition drun_rest (rs : rsetup) (init wrap wb : val) (nf dset hset clen ended : Z) (Rp : val) : mpred :=
  field_at Ews t_drun (DOT _level) (vi (rs_level rs)) Rp *
  field_at Ews t_drun (DOT _method) (vi (rs_method rs)) Rp *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) Rp *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) Rp *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) Rp *
  field_at Ews t_drun (DOT _init) init Rp *
  field_at Ews t_drun (DOT _wrap) wrap Rp *
  field_at Ews t_drun (DOT _wb) wb Rp *
  field_at Ews t_drun (DOT _data) (rs_datap rs) Rp *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) Rp *
  field_at Ews t_drun (DOT _nf) (vi nf) Rp *
  field_at Ews t_drun (DOT _dict) (rs_dictp rs) Rp *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) Rp *
  field_at Ews t_drun (DOT _dict_set) (vi dset) Rp *
  field_at Ews t_drun (DOT _head_set) (vi hset) Rp *
  field_at Ews t_drun (DOT _xf) (rs_xfp rs) Rp *
  field_at Ews t_drun (DOT _nf_) (rs_nfp rs) Rp *
  field_at Ews t_drun (DOT _cf) (rs_cfp rs) Rp *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) Rp *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) Rp *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) Rp *
  field_at Ews t_drun (DOT _comp) (rs_compp rs) Rp *
  field_at Ews t_drun (DOT _clen) (vl clen) Rp *
  field_at Ews t_drun (DOT _ended) (vi ended) Rp *
  field_at Ews t_drun (DOT _api_ok) (vi 1) Rp *
  drun_pad Rp.

(* R->h when the stream does not hold it *)
Definition hpart (hset : Z) (Rp : val) : mpred :=
  if hset =? 1 then gzh_pad (hp_of Rp) else field_at_ Ews t_drun (DOT _h) Rp.

(** ** The run's objects *)
Definition obj (p : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) p * data_at Ews (tarray tuchar (Zlength l)) (map vi l) p.

Definition COMP_MAX : Z := 4194304.

(* comp: the output O so far, the rest undefined *)
Definition comp_at (O : list Z) (p : val) : mpred :=
  malloc_token Ews (tarray tuchar COMP_MAX) p *
  data_at Ews (tarray tuchar COMP_MAX) (map vi O ++ Zrepeat Vundef (COMP_MAX - Zlength O)) p.

(** ** deflate_run's specification *)

(* the end of a successful run (deflateInit2 Z_OK, the loop ended with Z_STREAM_END): what main checks and
   needs for its calls after the run *)
Record rfinal := mkRF {
  rf_rs : rsetup; rf_dict : list Z; rf_nf : Z; rf_dset : Z; rf_hset : Z; rf_O : list Z; rf_s : dstate;
  rf_tin : Z; rf_tout : Z; rf_adler : Z; rf_nin : val; rf_ain : Z; rf_nout : val; rf_aout : Z;
  rf_msgv : val; rf_ghp : val }.

Definition rf_wrap (rf : rfinal) : Z := wrap_of (rs_wbits (rf_rs rf)).

Definition rf_ok (Iend : dstate -> Prop) (Rp : val) (rf : rfinal) : Prop :=
  let rs := rf_rs rf in
  rs_ok rs /\ Iend (rf_s rf) /\ is_pointer_or_null (rf_msgv rf) /\
  final_ok (rf_dict rf) (rf_wrap rf) (sublist 0 (rf_nf rf) (rs_data rs)) (rf_O rf) (rf_adler rf) /\
  0 <= rf_nf rf <= Zlength (rs_data rs) /\ Zlength (rf_O rf) <= COMP_MAX /\
  ((rf_dset rf = 1 /\ rf_dict rf = rs_dict rs /\ rs_dict rs <> []) \/ (rf_dset rf = 0 /\ rf_dict rf = [])) /\
  ((rf_hset rf = 1 /\ rf_ghp rf = hp_of Rp /\ d_gzhead (rf_s rf) = Some (hdr_of rs)) \/
   (rf_hset rf = 0 /\ d_gzhead (rf_s rf) = None)) /\
  (* the round trip (rt_extra): the output is the well-formed stream of the data, with deflate's window bits *)
  dfinal (rf_dict rf) (rf_wrap rf) (rwbe (rs_wbits rs)) (d_gzhead (rf_s rf)) (sublist 0 (rf_nf rf) (rs_data rs))
    (rf_O rf) /\
  (rf_wrap rf = 0 -> rwbe (rs_wbits rs) = wb_of (rs_wbits rs)) /\
  (* deflateSetHeader succeeds only on a gzip stream *)
  (rf_hset rf = 1 -> rf_wrap rf = 2).

Definition run_ok_at (rf : rfinal) (Rp sp : val) (gv : globals) : mpred :=
  let rs := rf_rs rf in
  drun_rest rs (vi 0) (vi (rf_wrap rf)) (vi (wb_of (rs_wbits rs))) (rf_nf rf) (rf_dset rf) (rf_hset rf)
    (Zlength (rf_O rf)) 1 Rp *
  hpart (rf_hset rf) Rp *
  dstream 2 (Some (rf_s rf)) sp (rf_ghp rf) gv *
  api_fields sp (rf_nin rf) (rf_ain rf) (rf_tin rf) (rf_nout rf) (rf_aout rf) (rf_tout rf) (rf_msgv rf)
    (rf_adler rf) * strm_pad sp *
  hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of rs) *
  obj (rs_datap rs) (rs_data rs) * obj (rs_dictp rs) (rs_dict rs) * comp_at (rf_O rf) (rs_compp rs) * TT.

Definition run_post (Iend : dstate -> Prop) (ret : Z) (Rp sp : val) (gv : globals) : mpred :=
  if ret =? 0 then data_at_ Ews t_drun Rp * data_at_ Ews t_strmL sp * TT
  else EX init : Z,
       if init =? 0 then EX rf : rfinal, !! rf_ok Iend Rp rf && run_ok_at rf Rp sp gv
       else EX rs : rsetup, !! s32 init &&
            drun_rest rs (vi init) Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 Rp *
            field_at_ Ews t_drun (DOT _h) Rp * data_at_ Ews t_strmL sp * TT.

(* deflate_run(R, s, api): for ANY invariants I, Iend with the facts of deflate_api (LawFacts.api_facts) and of
   the round trip (RTXFacts.rt_extra) *)
Definition deflate_run_spec (I : api_inv) (Iend : dstate -> Prop) :=
  DECLARE _deflate_run
  WITH Rp : val, sp : val, api : Z, gv : globals
  PRE [ tptr t_drun, tptr t_strmL, tint ]
    PROP (api_facts I Iend; s32 api; rt_extra I)
    PARAMS (Rp; sp; vi api) GLOBALS (gv)
    SEP (data_at_ Ews t_drun Rp; data_at_ Ews t_strmL sp; mem_mgr gv; deflate_globals gv; version_at gv vlit)
  POST [ tint ]
    EX ret : Z,
    PROP (ret = 0 \/ ret = 1)
    RETURN (vi ret)
    SEP (mem_mgr gv; deflate_globals gv; version_at gv vlit; run_post Iend ret Rp sp gv).

(** ** The contexts *)
Definition Grun : funspecs :=
  [stream_defaults_spec; deflate_params_ok_spec; draw_nonzero_bytes_spec; exact_copy_spec; exact_space_spec;
   deflateInit2__spec_v9; deflateTune_spec; deflateSetDictionary_spec; deflateSetHeader_spec; deflate_spec;
   deflateParams_spec; bytes_copy_spec; bytes_same_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

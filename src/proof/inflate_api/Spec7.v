(* inflate() for any input and output space a call can be given: avail_in and avail_out up to UINT_MAX.

   Spec5.inflate_spec bounds both by Int.max_signed (2^31 - 1).  The laws that cut their input and output
   with laws_common.h's clip() (rt_partial, rj_truncated, rj_bad_checksum, rfc_trailing_bytes, and the
   inflate laws rfc_stored, rj_any_input, api_counters, api_untouched_output, rj_far_back) give a call up to
   UINT_MAX = 2^32 - 1 bytes of each.  [inflate_spec7] is Spec5's inflate_spec with these two bounds raised
   to Int.max_unsigned; everything else (the stream predicate, the model run2, the buffers) is the same, so
   inflate_spec7 is a funspec_sub of inflate_spec.

   inflate() calls inflate_fast, whose Spec3 specification (Callees3.inflate_fast_spec3) carries the same
   2^31 - 1 bound in the machine invariant mwf.  [inflate_body7_stmt]: inflate_fast has SOME specification
   proved of its body, and inflate()'s body is proved against inflate_spec7 in Spec5's context with that
   specification for inflate_fast. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inffast.Body.
Require Export Zlib.proof.inflate.Callees3.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition inflate_spec7 :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          zf_ai z <= Int.max_unsigned; zf_ao z <= Int.max_unsigned)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* inflate()'s context of Callees3 with [fast] for inflate_fast *)
Definition Gprog_inflate7 (fast : funspec) : funspecs :=
  map (fun f : ident * funspec => if ident_eq (fst f) _inflate_fast then (_inflate_fast, fast) else f)
    Gprog_inflate3.

Definition inflate_body7_stmt : Prop :=
  exists fast : funspec,
    (forall {Espec: OracleKind},
       semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast (_inflate_fast, fast)) /\
    (forall {Espec: OracleKind}, semax_body Vprog_inflate (Gprog_inflate7 fast) f_inflate inflate_spec7).

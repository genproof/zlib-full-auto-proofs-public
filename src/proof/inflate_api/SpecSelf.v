(* inflate() with its output pointer inside the z_stream itself.

   uncompr.c's uncompress2_z, given a Z_NULL destination with *destLen = 0, points next_out at the stream's own
   `reserved` member ("next_out cannot be NULL") and offers avail_out = 0.  Spec5.inflate_spec does not cover that
   call: an empty output object needs its malloc token (out_tok_ok), for VST's validity of the pointer that the
   prologue compares with Z_NULL.  Here the pointer is valid because it points into the z_stream that the
   precondition holds (istream).

   [inflate_spec_s] is Spec5.inflate_spec with one more admissible output: [self_out strmp otok ob (zf_ao z)], an
   empty output object (0 bytes, no token) at offset 104 of the stream (the member `reserved`), with avail_out = 0.
   The relation of the call is Spec5's [inflate_rel], unchanged.  [inflate_spec_s_sub]: every caller of Spec5's
   inflate_spec is a caller of this one. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate_api.Spec5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the address of the member `reserved` of the z_stream at strmp *)
Definition strm_res_ptr (strmp: val) : val := offset_val 104 strmp.

(* the output is the empty object at the stream's member `reserved`, without a token, and nothing is offered *)
Definition self_out (strmp: val) (otok: bool) (ob: option outbuf) (aout: Z) : Prop :=
  otok = false /\ aout = 0 /\
  exists sh, writable_share sh /\ ob = Some (OutBuf sh (strm_res_ptr strmp) 0 0 []).

Definition inflate_spec_s :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob \/ self_out strmp otok ob (zf_ao z);
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          zf_ai z <= Int.max_signed; zf_ao z <= Int.max_signed)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; head_opt (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* the body of inflate() against it, in the context of Spec5's body (Bodies5.body_inflate_stmt) *)
Definition body_inflate_s_stmt : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog_inflate Gprog_inflate3 f_inflate inflate_spec_s.

(* a statement of the subsumption (proved in round 1's BodySelf.v; no law here needs it) *)
Definition inflate_spec_s_sub_stmt : Prop := funspec_sub (snd inflate_spec_s) (snd inflate_spec).

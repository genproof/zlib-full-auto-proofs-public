(* inflate() for any sizes with its output pointer inside the z_stream itself.

   uncompr.c's uncompress2_z, given a Z_NULL destination with *destLen = 0, points next_out at the stream's own
   member `reserved` ("next_out cannot be NULL") and offers avail_out = 0; with a source of any length it offers
   avail_in up to 2^32-1.  SpecW.inflate_specW (any uInt sizes) needs the malloc token of an empty output object
   (out_tok_ok); SpecSelf.inflate_spec_s (the stream's own member allowed) takes sizes below 2^31 only.

   [inflate_specW_s] is SpecW.inflate_specW with one more admissible output, SpecSelf's [self_out]: the empty
   object at offset 104 of the stream, without a token, with avail_out = 0.  The relation of the call is
   Spec5's [inflate_rel], unchanged.  [inflate_specW_s_sub]: every caller of inflate_specW is a caller of this
   one.  [body_inflate_ws_stmt]: inflate()'s body against it, in the context of its callees as a law's program
   lists them (the allocator-generic port's specifications at zlib's default allocator, as in SpecWLib.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.SpecW.
Require Export Zlib.proof.inflate_api.SpecSelf.
Require Import Zlib.proof.inflate_api.SpecWLib.
Require Import Zlib.proof.inflate.Callees5.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition inflate_specW_s :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, av: val, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob \/ self_out strmp otok ob (zf_ao z);
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          match st with Some L => swfW (l_s L) | None => True end)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istreamA_opt gv shs strmp z av st; head_opt (is_live strmp st);
         bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow; raw_live st' = raw_live st;
          match st' with Some L' => swfW (l_s L') | None => True end)
    RETURN (Vint (Int.repr r))
    SEP (istreamA_opt gv shs strmp z' Vundef st'; head_opt (is_live strmp st');
         bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* inflate_specW's precondition is the first case of this one; the postconditions are the same *)
Lemma inflate_specW_s_sub : funspec_sub (snd inflate_specW_s) (snd inflate_specW).
Proof.
do_funspec_sub.
destruct w as [[[[[[[[[[[[[gv shs] strmp] z] av] st] ib] inp] ob] flush] gsh] tsh] itok] otok].
Exists (gv, shs, strmp, z, av, st, ib, inp, ob, flush, gsh, tsh, itok, otok) emp.
rewrite emp_sepcon. apply andp_right.
- apply andp_derives; [apply prop_derives; intuition | apply derives_refl].
- apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2, derives_refl.
Qed.

(* the body of inflate() against inflate_specW_s, in the context of its callees at zlib's default allocator
   (USpec.GU_inflate at SpecWLib.zc_alloc: the specifications a law's program gives inflate_fast, updatewindow,
   inflateStateCheck, inflate_table, adler32, crc32, memcpy) *)
Definition body_inflate_ws_stmt : Prop :=
  forall {Espec: OracleKind},
  semax_body Vprog_inflate (@Zlib.proof.za.inflate_api.USpec.GU_inflate globals zc_alloc) f_inflate inflate_specW_s.

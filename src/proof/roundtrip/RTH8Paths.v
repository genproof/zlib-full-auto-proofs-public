(* inflate()'s body against RTH8Spec.inflate_spec8, split by the header the call starts with (head_mem8's three
   disjuncts): [inflate_spec8x Pre] is inflate_spec8 with the precondition's header part Pre instead of head_opt8.
   - [hd8pre_a]: no header attached, or Spec5's defined header with Spec5's sizes: Spec5's body
     (Body5_inflate.body_inflate_proof5), on the stream with the small header model RTH8W.lcanon when no header is
     attached (the run does not read it, RTH8W.sim_stmt);
   - [hd8pre_b]: a partial header (head_rep6) in a header mode: the prologue (RTHPro6), the header cases with a
     header of any sizes (RTH8W.cases8w_all) until the header is passed (hpass8), then the headless loop
     (RTH8Defs.loop_part8_stmt) and exit (the port's exit_part5_hl) on the machine with the small header;
   - [hd8pre_c]: a partial header past the header modes (head_rep8a): the prologue, the headless loop and exit.
   The three bodies are proved in the context Gprog_inflate3_hl of the port (= Gprog_inflate8 with the headless
   inflate_fast specification, RTH8Defs.rth8_delta_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.roundtrip.RTH8W.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition inflate_spec8x (Pre: option live -> mpred) :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          zf_ai z <= Int.max_signed; zf_ao z <= Int.max_signed;
          hd8_ok flush strmp z st inp)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream8_opt gv shs strmp z st; Pre (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream8_opt gv shs strmp z' st'; head_opt8 (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* the header buffers' malloc tokens of a live stream *)
Definition btoks8 (L: live) : mpred :=
  btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L)).

(* no header, or Spec5's defined header with Spec5's sizes *)
Definition hd8pre_a (st: option live) : mpred :=
  match st with
  | None => emp
  | Some L =>
      if i_head (l_s L) then
        (!! hwf (l_h L) && head_rep (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L)) * btoks8 L
      else emp
  end.

(* a partial header in a header mode *)
Definition hd8pre_b (st: option live) : mpred :=
  match st with
  | None => FF
  | Some L =>
      if i_head (l_s L) then
        (!! (hdr_mode (i_mode (l_s L)) = true) &&
         head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)) * btoks8 L
      else FF
  end.

(* a partial header past the header modes *)
Definition hd8pre_c (st: option live) : mpred :=
  match st with
  | None => FF
  | Some L =>
      if i_head (l_s L) then
        (!! (hdr_mode (i_mode (l_s L)) = false) &&
         head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)) * btoks8 L
      else FF
  end.

Definition body8_stmt (Pre: option live -> mpred) : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog_inflate Gprog_inflate3_hl f_inflate (inflate_spec8x Pre).

(* RT-H: the pieces of inflate()'s body against RTHSpec.inflate_spec6.
   inflate_spec6's precondition is Spec5's (head_mem6's left disjunct, or no header) or the header case
   (head_mem6's right disjunct: i_head, a header mode, head_rep6): inflate_spec6h.
   - rth_split: a body for Spec5's inflate_spec and one for inflate_spec6h give one for inflate_spec6;
   - hloop6: the main loop from a header machine (headless loop state + hd6) passing the header (hpass),
     then Spec5's loop_part5 from the first machine past it;
   - rth_body6h: the body for inflate_spec6h (prologue pro_part6, hloop6, Spec5's exit). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTHCase.
Require Import Zlib.proof.inflate_api.Body5Loop.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the header part of inflate_spec6's precondition in the header case; FF otherwise *)
Definition hd6pre (st: option live) : mpred :=
  match st with
  | Some L =>
      if i_head (l_s L) then
        !! (hdr_mode (i_mode (l_s L)) = true) &&
        head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) *
        hdr_btoks (l_xb L) (l_nb L) (l_cb L) (l_h L)
      else FF
  | None => FF
  end.

Definition inflate_spec6h :=
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
          hd6_ok flush strmp z st inp)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream_opt gv shs strmp z st; hd6pre (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream_opt gv shs strmp z' st'; head_opt6 (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* head_mem6 is Spec5's head_mem or the header case *)
Lemma head_opt6_split: forall st,
  head_opt6 st |-- head_opt st || hd6pre st.
Proof.
  intros [L | ]; simpl; [ | apply orp_right1; apply derives_refl].
  unfold head_mem6, head_mem, hdr_btoks.
  destruct (i_head (l_s L)); [ | apply orp_right1; apply derives_refl].
  rewrite !sepcon_assoc, distrib_orp_sepcon.
  apply orp_left.
  - apply orp_right1. cancel.
  - apply orp_right2. cancel.
Qed.

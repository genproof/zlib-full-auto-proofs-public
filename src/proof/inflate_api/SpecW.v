(* The wide external specifications of inflate() and inflateSetDictionary: Spec5's inflate_spec and
   inflateSetDictionary_spec for every client of zlib's API, at the compspecs of the inflate unit.

   They differ from Spec5's in two points, both needed by the short laws (whose harnesses use
   harness/laws_common.h):
   - inflate() takes avail_in and avail_out up to 2^32-1 (uInt; Spec5 requires <= 2^31-1, its machine
     invariant Inv.mwf too; the wide one is InvW.mwfW);
   - on a raw stream (state->wrap = 0) the member strm->adler may hold any value, Vundef included:
     inflateResetKeep sets it only when wrap <> 0, and new_stream() does not set it; inflate() and
     inflateSetDictionary never read it, and write it only when wrap <> 0.  The stream is then
     `istreamA gv shs strmp z av st`: Spec5's istream except that strm->adler holds `adler_v (raw_live st) z
     av` (av on a raw stream, the model's zf_adler z otherwise; istreamA_istream).  The postconditions give
     a raw stream's member back as Vundef (any contents): inflate() writes it in the modes DICTID and DICT
     without testing wrap, and live_ok does not exclude a raw stream in these modes.
   - inflate() takes a live state with InvW.swfW (the extra field's length and the bit buffer before it:
     what the wider input needs in case EXTRA) and gives it back.
   The relations are Spec5's: a call is inflate_rel (the exact model run2), inflateSetDictionary is
   setdict_f. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate_api.Spec5.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* a live raw stream *)
Definition raw_live (st: option live) : bool :=
  match st with Some L => i_wrap (l_s L) =? 0 | None => false end.

(* the contents of strm->adler: av on a raw stream, the model's value otherwise *)
Definition adler_v (raw: bool) (z: zfields) (av: val) : val :=
  if raw then av else Vlong (Int64.repr (zf_adler z)).

(* struct z_stream with the fields z, strm->state = st and strm->adler = adv *)
Definition zstrm_atA (gv: globals) (shs: share) (strmp: val) (z: zfields) (adv: val) (st: val) : mpred :=
  data_at shs t_strm
    (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z,
     (Vint (Int.repr (zf_ao z)), (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (st,
     (gv _zcalloc, (gv _zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (adv, zf_res z))))))))))))) strmp.

Definition istreamA (gv: globals) (shs: share) (strmp: val) (z: zfields) (av: val) (st: option live) : mpred :=
  !! (zf_ok z /\ writable_share shs) &&
  match st with
  | None => zstrm_atA gv shs strmp z (adler_v (raw_live st) z av) nullval
  | Some L => !! live_ok L &&
      (zstrm_atA gv shs strmp z (adler_v (raw_live st) z av) (l_sp L) * state_mem gv strmp L)
  end.

Definition istreamA_opt (gv: globals) (shs: share) (strmp: val) (z: zfields) (av: val) (st: option live)
    : mpred :=
  if eq_dec strmp nullval then emp else istreamA gv shs strmp z av st.

Lemma istreamA_istream: forall gv shs strmp z av st,
  raw_live st = false -> istreamA gv shs strmp z av st = istream gv shs strmp z st.
Proof.
  intros gv shs strmp z av st R. unfold istreamA, istream, adler_v. rewrite R. reflexivity.
Qed.

(* inflate(strm, flush): Spec5's inflate_spec without the bounds avail_in, avail_out <= 2^31-1, on an
   istreamA whose live state satisfies swfW *)
Definition inflate_specW :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, av: val, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
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

(* inflateSetDictionary(strm, dictionary, dictLength): Spec5's inflateSetDictionary_spec on an istreamA *)
Definition inflateSetDictionary_specW :=
  DECLARE _inflateSetDictionary
  WITH gv: globals, shs: share, strmp: val, z: zfields, av: val, st: option live,
       dsh: share, p: val, lo: Z, n: Z, c: list val, dict: list Z, tok: bool
  PRE [ tptr t_strm, tptr tuchar, tuint ]
    PROP (readable_share dsh; isptr p; 0 <= lo; lo + Zlength dict <= n; Zlength c = n; n = 0 -> tok = true;
          Zlength dict <= Int.max_unsigned;
          n <= Ptrofs.max_unsigned; sublist lo (lo + Zlength dict) c = byte_vals dict; bytes_ok dict)
    PARAMS (strmp; offset_val lo p; Vint (Int.repr (Zlength dict))) GLOBALS (gv)
    SEP (istreamA_opt gv shs strmp z av st; data_at dsh (tarray tuchar n) c p;
         if tok then malloc_token Ews (tarray tuchar n) p else emp; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX alloc_ok: bool, EX winp: val,
    PROP (raw_live (thd3 (on_live strmp z st (setdict_f dict alloc_ok winp))) = raw_live st)
    RETURN (Vint (Int.repr (fst3 (on_live strmp z st (setdict_f dict alloc_ok winp)))))
    SEP (istreamA_opt gv shs strmp (snd3 (on_live strmp z st (setdict_f dict alloc_ok winp))) Vundef
           (thd3 (on_live strmp z st (setdict_f dict alloc_ok winp)));
         data_at dsh (tarray tuchar n) c p;
         if tok then malloc_token Ews (tarray tuchar n) p else emp; mem_mgr gv; zfuncs gv).

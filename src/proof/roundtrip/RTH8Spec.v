(* inflate() with an application gz_header whose ABSENT fields stay undefined (version 8 of the header spec).

   harness/rt_gzip_header.c gives inflateGetHeader a local `gz_header got` with malloc'ed buffers: every scalar
   field and every buffer byte is undefined until inflate writes it.  When the gzip header has no extra field,
   inflate sets got.extra = Z_NULL in mode EXLEN and never writes got.extra_len; when it has no name (comment),
   the name (comment) buffer is never written.  RTHSpec's v6 spec covers only headers with all three fields:
   at the end of the header modes it hands over Spec5's DEFINED head_rep (RTHSpec.hfull), which sits in
   Loop.mem_rep of every switch case of Spec5's body proof.  Here:
   - in the header modes HEAD .. HCRC the header is RTHSpec.head_rep6 (as in v6);
   - after a header passed by inflate (done = 1) it is [head_rep8a]: RTHSpec.head_rep6p at phase 5 (text, time,
     xflags, os, hcrc, done written; extra_len written exactly when the header has FEXTRA), each buffer holding
     the model's bytes in its first [cxa]/[cna]/[cca] bytes (what inflate copied: 0 for an absent field) and
     anything after them;
   - or it is Spec5's defined head_rep (any mode), so that calls with a defined header are covered too.
   A call that starts in a header mode with a header attached must pass the header ([hpass8]: no return before
   a non-header mode, which is reached with done = 1, i.e. through HCRC); unlike RTHSpec.hpass the fields may
   be absent and the buffers need not be filled.
   The header's buffer sizes: Spec5's hwf (in live_ok, hence in istream) caps extra_max / name_max / comm_max at
   65536, but rt_gzip_header gives a name and a comment buffer of up to 2^20 + 1 bytes.  Here the stream is
   [istream8]: Spec5's istream with [live_ok8], whose [hwf8] allows any uInt sizes; a defined header (Spec5's
   head_rep) is accepted with Spec5's hwf only.
   inflateGetHeader is [inflateGetHeader_spec8] = RTHSpec.inflateGetHeader_spec6 (any field values and buffer
   bytes) with hwf8, istream8 and head_mem8 (in mode HEAD or FLAGS: its head_rep6 disjunct).

   [inflate_body8_stmt]: inflate_fast has SOME specification (calling convention cc_default) proved of its body,
   inflate()'s body is proved against [inflate_spec8] in Spec5's context with that specification for
   inflate_fast, and inflateGetHeader's body against [inflateGetHeader_spec8]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTHSpec.
Require Export Zlib.proof.inffast.Body.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the stream with header buffers of any uInt size                                               *)

(* Spec5's hwf (inflate/Inv.v) with the buffer sizes any uInt *)
Definition hwf8 (h: hstate) : Prop :=
  srange (h_text h) /\ lrange (h_time h) /\ srange (h_xflags h) /\ srange (h_os h) /\ urange (h_extra_len h) /\
  0 <= h_extra_max h <= Int.max_unsigned /\ 0 <= h_name_max h <= Int.max_unsigned /\
  0 <= h_comm_max h <= Int.max_unsigned /\
  (Zlength (h_xbuf h) = h_extra_max h /\ bytes_ok (h_xbuf h)) /\
  (Zlength (h_nbuf h) = h_name_max h /\ bytes_ok (h_nbuf h)) /\
  (Zlength (h_cbuf h) = h_comm_max h /\ bytes_ok (h_cbuf h)) /\
  srange (h_hcrc h) /\ srange (h_done h).

(* Spec5's live_ok with hwf8 *)
Definition live_ok8 (L: live) : Prop :=
  isptr (l_sp L) /\ swf (l_s L) /\ modewf (l_s L) /\ hwf8 (l_h L) /\ swf3 (l_s L) /\ writable_share (l_hsh L) /\
  (i_wbits (l_s L) = 0 -> Z.land (i_wrap (l_s L)) 3 <> 0 /\ i_win (l_s L) = false) /\
  (i_head (l_s L) = true ->
     (h_xp (l_h L) = true -> l_xb L <> nullval) /\ (h_np (l_h L) = true -> l_nb L <> nullval) /\
     (h_cp (l_h L) = true -> l_cb L <> nullval)) /\
  (i_wbits (l_s L) = 0 -> i_wrap (l_s L) <> 0 ->
     i_flags (l_s L) = -1 /\ (i_mode (l_s L) = HEAD \/ i_mode (l_s L) = BAD \/ i_mode (l_s L) = SYNC \/
                              i_mode (l_s L) = MEM)).

(* Spec5's istream with live_ok8 *)
Definition istream8 (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) : mpred :=
  !! (zf_ok z /\ writable_share shs) &&
  match st with
  | None => zstrm_at gv shs strmp z nullval
  | Some L => !! live_ok8 L && (zstrm_at gv shs strmp z (l_sp L) * state_mem gv strmp L)
  end.

Definition istream8_opt (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) : mpred :=
  if eq_dec strmp nullval then emp else istream8 gv shs strmp z st.

(* Spec5's streams are istream8 streams *)
Lemma hwf_8: forall h, hwf h -> hwf8 h.
Proof.
  intros h [A B C D E X N M XB NB CB HC DN]. unfold hwf8.
  assert (X' : 0 <= h_extra_max h <= Int.max_unsigned) by (unfold Int.max_unsigned; simpl; lia).
  assert (N' : 0 <= h_name_max h <= Int.max_unsigned) by (unfold Int.max_unsigned; simpl; lia).
  assert (M' : 0 <= h_comm_max h <= Int.max_unsigned) by (unfold Int.max_unsigned; simpl; lia).
  exact (conj A (conj B (conj C (conj D (conj E (conj X' (conj N' (conj M'
          (conj XB (conj NB (conj CB (conj HC DN)))))))))))).
Qed.

Lemma live_ok_8: forall L, live_ok L -> live_ok8 L.
Proof.
  intros L (A & B & C & D & E & F & G & H & I). unfold live_ok8. apply hwf_8 in D. tauto.
Qed.

Lemma istream_8: forall gv shs strmp z st, istream gv shs strmp z st |-- istream8 gv shs strmp z st.
Proof.
  intros. unfold istream, istream8. destruct st as [L|]; [ | apply derives_refl].
  Intros. pose proof (live_ok_8 L H1). entailer!.
Qed.

Lemma istream_opt_8: forall gv shs strmp z st, istream_opt gv shs strmp z st |-- istream8_opt gv shs strmp z st.
Proof.
  intros. unfold istream_opt, istream8_opt. destruct (eq_dec strmp nullval); [apply derives_refl | apply istream_8].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the header after the header modes                                                             *)

(* the bytes inflate copied into each buffer once the header is passed (RTHSpec's counts in mode HCRC) *)
Definition cxa (h: hstate) : Z := if h_xp h then Z.min (h_extra_len h) (h_extra_max h) else 0.
Definition cna (h: hstate) : Z := if h_np h then Z.min (fz (h_nbuf h) + 1) (h_name_max h) else 0.
Definition cca (h: hstate) : Z := if h_cp h then Z.min (fz (h_cbuf h) + 1) (h_comm_max h) else 0.

(* every scalar field written but extra_len (written iff FEXTRA); the buffers' first cxa/cna/cca bytes *)
Definition head_rep8a (hsh: share) (headp xb nb cb: val) (s: istate) (h: hstate) : mpred :=
  head_rep6p hsh headp xb nb cb 5 (fextra s) (cxa h) (cna h) (cca h) h.

(* the application's gz_header while inflate holds it: defined (Spec5's head_rep, with Spec5's sizes), or partial: head_rep6 in a
   header mode, head_rep8a after the header *)
Definition head_mem8 (L: live) : mpred :=
  if i_head (l_s L) then
    (!! hwf (l_h L) && head_rep (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L) ||
     !! (hdr_mode (i_mode (l_s L)) = true) &&
     head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) ||
     !! (hdr_mode (i_mode (l_s L)) = false) &&
     head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L)) *
    btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L))
  else emp.
Definition head_opt8 (st: option live) : mpred :=
  match st with None => emp | Some L => head_mem8 L end.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate(): a call starting in a header mode with a header attached passes the header           *)

(* from m, the passes of the switch through the header modes neither return nor leave, and reach a non-header
   mode with done = 1 (the end of HCRC; a BAD header ends with done = 0) *)
Fixpoint hpass8 (flush: Z) (n: nat) (m: mst) : Prop :=
  match n with
  | O => False
  | S n =>
      if hdr_mode (m_mode m) then
        match stepf2 flush lenfix_list distfix_list m with
        | IBrk m' => m_leave m' = 0 /\ hpass8 flush n m'
        | IRet _ _ => False
        end
      else h_done (m_h m) = 1
  end.

Definition hd8_ok (flush: Z) (strmp: val) (z: zfields) (st: option live) (inp: list Z) : Prop :=
  match is_live strmp st with
  | Some L => i_head (l_s L) = true -> hdr_mode (i_mode (l_s L)) = true ->
              exists n, hpass8 flush n (m_init z L inp)
  | None => True
  end.

Definition inflate_spec8 :=
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
    SEP (istream8_opt gv shs strmp z st; head_opt8 (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow)
    RETURN (Vint (Int.repr r))
    SEP (istream8_opt gv shs strmp z' st'; head_opt8 (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetHeader(strm, head): RTHSpec.inflateGetHeader_spec6 with hwf8 and istream8            *)

Definition inflateGetHeader_spec8 :=
  DECLARE _inflateGetHeader
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live,
       headp: val, hsh: share, xb: val, nb: val, cb: val, h: hstate
  PRE [ tptr t_strm, tptr t_head ]
    PROP (writable_share hsh; hwf8 h; hattach_ok strmp st;
          h_xp h = true -> xb <> nullval; h_np h = true -> nb <> nullval; h_cp h = true -> cb <> nullval)
    PARAMS (strmp; headp) GLOBALS (gv)
    SEP (istream8_opt gv shs strmp z st; hraw6 hsh headp xb nb cb h; hdr_btoks xb nb cb h; zfuncs gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (match is_live strmp st with
                            | Some L => if Z.land (i_wrap (l_s L)) 2 =? 0 then Z_STREAM_ERROR else Z_OK
                            | None => Z_STREAM_ERROR end)))
    SEP (match is_live strmp st with
         | Some L =>
             if Z.land (i_wrap (l_s L)) 2 =? 0 then
               istream8_opt gv shs strmp z st * hraw6 hsh headp xb nb cb h * hdr_btoks xb nb cb h
             else
               let L' := set_l_head (set_l_s L (set_i_head (l_s L) true)) (set_h_done h 0) headp hsh xb nb cb in
               istream8_opt gv shs strmp z (Some L') * head_mem8 L'
         | None => istream8_opt gv shs strmp z st * hraw6 hsh headp xb nb cb h * hdr_btoks xb nb cb h
         end;
         zfuncs gv).

(* ---------------------------------------------------------------------------------------------- *)
(* the body obligations                                                                           *)

(* Spec5's context of inflate() with the specification [fast] for inflate_fast *)
Definition Gprog_inflate8 (fast : funspec) : funspecs :=
  map (fun f : ident * funspec => if ident_eq (fst f) _inflate_fast then (_inflate_fast, fast) else f)
    Gprog_inflate3.

Definition inflate_body8_stmt : Prop :=
  exists fast : funspec,
    callingconvention_of_funspec fast = cc_default /\
    (forall {Espec: OracleKind},
       semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast (_inflate_fast, fast)) /\
    (forall {Espec: OracleKind}, semax_body Vprog_inflate (Gprog_inflate8 fast) f_inflate inflate_spec8) /\
    (forall {Espec: OracleKind}, semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec8).

(* ---------------------------------------------------------------------------------------------- *)
(* with Spec5's buffer sizes, RTHSpec's head_mem6 is a head_mem8                                  *)

Lemma head_mem6_8: forall L, hwf (l_h L) -> head_mem6 L |-- head_mem8 L.
Proof.
  intros L HW. unfold head_mem6, head_mem8.
  destruct (i_head (l_s L)); [ | apply derives_refl].
  cancel. apply orp_left.
  - apply orp_right1. apply orp_right1. apply andp_right; [apply prop_right; exact HW | apply derives_refl].
  - apply orp_right1. apply orp_right2. apply derives_refl.
Qed.

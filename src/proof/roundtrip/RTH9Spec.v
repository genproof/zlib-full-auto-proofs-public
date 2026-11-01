(* inflate() with an application gz_header whose absent fields stay undefined, fed in pieces of any uInt size
   (version 9 of the header spec).

   harness/rt_gzip_header.c gives inflateGetHeader a local `gz_header got` with malloc'ed buffers (every scalar
   field and buffer byte undefined until inflate writes it; buffers of up to 2^32 - 1 bytes), and then calls
   inflate(Z_FINISH) in a loop, each call offered the next piece of at most 2^32 - 1 bytes of the compressed
   stream.  The gzip header (a name and a comment of up to 2^32 - 2 bytes each) may then span several calls.
   RTH8Spec.inflate_spec8 has the header representation this starts from (RTH8Spec.istream8 with buffers of any
   uInt size; RTHSpec.head_rep6 in the header modes, RTH8Spec.head_rep8a after them) but asks for avail_in,
   avail_out <= 2^31 - 1 and for a call that starts in a header mode to pass the whole header (RTH8Spec.hd8_ok).
   [inflate_spec9] differs from it in four points:
   - avail_in and avail_out any uInt (as SpecW.inflate_specW);
   - a call may return in any mode, a header mode included (the header then stays head_rep6 with the bytes
     copied so far);
   - the header is always attached (i_head; the harness calls inflate only after inflateGetHeader returned Z_OK)
     and is held as [head_mem9]: head_rep6 in a header mode, head_rep8a after the header modes, or, after header
     modes left without passing them (a bad method, flags or header CRC: mode BAD; a zlib stream on a wrap 7
     stream: done = -1), the raw header of inflateGetHeader (RTHSpec.hraw6: only the pointer and size fields
     known).  The last case has done <> 1, so a header whose done is 1 after the header modes is head_rep8a.
     Spec5's defined head_rep is not a case: [head_mem8_9] turns inflateGetHeader_spec8's result (mode HEAD or
     FLAGS, done 0) into head_mem9;
   - as in SpecW, the live state carries InvW.swfW (the extra field's length in mode EXTRA and the bit buffer in
     mode EXLEN: what a wide input needs) before and after the call.
   The relation is Spec5's inflate_rel (the exact model run Model2.run2).

   [inflate_body9_stmt]: inflate_fast has SOME specification (calling convention cc_default) proved of its body,
   inflate()'s body is proved against [inflate_spec9] in Spec5's context with that specification for
   inflate_fast (RTH8Spec.Gprog_inflate8: Callees3's updatewindow_spec3 already takes any uInt length), and
   inflateGetHeader's body against RTH8Spec.inflateGetHeader_spec8. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.inflate.InvW.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the application's gz_header while inflate holds it *)
Definition head_mem9 (L: live) : mpred :=
  (!! (hdr_mode (i_mode (l_s L)) = true) &&
     head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) ||
   !! (hdr_mode (i_mode (l_s L)) = false) &&
     head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) ||
   !! (hdr_mode (i_mode (l_s L)) = false /\ h_done (l_h L) <> 1) &&
     hraw6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L)) *
  btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L)).

Definition head_opt9 (st: option live) : mpred :=
  match st with None => emp | Some L => head_mem9 L end.

(* a live state has the header attached and InvW.swfW *)
Definition hd9_ok (st: option live) : Prop :=
  match st with Some L => i_head (l_s L) = true /\ swfW (l_s L) | None => True end.

Definition inflate_spec9 :=
  DECLARE _inflate
  WITH gv: globals, shs: share, strmp: val, z: zfields, st: option live, ib: inbuf, inp: list Z,
       ob: option outbuf, flush: Z, gsh: share, tsh: share, itok: bool, otok: bool
  PRE [ tptr t_strm, tint ]
    PROP (Int.min_signed <= flush <= Int.max_signed; readable_share gsh; readable_share tsh;
          in_tok_ok itok ib; out_tok_ok otok ob;
          zf_ni z = in_ptr ib 0;
          match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end;
          match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end;
          hd9_ok st)
    PARAMS (strmp; Vint (Int.repr flush)) GLOBALS (gv)
    SEP (istream8_opt gv shs strmp z st; head_opt9 (is_live strmp st); bufs_opt (is_live strmp st) ib ob [] itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX z': zfields, EX st': option live, EX ow: list Z,
    PROP (inflate_rel flush strmp z st ib inp ob r z' st' ow; hd9_ok st')
    RETURN (Vint (Int.repr r))
    SEP (istream8_opt gv shs strmp z' st'; head_opt9 (is_live strmp st'); bufs_opt (is_live strmp st) ib ob ow itok otok;
         tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

Definition inflate_body9_stmt : Prop :=
  exists fast : funspec,
    callingconvention_of_funspec fast = cc_default /\
    (forall {Espec: OracleKind},
       semax_body Vprog_fast Gprog_fast Zlib.inffast.code.f_inflate_fast (_inflate_fast, fast)) /\
    (forall {Espec: OracleKind}, semax_body Vprog_inflate (Gprog_inflate8 fast) f_inflate inflate_spec9) /\
    (forall {Espec: OracleKind}, semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec8).

(* ---------------------------------------------------------------------------------------------- *)
(* from inflateGetHeader_spec8's result to head_mem9, and from head_mem9 to the passed header      *)

Lemma head_mem8_9: forall L,
  i_head (l_s L) = true -> i_mode (l_s L) = IM.HEAD \/ i_mode (l_s L) = IM.FLAGS -> h_done (l_h L) = 0 ->
  head_mem8 L |-- head_mem9 L.
Proof.
  intros L Hi Hm Hd. unfold head_mem8, head_mem9. rewrite Hi.
  assert (Hh : hdr_mode (i_mode (l_s L)) = true) by (destruct Hm as [E|E]; rewrite E; reflexivity).
  apply sepcon_derives; [apply sepcon_derives; [apply sepcon_derives|] |]; try apply derives_refl.
  apply orp_left; [apply orp_left|].
  - apply derives_extract_prop; intro HW.
    apply orp_right1; apply orp_right1. apply andp_right; [apply prop_right; exact Hh|].
    unfold head_rep6, head_rep6p, head_rep, hbuf_rep, hbuf6.
    assert (Hp : hph (l_s L) = 0) by (unfold hph; destruct Hm as [E|E]; rewrite E; reflexivity).
    assert (Hx : cx6 (l_s L) (l_h L) = 0) by (unfold cx6; destruct Hm as [E|E]; rewrite E; reflexivity).
    assert (Hn : cn6 (l_s L) (l_h L) = 0) by (unfold cn6; destruct Hm as [E|E]; rewrite E; reflexivity).
    assert (Hc : cc6 (l_s L) (l_h L) = 0) by (unfold cc6; destruct Hm as [E|E]; rewrite E; reflexivity).
    rewrite Hp, Hx, Hn, Hc.
    destruct HW as [_ _ _ _ _ _ _ _ [X _] [N _] [C _] _ _].
    Exists (zv (h_text (l_h L))) (lv (h_time (l_h L))) (zv (h_xflags (l_h L))) (zv (h_os (l_h L)))
           (zv (h_extra_len (l_h L))) (zv (h_hcrc (l_h L)))
           (byte_vals (h_xbuf (l_h L))) (byte_vals (h_nbuf (l_h L))) (byte_vals (h_cbuf (l_h L))).
    rewrite Hd. unfold bufok6, byte_vals. rewrite !Zlength_map, X, N, C. rewrite !sublist_nil.
    apply andp_right.
    + apply prop_right. unfold hinv6. destruct Hm as [E|E]; rewrite E; cbn; repeat split; try lia; discriminate.
    + entailer!.
  - apply derives_extract_prop; intro H.
    apply orp_right1; apply orp_right1. apply andp_right; [apply prop_right; exact H | apply derives_refl].
  - apply derives_extract_prop; intro H. rewrite Hh in H. discriminate.
Qed.

Lemma head_mem9_passed: forall L,
  hdr_mode (i_mode (l_s L)) = false -> h_done (l_h L) = 1 ->
  head_mem9 L |--
  head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) *
  btok (l_xb L) (h_extra_max (l_h L)) * btok (l_nb L) (h_name_max (l_h L)) * btok (l_cb L) (h_comm_max (l_h L)).
Proof.
  intros L Hm Hd. unfold head_mem9.
  apply sepcon_derives; [apply sepcon_derives; [apply sepcon_derives|] |]; try apply derives_refl.
  apply orp_left; [apply orp_left|].
  - apply derives_extract_prop; intro H. rewrite Hm in H. discriminate.
  - apply derives_extract_prop; intros _. apply derives_refl.
  - apply derives_extract_prop; intros [_ H]. contradiction.
Qed.

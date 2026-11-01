(* Law inflate_codes, main, the branch `op >= 24` (MainInf.v): the kit of its parts.
   - the stream struct at the law's compspecs (mi_tup), the call's buffers (mi_ib/mi_ob) and their moves;
   - the statements after the call: seg_inf_rest = A (the asserts up to the finality check) ; B ; C, with
     B = `if (r == Z_NEED_DICT) {...}` (MainInfB.v) and C = the updates of final/in_dict and pos += used
     (MainInfC.v); A in MainInfA.v;
   - the assertions between them (mi_pre_A, mi_pre_B, mi_post_C) and the facts they use (mi_facts). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts Zlib.proof.harness.inflate_codes.MainKit.
Require Import Zlib.harness.x_inflate_codes.code.

(* the stream at the law's compspecs *)
Definition mi_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma mi_strm_cs sh (v: mi_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition mi_tup (gv: globals) (z: zfields) (sp: val) : mi_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma mi_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (mi_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite mi_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma mi_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma mi_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Lemma mi_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (@data_at CS shs (Tstruct _z_stream_s noattr) (mi_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite mi_istream_unfold. entailer!. Qed.

Lemma mi_tup_set gv z sp ni ai no ao:
  mi_tup gv (set_zf_call z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (mi_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (mi_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* the call's input and output objects *)
Definition mi_ib (innull: Z) (ibp: val) (ain: Z) (c: list val) : inbuf :=
  if innull =? 0 then InNull else InBuf Ews ibp 0 ain c.
Definition mi_ob (outnull: Z) (obp: val) (aout: Z) (c: list val) : option outbuf :=
  if outnull =? 0 then None else Some (OutBuf Ews obp 0 aout c).
(* what the call does not take of them *)
Definition mi_rin (innull: Z) (ibp: val) (ain: Z) (c: list val) : mpred :=
  if innull =? 0 then (@data_at CS Ews (tarray tuchar ain) c ibp * @malloc_token CS Ews (tarray tuchar ain) ibp)%logic
  else emp.
Definition mi_rout (outnull: Z) (obp: val) (aout: Z) (c: list val) : mpred :=
  if outnull =? 0 then (@data_at CS Ews (tarray tuchar aout) c obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic
  else emp.

Lemma mi_in_ptr innull ibp ain c: isptr ibp ->
  in_ptr (mi_ib innull ibp ain c) 0 = (if innull =? 0 then nullval else ibp).
Proof.
  intros P. unfold mi_ib. destruct (innull =? 0); simpl; auto.
  destruct ibp; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma mi_ob_ptr outnull obp aout c: isptr obp ->
  ob_ptr (mi_ob outnull obp aout c) = (if outnull =? 0 then nullval else obp).
Proof.
  intros P. unfold mi_ob. destruct (outnull =? 0); simpl; auto.
  destruct obp; try contradiction. simpl. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma mi_bufs_pre L innull outnull ibp obp ain aout (ci co: list val):
  Zlength co = aout ->
  (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
   @data_at CS Ews (tarray tuchar aout) co obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic
  |-- (bufs_opt (Some L) (mi_ib innull ibp ain ci) (mi_ob outnull obp aout co) [] true true *
       mi_rin innull ibp ain ci * mi_rout outnull obp aout co)%logic.
Proof.
  intros Hc. unfold bufs_opt, mi_ib, mi_ob, mi_rin, mi_rout.
  rewrite <- (bytes_inflate_cs Ews ain ci ibp), <- (tok_inflate_cs Ews ain ibp),
          <- (bytes_inflate_cs Ews aout co obp), <- (tok_inflate_cs Ews aout obp).
  assert (Eo: sublist 0 0 co ++ byte_vals [] ++ sublist (0 + Zlength (@nil Z)) aout co = co).
  { rewrite sublist_nil. simpl. rewrite sublist_same by lia. reflexivity. }
  destruct (innull =? 0), (outnull =? 0); unfold in_rep, out_opt, out_rep, in_tok, out_tok; rewrite ?Eo; cancel.
Qed.

Lemma mi_bufs_post L innull outnull ibp obp ain aout (ci co: list val) (ow: list Z):
  (bufs_opt (Some L) (mi_ib innull ibp ain ci) (mi_ob outnull obp aout co) ow true true *
   mi_rin innull ibp ain ci * mi_rout outnull obp aout co)%logic
  |-- EX cont: list val,
      (@data_at CS Ews (tarray tuchar ain) ci ibp * @malloc_token CS Ews (tarray tuchar ain) ibp *
       @data_at CS Ews (tarray tuchar aout) cont obp * @malloc_token CS Ews (tarray tuchar aout) obp)%logic.
Proof.
  unfold bufs_opt, mi_ib, mi_ob, mi_rin, mi_rout.
  set (X := sublist 0 0 co ++ byte_vals ow ++ sublist (0 + Zlength ow) aout co).
  destruct (innull =? 0), (outnull =? 0); unfold in_rep, out_opt, out_rep, in_tok, out_tok; fold X.
  - Exists co. cancel.
  - rewrite (bytes_inflate_cs Ews aout X obp), (tok_inflate_cs Ews aout obp). Exists X. cancel.
  - rewrite (bytes_inflate_cs Ews ain ci ibp), (tok_inflate_cs Ews ain ibp). Exists co. cancel.
  - rewrite (bytes_inflate_cs Ews aout X obp), (tok_inflate_cs Ews aout obp),
            (bytes_inflate_cs Ews ain ci ibp), (tok_inflate_cs Ews ain ibp). Exists X. cancel.
Qed.

Ltac eqz := first [reflexivity | match goal with |- context [?x =? 0] => destruct (Z.eqb_spec x 0); try lia; reflexivity end].


(* ---------------------------------------------------------------------------------------------- *)
(* The statements after the call r = inflate(&s, flush)                                            *)

Definition seg_inf_rest : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [sub_stmt seg_inflate] in (sub_stmt [1;1;1;1;1]%nat seg_inflate) in
        exact x).
Definition seg_inf_BC : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [sub_stmt seg_inf_rest] in
          (sub_stmt [1;1;1;1;1;1;1;1;1;1]%nat seg_inf_rest) in exact x).
Definition seg_inf_B : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [sub_stmt seg_inf_BC] in (sub_stmt [0]%nat seg_inf_BC) in exact x).
Definition seg_inf_C : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [sub_stmt seg_inf_BC] in (sub_stmt [1]%nat seg_inf_BC) in exact x).

Lemma seg_inf_BC_eq : seg_inf_BC = Ssequence seg_inf_B seg_inf_C.
Proof. reflexivity. Qed.

(* the harness's badptr *)
Definition mi_bad (innull outnull ain: Z) : bool := (outnull =? 0) || ((innull =? 0) && negb (ain =? 0)).

Lemma mi_badptr innull outnull ibp obp ain aout ci co:
  badptr (mi_ib innull ibp ain ci) (mi_ob outnull obp aout co) ain = mi_bad innull outnull ain.
Proof. unfold badptr, mi_ib, mi_ob, mi_bad. destruct (innull =? 0), (outnull =? 0); reflexivity. Qed.

(* what the parts know: the ranges of the harness's variables and inflate_post's checks (w/o the invariant);
   z' the stream fields after the call *)
Definition mi_facts (w: Z) (src: list Z) (pos final indict ain aout flush innull outnull r: Z) (z': zfields)
    : Prop :=
  let bad := mi_bad innull outnull ain in
  let used := ain - zf_ai z' in
  let made := aout - zf_ao z' in
  Int.min_signed <= w <= Int.max_signed /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ Zlength src <= 2 ^ 24 /\ is_bytes src /\
  0 <= aout <= 2 ^ 20 /\ Int.min_signed <= flush <= Int.max_signed /\
  0 <= innull <= 255 /\ 0 <= outnull <= 255 /\
  (final = Z_OK \/ final = Z_STREAM_END \/ final = Z_DATA_ERROR \/ final = Z_MEM_ERROR) /\
  (indict = 0 \/ indict = 1) /\ zf_ok z' /\
  code_okb r = true /\
  0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\
  (r = Z_STREAM_ERROR <-> bad = true) /\
  (r = Z_OK -> (used <> 0 \/ made <> 0) /\ flush <> Z_FINISH) /\
  (r = Z_BUF_ERROR -> (used = 0 /\ made = 0) \/ flush = Z_FINISH) /\
  (r = Z_DATA_ERROR -> zf_msg z' <> None) /\
  (bad = false -> final <> Z_OK -> r = final /\ used = 0 /\ made = 0) /\
  (r = Z_NEED_DICT ->
     zlib_okb w = true /\ pos + used = 6 /\ Z.land (Znth 1 src) 32 <> 0 /\
     zf_adler z' = be32 (sublist 2 6 src) /\ (indict <> 0 -> used = 0 /\ made = 0)).

(* right after the call (sp: strm->state; Rest: the memory the parts do not touch) *)
Definition mi_pre_A (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z) (pos final indict: Z)
    (ain aout flush innull outnull stop: Z) (ibp obp: val) (r: Z) (z': zfields) (sp: val) (Rest: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r));
         temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _in_null (Vint (Int.repr innull)); temp _out_null (Vint (Int.repr outnull));
         temp _ain (Vint (Int.repr ain));
         temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
         temp _in_dict (Vint (Int.repr indict));
         temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (data_at Tsh (Tstruct _z_stream_s noattr) (mi_tup gv z' sp) vs; msg_lits gv;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp; Rest).

(* before B (and after it), before C: used = ain - zf_ai z', made = aout - zf_ao z', badptr computed *)
Definition mi_pre_B (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z) (pos final indict: Z)
    (ain aout innull outnull stop: Z) (ibp obp: val) (r: Z) (z': zfields) (sp: val) (Rest: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r));
         temp _used (Vint (Int.repr (ain - zf_ai z'))); temp _made (Vint (Int.repr (aout - zf_ao z')));
         temp _badptr (Vint (Int.repr (if mi_bad innull outnull ain then 1 else 0)));
         temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
         temp _in_dict (Vint (Int.repr indict));
         temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (data_at Tsh (Tstruct _z_stream_s noattr) (mi_tup gv z' sp) vs; msg_lits gv;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp; Rest).

(* after C: the harness's variables updated *)
Definition mi_post_C (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z) (pos final indict: Z)
    (stop: Z) (ibp obp: val) (z': zfields) (sp: val) (Rest: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
         temp _in_dict (Vint (Int.repr indict));
         temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (data_at Tsh (Tstruct _z_stream_s noattr) (mi_tup gv z' sp) vs; msg_lits gv;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp; Rest).

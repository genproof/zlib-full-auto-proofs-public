(* Law inflate_header, main (IHMain.v): the kit shared by the segment lemmas of main's proof (as
   inflate_check/IKMainKit.v and inflate_codes/MainKit.v).
   - Delta_m (main's type context), POST_m (main's postcondition after start_function), POST_b (the
     postcondition of main's body b0, which always ends by a return);
   - the segments of f_main's body: b0 (all of it but the final `return 0`), its suffixes seg_24 (from
     nondet_bytes(xf, xlen)), seg_53 (from stream_defaults(&s)), seg_75 (from the loop), seg_76 (inflateEnd(&s);
     return 0); the loop body seg_loop (after its leading Sskip) and its suffixes segL10 (the stores into s),
     segL18 (`if (reserved || badcrc) ...`), segL20 (`if (h.done != 0) {...}`), segL21 (`if (r == Z_STREAM_END)
     {...}` and the frees);
   - the assertions at the segments' boundaries and their facts;
   - moves of byte arrays, malloc tokens, struct z_stream and struct gz_header between the units' compspecs
     and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the postcondition of b0 (main's body is Ssequence b0 (return 0); b0 itself always returns) *)
Definition POST_b : ret_assert := overridePost FF POST_m.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

Fixpoint ih_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => ih_drop n' b
  | _, _ => Sskip
  end.

Definition ih_first (s: statement) : statement := match s with Ssequence a _ => a | _ => Sskip end.
Definition ih_second (s: statement) : statement := match s with Ssequence _ b => b | _ => Sskip end.
(* the body of `for (;;) { body }` at the head of a statement: Ssequence (Sloop (Ssequence Sskip body) Sskip) _ *)
Definition ih_loop_body (s: statement) : statement :=
  match s with Ssequence (Sloop (Ssequence Sskip x) _) _ => x | _ => Sskip end.

Ltac ih_seg t :=
  let x := eval cbv beta iota zeta delta [ih_drop ih_first ih_second ih_loop_body f_main fn_body] in t in exact x.

(* main's body without its final `return 0` (78 statements; numbers below are 0-based positions in it) *)
Definition b0 : statement := ltac:(ih_seg (ih_first (fn_body f_main))).
Definition b0_ret : statement := ltac:(ih_seg (ih_second (fn_body f_main))).
(* from nondet_bytes(xf, xlen) *)
Definition seg_24 : statement := ltac:(ih_seg (ih_drop 24 (ih_first (fn_body f_main)))).
(* from stream_defaults(&s) *)
Definition seg_53 : statement := ltac:(ih_seg (ih_drop 53 (ih_first (fn_body f_main)))).
(* from the loop: Ssequence (Sloop ..) (Ssequence inflateEnd(&s) (return 0)) *)
Definition seg_75 : statement := ltac:(ih_seg (ih_drop 75 (ih_first (fn_body f_main)))).
(* inflateEnd(&s); return 0 *)
Definition seg_76 : statement := ltac:(ih_seg (ih_drop 76 (ih_first (fn_body f_main)))).
(* the loop body (26 statements) *)
Definition seg_loop : statement := ltac:(ih_seg (ih_loop_body (ih_drop 75 (ih_first (fn_body f_main))))).
(* from s.next_in = ib *)
Definition segL10 : statement := ltac:(ih_seg (ih_drop 10 (ih_loop_body (ih_drop 75 (ih_first (fn_body f_main)))))).
(* from if (reserved || badcrc) gp_assert(r != Z_STREAM_END); else gp_assert(r != Z_DATA_ERROR); *)
Definition segL18 : statement := ltac:(ih_seg (ih_drop 18 (ih_loop_body (ih_drop 75 (ih_first (fn_body f_main)))))).
(* from if (h.done != 0) { ... } *)
Definition segL20 : statement := ltac:(ih_seg (ih_drop 20 (ih_loop_body (ih_drop 75 (ih_first (fn_body f_main)))))).
(* from if (r == Z_STREAM_END) { ... }, then free(ib); free(ob); free(osnap); if (stop == 0) break; *)
Definition segL21 : statement := ltac:(ih_seg (ih_drop 21 (ih_loop_body (ih_drop 75 (ih_first (fn_body f_main)))))).

Lemma ih_body_eq: fn_body f_main = Ssequence b0 b0_ret.
Proof. reflexivity. Qed.
Lemma ih_seg75_eq: seg_75 = Ssequence (Sloop (Ssequence Sskip seg_loop) Sskip) seg_76.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Lemma ih_bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_bytes_crc_cs sh n (v: list val) q:
  @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_crc32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma ih_tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ih_ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ih_ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Definition ih_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma ih_strm_cs sh (v: ih_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition ih_strm_undef : ih_strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma ih_strm_undef_cs sh q:
  @data_at_ CS sh (Tstruct _z_stream_s noattr) q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm ih_strm_undef q.
Proof. unfold data_at_. rewrite ih_strm_cs. reflexivity. Qed.

Lemma ih_strm_to_undef sh (v: ih_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh (Tstruct _z_stream_s noattr) q.
Proof. rewrite ih_strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

Lemma ih_istream_to_undef gv vs z st:
  istream gv Tsh vs z st |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - sep_apply ih_strm_to_undef. cancel.
  - sep_apply ih_strm_to_undef. cancel.
Qed.

(* the stream at the law's compspecs *)
Definition ih_tup (gv: globals) (z: zfields) (sp: val) : ih_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma ih_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (ih_tup gv z (l_sp L)) vs * state_mem gv vs L).
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite ih_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma ih_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs (Tstruct _z_stream_s noattr) (ih_tup gv z (l_sp L)) vs * state_mem gv vs L
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite ih_istream_unfold. entailer!. Qed.

Lemma ih_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ih_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ih_tup_set gv z sp ni ai no ao:
  ih_tup gv (ih_zcall z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (ih_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (ih_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* struct gz_header *)
Definition ih_head_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val))))))))))))%type.

Lemma ih_head_cs sh (v: ih_head_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_head v q = @data_at CS sh (Tstruct _gz_header_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* the gz_header's fields as main sees them (head_rep of Rep.v) *)
Definition ih_htup (xb nb cb: val) (h: hstate) : ih_head_tuple :=
  (Vint (Int.repr (h_text h)), (Vlong (Int64.repr (h_time h)), (Vint (Int.repr (h_xflags h)),
   (Vint (Int.repr (h_os h)),
   ((if h_xp h then xb else nullval), (Vint (Int.repr (h_extra_len h)), (Vint (Int.repr (h_extra_max h)),
   ((if h_np h then nb else nullval), (Vint (Int.repr (h_name_max h)),
   ((if h_cp h then cb else nullval), (Vint (Int.repr (h_comm_max h)), (Vint (Int.repr (h_hcrc h)),
    Vint (Int.repr (h_done h)))))))))))))).

(* a header buffer as main sees it: nothing for Z_NULL, else the max bytes cont *)
Definition ih_hbuf (b: val) (max: Z) (cont: list Z) : mpred :=
  if eq_dec b nullval then emp else @data_at CS Ews (tarray tuchar max) (bytes_rep cont) b.

Lemma ih_head_rep_eq hsh headp xb nb cb h:
  head_rep hsh headp xb nb cb h =
  @data_at CS hsh (Tstruct _gz_header_s noattr) (ih_htup xb nb cb h) headp *
  ih_hbuf xb (h_extra_max h) (h_xbuf h) * ih_hbuf nb (h_name_max h) (h_nbuf h) *
  ih_hbuf cb (h_comm_max h) (h_cbuf h).
Proof.
  unfold head_rep, hbuf_rep, ih_hbuf. rewrite ih_head_cs.
  rewrite !ih_bytes_inflate_cs. reflexivity.
Qed.

(* the token of a zero-size header buffer (btok, at the law's CS) *)
Definition ih_btok (b: val) (n: Z) : mpred :=
  if eq_dec b nullval then emp else if zeq n 0 then @malloc_token CS Ews (tarray tuchar 0) b else emp.

Lemma ih_btok_eq b n: btok b n = ih_btok b n.
Proof. unfold btok, ih_btok. rewrite ih_tok_inflate_cs. reflexivity. Qed.

Lemma ih_head_mem_eq L:
  i_head (l_s L) = true ->
  head_mem L =
  @data_at CS (l_hsh L) (Tstruct _gz_header_s noattr) (ih_htup (l_xb L) (l_nb L) (l_cb L) (l_h L)) (l_headp L) *
  ih_hbuf (l_xb L) (h_extra_max (l_h L)) (h_xbuf (l_h L)) * ih_hbuf (l_nb L) (h_name_max (l_h L)) (h_nbuf (l_h L)) *
  ih_hbuf (l_cb L) (h_comm_max (l_h L)) (h_cbuf (l_h L)) *
  ih_btok (l_xb L) (h_extra_max (l_h L)) * ih_btok (l_nb L) (h_name_max (l_h L)) *
  ih_btok (l_cb L) (h_comm_max (l_h L)).
Proof. intros E. unfold head_mem. rewrite E, ih_head_rep_eq, !ih_btok_eq. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The ghost values of main                                                                       *)

(* the addresses of main's local variables s, h, xs, ns, cs, osnap *)
Record ihv := IHV { v_s_: val; v_h_: val; v_xs_: val; v_ns_: val; v_cs_: val; v_osn_: val }.

(* the header numbers drawn (FLG, MTIME, XFL, OS, XLEN, the name and comment lengths, delta) *)
Record ihn := IHN { n_flg: Z; n_mtime: Z; n_xfl: Z; n_os: Z; n_xlen: Z; n_nl: Z; n_cl: Z; n_delta: Z }.

(* the other draws: windowBits, the buffer maxima, the "not Z_NULL" bytes of the header buffers *)
Record ihb := IHB { b_w: Z; b_xmax: Z; b_nmax: Z; b_cmax: Z; b_xnul: Z; b_nnul: Z; b_cnul: Z }.

(* the malloc'ed objects src, xf, nf, cf *)
Record ihp := IHP { p_src: val; p_xf: val; p_nf: val; p_cf: val }.

(* the header buffers given to inflateGetHeader (Z_NULL or exactly their maxima) and their snapshots *)
Record ihh := IHH { h_xb: val; h_nb: val; h_cb: val; h_xq: val; h_nq: val; h_cq: val }.

Definition flb (flg bit: Z) : bool := negb (Z.land flg bit =? 0).

Definition ih_num (g: ihg) : ihn :=
  IHN (g_flg g) (g_mtime g) (g_xfl g) (g_os g) (Zlength (g_xf g)) (Zlength (g_nf g)) (Zlength (g_cf g)) (g_delta g).

(* hlen and total of the harness *)
Definition n_hlen (n: ihn) : Z :=
  10 + (if flb (n_flg n) 4 then 2 + n_xlen n else 0) + (if flb (n_flg n) 8 then n_nl n + 1 else 0) +
  (if flb (n_flg n) 16 then n_cl n + 1 else 0).
Definition n_total (n: ihn) : Z := n_hlen n + (if flb (n_flg n) 2 then 2 else 0) + 13.

Definition b2z (b: bool) : Z := if b then 1 else 0.

(* ---------------------------------------------------------------------------------------------- *)
(* Before the body (after start_function, R unfolded, zfuncs gathered)                             *)

Definition ih_pre0 (gv: globals) (V: ihv) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; ih_hversion_lit gv;
       data_at_ Tsh (Tstruct _z_stream_s noattr) (v_s_ V); data_at_ Tsh (Tstruct _gz_header_s noattr) (v_h_ V);
       data_at_ Tsh (tptr tuchar) (v_xs_ V); data_at_ Tsh (tptr tuchar) (v_ns_ V);
       data_at_ Tsh (tptr tuchar) (v_cs_ V); data_at_ Tsh (tptr tuchar) (v_osn_ V)).

(* ---------------------------------------------------------------------------------------------- *)
(* Position 24: after the draws, the assumptions, hlen, total, the four malloc()s and their null check *)

Definition ih_f24 (n: ihn) (b: ihb) (P: ihp) : Prop :=
  0 <= n_flg n <= 255 /\ 0 <= n_mtime n < 2 ^ 32 /\ 0 <= n_xfl n <= 255 /\ 0 <= n_os n <= 255 /\
  0 <= n_xlen n <= 65535 /\ 0 <= n_nl n <= 2 ^ 16 /\ 0 <= n_cl n <= 2 ^ 16 /\ 0 <= n_delta n < 2 ^ 32 /\
  Int.min_signed <= b_w b <= Int.max_signed /\
  0 <= b_xmax b <= 2 ^ 16 /\ 0 <= b_nmax b <= 2 ^ 16 /\ 0 <= b_cmax b <= 2 ^ 16 /\
  0 <= b_xnul b <= 255 /\ 0 <= b_nnul b <= 255 /\ 0 <= b_cnul b <= 255 /\
  isptr (p_src P) /\ isptr (p_xf P) /\ isptr (p_nf P) /\ isptr (p_cf P).

Definition ih_s24 (gv: globals) (V: ihv) (n: ihn) (b: ihb) (P: ihp) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (n_flg n)));
         temp _mtime (Vlong (Int64.repr (n_mtime n))); temp _xfl (Vint (Int.repr (n_xfl n)));
         temp _os (Vint (Int.repr (n_os n))); temp _xlen (Vint (Int.repr (n_xlen n)));
         temp _nl (Vint (Int.repr (n_nl n))); temp _cl (Vint (Int.repr (n_cl n)));
         temp _delta (Vint (Int.repr (n_delta n)));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _hlen (Vint (Int.repr (n_hlen n))); temp _total (Vint (Int.repr (n_total n)));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; ih_hversion_lit gv;
       data_at_ Tsh (Tstruct _z_stream_s noattr) (v_s_ V); data_at_ Tsh (Tstruct _gz_header_s noattr) (v_h_ V);
       data_at_ Tsh (tptr tuchar) (v_xs_ V); data_at_ Tsh (tptr tuchar) (v_ns_ V);
       data_at_ Tsh (tptr tuchar) (v_cs_ V); data_at_ Tsh (tptr tuchar) (v_osn_ V);
       malloc_token Ews (tarray tuchar (n_total n)) (p_src P);
       data_at_ Ews (tarray tuchar (n_total n)) (p_src P);
       malloc_token Ews (tarray tuchar (n_xlen n)) (p_xf P); data_at_ Ews (tarray tuchar (n_xlen n)) (p_xf P);
       malloc_token Ews (tarray tuchar (n_nl n + 1)) (p_nf P); data_at_ Ews (tarray tuchar (n_nl n + 1)) (p_nf P);
       malloc_token Ews (tarray tuchar (n_cl n + 1)) (p_cf P); data_at_ Ews (tarray tuchar (n_cl n + 1)) (p_cf P)).

(* ---------------------------------------------------------------------------------------------- *)
(* Position 53: the member src = ih_src g built, xf, nf, cf filled, reserved and badcrc computed  *)

Definition ih_f53 (g: ihg) (b: ihb) (P: ihp) : Prop :=
  ih_ok g /\
  Int.min_signed <= b_w b <= Int.max_signed /\
  0 <= b_xmax b <= 2 ^ 16 /\ 0 <= b_nmax b <= 2 ^ 16 /\ 0 <= b_cmax b <= 2 ^ 16 /\
  0 <= b_xnul b <= 255 /\ 0 <= b_nnul b <= 255 /\ 0 <= b_cnul b <= 255 /\
  isptr (p_src P) /\ isptr (p_xf P) /\ isptr (p_nf P) /\ isptr (p_cf P).

Definition ih_s53 (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; ih_hversion_lit gv;
       data_at_ Tsh (Tstruct _z_stream_s noattr) (v_s_ V); data_at_ Tsh (Tstruct _gz_header_s noattr) (v_h_ V);
       data_at_ Tsh (tptr tuchar) (v_xs_ V); data_at_ Tsh (tptr tuchar) (v_ns_ V);
       data_at_ Tsh (tptr tuchar) (v_cs_ V); data_at_ Tsh (tptr tuchar) (v_osn_ V);
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P)).

(* ---------------------------------------------------------------------------------------------- *)
(* The loop                                                                                       *)

(* a header buffer's memory outside the stream: its snapshot q (the buffer's first contents bs) and the
   malloc token of a non-empty buffer (head_mem holds the token of an empty one: btok) *)
Definition ih_hrest (bp q: val) (max: Z) (bs: list Z) : mpred :=
  if eq_dec bp nullval then emp else
    (malloc_token Ews (tarray tuchar max) q * data_at Ews (tarray tuchar max) (bytes_rep bs) q *
     (if zeq max 0 then emp else malloc_token Ews (tarray tuchar max) bp)).

(* the facts that hold in the whole loop; h0: the gz_header given to inflateGetHeader *)
Definition ih_glob (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) (g: ihg) (b: ihb) (P: ihp)
    (h0: hstate) (H: ihh) : Prop :=
  ih_facts I /\ ih_f53 g b P /\ wbits_ok (b_w b) = true /\ 16 <= b_w b /\
  hwf h0 /\ h_extra_max h0 = b_xmax b /\ h_name_max h0 = b_nmax b /\ h_comm_max h0 = b_cmax b /\
  h_xp h0 = negb (b_xnul b =? 0) /\ h_np h0 = negb (b_nnul b =? 0) /\ h_cp h0 = negb (b_cnul b =? 0) /\
  (b_xnul b = 0 -> h_xb H = nullval /\ h_xq H = nullval) /\ (b_xnul b <> 0 -> isptr (h_xb H) /\ isptr (h_xq H)) /\
  (b_nnul b = 0 -> h_nb H = nullval /\ h_nq H = nullval) /\ (b_nnul b <> 0 -> isptr (h_nb H) /\ isptr (h_nq H)) /\
  (b_cnul b = 0 -> h_cb H = nullval /\ h_cq H = nullval) /\ (b_cnul b <> 0 -> isptr (h_cb H) /\ isptr (h_cq H)).

(* the live part keeps main's gz_header and its buffers *)
Definition ih_Lok (V: ihv) (H: ihh) (L: live) : Prop :=
  l_headp L = v_h_ V /\ l_hsh L = Tsh /\ l_xb L = h_xb H /\ l_nb L = h_nb H /\ l_cb L = h_cb H.

(* the loop invariant's assertion for given pos, z, L (its PROP part is in the hypotheses); Fr: the rest of
   the memory (the version literals) *)
Definition ih_at (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) (h0: hstate) (H: ihh) (Fr: mpred)
    (pos: Z) (z: zfields) (L: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         temp _pos (Vint (Int.repr pos));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (istream gv Tsh (v_s_ V) z (Some L); head_mem L;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P);
       data_at Tsh (tptr tuchar) (h_xq H) (v_xs_ V); data_at Tsh (tptr tuchar) (h_nq H) (v_ns_ V);
       data_at Tsh (tptr tuchar) (h_cq H) (v_cs_ V);
       ih_hrest (h_xb H) (h_xq H) (b_xmax b) (h_xbuf h0); ih_hrest (h_nb H) (h_nq H) (b_nmax b) (h_nbuf h0);
       ih_hrest (h_cb H) (h_cq H) (b_cmax b) (h_cbuf h0);
       data_at_ Tsh (tptr tuchar) (v_osn_ V); Fr).

(* the loop invariant *)
Definition ih_inv (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) (gv: globals) (V: ihv) (g: ihg)
    (b: ihb) (P: ihp) (h0: hstate) (H: ihh) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX z: zfields, EX L: live,
  !! (I g (b_w b) h0 pos z L /\ 0 <= pos <= Zlength (ih_src g) /\ ih_Lok V H L) &&
  ih_at gv V g b P h0 H Fr pos z L.

(* the postcondition of the loop body (Inv: the loop invariant) *)
Definition ih_PL (Inv: environ -> mpred) : ret_assert :=
  loop_nocontinue_ret_assert Inv (overridePost Inv POST_b).

(* position L10 (after the null check of ib / ob, before the stores into s): ib = exact_copy of
   src[pos .. pos + ain), ob = a new object of aout bytes bs, osnap = q (the copy of bs) *)
Definition ih_buf (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) (h0: hstate) (H: ihh) (Fr: mpred)
    (pos: Z) (z: zfields) (L: live) (ain aout flush stop: Z) (ibp obp q: val) (bs: list Z)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush)); temp _stop (Vint (Int.repr stop));
         temp _ain (Vint (Int.repr ain)); temp _ib ibp; temp _ob obp;
         temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         temp _pos (Vint (Int.repr pos));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (istream gv Tsh (v_s_ V) z (Some L); head_mem L;
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P);
       data_at Tsh (tptr tuchar) (h_xq H) (v_xs_ V); data_at Tsh (tptr tuchar) (h_nq H) (v_ns_ V);
       data_at Tsh (tptr tuchar) (h_cq H) (v_cs_ V);
       ih_hrest (h_xb H) (h_xq H) (b_xmax b) (h_xbuf h0); ih_hrest (h_nb H) (h_nq H) (b_nmax b) (h_nbuf h0);
       ih_hrest (h_cb H) (h_cq H) (b_cmax b) (h_cbuf h0);
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) (ih_src g))) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep bs) obp;
       data_at Tsh (tptr tuchar) q (v_osn_ V);
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
       Fr).

Definition ih_buf_facts (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) (V: ihv) (g: ihg) (b: ihb)
    (P: ihp) (h0: hstate) (H: ihh) (pos: Z) (z: zfields) (L: live) (ain aout flush stop: Z) (ibp obp q: val)
    (bs: list Z) : Prop :=
  ih_glob I g b P h0 H /\ I g (b_w b) h0 pos z L /\ ih_Lok V H L /\ 0 <= pos /\
  0 <= ain /\ pos + ain <= Zlength (ih_src g) /\ 0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ is_bytes bs /\
  Int.min_signed <= flush <= Int.max_signed /\ 0 <= stop <= 255 /\ isptr ibp /\ isptr obp /\ isptr q.

(* positions L18 .. L21 (after `pos += ain - s.avail_in`): r the code inflate() returned (not Z_MEM_ERROR),
   pos' the new pos, the stream (z', L'), cont the output object's contents *)
Definition ih_mid (gv: globals) (V: ihv) (g: ihg) (b: ihb) (P: ihp) (h0: hstate) (H: ihh) (Fr: mpred)
    (pos' r: Z) (z': zfields) (L': live) (ain aout stop: Z) (ibp obp q: val) (inb cont: list val) (bs: list Z)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r)); temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         temp _wbits (Vint (Int.repr (b_w b))); temp _flg (Vint (Int.repr (g_flg g)));
         temp _mtime (Vlong (Int64.repr (g_mtime g))); temp _xfl (Vint (Int.repr (g_xfl g)));
         temp _os (Vint (Int.repr (g_os g))); temp _xlen (Vint (Int.repr (Zlength (g_xf g))));
         temp _nl (Vint (Int.repr (Zlength (g_nf g)))); temp _cl (Vint (Int.repr (Zlength (g_cf g))));
         temp _xmax (Vint (Int.repr (b_xmax b))); temp _nmax (Vint (Int.repr (b_nmax b)));
         temp _cmax (Vint (Int.repr (b_cmax b)));
         temp _xnul (Vint (Int.repr (b_xnul b))); temp _nnul (Vint (Int.repr (b_nnul b)));
         temp _cnul (Vint (Int.repr (b_cnul b)));
         temp _total (Vint (Int.repr (Zlength (ih_src g))));
         temp _src (p_src P); temp _xf (p_xf P); temp _nf (p_nf P); temp _cf (p_cf P);
         temp _reserved (Vint (Int.repr (b2z (ih_reserved g)))); temp _badcrc (Vint (Int.repr (b2z (ih_badcrc g))));
         temp _pos (Vint (Int.repr pos'));
         lvar _s (Tstruct _z_stream_s noattr) (v_s_ V); lvar _h (Tstruct _gz_header_s noattr) (v_h_ V);
         lvar _xs (tptr tuchar) (v_xs_ V); lvar _ns (tptr tuchar) (v_ns_ V); lvar _cs (tptr tuchar) (v_cs_ V);
         lvar _osnap (tptr tuchar) (v_osn_ V); gvars gv)
  SEP (istream gv Tsh (v_s_ V) z' (Some L'); head_mem L';
       mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (ih_src g))) (p_src P);
       data_at Ews (tarray tuchar (Zlength (ih_src g))) (bytes_rep (ih_src g)) (p_src P);
       malloc_token Ews (tarray tuchar (Zlength (g_xf g))) (p_xf P);
       data_at Ews (tarray tuchar (Zlength (g_xf g))) (bytes_rep (g_xf g)) (p_xf P);
       malloc_token Ews (tarray tuchar (Zlength (g_nf g) + 1)) (p_nf P);
       data_at Ews (tarray tuchar (Zlength (g_nf g) + 1)) (bytes_rep (g_nf g ++ [0])) (p_nf P);
       malloc_token Ews (tarray tuchar (Zlength (g_cf g) + 1)) (p_cf P);
       data_at Ews (tarray tuchar (Zlength (g_cf g) + 1)) (bytes_rep (g_cf g ++ [0])) (p_cf P);
       data_at Tsh (tptr tuchar) (h_xq H) (v_xs_ V); data_at Tsh (tptr tuchar) (h_nq H) (v_ns_ V);
       data_at Tsh (tptr tuchar) (h_cq H) (v_cs_ V);
       ih_hrest (h_xb H) (h_xq H) (b_xmax b) (h_xbuf h0); ih_hrest (h_nb H) (h_nq H) (b_nmax b) (h_nbuf h0);
       ih_hrest (h_cb H) (h_cq H) (b_cmax b) (h_cbuf h0);
       malloc_token Ews (tarray tuchar ain) ibp; data_at Ews (tarray tuchar ain) inb ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) cont obp;
       data_at Tsh (tptr tuchar) q (v_osn_ V);
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
       Fr).

(* what holds at L18 .. L21: the checks' facts (ih_post for the call that started at pos, offered ain bytes),
   the invariant at pos' *)
Definition ih_mid_facts (I: ihg -> Z -> hstate -> Z -> zfields -> live -> Prop) (V: ihv) (g: ihg) (b: ihb)
    (P: ihp) (h0: hstate) (H: ihh) (pos pos' ain r: Z) (z': zfields) (L': live) (aout stop: Z)
    (ibp obp q: val) (inb cont: list val) (bs: list Z) : Prop :=
  ih_glob I g b P h0 H /\ ih_post I g (b_w b) h0 pos ain r z' L' /\ r <> Z_MEM_ERROR /\
  pos' = pos + (ain - zf_ai z') /\ 0 <= pos /\ pos + ain <= Zlength (ih_src g) /\
  zf_ok z' /\ live_ok L' /\ ih_Lok V H L' /\
  0 <= ain /\ 0 <= aout <= 2 ^ 20 /\ Zlength inb = ain /\ Zlength cont = aout /\ Zlength bs = aout /\
  0 <= stop <= 255 /\ isptr ibp /\ isptr obp /\ isptr q.

(* the local variable h's memory, out of the gz_header the stream holds *)
Lemma ih_head_mem_undef L vh:
  i_head (l_s L) = true -> l_headp L = vh -> l_hsh L = Tsh ->
  head_mem L |-- data_at_ Tsh (Tstruct _gz_header_s noattr) vh * TT.
Proof.
  intros E Hp Hs. rewrite ih_head_mem_eq by auto. rewrite Hp, Hs.
  sep_apply (data_at_data_at_ Tsh (Tstruct _gz_header_s noattr)). cancel.
Qed.

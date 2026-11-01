(* Law inflate_dict, main, the inflate half (ITMainInf.v): the kit shared by its part lemmas (as
   inflate_codes/MainKit.v, MainInfKit.v, MainHelp.v; inflate_check/IKMainKit.v).
   - the segments of seg_inf (ITMainKit.v): seg_loop (the body of the loop of inflate() calls, after its leading
     Sskip), seg_tail (after the loop) and the suffixes of seg_loop: seg_L1 (from the stores into s before
     inflate()), seg_L2 (from `if (r == Z_NEED_DICT) ... else ...`), seg_L3 (from the inflateGetDictionary checks
     `if (dict_set && (r != Z_STREAM_END || !zlib)) {...}`), seg_L4 (from the three free()s);
   - the assertions at their boundaries: it_at (the loop body's entry), it_buf (after the null check of ib / ob),
     it_mid (after `pos += ain - s.avail_in`), it_mid2 (after the Z_NEED_DICT / else branch); the loop invariant
     it_inv and the loop's break assertion it_brk; it_PL (the body's postcondition);
   - their facts (it_glob: everywhere; it_buf_facts, it_mid_facts, it_mid2_facts);
   - moves of byte arrays, malloc tokens, pointers and struct z_stream between the units' compspecs and the law's.
   The part lemmas are continuation-passing: each proves its segment from its entry assertion, given ANY proof of
   the next segment from the next entry assertion. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of seg_inf                                                                       *)

Fixpoint it_sub (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => it_sub pth a
  | S _ :: pth, Ssequence _ b => it_sub pth b
  | O :: pth, Sifthenelse _ a _ => it_sub pth a
  | S _ :: pth, Sifthenelse _ _ b => it_sub pth b
  | O :: pth, Sloop a _ => it_sub pth a
  | S _ :: pth, Sloop _ b => it_sub pth b
  | _, _ => Sskip
  end.

Definition it_opt_or {A} (x y: option A) : option A := match x with Some _ => x | None => y end.
Definition it_opt_cons {A} (k: A) (x: option (list A)) : option (list A) :=
  match x with Some l => Some (k :: l) | None => None end.

(* the path of the first `Ssequence (Sloop _ _) _` *)
Fixpoint it_find_loop (s: statement) : option (list nat) :=
  match s with
  | Ssequence (Sloop _ _) _ => Some nil
  | Ssequence a b => it_opt_or (it_opt_cons O (it_find_loop a)) (it_opt_cons 1%nat (it_find_loop b))
  | Sifthenelse _ a b => it_opt_or (it_opt_cons O (it_find_loop a)) (it_opt_cons 1%nat (it_find_loop b))
  | Sloop a b => it_opt_or (it_opt_cons O (it_find_loop a)) (it_opt_cons 1%nat (it_find_loop b))
  | _ => None
  end.

(* drop the first n statements of a chain Ssequence s1 (Ssequence s2 ...) *)
Fixpoint it_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => it_drop n' b
  | _, _ => Sskip
  end.

Ltac it_get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [it_sub seg_inf] in (it_sub p seg_inf) in
  exact x.

(* the loop body (after its leading Sskip) and the statements after the loop *)
Definition seg_loop : statement := ltac:(it_get_seg (it_find_loop seg_inf) [0; 0; 1]%nat).
Definition seg_tail : statement := ltac:(it_get_seg (it_find_loop seg_inf) [1]%nat).

Ltac it_drop_seg n :=
  let x := eval cbv beta iota zeta delta [it_drop seg_loop] in (it_drop n seg_loop) in exact x.

(* from s.next_in = ib; s.avail_in = ain; s.next_out = ob; s.avail_out = aout; r = inflate(&s, flush); ... *)
Definition seg_L1 : statement := ltac:(it_drop_seg 9%nat).
(* from `if (r == Z_NEED_DICT) {...} else {...}` *)
Definition seg_L2 : statement := ltac:(it_drop_seg 17%nat).
(* from `if (dict_set && (r != Z_STREAM_END || !zlib)) {...}` *)
Definition seg_L3 : statement := ltac:(it_drop_seg 18%nat).
(* from free(ib); free(ob); free(osnap); if (r == Z_STREAM_END) break; *)
Definition seg_L4 : statement := ltac:(it_drop_seg 19%nat).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Lemma it_bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma it_bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma it_tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma it_tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma it_ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma it_ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma it_uint_inflate_cs sh (v: val) q:
  @data_at Zlib.units.Inflate.CS sh tuint v q = @data_at CS sh tuint v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition it_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma it_strm_cs sh (v: it_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition it_strm_undef : it_strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma it_strm_undef_cs sh q:
  @data_at_ CS sh (Tstruct _z_stream_s noattr) q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm it_strm_undef q.
Proof. unfold data_at_. rewrite it_strm_cs. reflexivity. Qed.

(* any stream contents (at the inflate unit's CS) give back the local variable's memory *)
Lemma it_strm_to_undef sh (v: it_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh (Tstruct _z_stream_s noattr) q.
Proof. rewrite it_strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

(* a stream (live or not) gives back the local variable's memory *)
Lemma it_istream_to_undef gv vs z st:
  istream gv Tsh vs z st |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - sep_apply it_strm_to_undef. cancel.
  - sep_apply it_strm_to_undef. cancel.
Qed.

(* the stream at the law's compspecs *)
Definition it_tup (gv: globals) (z: zfields) (sp: val) : it_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma it_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (it_tup gv z (l_sp L)) vs * state_mem gv vs L).
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite it_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma it_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs (Tstruct _z_stream_s noattr) (it_tup gv z (l_sp L)) vs * state_mem gv vs L
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite it_istream_unfold. entailer!. Qed.

Lemma it_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma it_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma it_on_live (vs: val) z L f: isptr vs ->
  on_live vs z (Some L) f = let '(r, z', L') := f z L in (r, z', Some L').
Proof. intros P. unfold on_live, is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma it_tup_set gv z sp ni ai no ao:
  it_tup gv (it_set_zf_call z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (it_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (it_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The facts and assertions                                                                       *)

(* Ghost values (as enc_done, ITMainKit.v): gv; the addresses of the local variables w (vw), s (vs), osnap
   (vosn), dl (vdl); the objects dict (dictp), bad (badp), data (datap, contents dcont), src (srcp, contents
   scont); the drawn wsel; G; Fr: the rest of the memory (the version literals, deflate_ref.h's tables).  The
   harness's variables: pos, lim, opos, dict_set (dset); the stream (z, L). *)

(* everywhere in the inflate half *)
Definition it_glob (I: it_inv) (G: it_ghost) (dictp badp datap srcp: val) (wsel: Z) (dcont scont: list val)
    : Prop :=
  it_facts I /\ it_ok G /\ 0 <= wsel <= 255 /\
  Zlength dcont = 2 ^ 18 /\ sublist 0 (Zlength (it_data G)) dcont = bytes_rep (it_data G) /\
  Zlength scont = 2 ^ 19 /\ sublist 0 (Zlength (it_src G)) scont = bytes_rep (it_src G) /\
  is_bytes (g_dict G) /\ is_bytes (it_data G) /\ is_bytes (it_src G) /\
  isptr dictp /\ isptr badp /\ isptr datap /\ isptr srcp.

(* the loop body's entry (the loop invariant for given values) *)
Definition it_at (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost) (wsel: Z)
    (dcont scont: list val) (Fr: mpred) (pos lim opos: Z) (dset: bool) (z: zfields) (L: live)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh tuint vdl; Fr).

(* the loop invariant *)
Definition it_inv_a (I: it_inv) (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost)
    (wsel: Z) (dcont scont: list val) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX lim: Z, EX opos: Z, EX dset: bool, EX z: zfields, EX L: live,
  PROP (I G pos opos dset false z L; pos <= lim <= Zlength (it_src G))
  LOCAL (temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh tuint vdl; Fr).

(* after the loop (break on Z_STREAM_END): all the data produced, all the stream consumed *)
Definition it_brk (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost)
    (wsel: Z) (dcont scont: list val) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX lim: Z, EX opos: Z, EX dset: bool, EX z: zfields, EX L: live,
  PROP (opos = Zlength (it_data G); pos = Zlength (it_src G))
  LOCAL (temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh tuint vdl; Fr).

(* the postcondition of the loop body (Inv: the loop invariant, Brk: the break assertion) *)
Definition it_PL (Inv Brk: environ -> mpred) : ret_assert :=
  loop_nocontinue_ret_assert Inv (overridePost Brk POST_m).

(* after the null check of ib / ob (before the stores into s): lim updated, ain = lim - pos, ib = exact_copy of
   src[pos .. lim), ob = a new object of aout bytes bs, osnap = q (the copy of bs) *)
Definition it_buf (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost) (wsel: Z)
    (dcont scont: list val) (Fr: mpred) (pos lim opos: Z) (dset: bool) (z: zfields) (L: live)
    (aout flush: Z) (ibp obp q: val) (bs: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _ain (Vint (Int.repr (lim - pos))); temp _ib ibp; temp _ob obp;
         temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       malloc_token Ews (tarray tuchar (lim - pos)) ibp;
       data_at Ews (tarray tuchar (lim - pos)) (bytes_rep (sublist pos lim (it_src G))) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep bs) obp;
       data_at Tsh (tptr tuchar) q vosn;
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh tuint vdl; Fr).

Definition it_buf_facts (I: it_inv) (G: it_ghost) (pos lim opos: Z) (dset: bool) (z: zfields) (L: live)
    (aout flush: Z) (ibp obp q: val) (bs: list Z) : Prop :=
  I G pos opos dset false z L /\ pos <= lim <= Zlength (it_src G) /\
  0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ is_bytes bs /\ Int.min_signed <= flush <= Int.max_signed /\
  isptr ibp /\ isptr obp /\ isptr q.

(* after `made = aout - s.avail_out; pos += ain - s.avail_in;` (pos, lim, opos, dset: the values before the
   call; pos2: the new pos; made; r: inflate's return value; the stream (z', L') after the call; cont: ob's
   contents, ow the bytes the call wrote at its start) *)
Definition it_mid (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost) (wsel: Z)
    (dcont scont: list val) (Fr: mpred) (pos lim opos: Z) (dset: bool)
    (aout: Z) (ibp obp q: val) (bs: list Z) (r pos2 made: Z) (z': zfields) (L': live) (cont: list val)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r)); temp _made (Vint (Int.repr made)); temp _ib ibp; temp _ob obp;
         temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos2)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z' (Some L'); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       malloc_token Ews (tarray tuchar (lim - pos)) ibp;
       data_at Ews (tarray tuchar (lim - pos)) (bytes_rep (sublist pos lim (it_src G))) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) cont obp;
       data_at Tsh (tptr tuchar) q vosn;
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh tuint vdl; Fr).

Definition it_mid_facts (I: it_inv) (G: it_ghost) (pos lim opos: Z) (dset: bool) (aout: Z) (ibp obp q: val)
    (bs: list Z) (r pos2 made: Z) (z': zfields) (L': live) (ow: list Z) (cont: list val) : Prop :=
  0 <= pos <= lim /\ lim <= Zlength (it_src G) /\ 0 <= opos <= Zlength (it_data G) /\
  0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ is_bytes bs /\ isptr ibp /\ isptr obp /\ isptr q /\
  pos2 = pos + (lim - pos - zf_ai z') /\ made = aout - zf_ao z' /\
  it_post I G pos opos dset (lim - pos) aout r z' L' ow /\ r <> Z_MEM_ERROR /\
  Int.min_signed <= r <= Int.max_signed /\ live_ok L' /\ zf_ok z' /\
  Zlength cont = aout /\ sublist 0 made cont = bytes_rep ow.

(* after the branch `if (r == Z_NEED_DICT) {...} else {...}` (pos, opos, dset, r: the harness's variables then;
   the stream (z, L); ib (ain bytes ic), ob (aout bytes oc) and osnap (q: aout bytes qc) still allocated) *)
Definition it_mid2 (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost) (wsel: Z)
    (dcont scont: list val) (Fr: mpred) (pos lim opos: Z) (dset: bool) (r: Z) (z: zfields) (L: live)
    (ain aout: Z) (ibp obp q: val) (ic oc qc: list val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r)); temp _ib ibp; temp _ob obp;
         temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0))); temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         temp _pos (Vint (Int.repr pos)); temp _lim (Vint (Int.repr lim)); temp _opos (Vint (Int.repr opos));
         temp _dict_set (Vint (Int.repr (if dset then 1 else 0)));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       malloc_token Ews (tarray tuchar ain) ibp; data_at Ews (tarray tuchar ain) ic ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) oc obp;
       data_at Tsh (tptr tuchar) q vosn;
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) qc q;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh tuint vdl; Fr).

Definition it_mid2_facts (I: it_inv) (G: it_ghost) (pos lim opos: Z) (dset: bool) (r: Z) (z: zfields)
    (L: live) (ain aout: Z) (ibp obp q: val) (ic oc qc: list val) : Prop :=
  (r = Z_STREAM_END -> opos = Zlength (it_data G) /\ pos = Zlength (it_src G) /\
                       (dset = true -> g_zlib G = false -> it_win G opos L)) /\
  (r <> Z_STREAM_END -> I G pos opos dset false z L) /\
  0 <= pos <= lim /\ lim <= Zlength (it_src G) /\ 0 <= opos <= Zlength (it_data G) /\
  Int.min_signed <= r <= Int.max_signed /\ live_ok L /\ zf_ok z /\
  0 <= ain /\ 0 <= aout <= 2 ^ 20 /\ Zlength ic = ain /\ Zlength oc = aout /\ Zlength qc = aout /\
  isptr ibp /\ isptr obp /\ isptr q.

(* ---------------------------------------------------------------------------------------------- *)
(* The statements of the parts (continuation-passing; proofs in ITMainInf*.v)                      *)

(* the draws, lim, ain, ib = exact_copy(src + pos, ain), ob = exact_space(aout, &osnap), the null check *)
Definition it_pre_stmt {Espec: OracleKind} : Prop :=
  forall I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr (Inv Brk: environ -> mpred)
         pos lim opos dset z L,
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  I G pos opos dset false z L -> pos <= lim <= Zlength (it_src G) ->
  (forall lim' aout flush ibp obp q bs,
     it_buf_facts I G pos lim' opos dset z L aout flush ibp obp q bs ->
     semax Delta_m
       (it_buf gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim' opos dset z L
          aout flush ibp obp q bs)
       seg_L1 (it_PL Inv Brk)) ->
  semax Delta_m (it_at gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset z L)
    seg_loop (it_PL Inv Brk).

(* the stores into s, r = inflate(&s, flush) (it_facts' it_inflate), `if (r == Z_MEM_ERROR) return 0;`, made,
   pos *)
Definition it_call_stmt {Espec: OracleKind} : Prop :=
  forall I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr (Inv Brk: environ -> mpred)
         pos lim opos dset z L aout flush ibp obp q bs,
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  it_buf_facts I G pos lim opos dset z L aout flush ibp obp q bs ->
  (forall r pos2 made z' L' ow cont,
     it_mid_facts I G pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont ->
     semax Delta_m
       (it_mid gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset
          aout ibp obp q bs r pos2 made z' L' cont)
       seg_L2 (it_PL Inv Brk)) ->
  semax Delta_m
    (it_buf gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset z L
       aout flush ibp obp q bs)
    seg_L1 (it_PL Inv Brk).

(* the branch r == Z_NEED_DICT: its gp_asserts, the wrong dictionary when wsel == 0 (it_bad_dict), the right
   one (it_good_dict; Z_MEM_ERROR -> return 0), dict_set = 1 *)
Definition it_nd_stmt {Espec: OracleKind} : Prop :=
  forall I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr (Inv Brk: environ -> mpred)
         pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont,
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  it_mid_facts I G pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont ->
  r = Z_NEED_DICT ->
  (forall opos3 dset3 r3 z3 L3,
     it_mid2_facts I G pos2 lim opos3 dset3 r3 z3 L3 (lim - pos) aout ibp obp q
       (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs) ->
     semax Delta_m
       (it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos2 lim opos3 dset3 r3 z3 L3
          (lim - pos) aout ibp obp q (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs))
       seg_L3 (it_PL Inv Brk)) ->
  semax Delta_m
    (it_mid gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset
       aout ibp obp q bs r pos2 made z' L' cont)
    seg_L2 (it_PL Inv Brk).

(* the other branch: gp_assert(r == Z_OK || r == Z_BUF_ERROR || r == Z_STREAM_END), made <= n - opos,
   bytes_same(ob, data + opos, made), opos += made *)
Definition it_else_stmt {Espec: OracleKind} : Prop :=
  forall I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr (Inv Brk: environ -> mpred)
         pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont,
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  it_mid_facts I G pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont ->
  r <> Z_NEED_DICT ->
  (forall opos3 dset3 r3 z3 L3,
     it_mid2_facts I G pos2 lim opos3 dset3 r3 z3 L3 (lim - pos) aout ibp obp q
       (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs) ->
     semax Delta_m
       (it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos2 lim opos3 dset3 r3 z3 L3
          (lim - pos) aout ibp obp q (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs))
       seg_L3 (it_PL Inv Brk)) ->
  semax Delta_m
    (it_mid gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset
       aout ibp obp q bs r pos2 made z' L' cont)
    seg_L2 (it_PL Inv Brk).

(* the window checks `if (dict_set && (r != Z_STREAM_END || !zlib)) {...}`: inflateGetDictionary for the length
   and the bytes, the hist() comparison loop, free(gd) *)
Definition it_win_stmt {Espec: OracleKind} : Prop :=
  forall I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr (Inv Brk: environ -> mpred)
         pos lim opos dset r z L ain aout ibp obp q ic oc qc,
  it_glob I G dictp badp datap srcp wsel dcont scont ->
  it_mid2_facts I G pos lim opos dset r z L ain aout ibp obp q ic oc qc ->
  semax Delta_m
    (it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset r z L
       ain aout ibp obp q ic oc qc)
    seg_L4 (it_PL Inv Brk) ->
  semax Delta_m
    (it_mid2 gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr pos lim opos dset r z L
       ain aout ibp obp q ic oc qc)
    seg_L3 (it_PL Inv Brk).

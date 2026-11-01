(* Law inflate_check, main (IKMain.v): the kit shared by the segment lemmas of main's proof (as
   inflate_codes/MainKit.v, MainHelp.v, MainInfKit.v).
   - Gmain_k (= IKMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: seg_loop (the loop body after its leading Sskip), seg_tail (after the loop),
     and the suffixes of seg_loop: seg_L1 (from the stores into s before inflate()), seg_L2 (from the check
     `if (raw) ... else if (tout != 0) ...`), seg_L3 (from `if (r == Z_STREAM_END && !raw) ...`), seg_L4 (from
     the three free()s);
   - the assertions at the boundaries: ik_inv (the loop invariant), ik_buf (after the input/output objects were
     made, before the stores), ik_mid (after ra and rc were updated: the stream unfolded at the law's CS);
   - moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; Zlib.proof.crc32.HarnessRef.ref_crc32_spec; be32_spec; le32_spec;
   exact_copy_spec; exact_space_spec; stream_defaults_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of f_main's body                                                                 *)

(* a sub-statement by its path (0: first component, other: second) *)
Fixpoint ik_sub (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => ik_sub pth a
  | S _ :: pth, Ssequence _ b => ik_sub pth b
  | O :: pth, Sifthenelse _ a _ => ik_sub pth a
  | S _ :: pth, Sifthenelse _ _ b => ik_sub pth b
  | O :: pth, Sloop a _ => ik_sub pth a
  | S _ :: pth, Sloop _ b => ik_sub pth b
  | _, _ => Sskip
  end.

Definition ik_opt_or {A} (x y: option A) : option A := match x with Some _ => x | None => y end.
Definition ik_opt_cons {A} (k: A) (x: option (list A)) : option (list A) :=
  match x with Some l => Some (k :: l) | None => None end.

(* the path of the first `Ssequence (Sloop _ _) _` *)
Fixpoint ik_find_loop (s: statement) : option (list nat) :=
  match s with
  | Ssequence (Sloop _ _) _ => Some nil
  | Ssequence a b => ik_opt_or (ik_opt_cons O (ik_find_loop a)) (ik_opt_cons 1%nat (ik_find_loop b))
  | Sifthenelse _ a b => ik_opt_or (ik_opt_cons O (ik_find_loop a)) (ik_opt_cons 1%nat (ik_find_loop b))
  | Sloop a b => ik_opt_or (ik_opt_cons O (ik_find_loop a)) (ik_opt_cons 1%nat (ik_find_loop b))
  | _ => None
  end.

(* drop the first n statements of a chain Ssequence s1 (Ssequence s2 ...) *)
Fixpoint ik_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => ik_drop n' b
  | _, _ => Sskip
  end.

Ltac ik_get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [ik_sub f_main fn_body] in (ik_sub p (fn_body f_main)) in
  exact x.

(* the loop body (after its leading Sskip) and the statements after the loop *)
Definition seg_loop : statement := ltac:(ik_get_seg (ik_find_loop (fn_body f_main)) [0; 0; 1]%nat).
Definition seg_tail : statement := ltac:(ik_get_seg (ik_find_loop (fn_body f_main)) [1]%nat).

Ltac ik_drop_seg n :=
  let x := eval cbv beta iota zeta delta [ik_drop seg_loop] in (ik_drop n seg_loop) in exact x.

(* from the stores s.next_in = ib; ... *)
Definition seg_L1 : statement := ltac:(ik_drop_seg 10%nat).
(* from `if (raw) gp_assert(s.adler == adler0); else if (tout != 0) ...` *)
Definition seg_L2 : statement := ltac:(ik_drop_seg 22%nat).
(* from `if (r == Z_STREAM_END && !raw) ...` *)
Definition seg_L3 : statement := ltac:(ik_drop_seg 23%nat).
(* from free(ib); free(ob); free(osnap); if (stop == 0) break; *)
Definition seg_L4 : statement := ltac:(ik_drop_seg 24%nat).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Lemma ik_bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma ik_bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ik_bytes_crc_cs sh n (v: list val) q:
  @data_at Zlib.units.Crc32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_crc32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ik_tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma ik_tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ik_ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ik_ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Definition ik_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma ik_strm_cs sh (v: ik_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition ik_strm_undef : ik_strm_tuple :=
  (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
   (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))).

Lemma ik_strm_undef_cs sh q:
  @data_at_ CS sh (Tstruct _z_stream_s noattr) q = @data_at Zlib.units.Inflate.CS sh Rep.t_strm ik_strm_undef q.
Proof. unfold data_at_. rewrite ik_strm_cs. reflexivity. Qed.

(* any stream contents (at the inflate unit's CS) give back the local variable's memory *)
Lemma ik_strm_to_undef sh (v: ik_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q |-- @data_at_ CS sh (Tstruct _z_stream_s noattr) q.
Proof. rewrite ik_strm_undef_cs. apply (@data_at_data_at_ Zlib.units.Inflate.CS). Qed.

(* a stream (live or not) gives back the local variable's memory *)
Lemma ik_istream_to_undef gv vs z st:
  istream gv Tsh vs z st |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof.
  unfold istream, zstrm_at, strm_rep. destruct st as [L | ]; Intros.
  - sep_apply ik_strm_to_undef. cancel.
  - sep_apply ik_strm_to_undef. cancel.
Qed.

(* the stream at the law's compspecs *)
Definition ik_tup (gv: globals) (z: zfields) (sp: val) : ik_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma ik_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (ik_tup gv z (l_sp L)) vs * state_mem gv vs L).
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite ik_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma ik_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  @data_at CS shs (Tstruct _z_stream_s noattr) (ik_tup gv z (l_sp L)) vs * state_mem gv vs L
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite ik_istream_unfold. entailer!. Qed.

Lemma ik_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ik_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ik_tup_set gv z sp ni ai no ao:
  ik_tup gv (ik_set_zf_call z ni ai no ao) sp =
  (ni, (Vint (Int.repr ai), (fst (snd (snd (ik_tup gv z sp))), (no, (Vint (Int.repr ao),
   snd (snd (snd (snd (snd (ik_tup gv z sp)))))))))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions at the segments' boundaries                                                    *)

(* Ghost values: gv; vs (the address of s), vosn (osnap); w = wbits; srcp/src = the n input bytes
   (n = Zlength src); adler0 (s.adler after stream_defaults); the harness's pos, and out (all the bytes inflate()
   produced so far: tout = |out| mod 2^64, ra = ref_adler32 1 out, rc = ref_crc32 0 out); the stream (z, L);
   Fr: the rest of the memory (the version literals). *)

Definition ik_raw (w: Z) : Z := if w <? 0 then 1 else 0.
Definition ik_gzv (w: Z) (src: list Z) : Z := if andb (0 <=? w) (ik_gz w src) then 1 else 0.

(* the loop invariant *)
Definition ik_inv (I: Z -> list Z -> Z -> list Z -> zfields -> live -> Prop)
    (gv: globals) (vs vosn: val) (w: Z) (srcp: val) (src: list Z) (adler0: Z) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX out: list Z, EX z: zfields, EX L: live,
  PROP (I w src pos out z L; 0 <= pos <= Zlength src; bytes_ok out; w < 0 -> zf_adler z = adler0)
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _adler0 (Vlong (Int64.repr adler0));
         temp _raw (Vint (Int.repr (ik_raw w))); temp _gz (Vint (Int.repr (ik_gzv w src)));
         temp _pos (Vint (Int.repr pos)); temp _tout (Vlong (Int64.repr (Zlength out)));
         temp _ra (Vlong (Int64.repr (ref_adler32 1 out))); temp _rc (Vlong (Int64.repr (ref_crc32 0 out)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh (tptr tuchar) vosn; Fr).

(* the loop invariant's assertion for given pos, out, z, L (its PROP part is in the hypotheses) *)
Definition ik_at (gv: globals) (vs vosn: val) (w: Z) (srcp: val) (src: list Z) (adler0: Z) (Fr: mpred)
    (pos: Z) (out: list Z) (z: zfields) (L: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _adler0 (Vlong (Int64.repr adler0));
         temp _raw (Vint (Int.repr (ik_raw w))); temp _gz (Vint (Int.repr (ik_gzv w src)));
         temp _pos (Vint (Int.repr pos)); temp _tout (Vlong (Int64.repr (Zlength out)));
         temp _ra (Vlong (Int64.repr (ref_adler32 1 out))); temp _rc (Vlong (Int64.repr (ref_crc32 0 out)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh (tptr tuchar) vosn; Fr).

(* the facts that hold everywhere in the loop body *)
Definition ik_glob (I: Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) (w: Z) (srcp: val) (src: list Z)
    (adler0: Z) : Prop :=
  check_facts I /\ wbits_ok w = true /\ Int.min_signed <= w <= Int.max_signed /\
  Zlength src <= 2 ^ 24 /\ bytes_ok src /\ isptr srcp /\ 0 <= adler0 <= Int64.max_unsigned.

(* the postcondition of the loop body (Inv: the loop invariant) *)
Definition ik_PL (Inv: environ -> mpred) : ret_assert :=
  loop_nocontinue_ret_assert Inv (overridePost Inv POST_m).

(* after the null check of ib / ob (before the stores into s): ib = exact_copy of src[pos .. pos + ain),
   ob = a new object of aout bytes bs, osnap = q (the copy of bs) *)
Definition ik_buf (gv: globals) (vs vosn: val) (w: Z) (srcp: val) (src: list Z) (adler0: Z) (Fr: mpred)
    (pos: Z) (out: list Z) (z: zfields) (L: live) (ain aout flush stop: Z) (ibp obp q: val) (bs: list Z)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush)); temp _stop (Vint (Int.repr stop));
         temp _ain (Vint (Int.repr ain)); temp _ib ibp; temp _ob obp;
         temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _adler0 (Vlong (Int64.repr adler0));
         temp _raw (Vint (Int.repr (ik_raw w))); temp _gz (Vint (Int.repr (ik_gzv w src)));
         temp _pos (Vint (Int.repr pos)); temp _tout (Vlong (Int64.repr (Zlength out)));
         temp _ra (Vlong (Int64.repr (ref_adler32 1 out))); temp _rc (Vlong (Int64.repr (ref_crc32 0 out)));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep bs) obp;
       data_at Tsh (tptr tuchar) q vosn;
       malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
       Fr).

Definition ik_buf_facts (I: Z -> list Z -> Z -> list Z -> zfields -> live -> Prop) (w: Z) (srcp: val)
    (src: list Z) (adler0: Z) (pos: Z) (out: list Z) (z: zfields) (L: live) (ain aout flush stop: Z)
    (ibp obp q: val) (bs: list Z) : Prop :=
  ik_glob I w srcp src adler0 /\
  I w src pos out z L /\ 0 <= pos /\ bytes_ok out /\ (w < 0 -> zf_adler z = adler0) /\
  0 <= ain /\ pos + ain <= Zlength src /\ 0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ bytes_ok bs /\
  Int.min_signed <= flush <= Int.max_signed /\ 0 <= stop <= 255 /\ isptr ibp /\ isptr obp /\ isptr q.

(* after ra and rc were updated: the harness's variables after the call (pos', out' = out ++ the bytes made),
   r the code inflate() returned; the stream struct at the law's CS (sp: strm->state); Rest: the memory
   the checks do not touch *)
Definition ik_mid (gv: globals) (vs vosn: val) (w: Z) (srcp: val) (src: list Z) (adler0: Z)
    (pos': Z) (out': list Z) (r stop: Z) (ibp obp: val) (z': zfields) (sp: val) (Rest: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr r)); temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _adler0 (Vlong (Int64.repr adler0));
         temp _raw (Vint (Int.repr (ik_raw w))); temp _gz (Vint (Int.repr (ik_gzv w src)));
         temp _pos (Vint (Int.repr pos')); temp _tout (Vlong (Int64.repr (Zlength out')));
         temp _ra (Vlong (Int64.repr (ref_adler32 1 out'))); temp _rc (Vlong (Int64.repr (ref_crc32 0 out')));
         lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (data_at Tsh (Tstruct _z_stream_s noattr) (ik_tup gv z' sp) vs;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp; Rest).

(* what the checks need (check_post, restated for pos', out') *)
Definition ik_mid_facts (w: Z) (srcp: val) (src: list Z) (adler0: Z) (pos': Z) (out': list Z) (r: Z)
    (z': zfields) : Prop :=
  Int.min_signed <= w <= Int.max_signed /\ 0 <= pos' <= Zlength src /\ Zlength src <= 2 ^ 24 /\
  bytes_ok src /\ isptr srcp /\ 0 <= adler0 <= Int64.max_unsigned /\ bytes_ok out' /\ zf_ok z' /\
  Int.min_signed <= r <= Int.max_signed /\
  (w < 0 -> zf_adler z' = adler0) /\
  (0 <= w -> out' <> [] -> ik_hdr (ik_gz w src) src) /\
  (0 <= w -> (out' <> [] \/ r = Z_STREAM_END) -> zf_adler z' = ik_chk (ik_gz w src) out') /\
  (0 <= w -> r = Z_STREAM_END ->
     zf_tout z' = Zlength out' mod 2 ^ 64 /\ ik_trailer (ik_gz w src) src pos' out').

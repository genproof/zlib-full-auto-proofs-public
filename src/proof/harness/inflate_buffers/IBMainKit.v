(* Law inflate_buffers, main (IBMain.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= IBMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: seg_loop (the loop body after its leading Sskip), seg_tail (after the loop),
     seg_ops (the dispatch `if (op < 200) inflate ... else inflateSyncPoint`) and its eleven branches seg_inf,
     seg_sync, seg_gd, seg_sd, seg_prime, seg_reset, seg_reset2, seg_val, seg_mark, seg_cu, seg_sp, and
     seg_checks (the statements after the dispatch up to the end of the loop body: the checks, pos += used,
     the three free()s, `if (stop == 0) break`);
   - the loop invariant ib_loop_inv; the assertions before the dispatch (ops_pre) and at its join (ops_post),
     the hypotheses of the segment lemmas (ops_hyps) and what the join knows (ops_out);
   - moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateSync_spec; inflateGetDictionary_spec; inflateSetDictionary_spec;
   inflatePrime_spec; inflateReset_spec; inflateReset2_spec; inflateValidate_spec; inflateMark_spec;
   inflateCodesUsed_spec; inflateSyncPoint_spec; inflateEnd_spec; zcalloc_i; zcfree_i;
   bytes_same_spec; bytes_copy_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; stream_defaults_spec;
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
Fixpoint sub_stmt (path: list nat) (s: statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => sub_stmt pth a
  | S _ :: pth, Ssequence _ b => sub_stmt pth b
  | O :: pth, Sifthenelse _ a _ => sub_stmt pth a
  | S _ :: pth, Sifthenelse _ _ b => sub_stmt pth b
  | O :: pth, Sloop a _ => sub_stmt pth a
  | S _ :: pth, Sloop _ b => sub_stmt pth b
  | _, _ => Sskip
  end.

Definition opt_or {A} (x y: option A) : option A := match x with Some _ => x | None => y end.
Definition opt_cons {A} (k: A) (x: option (list A)) : option (list A) :=
  match x with Some l => Some (k :: l) | None => None end.

(* the path of the first `Ssequence (Sloop _ _) _` *)
Fixpoint find_loop (s: statement) : option (list nat) :=
  match s with
  | Ssequence (Sloop _ _) _ => Some nil
  | Ssequence a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | Sifthenelse _ a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | Sloop a b => opt_or (opt_cons O (find_loop a)) (opt_cons 1%nat (find_loop b))
  | _ => None
  end.

(* the path of the first `Sifthenelse _ (Ssequence (Ssequence (Scall _ (Evar f _) _) _) _) _` or
   `Sifthenelse _ (Ssequence (Scall _ (Evar f _) _) _) _`: the `if` whose then-branch starts by calling f *)
Definition starts_with_call (f: ident) (s: statement) : bool :=
  match s with
  | Ssequence (Scall _ (Evar g _) _) _ => Pos.eqb f g
  | Ssequence (Ssequence (Scall _ (Evar g _) _) _) _ => Pos.eqb f g
  | _ => false
  end.

Fixpoint find_callif (f: ident) (s: statement) : option (list nat) :=
  match s with
  | Sifthenelse _ a b =>
      if starts_with_call f a then Some nil
      else opt_or (opt_cons O (find_callif f a)) (opt_cons 1%nat (find_callif f b))
  | Ssequence a b => opt_or (opt_cons O (find_callif f a)) (opt_cons 1%nat (find_callif f b))
  | Sloop a b => opt_or (opt_cons O (find_callif f a)) (opt_cons 1%nat (find_callif f b))
  | _ => None
  end.

Ltac get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [sub_stmt f_main fn_body] in (sub_stmt p (fn_body f_main)) in
  exact x.

(* the path of the dispatch, and of the statements after it *)
Definition ops_path : option (list nat) := ltac:(let x := eval vm_compute in (find_callif _inflate (fn_body f_main)) in exact x).
Definition checks_path : option (list nat) :=
  ltac:(let x := eval vm_compute in (match ops_path with Some l => Some (removelast l ++ [1%nat]) | None => None end) in exact x).

(* the loop body (after its leading Sskip) and the statements after the loop *)
Definition seg_loop : statement := ltac:(get_seg (find_loop (fn_body f_main)) [0; 0; 1]%nat).
Definition seg_tail : statement := ltac:(get_seg (find_loop (fn_body f_main)) [1]%nat).
(* the dispatch and its branches *)
Definition seg_ops : statement := ltac:(get_seg ops_path (@nil nat)).
Definition seg_inf : statement := ltac:(get_seg ops_path [0]%nat).
Definition seg_sync : statement := ltac:(get_seg ops_path [1; 0]%nat).
Definition seg_gd : statement := ltac:(get_seg ops_path [1; 1; 0]%nat).
Definition seg_sd : statement := ltac:(get_seg ops_path [1; 1; 1; 0]%nat).
Definition seg_prime : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 0]%nat).
Definition seg_reset : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 0]%nat).
Definition seg_reset2 : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 1; 0]%nat).
Definition seg_val : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 1; 1; 0]%nat).
Definition seg_mark : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 1; 1; 1; 0]%nat).
Definition seg_cu : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 1; 1; 1; 1; 0]%nat).
Definition seg_sp : statement := ltac:(get_seg ops_path [1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%nat).
(* the checks after the dispatch, to the end of the loop body *)
Definition seg_checks : statement := ltac:(get_seg checks_path (@nil nat)).

(* ---------------------------------------------------------------------------------------------- *)
(* Compspecs moves (the specs are at the units' CS, main at the law's CS)                          *)

Lemma bytes_inflate_cs sh n (v: list val) q:
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma bytes_adler_cs sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma tok_inflate_cs sh n q:
  @malloc_token Zlib.units.Inflate.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_inflate). reflexivity. Qed.
Lemma tok_adler_cs sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ptr_adler_cs_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ptr_adler_cs sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma uint_inflate_cs sh (v: val) q:
  @data_at Zlib.units.Inflate.CS sh tuint v q = @data_at CS sh tuint v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.
Lemma uint_inflate_cs_ sh q:
  @data_at_ Zlib.units.Inflate.CS sh tuint q = @data_at_ CS sh tuint q.
Proof. unfold data_at_. apply uint_inflate_cs. Qed.

(* the stream struct at the law's compspecs *)
Definition ib_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma ib_strm_cs sh (v: ib_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition ib_tup (gv: globals) (z: zfields) (sp: val) : ib_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

(* a live stream: the struct (law's CS) and the memory behind strm->state *)
Lemma ib_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (ib_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite ib_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma ib_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (@data_at CS shs (Tstruct _z_stream_s noattr) (ib_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite ib_istream_unfold. entailer!. Qed.

Lemma ib_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ib_is_live (vs: val) st: isptr vs -> is_live vs st = st.
Proof. intros P. unfold is_live. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The harness's variables                                                                        *)

(* nin = op < 200 && in_null == 0; nout = op < 200 && out_null == 0 *)
Definition ib_nin (op innull: Z) : bool := (op <? 200) && (innull =? 0).
Definition ib_nout (op outnull: Z) : bool := (op <? 200) && (outnull =? 0).

(* the stream fields after `s.next_in = nin ? Z_NULL : ib; s.avail_in = ain; s.next_out = ...; s.avail_out = aout` *)
Definition ib_zcall (z: zfields) (nin nout: bool) (ibp obp: val) (ain aout: Z) : zfields :=
  ZF (if nin then nullval else ibp) ain (zf_tin z) (if nout then nullval else obp) aout (zf_tout z) (zf_msg z)
     (zf_dt z) (zf_adler z) (zf_res z).

(* the loop invariant (at the loop head): the input src (n = Zlength src bytes), pos bytes of it consumed, the
   live stream (z, L) with ib_inv L; Fr: the rest (the string literals) *)
Definition ib_loop_inv (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (Fr: mpred) : environ -> mpred :=
  EX pos: Z, EX z: zfields, EX L: live,
  PROP (ib_inv L; 0 <= pos <= Zlength src)
  LOCAL (temp _n (Vint (Int.repr (Zlength src))); temp _src srcp; temp _pos (Vint (Int.repr pos));
         lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn; Fr).

(* Ghost values of one iteration: gv; the local variables' addresses vs (s), vosn (osnap), vdl (dl); srcp/src
   the n input bytes; pos (consumed); the draws aout, flush, arg, op, innull, outnull, stop; ain = nlim - pos;
   ibp = ib (exact_copy of src[pos .. pos + ain)), obp = ob and q = osnap (exact_space: both hold bs, aout
   bytes); the stream z, L before the stores; Fr the rest of the memory. *)

(* the hypotheses of the segment lemmas *)
Definition ops_hyps (srcp: val) (src: list Z) (pos aout flush arg op innull outnull stop ain: Z)
    (ibp obp q: val) (bs: list Z) (L: live) : Prop :=
  ib_facts /\ ib_inv L /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ Zlength src <= 2 ^ 24 /\ is_bytes src /\
  0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ is_bytes bs /\ Int.min_signed <= flush <= Int.max_signed /\
  0 <= arg <= Int.max_unsigned /\ 0 <= op <= 255 /\ 0 <= innull <= 255 /\ 0 <= outnull <= 255 /\
  0 <= stop <= 255 /\ isptr srcp /\ isptr ibp /\ isptr obp /\ isptr q.

(* the LOCALs common to ops_pre and ops_post *)
Definition ops_locals (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (pos aout flush arg op innull
    outnull stop ain: Z) (ibp obp: val) (z: zfields) : list localdef :=
  [temp _tin (Vlong (Int64.repr (zf_tin z))); temp _tout (Vlong (Int64.repr (zf_tout z)));
   temp _nin (Vint (Int.repr (if ib_nin op innull then 1 else 0)));
   temp _nout (Vint (Int.repr (if ib_nout op outnull then 1 else 0)));
   temp _ib ibp; temp _ob obp; temp _ain (Vint (Int.repr ain));
   temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush)); temp _arg (Vint (Int.repr arg));
   temp _op (Vint (Int.repr op)); temp _in_null (Vint (Int.repr innull)); temp _out_null (Vint (Int.repr outnull));
   temp _stop (Vint (Int.repr stop));
   temp _n (Vint (Int.repr (Zlength src))); temp _src srcp; temp _pos (Vint (Int.repr pos));
   lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv].

(* before the dispatch (after `reset = 0`): the stream with the call's buffers stored *)
Definition ops_pre (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (pos aout flush arg op innull
    outnull stop ain: Z) (ibp obp q: val) (bs: list Z) (z: zfields) (L: live) (Fr: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (temp _reset (Vint (Int.repr 0)) ::
           ops_locals gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp z)
  (SEPx [istream gv Tsh vs (ib_zcall z (ib_nin op innull) (ib_nout op outnull) ibp obp ain aout) (Some L);
         mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
         malloc_token Ews (tarray tuchar (Zlength src)) srcp;
         data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
         malloc_token Ews (tarray tuchar ain) ibp;
         data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
         malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep bs) obp;
         data_at Tsh (tptr tuchar) q vosn;
         malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep bs) q;
         data_at_ Tsh tuint vdl; Fr])).

(* what the join knows of a call: r its result (r = 0 for inflateMark / inflateCodesUsed), reset its flag, z'
   the stream fields after it, obl / snl the bytes of ob / osnap; used = ain - avail_in, made = aout - avail_out *)
Definition ops_out (op ain aout: Z) (nin nout: bool) (ibp obp: val) (z z': zfields) (r reset: Z)
    (obl snl: list Z) : Prop :=
  let used := ain - zf_ai z' in
  let made := aout - zf_ao z' in
  Int.min_signed <= r <= Int.max_signed /\ (reset = 0 \/ reset = 1) /\
  0 <= zf_ai z' <= ain /\ 0 <= zf_ao z' <= aout /\
  zf_ni z' = (if nin then nullval else offset_val used ibp) /\ (nin = true -> used = 0) /\
  zf_no z' = (if nout then nullval else offset_val made obp) /\ (nout = true -> made = 0) /\
  Zlength obl = aout /\ Zlength snl = aout /\ is_bytes obl /\ is_bytes snl /\
  sublist made aout obl = sublist made aout snl /\
  (reset = 1 -> zf_tin z' = 0 /\ zf_tout z' = 0) /\
  (reset = 0 -> andb (op <? 200) (r =? Z_MEM_ERROR) = false ->
     zf_tin z' = Zlib.proof.inflate.Model.u64 (zf_tin z + used) /\
     zf_tout z' = Zlib.proof.inflate.Model.u64 (zf_tout z + made)).

(* the state at the join after the dispatch (one call made), for fixed outcomes *)
Definition ops_post_at (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (pos aout flush arg op innull
    outnull stop ain: Z) (ibp obp q: val) (z: zfields) (Fr: mpred)
    (r reset: Z) (z': zfields) (L': live) (obl snl: list Z) : environ -> mpred :=
  PROPx [ib_inv L'; ops_out op ain aout (ib_nin op innull) (ib_nout op outnull) ibp obp z z' r reset obl snl]
  (LOCALx (temp _r (Vint (Int.repr r)) :: temp _reset (Vint (Int.repr reset)) ::
           ops_locals gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp z)
  (SEPx [istream gv Tsh vs z' (Some L');
         mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
         malloc_token Ews (tarray tuchar (Zlength src)) srcp;
         data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
         malloc_token Ews (tarray tuchar ain) ibp;
         data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
         malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep obl) obp;
         data_at Tsh (tptr tuchar) q vosn;
         malloc_token Ews (tarray tuchar aout) q; data_at Ews (tarray tuchar aout) (bytes_rep snl) q;
         data_at_ Tsh tuint vdl; Fr])).

Definition ops_post (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (pos aout flush arg op innull
    outnull stop ain: Z) (ibp obp q: val) (z: zfields) (Fr: mpred) : environ -> mpred :=
  EX r: Z, EX reset: Z, EX z': zfields, EX L': live, EX obl: list Z, EX snl: list Z,
  ops_post_at gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr r reset z' L' obl snl.

(* for op >= 200: nin = nout = 0 *)
Lemma ib_nin_ge op x: 200 <= op -> ib_nin op x = false.
Proof. intros H. unfold ib_nin. destruct (Z.ltb_spec op 200); [lia | reflexivity]. Qed.
Lemma ib_nout_ge op x: 200 <= op -> ib_nout op x = false.
Proof. intros H. unfold ib_nout. destruct (Z.ltb_spec op 200); [lia | reflexivity]. Qed.

(* ops_out of a call (op >= 200) that changes neither the stream fields nor the buffers *)
Lemma ops_out_same op ain aout ibp obp z r obl:
  200 <= op -> zf_ok (ib_zcall z false false ibp obp ain aout) -> isptr ibp -> isptr obp ->
  Int.min_signed <= r <= Int.max_signed -> Zlength obl = aout -> is_bytes obl ->
  ops_out op ain aout false false ibp obp z (ib_zcall z false false ibp obp ain aout) r 0 obl obl.
Proof.
  intros Hop Z Pi Po Hr Hl Hb.
  destruct Z as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). cbn [ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no] in *.
  unfold ops_out; cbn [ib_zcall zf_ai zf_ao zf_tin zf_tout zf_ni zf_no].
  rewrite !Z.sub_diag, !Z.add_0_r.
  unfold Zlib.proof.inflate.Model.u64.
  rewrite !Z.mod_small by rep_lia.
  repeat split; auto; try lia; try discriminate.
  all: destruct ibp, obp; try contradiction; simpl; rewrite ?Ptrofs.add_zero; reflexivity.
Qed.

(* after the loop (before inflateEnd) *)
Definition tail_pre (gv: globals) (vs vosn vdl: val) (srcp: val) (src: list Z) (z: zfields) (L: live)
    (Fr: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp _src srcp; lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn; Fr).

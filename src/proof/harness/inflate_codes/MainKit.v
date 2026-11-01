(* Law inflate_codes, main (Main.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= Main.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body (seg_setdict, seg_inflate: the two branches of `if (op < 24)` in the loop;
     seg_tail: the statements after the loop);
   - the assertions at the segments' boundaries (br_pre_sd / br_pre_inf: the branch entry, br_post: the join
     before the three free()s; tail_pre);
   - moves of byte arrays, malloc tokens and struct z_stream between the units' compspecs and the law's. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_codes.LawCS Zlib.proof.harness.inflate_codes.Globals
               Zlib.proof.harness.inflate_codes.Facts.
Require Import Zlib.harness.x_inflate_codes.code.
Require Import Zlib.proof.crc32.Spec.

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateSetDictionary_spec; inflateEnd_spec; inflateReset_spec;
   inflateReset2_spec; inflateGetDictionary_spec; inflateSync_spec; inflatePrime_spec; inflateValidate_spec;
   inflateMark_spec; inflateCodesUsed_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; be32_spec; exact_copy_spec; exact_space_spec; inflate_wbits_ok_spec; inflate_code_ok_spec;
   stream_defaults_spec;
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

(* the path of the first `Sifthenelse (Ebinop _ (Etempvar x _) _ _) _ _` *)
Fixpoint find_if (x: ident) (s: statement) : option (list nat) :=
  match s with
  | Sifthenelse (Ebinop _ (Etempvar y _) _ _) a b =>
      if Pos.eqb x y then Some nil
      else opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Sifthenelse _ a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Ssequence a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | Sloop a b => opt_or (opt_cons O (find_if x a)) (opt_cons 1%nat (find_if x b))
  | _ => None
  end.

Ltac get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [sub_stmt f_main fn_body] in (sub_stmt p (fn_body f_main)) in
  exact x.

(* the loop body (after its leading Sskip) and the statements after the loop *)
Definition seg_loop : statement := ltac:(get_seg (find_loop (fn_body f_main)) [0; 0; 1]%nat).
Definition seg_tail : statement := ltac:(get_seg (find_loop (fn_body f_main)) [1]%nat).
(* the branches of `if (op < 24)` *)
Definition seg_setdict : statement := ltac:(get_seg (find_if _op (fn_body f_main)) [0]%nat).
Definition seg_inflate : statement := ltac:(get_seg (find_if _op (fn_body f_main)) [1]%nat).

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

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions at the segments' boundaries                                                    *)

(* Ghost values: gv; the local variables' addresses vs (s), vo (other), vosn (osnap), vb (b), vdl (dl);
   w = wbits; srcp/src = the n input bytes (n = Zlength src); the harness variables pos, final, in_dict; the
   stream (z, L); in the loop body: ain = nlim - pos, aout, flush, the bytes innull, outnull, stop; ibp = ib
   (exact_copy of src[pos .. pos + ain)), obp = ob (aout arbitrary bytes bs); Fr: the rest of the memory
   (osnap and its object, the version strings, `other`, b, dl, ...). *)

(* entry of both branches of `if (op < 24)` *)
Definition br_pre (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z) (pos final indict: Z)
    (z: zfields) (L: live) (ain aout flush innull outnull stop: Z) (ibp obp: val) (bs: list Z) (Fr: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos)); temp _final (Vint (Int.repr final));
         temp _in_dict (Vint (Int.repr indict));
         temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _in_null (Vint (Int.repr innull)); temp _out_null (Vint (Int.repr outnull));
         temp _stop (Vint (Int.repr stop)); temp _ain (Vint (Int.repr ain)); temp _ib ibp; temp _ob obp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv; msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) (bytes_rep bs) obp;
       Fr).

(* the join after the branches (before free(ib), free(ob), free(osnap)): the harness variables and the
   stream after the call, the invariant I for them; ob's contents anything *)
Definition br_post (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop)
    (gv: globals) (vs vo vosn vb vdl: val) (w: Z) (srcp: val) (src: list Z)
    (pos ain aout stop: Z) (ibp obp: val) (Fr: mpred) : environ -> mpred :=
  EX pos': Z, EX final': Z, EX indict': Z, EX z': zfields, EX L': live, EX cont: list val,
  PROP (I w src pos' final' indict' z' L'; 0 <= pos' <= Zlength src)
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _zlib_ok (Vint (Int.repr (if zlib_okb w then 1 else 0)));
         temp _pos (Vint (Int.repr pos')); temp _final (Vint (Int.repr final'));
         temp _in_dict (Vint (Int.repr indict'));
         temp _stop (Vint (Int.repr stop)); temp _ib ibp; temp _ob obp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (istream gv Tsh vs z' (Some L'); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar aout) obp; data_at Ews (tarray tuchar aout) cont obp;
       Fr).

(* the hypotheses of the branch lemmas *)
Definition br_facts (I: Z -> list Z -> Z -> Z -> Z -> zfields -> live -> Prop)
    (w: Z) (srcp: val) (src: list Z) (pos final indict: Z) (z: zfields) (L: live)
    (ain aout flush innull outnull stop: Z) (ibp obp: val) (bs: list Z) : Prop :=
  codes_facts I /\ I w src pos final indict z L /\
  wbits_ok w = true /\ Int.min_signed <= w <= Int.max_signed /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ Zlength src <= 2 ^ 24 /\ is_bytes src /\
  0 <= aout <= 2 ^ 20 /\ Zlength bs = aout /\ is_bytes bs /\ Int.min_signed <= flush <= Int.max_signed /\
  0 <= innull <= 255 /\ 0 <= outnull <= 255 /\ 0 <= stop <= 255 /\
  isptr srcp /\ isptr ibp /\ isptr obp.

(* after the loop (before inflateEnd) *)
Definition tail_pre (gv: globals) (vs vo vosn vb vdl: val) (srcp: val) (src: list Z) (z: zfields) (L: live)
    (Fr: mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp _src srcp;
         lvar _dl tuint vdl; lvar _b (tarray tuchar 1) vb; lvar _osnap (tptr tuchar) vosn;
         lvar _s (Tstruct _z_stream_s noattr) vs; lvar _other (tarray tschar 2) vo; gvars gv)
  SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at_ Tsh (tarray tuchar 1) vb; data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn;
       data_at_ Tsh (tarray tschar 2) vo; Fr).

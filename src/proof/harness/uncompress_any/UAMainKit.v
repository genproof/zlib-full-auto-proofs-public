(* Law uncompress_any, main (UAMain.v): the kit shared by the segment lemmas of main's proof.
   - Gmain_k (= UAMain.Gmain), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - the segments of f_main's body: seg_then (the branch `if (r == Z_OK) { ... }`), seg_rest (its part after
     the four checks of the source: from `d2 = exact_space(cap, &snap2)` on);
   - the assertions: ua_okpre (entry of seg_then; also the entry of seg_rest: the checks change no memory),
     ua_join (after the `if (r == Z_OK)`, before `return 0`), the facts ua_ok_facts;
   - moves of byte arrays, malloc tokens, pointers and unsigned longs between the units' compspecs and the
     law's (ua_law rewrites everything to the law's). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpec5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.uncompress_any.UALawCS Zlib.proof.harness.uncompress_any.UAGlobals
               Zlib.proof.harness.uncompress_any.UAFacts.
Require Import Zlib.harness.x_uncompress_any.code.

Local Open Scope logic.

Definition Gmain_k : funspecs :=
  [uncompress2_spec; uncompress_spec; zcalloc_i; zcfree_i;
   ref_adler32_spec; bytes_same_spec; be32_spec; exact_space_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

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

Fixpoint first_stmt (s: statement) : statement :=
  match s with Ssequence a _ => first_stmt a | _ => s end.

Definition is_set (x: ident) (s: statement) : bool :=
  match s with Sset y _ => Pos.eqb x y | _ => false end.

(* the path of the first `Sifthenelse _ a _` whose then-branch starts with `x = ...` *)
Fixpoint find_then (x: ident) (s: statement) : option (list nat) :=
  match s with
  | Sifthenelse _ a b =>
      if is_set x (first_stmt a) then Some nil
      else opt_or (opt_cons O (find_then x a)) (opt_cons 1%nat (find_then x b))
  | Ssequence a b => opt_or (opt_cons O (find_then x a)) (opt_cons 1%nat (find_then x b))
  | Sloop a b => opt_or (opt_cons O (find_then x a)) (opt_cons 1%nat (find_then x b))
  | _ => None
  end.

Ltac get_seg pth sfx :=
  let p := eval vm_compute in (match pth with Some l => l ++ sfx | None => nil end) in
  let x := eval cbv beta iota zeta delta [sub_stmt f_main fn_body] in (sub_stmt p (fn_body f_main)) in
  exact x.

(* the branch `if (r == Z_OK) { gp_assert(slen >= 6); ... }` and its part after the four checks *)
Definition seg_then : statement := ltac:(get_seg (find_then _t'31 (fn_body f_main)) [0]%nat).
Definition seg_rest : statement := ltac:(get_seg (find_then _t'31 (fn_body f_main)) [0; 1; 1; 1; 1]%nat).

(* ---------------------------------------------------------------------------------------------- *)
(* moves between the units' compspecs and the law's *)
Lemma ua_ptr_adler sh (v: val) q:
  @data_at Zlib.units.Adler32.CS sh (tptr tuchar) v q = @data_at CS sh (tptr tuchar) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ua_ptr_adler_ sh q:
  @data_at_ Zlib.units.Adler32.CS sh (tptr tuchar) q = @data_at_ CS sh (tptr tuchar) q.
Proof. unfold data_at_. apply ua_ptr_adler. Qed.
Lemma ua_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma ua_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.
Lemma ua_bytes_uncompr sh n (v: list val) q:
  @data_at Zlib.units.Uncompr.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.
Lemma ua_tok_uncompr sh n q:
  @malloc_token Zlib.units.Uncompr.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_uncompr). reflexivity. Qed.
Lemma ua_ulong_uncompr sh (v: val) q:
  @data_at Zlib.units.Uncompr.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_uncompr); [apply JMeq_refl | reflexivity]. Qed.

Ltac ua_law := repeat first [ rewrite ua_bytes_adler | rewrite ua_tok_adler | rewrite ua_ptr_adler | rewrite ua_ptr_adler_
                            | rewrite ua_bytes_uncompr | rewrite ua_tok_uncompr | rewrite ua_ulong_uncompr ].

Lemma ua_ig_to gv:
  tables_rep Ers gv * Spec.crc_table_at Ers gv * version_lit gv * zfuncs gv |-- inflate_globals Ers Ers gv.
Proof. unfold inflate_globals. cancel. Qed.
Lemma ua_ig_from gv:
  inflate_globals Ers Ers gv |-- tables_rep Ers gv * Spec.crc_table_at Ers gv * version_lit gv * zfuncs gv.
Proof. unfold inflate_globals. cancel. Qed.

Ltac ua_shl :=
  change (Int.shl (Int.repr 1) (Int.repr 24)) with (Int.repr (2 ^ 24)) in *;
  change (Int.shl (Int.repr 1) (Int.repr 20)) with (Int.repr (2 ^ 20)) in *;
  repeat match goal with H: context [Int.unsigned (Int.repr (2 ^ ?k))] |- _ =>
    rewrite (Int.unsigned_repr (2 ^ k)) in H by rep_lia end.

(* ---------------------------------------------------------------------------------------------- *)

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

(* Ghost values: gv; the local variables' addresses vsnap, vdlen, vslen, vsnap2, vdlen2; srcp/src = the n source
   bytes (n = Zlength src, malloc'ed); dstp = dst (cap bytes, malloc'ed by exact_space, first contents bs),
   snapq = snap (its copy, bs); uncompress2's outcome slen, dlen, out (dst now holds dest_after (bytes_rep bs) cap
   out, i.e. out then bs from |out| on).  Everything at the law's compspecs. *)
Definition ua_okpre (gv: globals) (vsnap vdlen vslen vsnap2 vdlen2: val) (srcp: val) (src: list Z)
    (dstp snapq: val) (cap: Z) (bs: list Z) (slen dlen: Z) (out: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _r (Vint (Int.repr 0)); temp _dst dstp; temp _src srcp; temp _cap (Vint (Int.repr cap));
         temp _n (Vint (Int.repr (Zlength src)));
         lvar _dlen2 tulong vdlen2; lvar _snap2 (tptr tuchar) vsnap2; lvar _slen tulong vslen;
         lvar _dlen tulong vdlen; lvar _snap (tptr tuchar) vsnap; gvars gv)
  SEP (data_at Ews (tarray tuchar cap) (dest_after (bytes_rep bs) cap out) dstp;
       malloc_token Ews (tarray tuchar cap) dstp;
       data_at Tsh tulong (Vlong (Int64.repr dlen)) vdlen;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Tsh tulong (Vlong (Int64.repr slen)) vslen;
       uversion_lit gv; inflate_globals Ers Ers gv; mem_mgr gv;
       data_at Tsh (tptr tuchar) snapq vsnap;
       malloc_token Ews (tarray tuchar cap) snapq;
       data_at Ews (tarray tuchar cap) (bytes_rep bs) snapq;
       data_at_ Tsh tulong vdlen2; data_at_ Tsh (tptr tuchar) vsnap2).

(* after `if (r == Z_OK) { ... }`, before `return 0`: the local variables, and anything *)
Definition ua_join (gv: globals) (vsnap vdlen vslen vsnap2 vdlen2: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _dlen2 tulong vdlen2; lvar _snap2 (tptr tuchar) vsnap2; lvar _slen tulong vslen;
         lvar _dlen tulong vdlen; lvar _snap (tptr tuchar) vsnap; gvars gv)
  SEP (data_at_ Tsh tulong vdlen2; data_at_ Tsh (tptr tuchar) vsnap2; data_at_ Tsh tulong vslen;
       data_at_ Tsh tulong vdlen; data_at_ Tsh (tptr tuchar) vsnap; TT).

(* what main knows at the entry of seg_then (UAFacts.ua_facts_stmt applied to uncompress2's outcome, r = Z_OK) *)
Definition ua_ok_facts (srcp: val) (src: list Z) (dstp: val) (cap: Z) (bs: list Z) (slen dlen: Z) (out: list Z)
    : Prop :=
  bytes_ok src /\ Zlength src <= 2 ^ 24 /\ 0 <= cap <= 2 ^ 20 /\ Zlength bs = cap /\ is_bytes bs /\
  isptr dstp /\ isptr srcp /\ 0 <= slen <= Zlength src /\ dlen = Zlength out /\ dlen <= cap /\ bytes_ok out /\
  6 <= slen /\ ua_hdr src /\ be32 (sublist (slen - 4) slen src) = ref_adler32 1 out /\
  (forall r2 slen2 dlen2 out2,
     uncompress_rel src cap r2 slen2 dlen2 out2 -> r2 <> Z_MEM_ERROR ->
     r2 = Z_OK /\ dlen2 = dlen /\ out2 = out).

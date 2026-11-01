(* Law rt_stream (data of any length), main's setup segment (UMainKit.segA, proved in USegA.v, USegANull.v,
   USegAInit.v and USegAStores.v): the objects data, expected (the copy of data), compressed and out as main
   holds them, the NULL tests'
   tactics, the compspecs conversions of the compressor's fields and of the version literal, and the statements
   and states at which the proof of segA is cut.  Round 1's MainSegAKit.v for the harness of round 2. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
Require Zlib.proof.harness.deflate_bound.MainInit.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac sa_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in sa_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := sa_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The objects data, compressed and out *)

(* any_bytes gives its object at the adler32 unit's compspecs; main keeps it at the law's *)
Lemma sa_bytes_cs sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

Lemma sa_tok_cs sh n q :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* data: the object of the bytes [l] *)
Definition sa_dobj (q : val) (l : list Z) : mpred :=
  malloc_token Ews (tarray tuchar (Zlength l)) q * data_at Ews (tarray tuchar (Zlength l)) (map vi l) q.

Lemma sa_dobj_fold q l :
  @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l)) q *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l)) (bytes_rep l) q = sa_dobj q l.
Proof. unfold sa_dobj. rewrite sa_bytes_cs, sa_tok_cs. reflexivity. Qed.

(* compressed and out: malloc's object of n undefined bytes *)
Definition sa_buf (n : Z) (q : val) : mpred :=
  malloc_token Ews (tarray tuchar n) q * data_at_ Ews (tarray tuchar n) q.

Lemma sa_buf_cbytes n q :
  sa_buf n q = malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (cbytes n []) q.
Proof.
  unfold sa_buf, data_at_, cbytes. f_equal. f_equal. rewrite Zlength_nil, Z.sub_0_r. reflexivity.
Qed.

Lemma sa_dobj_isptr q l : sa_dobj q l |-- !! isptr q.
Proof. unfold sa_dobj. entailer!; match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. Qed.

Lemma sa_buf_isptr n q : sa_buf n q |-- !! isptr q.
Proof. unfold sa_buf. entailer!; match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end. Qed.

(* a malloc'ed object (any size, also 0) can be compared with NULL *)
Lemma sa_dobj_test_eq P q l : P |-- sa_dobj q l * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q ltac:(apply Zlength_nonneg)).
  eapply derives_trans; [exact HP | ]. unfold sa_dobj. cancel.
Qed.

Lemma sa_buf_test_eq P n q : 0 <= n -> P |-- sa_buf n q * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros Hn HP. apply (malloc_test_eq P n q Hn).
  eapply derives_trans; [exact HP | ]. unfold sa_buf. cancel.
Qed.

(* the tc goal of `q == NULL` (or of the expression containing it) for an object q *)
Ltac sa_tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with
  | context [sa_dobj q ?l] => apply (sa_dobj_test_eq _ q l); cancel
  | context [sa_buf ?n q] => apply (sa_buf_test_eq _ n q); [lia | cancel]
  end end.
Ltac sa_tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => sa_tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; sa_tceq_obj
  end.

(* the join point of an if that sets the temporary t to v *)
Ltac ifpost t v := match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp t (Vint v) :: Q) (SEPx R))) end.

(* a branch excluded by the value of its test *)
Ltac sa_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* return 0: the two local z_streams are given back, the rest goes to TT *)
Ltac sa_ret := forward; Exists (Int.repr 0); entailer!.

(* the NULL test chain once one pointer was NULL: every later test is 1, then return 0 *)
Ltac sa_exit_ones :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ => ifpost t Int.one; [forward; entailer! | sa_nob | ]
  | |- semax _ _ (Ssequence (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _) _ =>
      ifpost t Int.one; [forward; entailer! | sa_nob | ]
  end;
  forward_if; [sa_ret | sa_nob].

(* an object's pointer is a concrete pointer *)
Ltac sa_mkptr P b o :=
  let Ip := fresh in
  assert_PROP (isptr P) as Ip by
    (match goal with
     | |- context [sa_dobj P ?l] => sep_apply (sa_dobj_isptr P l)
     | |- context [sa_buf ?n P] => sep_apply (sa_buf_isptr n P)
     end; entailer!);
  destruct P as [ | | | | | b o]; try contradiction; clear Ip.

(* the fields next_in and next_out of the compressor, as deflate.c's specifications hold them and as main stores
   into them *)
Lemma sa_next_in_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) v p = @field_at CS Ews t_z (DOT _next_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma sa_next_out_cs (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) v p = @field_at CS Ews t_z (DOT _next_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

(* the harness's ZLIB_VERSION literal as deflateInit2_'s version argument *)
Lemma sa_version_cs gv :
  hversion_at gv =
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0]))
    (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_stream_1).
Proof.
  unfold hversion_at. change (Zlength [49; 46; 51; 46; 50; 0]) with 6. symmetry.
  apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

(* the drawn int parameters as the signed values main passes on *)
Lemma sa_vi_signed x : Vint (Int.repr x) = vi (Int.signed (Int.repr x)).
Proof. unfold vi; rewrite Int.repr_signed; reflexivity. Qed.


(** ** The cut points of segA *)

(* segA from its thirteenth statement on (the block of NULL tests of expected, compressed and out, then new_stream,
   deflateInit2_, its return code's tests and the stores), and from its fourteenth on (new_stream onwards) *)
Definition segA_tests : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA] in (suf 12 segA) in exact x).
Definition segA_init : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA] in (suf 13 segA) in exact x).

(* the state before the NULL test of out: the draws are done, data, expected (its copy) and compressed are
   objects, out (op) is what malloc returned *)
Definition PRE_tests (gv : globals) (vc vd va : val) (lv wv mv sv : Z) (data : list Z) (cap : Z) (bd : block)
    (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (op : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out op; temp _compressed (Vptr bc oc); temp _expected (Vptr be oe); temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (Vint (Int.repr sv)); temp _mem_level (Vint (Int.repr mv));
         temp _window_bits (Vint (Int.repr wv)); temp _level (Vint (Int.repr lv));
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec op nullval then emp
       else malloc_token Ews (tarray tuchar (Zlength data)) op * data_at_ Ews (tarray tuchar (Zlength data)) op;
       sa_buf cap (Vptr bc oc); sa_dobj (Vptr be oe) data; sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd;
       data_at_ Tsh t_z vc; Rm gv; data_at_ Tsh t_p va).

(* the state after the NULL tests, none of the three pointers NULL *)
Definition PRE_init (gv : globals) (vc vd va : val) (lv wv mv sv : Z) (data : list Z) (cap : Z) (bd : block)
    (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (bout : block) (oout : ptrofs)
    : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'13 (Vint Int.zero); temp _t'12 (Vint Int.zero);
         temp _out (Vptr bout oout); temp _compressed (Vptr bc oc); temp _expected (Vptr be oe);
         temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (Vint (Int.repr sv)); temp _mem_level (Vint (Int.repr mv));
         temp _window_bits (Vint (Int.repr wv)); temp _level (Vint (Int.repr lv));
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (mem_mgr gv; sa_buf (Zlength data) (Vptr bout oout); sa_buf cap (Vptr bc oc); sa_dobj (Vptr be oe) data;
       sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd; data_at_ Tsh t_z vc; Rm gv;
       data_at_ Tsh t_p va).

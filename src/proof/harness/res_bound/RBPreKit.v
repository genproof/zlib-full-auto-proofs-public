(* Law res_bound, main: the kit of part_pre (RBKit.part_pre_stmt, statements 0-16 of main), cut in two:
   RBPreA (the values drawn, the parameters' range test and the objects allocated, statements 0-15: the only part
   that depends on the harness's size limits, RBKit.str_max) and RBPreB (the NULL test of the five objects,
   statement 16).  Between them, [A0]: everything drawn, each object allocated or NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac rp_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rp_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rp_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* laws_common.h's helpers and any_string give their objects at the adler32 unit's compspecs; main's are DCS.CS *)
Lemma rp_bytes_cs sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at DCS.CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32_dcs); [apply JMeq_refl | reflexivity]. Qed.
Lemma rp_tok_cs sh n q :
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token DCS.CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32_dcs). reflexivity. Qed.

(* a branch excluded by the value of its test *)
Ltac nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* the NULL test chain once one pointer was NULL: every later test is 1, then return 0 *)
Ltac exit_ones :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ => ifpost t Int.one; [forward; entailer! | nob | ]
  | |- semax _ _ (Ssequence (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _) _ =>
      ifpost t Int.one; [forward; entailer! | nob | ]
  end;
  forward_if False; [ret0 | nob].

(* the objects any_bytes and any_string give, as main's objects (RBKit.obj) *)
Lemma rp_obj_fold p l :
  @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l)) p *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l)) (bytes_rep l) p = obj p l.
Proof. unfold obj, BoundKit.obj. rewrite rp_bytes_cs, rp_tok_cs. reflexivity. Qed.

Lemma rp_obj_fold0 p l :
  @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l + 1)) p *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength l + 1)) (bytes_rep (l ++ [0])) p = obj p (l ++ [0]).
Proof. rewrite <- rp_obj_fold, Zlength_app. reflexivity. Qed.

Lemma obj_isptr p l : obj p l |-- !! isptr p.
Proof.
  unfold obj, BoundKit.obj. entailer!.
Qed.

(* an object (malloc'ed, any size, also 0) can be compared with NULL *)
Lemma obj_test_eq P q l : P |-- obj q l * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q ltac:(apply Zlength_nonneg)).
  eapply derives_trans; [exact HP | ]. unfold obj, BoundKit.obj. cancel.
Qed.

(* the tc goal of `!q` (or of the expression containing it) for an object q *)
Ltac tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with context [obj q ?l] => apply (obj_test_eq _ q l); cancel end end.
Ltac tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; tceq_obj
  end.

(* an object's pointer is a concrete pointer *)
Ltac mkptr p l b o :=
  let Ip := fresh in
  assert_PROP (isptr p) as Ip by (sep_apply (obj_isptr p l); entailer!);
  destruct p as [ | | | | | b o]; try contradiction; clear Ip.

Definition msuf16 : statement := ltac:(get_msuf 16%nat).

(* an object of main or NULL (malloc failed) *)
Definition optobj (p : val) (l : list Z) : mpred := if eq_dec p nullval then emp else obj p l.

(* rs_ok without the five pointers being objects (they may be NULL) *)
Definition rs_ok0 (rs : rsetup) : Prop :=
  s32 (r_level rs) /\ s32 (r_wbits rs) /\ s32 (r_mem rs) /\ s32 (r_strategy rs) /\
  0 <= r_n rs <= 4294967295 /\ 0 <= r_choice rs < 256 /\ 0 <= r_dlen rs <= 4294967295 /\
  0 <= r_xlen rs <= 65535 /\ 0 <= r_nl rs <= str_max /\ 0 <= r_cl rs <= str_max /\
  Zlength (r_data rs) = r_n rs /\ bytes (r_data rs) /\ Zlength (r_dict rs) = r_dlen rs /\ bytes (r_dict rs) /\
  Zlength (r_xf rs) = r_xlen rs /\ bytes (r_xf rs) /\ Zlength (r_nm rs) = r_nl rs /\ nzbytes (r_nm rs) /\
  Zlength (r_cm rs) = r_cl rs /\ nzbytes (r_cm rs) /\
  params_ok (r_level rs) 8 (r_wbits rs) (r_mem rs) (r_strategy rs) = true.

Lemma rs_ok_of0 (rs : rsetup) :
  rs_ok0 rs -> isptr (r_datap rs) -> isptr (r_dictp rs) -> isptr (r_xp rs) -> isptr (r_np rs) -> isptr (r_cp rs) ->
  rs_ok rs.
Proof. unfold rs_ok0, rs_ok. tauto. Qed.

(* A0 (msuf 16, before the NULL test) *)
Definition A0 (gv : globals) (vh vs : val) (rs : rsetup) : environ -> mpred :=
  PROPx [rs_ok0 rs]
  (LOCALx (rs_locals rs ++ [lvar _head t_gzh vh; lvar _strm t_strm vs; gvars gv])
  (SEPx [mem_mgr gv; optobj (r_cp rs) (r_cm rs ++ [0]); optobj (r_np rs) (r_nm rs ++ [0]);
         optobj (r_xp rs) (r_xf rs); optobj (r_dictp rs) (r_dict rs); optobj (r_datap rs) (r_data rs);
         data_at_ Tsh t_strm vs; data_at_ Tsh t_gzh vh; deflate_globals gv; version_at gv vlit])).

Definition part_preA_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val),
  (forall rs, semax Delta_m (A0 gv vh vs rs) msuf16 POST_m) ->
  semax Delta_m (PRE0 gv vh vs) msuf0 POST_m.

Definition part_preB_stmt : Prop :=
  forall {Espec : OracleKind} (gv : globals) (vh vs : val) (rs : rsetup),
  (forall rs', semax Delta_m (A1 gv vh vs rs') msuf17 POST_m) ->
  semax Delta_m (A0 gv vh vs rs) msuf16 POST_m.

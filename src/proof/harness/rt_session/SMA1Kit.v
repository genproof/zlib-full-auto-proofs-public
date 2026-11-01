(* Law rt_session (harness/rt_session.c), main's statements 0-23 (SMKit.segA1_stmt): the kit of the proof of
   statement 23, `if (!dict || !extra || !name || !comment || !data) return 0;`.

   SMSegA1.v proves statements 0-22 (the draws and the five allocations) up to the state [Q23], then statement 23
   by the cases of the five pointers, one case per file, as each costs seconds per operand at main's compspecs:
     SMA1C1.v  dict NULL                  SMA1C4.v  dict, extra, name not NULL, comment NULL
     SMA1C2.v  dict not NULL, extra NULL  SMA1C5.v  the first four not NULL, data NULL
     SMA1C3.v  dict, extra not NULL, name NULL   SMA1C6.v  none NULL: A24.
   This file holds [Q23], statement 23 [S23], the facts of the draws [a1_facts], the triple each case proves
   [a1_triple], and the lemmas and tactics on the objects and on the operands of the test. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(** ** Statement 23 and the state before it *)

Definition S23 : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA1] in (suf 23 segA1) in exact x).

(* what alloc_any_bytes and any_string give: NULL, or the object of the n bytes l (at the compspecs of
   laws_common.h) *)
Definition aobj (q : val) (n : Z) (l : list Z) : mpred :=
  if eq_dec q nullval then emp
  else @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q.

(* after statement 22: the drawn values (window_bits is wb, time utm, upto(UINT_MAX - 1) for dict_len dl) and the
   five pointers as main holds them, with the temporaries the draws left *)
Definition Q23 (gv : globals) (vh vg vc va vd : val) (lvl wb mem str ch dl cap text utm os hcrc : Z)
    (dict xf nm cm data : list Z) (dp xp np cmp datp : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _data datp; temp _comment cmp; temp _name np; temp _extra xp; temp _dict dp;
         temp _hcrc (vi hcrc); temp _os (vi os); temp _time (Vlong (Int64.repr utm));
         temp _t'16 (Vint (Int.repr utm)); temp _text (vi text); temp _out_size (Vlong (Int64.repr cap));
         temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _comment_len (Vlong (Int64.repr (Zlength cm)));
         temp _name_len (Vlong (Int64.repr (Zlength nm)));
         temp _extra_len (Vlong (Int64.repr (Zlength xf)));
         temp _dict_len (Vlong (Int64.repr (Zlength dict))); temp _t'9 (Vlong (Int64.repr dl));
         temp _with_head (Vint (Int.repr (Z.b2z ((15 <? wb) && Z.odd ch))));
         temp _t'8 (vi (Z.b2z ((15 <? wb) && Z.odd ch)));
         temp _with_dict (Vint (Int.repr (Z.b2z ((wb <=? 15) && Z.odd ch))));
         temp _t'7 (vi (Z.b2z ((wb <=? 15) && Z.odd ch)));
         temp _choice (Vint (Int.repr ch)); temp _t'5 (Val.of_bool true);
         temp _strategy (vi str); temp _mem_level (vi mem); temp _window_bits (vi wb); temp _level (vi lvl);
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; lvar _got t_g vg;
         lvar _head t_g vh; gvars gv)
  SEP (mem_mgr gv; aobj datp (Zlength data) data; aobj cmp (Zlength cm + 1) (cm ++ [0]);
       aobj np (Zlength nm + 1) (nm ++ [0]); aobj xp (Zlength xf) xf; aobj dp (Zlength dict) dict;
       data_at_ Tsh t_z vd; data_at_ Tsh t_p va; data_at_ Tsh t_z vc; data_at_ Tsh t_g vg; data_at_ Tsh t_g vh;
       Rm gv).

(* the facts of the draws (SMKit.su_dok without the pointers) *)
Definition a1_facts (lvl wb mem str ch dl cap text utm os hcrc : Z) (dict xf nm cm data : list Z) : Prop :=
  rs32 lvl /\ rs32 wb /\ rs32 mem /\ rs32 str /\ rparams_ok lvl 8 wb mem str = true /\ 0 <= ch <= 255 /\
  Zlength dict = 1 + dl /\ 0 <= dl <= 4294967294 /\ rbytes dict /\
  Zlength xf <= 65535 /\ rbytes xf /\ Zlength nm <= 4294967294 /\ nzbytes nm /\
  Zlength cm <= 4294967294 /\ nzbytes cm /\ Zlength data <= max_size /\ rbytes data /\ 0 <= cap <= max_size /\
  rs32 text /\ 0 <= utm <= 4294967295 /\ rs32 os /\ rs32 hcrc.

(* statement 23 from Q23: return 0, or A24 *)
Definition a1_triple {Espec : OracleKind} (gv : globals) (vh vg vc va vd : val)
    (lvl wb mem str ch dl cap text utm os hcrc : Z) (dict xf nm cm data : list Z) (dp xp np cmp datp : val)
    : Prop :=
  semax Delta_s (Q23 gv vh vg vc va vd lvl wb mem str ch dl cap text utm os hcrc dict xf nm cm data dp xp np cmp datp)
    S23 (overridePost (EX u : setup, A24 gv vh vg vc va vd u) POST_s).

(* the join point of an if that sets the temporary t to v *)
Ltac sa1_ifpost t v := match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end.

(** ** The five objects and their NULL tests *)

(* alloc_any_bytes and any_string give their objects at the adler32 unit's compspecs; main keeps them at its own *)
Lemma sa1_fold q n l : n = Zlength l ->
  @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q = bobj q l.
Proof.
  intros ->. unfold bobj. f_equal.
  - apply equal_f. apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity.
  - apply equal_f. apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity].
Qed.

Lemma sa1_bobj_isptr q l : bobj q l |-- !! isptr q.
Proof.
  unfold bobj. entailer!;
    match goal with Hf : field_compatible _ _ _ |- _ => exact (field_compatible_isptr _ _ _ Hf) end.
Qed.

(* a malloc'ed object (any size, also 0) can be compared with NULL *)
Lemma sa1_test_eq P q l : P |-- bobj q l * TT -> P |-- denote_tc_test_eq q (Vlong Int64.zero).
Proof.
  intros HP. apply (malloc_test_eq P (Zlength l) q ltac:(apply Zlength_nonneg)).
  eapply derives_trans; [exact HP | ]. unfold bobj. cancel.
Qed.

(* the tc goal of `!q` (or of the expression containing it) for an object q *)
Ltac sa1_tceq_obj := match goal with |- ?P |-- denote_tc_test_eq ?q _ =>
  match P with context [bobj q ?l] => apply (sa1_test_eq _ q l); cancel end end.
Ltac sa1_tceq := match goal with
  | |- _ |-- denote_tc_test_eq _ _ => sa1_tceq_obj
  | |- ENTAIL _, _ |-- tc_expr _ _ => go_lower; unfold tc_expr; simpl typecheck_expr; cbv beta iota; sa1_tceq_obj
  end.

(* a branch excluded by the value of its test *)
Ltac sa1_nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* the end of an operand's branch: the temporary holds the value of the join point, up to conversion *)
Ltac sa1_close := first [apply ENTAIL_refl | entailer!].

(* return 0: the five locals are given back, the rest goes to TT *)
Ltac sa1_ret := forward; Exists (Int.repr 0); entailer!.

(* the NULL test chain once one pointer was NULL: every later operand is 1, then return 0 *)
Ltac sa1_ones :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ =>
      sa1_ifpost t (Vint Int.one); [forward; sa1_close | sa1_nob | ]
  end;
  forward_if; [sa1_ret | sa1_nob].

(* the ifs of eq_dec a destruct decided *)
Ltac sa1_if_simpl :=
  repeat match goal with
  | |- context [if @left ?A ?B ?h then ?x else ?y] => change (if @left A B h then x else y) with x
  | |- context [if @right ?A ?B ?h then ?x else ?y] => change (if @right A B h then x else y) with y
  end.

(* an object's pointer is a concrete pointer *)
Ltac sa1_mkptr P b o :=
  let Ip := fresh in
  assert_PROP (isptr P) as Ip by
    (match goal with |- context [bobj P ?l] => sep_apply (sa1_bobj_isptr P l) end; entailer!);
  destruct P as [ | | | | | b o]; try contradiction; clear Ip.

(* a pointer known to be NULL: its object is emp *)
Ltac sa1_nul := match goal with |- context [eq_dec nullval nullval] =>
  let Hc := fresh in destruct (eq_dec nullval nullval) as [_ | Hc]; [sa1_if_simpl | contradiction Hc; reflexivity]
  end.

(* a pointer q known not to be NULL: the object of the bytes l *)
Ltac sa1_nn q l :=
  let Hc := fresh in
  destruct (eq_dec q nullval) as [Hc | _]; [contradiction | sa1_if_simpl];
  rewrite (sa1_fold q _ l) by (rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia).

(* the start of a case: the state and the statement unfolded, the left-nested operands of statement 23 in a row *)
Ltac sa1_start :=
  unfold a1_triple, Q23, S23, aobj, POST_s; unfold Delta_s; simplify_func_tycontext; abbreviate_semax;
  rewrite <- !seq_assoc.

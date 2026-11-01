(* Law res_bound, main: the four parameters and their range test (gp_assume(deflate_params_ok(...))), data_len,
   data, choice, the four lengths (data_len and dict_len by nondet_u32, whose 32-bit result is cast to size_t;
   extra_len, name_len and comment_len by upto: the harness's size limits, RBKit.str_max for name and comment),
   dict, extra (alloc_any_bytes), name, comment (any_string): msuf 0 -> msuf 16 (RBPreKit.part_preA_stmt). *)
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
Require Import Zlib.proof.harness.res_bound.RBPreKit.
Require Import Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma part_preA : part_preA_stmt.
Proof.
  intros Espec gv vh vs HA0. unfold Delta_m, PRE0, msuf0, POST_m, R. simplify_func_tycontext. Intros.
  forward_call tt. Intros u_level. forward_call tt. Intros u_wbits.
  forward_call tt. Intros u_mem. forward_call tt. Intros u_strat.
  (* gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy)): the parameters are in zlib.h's ranges *)
  pose proof (Int.signed_range (Int.repr u_level)). pose proof (Int.signed_range (Int.repr u_wbits)).
  pose proof (Int.signed_range (Int.repr u_mem)). pose proof (Int.signed_range (Int.repr u_strat)).
  forward_call (Int.signed (Int.repr u_level), Int.signed (Int.repr u_wbits), Int.signed (Int.repr u_mem),
                Int.signed (Int.repr u_strat)).
  { rewrite !Int.repr_signed. entailer!. }
  forward_call (if deflate_params_valid (Int.signed (Int.repr u_level)) (Int.signed (Int.repr u_wbits))
                   (Int.signed (Int.repr u_mem)) (Int.signed (Int.repr u_strat)) then Int.one else Int.zero).
  { match goal with |- context [deflate_params_valid ?a ?b ?c ?d] => destruct (deflate_params_valid a b c d) end;
      entailer!. }
  Intros.
  assert (Hv : params_ok (Int.signed (Int.repr u_level)) 8 (Int.signed (Int.repr u_wbits))
                 (Int.signed (Int.repr u_mem)) (Int.signed (Int.repr u_strat)) = true).
  { rewrite <- Zlib.proof.harness.laws_session.Facts.deflate_params_valid_ok.
    match goal with H : (if ?c then _ else _) <> Int.zero |- _ => destruct c; [reflexivity | contradiction] end. }
  do 2 rewrite <- seq_assoc. forward_call tt. Intros n. forward. rewrite Int.unsigned_repr by rep_lia.
  forward_call (n, gv). Intros vret. destruct vret as [datap data]. simpl fst in *; simpl snd in *.
  forward_call tt. Intros ch.
  do 2 rewrite <- seq_assoc. forward_call tt. Intros dlen. forward. rewrite Int.unsigned_repr by rep_lia.
  forward_call 65535. Intros xlen.
  forward_call str_max. Intros nl.
  forward_call str_max. Intros cl. pose proof str_max_range as Hsm.
  forward_call (dlen, gv). Intros vret. destruct vret as [dictp dict]. simpl fst in *; simpl snd in *.
  forward_call (xlen, gv). Intros vret. destruct vret as [xp xf]. simpl fst in *; simpl snd in *.
  forward_call (nl, gv). Intros vret. destruct vret as [np nm]. simpl fst in *; simpl snd in *.
  forward_call (cl, gv). Intros vret. destruct vret as [cp cm]. simpl fst in *; simpl snd in *.
  subst n dlen xlen nl cl. rewrite !rp_obj_fold, !rp_obj_fold0.
  assert (Elv : Vint (Int.repr u_level) = vi (Int.signed (Int.repr u_level)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Ewv : Vint (Int.repr u_wbits) = vi (Int.signed (Int.repr u_wbits)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Emv : Vint (Int.repr u_mem) = vi (Int.signed (Int.repr u_mem)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Esv : Vint (Int.repr u_strat) = vi (Int.signed (Int.repr u_strat)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  rewrite Elv, Ewv, Emv, Esv. clear Elv Ewv Emv Esv.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  set (rs := mkRS (Int.signed (Int.repr u_level)) (Int.signed (Int.repr u_wbits)) (Int.signed (Int.repr u_mem))
               (Int.signed (Int.repr u_strat)) (Zlength data) ch (Zlength dict) (Zlength xf) (Zlength nm)
               (Zlength cm) datap dictp xp np cp data dict xf nm cm).
  assert (OK : rs_ok0 rs).
  { assert (B : forall l : list Z, Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes l)
      by (intros l Fl; eapply Forall_impl; [ | exact Fl ]; cbv beta; rep_lia).
    assert (NB : forall l : list Z, Forall (fun b => 0 < b <= Byte.max_unsigned) l -> nzbytes l)
      by (intros l Fl; eapply Forall_impl; [ | exact Fl ]; cbv beta; rep_lia).
    unfold rs_ok0, s32; cbn. repeat split; auto; rep_lia. }
  eapply semax_pre; [ | apply (HA0 rs) ].
  unfold A0, optobj, rs_locals. subst rs. cbn [r_level r_wbits r_mem r_strategy r_n r_choice r_dlen r_xlen r_nl
    r_cl r_datap r_dictp r_xp r_np r_cp r_data r_dict r_xf r_nm r_cm app].
  unfold vl. entailer!.
Qed.

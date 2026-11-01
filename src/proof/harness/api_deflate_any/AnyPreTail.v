(* Law api_deflate_any: the loop body from the NULL test of the piece and the output space to set_buffer
   (AnyKit.any_pre_stmt's second half): when the piece or the output space is NULL main returns 0, else it copies
   the output space ([before]; NULL: return 0) and offers the piece and the output space on the stream.  [M_at]
   is main's state after alloc_any_bytes; AnyPre.v proves the body up to it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.api_deflate_any.AnyFacts.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Zlib.proof.harness.api_deterministic.DetPreOffer2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Zlib.proof.harness.laws_session.Spec.
Require Import Zlib.proof.harness.api_deflate_any.AnyAt.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.

(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which can take minutes on main's
   LOCAL list (it holds the temporaries _out and _out_size); the same list built syntactically *)
Ltac rlt_list i L := Zlib.proof.harness.api_deterministic.DetPreOffer2.rlt_list i L.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* a branch of an if whose condition is known: its hypothesis is false *)
Ltac any_false :=
  first [ contradiction | discriminate
        | match goal with H : _ <> _ |- _ => contradiction H; reflexivity end ].

(* (tbool) (p == NULL) is 0 for a malloc'd p *)
Ltac any_nonnull :=
  match goal with |- context [sem_cmp_pp Ceq ?p _] =>
    destruct p; try contradiction;
    match goal with H : malloc_compatible _ _ |- _ => simpl in H; try contradiction end;
    reflexivity
  end.

(* return 0 after a failed allocation: the stream back to main's local, both locals at the law's compspecs
   (POST_m's frame), everything else dropped *)
Ltac any_ret :=
  forward; Exists (Int.repr 0); entailer!;
  repeat match goal with |- context [DetKit2.shead ?p ?s ?sp ?ti ?to ?m ?a ?g] =>
    sep_apply (DetKit2.det_shead_back p s sp ti to m a g) end;
  rewrite any_strm_cs, any_at_cs; cancel.

(* the loop body from the NULL test on (statement 5, AnyKit.v) *)
Definition lsuf5 : statement := ltac:(get_lsuf 5%nat).

(* main's state after the piece and the output space were allocated (each maybe NULL): [take], [room] =
   out_size, the flush [fl], the output space's bytes [bs] *)
Definition M_at (J : det_inv) (n : Z) (data : list Z) (datap v sp : val) (gv : globals) (ap : val) (ls : lstate)
    (take room fl : Z) (bs : list Z) (piece out : val) : environ -> mpred :=
  PROP (J_ok J n data datap ls; 0 <= take <= 4294967295; ls_read ls + take <= n;
        Int.min_signed <= fl <= Int.max_signed; ls_fin ls <> None -> fl = Z_FINISH /\ take = ls_left ls;
        0 <= room <= 4294967295; Zlength bs = room; is_bytes bs)
  LOCAL (temp _data datap; temp _data_len (vl n); temp _read (vl (ls_read ls)); temp _left (vl (ls_left ls));
         temp _finishing (vi (fin_flag (ls_fin ls))); temp _take (vl take); temp _out_size (vl room);
         temp _flush (vi fl); temp _piece piece; temp _out out; lvar _strm t_strm v; lvar _at LS.t_pos ap;
         gvars gv)
  SEP (mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
       if eq_dec piece nullval then emp
       else malloc_token Ews (tarray tuchar take) piece *
            data_at Ews (tarray tuchar take) (bytes_rep (sublist (ls_read ls) (ls_read ls + take) data)) piece;
       if eq_dec out nullval then emp
       else malloc_token Ews (tarray tuchar room) out * data_at Ews (tarray tuchar room) (bytes_rep bs) out;
       DetKit2.shead v (ls_s ls) sp (ls_read ls) (ls_tout ls) (ls_msgv ls) (ls_adler ls) gv; at_free ap; TT).

(* the piece or the output space is NULL: main returns 0 *)
Lemma any_pre_null {Espec : OracleKind} J n data datap v sp gv ap ls take room fl bs piece out :
  piece = nullval \/ out = nullval ->
  @semax AnyCS.CS _ Delta_m (M_at J n data datap v sp gv ap ls take room fl bs piece out) lsuf5 (Rbody J n data datap v sp gv ap).
Proof.
  intros Hnn.
  unfold M_at. Intros.
  unfold lsuf5, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  abbreviate_semax.
  freeze FR := (mem_mgr gv) (deflate_globals gv) (data_at Ews _ _ datap) (DetKit2.shead v _ _ _ _ _ _ _)
    (at_free ap) TT.
  (* floyd's own reassociation elaborates at the local instance DCS.CS, not at the goal's AnyCS.CS *)
  rewrite <- seq_assoc.
  destruct (eq_dec piece nullval) as [E1|E1].
  { subst piece.
    forward_if (temp _t'19 (vi 1)); [ | any_false | ]. { forward. apply ENTAIL_refl. }
    forward_if; [ | any_false ].
    thaw FR. any_ret. }
  Intros.
  destruct (eq_dec out nullval) as [E2|E2]; [ | destruct Hnn; contradiction ].
  subst out.
  forward_if (temp _t'19 (vi 1)); [ any_false | | ]. { forward. entailer!. }
  forward_if; [ | any_false ].
  thaw FR. any_ret.
Qed.

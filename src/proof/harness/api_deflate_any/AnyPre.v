(* Law api_deflate_any: the loop body's first part (AnyKit.any_pre_stmt): take, out_size, flush, the piece, the
   output space and its copy (return 0 when an allocation fails), set_buffer; the stream as C_at with c0.  This file
   proves the body up to alloc_any_bytes (main's state AnyPreTail.M_at); from the NULL test on the body is
   AnyPreTail.v (an object is NULL) and AnyPreOffer.v (none is). *)
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
Require Zlib.proof.harness.api_deflate_any.AnyCodes.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.api_deterministic.DetMem2.
Require Zlib.proof.harness.api_deterministic.DetMem2b.
Require Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deflate_any.AnyCS.
Require Import Zlib.proof.harness.api_deflate_any.AnyMainStmt.
Require Import Zlib.proof.harness.api_deflate_any.AnyKit.
Require Zlib.proof.harness.api_deterministic.DetPreOffer2.
Require Import Zlib.proof.harness.api_deflate_any.AnyPreTail.
Require Import Zlib.proof.harness.api_deflate_any.AnyPreOffer.
Require Import Zlib.harness.api_deflate_any.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.


Ltac rlt_list i L := Zlib.proof.harness.api_deterministic.DetPreOffer2.rlt_list i L.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* from the NULL test on: return 0 when an object is NULL, else the copy of the output space and set_buffer *)
Lemma any_pre_tail {Espec : OracleKind} J n data datap v sp gv ap ls take room fl bs piece out :
  (forall ci, @semax AnyCS.CS _ Delta_m (C_at J n data datap v sp gv ap ls ci (c0 ls)) lsuf9 (Rbody J n data datap v sp gv ap)) ->
  @semax AnyCS.CS _ Delta_m (M_at J n data datap v sp gv ap ls take room fl bs piece out) lsuf5 (Rbody J n data datap v sp gv ap).
Proof.
  intros HC.
  destruct (eq_dec piece nullval); [ apply any_pre_null; tauto | ].
  destruct (eq_dec out nullval); [ apply any_pre_null; tauto | ].
  apply any_pre_ok; auto.
Qed.

(* copy_of(data + read, take)'s slice: [read, read + take) of the data *)
Lemma any_copy_cbuf (data : list Z) (datap : val) (n rd tk : Z) :
  Zlength data = n -> bytes data -> 0 <= rd -> 0 <= tk -> rd + tk <= n ->
  cbuf_ok false (offset_val rd datap) Ews datap rd n tk (map vi data) (sublist rd (rd + tk) data).
Proof.
  intros H1 H2 H3 H4 H5.
  unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist by lia; lia | ]. split.
  - unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact H2 ]. simpl; intros; rep_lia.
  - unfold bytes_rep. rewrite sublist_map. reflexivity.
Qed.

Lemma any_pre : any_pre_stmt.
Proof.
  intros Espec J n data datap v sp gv ap ls HC.
  unfold J_at, J_ok, J_loc, J_sep, setup_ok. Intros.
  unfold lbody, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  abbreviate_semax.
  (* floyd's own reassociation elaborates at the local instance DCS.CS, not at the goal's AnyCS.CS: main's
     sequences are reassociated by hand *)
  (* take = finishing ? left : upto(clip(data_len - read)) *)
  rewrite <- seq_assoc.
  forward_if (EX take : Z,
    PROP (0 <= take <= 4294967295; ls_read ls + take <= n; ls_fin ls <> None -> take = ls_left ls)
    LOCAL (temp _t'11 (vl take); temp _data datap; temp _data_len (vl n); temp _read (vl (ls_read ls));
           temp _left (vl (ls_left ls)); temp _finishing (vi (fin_flag (ls_fin ls))); lvar _strm t_strm v;
           lvar _at LS.t_pos ap; gvars gv)
    SEP (mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
         DetKit2.shead v (ls_s ls) sp (ls_read ls) (ls_tout ls) (ls_msgv ls) (ls_adler ls) gv; at_free ap; TT)).
  { destruct (ls_fin ls) as [R|] eqn:EF; [ | contradiction ].
    forward. Exists (ls_left ls). entailer!. }
  { destruct (ls_fin ls) as [R|] eqn:EF; [ discriminate | ].
    forward_call (n - ls_read ls).
    forward_call (Z.min (n - ls_read ls) Int.max_unsigned).
    Intros t. forward. Exists t. entailer!. }
  Intros take. forward.
  (* out_size = nondet_u32() *)
  rewrite <- !seq_assoc. forward_call tt. Intros room. forward.
  rewrite Int.unsigned_repr by rep_lia.
  (* flush = finishing ? Z_FINISH : (int) nondet_u32(): any int *)
  rewrite <- seq_assoc.
  forward_if (EX fl : Z,
    PROP (Int.min_signed <= fl <= Int.max_signed; ls_fin ls <> None -> fl = 4)
    LOCAL (temp _t'15 (vi fl); temp _out_size (vl room); temp _take (vl take); temp _data datap;
           temp _data_len (vl n); temp _read (vl (ls_read ls)); temp _left (vl (ls_left ls));
           temp _finishing (vi (fin_flag (ls_fin ls))); lvar _strm t_strm v; lvar _at LS.t_pos ap; gvars gv)
    SEP (mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
         DetKit2.shead v (ls_s ls) sp (ls_read ls) (ls_tout ls) (ls_msgv ls) (ls_adler ls) gv; at_free ap; TT)).
  { forward. Exists 4. entailer!. }
  { destruct (ls_fin ls) as [R|] eqn:EF; [ discriminate | ].
    forward_call tt. Intros f. forward. Exists (Int.signed (Int.repr f)).
    pose proof (Int.signed_range (Int.repr f)).
    entailer!. unfold vi. rewrite Int.repr_signed. reflexivity. }
  Intros fl. forward.
  (* piece = copy_of(data + read, take) *)
  rewrite <- !seq_assoc.
  forward_call (offset_val (ls_read ls) datap, Ews, datap, ls_read ls, n, map vi data, take,
                sublist (ls_read ls) (ls_read ls + take) data, gv).
  { entailer!. simpl. destruct datap; try contradiction.
    unfold vl; simpl. f_equal; f_equal; f_equal.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_int64.
    rewrite Int64.unsigned_repr by rep_lia; reflexivity. }
  { rewrite DetMem2.det_bytes_cs. cancel. }
  { apply any_copy_cbuf; auto; lia. }
  Intros piece. rewrite !DetMem2.det_bytes_cs, !DetMem2.det_token_cs.
  forward.
  (* out = alloc_any_bytes(out_size) *)
  forward_call (room, gv).
  Intros vret. destruct vret as [out bs]. cbn [fst snd] in *.
  rewrite !DetMem2.det_bytes_cs, !DetMem2.det_token_cs.
  (* from the NULL test on: AnyPreTail.v, AnyPreOffer.v *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  eapply semax_pre; [ | apply (any_pre_tail J n data datap v sp gv ap ls take room fl bs piece out HC) ].
  unfold M_at. entailer!.
  unfold J_ok, setup_ok. split; [ split; [ auto | split; [ lia | split; [ reflexivity | auto ] ] ] | ]. tauto.
Qed.

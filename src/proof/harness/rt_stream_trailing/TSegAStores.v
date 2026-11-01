(* Law rt_stream_trailing (harness/rt_stream_trailing.c), main's setup segment after a successful deflateInit2_
   (statements 17-20 of main's body): the stores of next_in = data, next_out = compressed, offered = 0 and
   flush = Z_NO_FLUSH, and the deflate loop's invariant DI_t with an empty input and output so far.  The proof is
   rt_stream's (rt_stream/USegAStores.v) on this program's main. *)
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
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.proof.harness.rt_stream_trailing.TSegAKit.
Require Import Zlib.harness.rt_stream_trailing.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Module DC := Zlib.deflate.code.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac st_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in st_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := st_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma st_stores {Espec : OracleKind} J gv vc vd va lvl wb mem str data cap bd od be oe bc oc bout oout s z' msgv' :
  urts_dfacts J -> 0 <= Zlength data <= max_size -> 0 <= cap <= max_size -> is_bytes data ->
  rs32 lvl -> rs32 wb -> rs32 mem -> rs32 str -> rparams_ok lvl 8 wb mem str = true ->
  J wb [] [] None s (z_total_in z') (z_total_out z') (z_adler z') ->
  msg_ok (z_msg z') msgv' ->
  semax Delta_t (PRE_stores_t gv vc vd va lvl wb mem str data cap bd od be oe bc oc bout oout s z' msgv') segA_stores_t
    (normal_ret_assert (EX u : setup, EX l : dls, DI_t gv vc vd va J u l)).
Proof.
  intros JF H3 H4 H6 Hlev Hwb Hmem Hstr Hpar HJ H10. unfold PRE_stores_t, segA_stores_t.
  unfold Delta_t; simplify_func_tycontext. abbreviate_semax.
  (* next_in = data, next_out = compressed, offered = 0, flush = Z_NO_FLUSH *)
  rewrite sa_next_in_cs, sa_next_out_cs.
  forward. forward. forward. forward.
  rewrite <- sa_next_in_cs, <- sa_next_out_cs, <- st_version_cs.
  change (Z_OK =? Z_OK) with true in *. change (Z_OK =? Z_VERSION_ERROR) with false in *. cbn [rfv] in *.
  destruct (ud_range _ JF _ _ _ _ _ _ _ _ HJ) as (Rtin & Rtout & Radl & _).
  Exists (mkSU lvl wb mem str data cap (Vptr bd od) (Vptr be oe) (Vptr bc oc) (Vptr bout oout))
    (mkDL [] [] None 0 0 (z_msg z')
       (mkCS s (offset_val 0 (Vptr bd od)) 0 (z_total_in z') (offset_val 0 (Vptr bc oc)) 0 (z_total_out z') msgv'
          (z_adler z'))).
  unfold DI_t, su_locals, lv_locals, cstream, srest, dobj, eobj, cobj, oobj, Rm_t.
  cbn [su_level su_wbits su_mem su_strategy su_data su_cap su_dp su_ep su_cp su_op dl_D dl_O dl_fin dl_off dl_flush
       dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler app].
  rewrite !isptr_offset_val_zero by exact I.
  rewrite !sa_buf_cbytes. unfold sa_dobj, api_fields, reset_fields.
  entailer!.
  assert (U0 : u32_ok 0) by (unfold u32_ok; rep_lia).
  assert (Rd : rbytes data) by (eapply Forall_impl; [ | exact H6]; simpl; intros; rep_lia).
  split; [| split; [| split; exact U0]].
  - unfold su_ok; cbn [su_level su_wbits su_mem su_strategy su_data su_cap su_dp su_ep su_cp su_op].
    unfold rs32 in Hlev, Hwb, Hmem, Hstr; unfold max_size in *; repeat split; try exact I; try assumption; rep_lia.
  - unfold dl_ok; cbn [su_level su_wbits su_mem su_strategy su_data su_cap su_dp su_ep su_cp su_op dl_D dl_O dl_fin
       dl_off dl_flush dl_msg dl_c cs_s cs_ni cs_ain cs_tin cs_no cs_aout cs_tout cs_msgv cs_adler].
    rewrite Zlength_nil, sublist_nil.
    split; [exact HJ|]. split; [reflexivity|]. split; [rep_lia|]. split; [lia|].
    split; [intros Hf; exfalso; compute in Hf; discriminate Hf|]. split; [discriminate|]. split; [lia|]. split; [constructor|].
    split; [exact H10|]. simpl offset_val; rewrite !Ptrofs.add_zero; split; reflexivity.
Qed.

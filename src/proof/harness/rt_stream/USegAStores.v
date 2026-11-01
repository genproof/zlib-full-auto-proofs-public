(* Law rt_stream (data of any length), main's setup segment after a successful deflateInit2_ (statements 17-20
   of main's body): the stores of next_in = data, next_out = compressed, offered = 0 and flush = Z_NO_FLUSH, and
   the deflate loop's invariant DI with an empty input and output so far.  Round 1's MainSegAStores.v with the
   sizes of round 2's harness. *)
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
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* segA from its eighteenth statement on (the four stores) *)
Definition segA_stores : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [suf segA] in (suf 17 segA) in exact x).

(* the state after deflateInit2_ returned Z_OK with the state s and the stream fields z' *)
Definition PRE_stores (gv : globals) (vc vd va : val) (lvl wb mem str : Z) (data : list Z) (cap : Z) (bd : block)
    (od : ptrofs) (be : block) (oe : ptrofs) (bc : block) (oc : ptrofs) (bout : block) (oout : ptrofs) (s : dstate) (z' : strm)
    (msgv' : val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out (Vptr bout oout); temp _compressed (Vptr bc oc); temp _expected (Vptr be oe);
         temp _data (Vptr bd od);
         temp _out_size (Vlong (Int64.repr cap)); temp _data_len (Vlong (Int64.repr (Zlength data)));
         temp _strategy (vi str); temp _mem_level (vi mem); temp _window_bits (vi wb); temp _level (vi lvl);
         lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
  SEP (dstream 2 (Some s) vc nullval gv;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) nullval vc;
       reset_fields vc (rfv (Z_OK =? Z_OK) (z_total_in z') Vundef) (rfv (Z_OK =? Z_OK) (z_total_out z') Vundef)
         msgv' (rfv (Z_OK =? Z_OK) (z_adler z') Vundef);
       @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar (Zlength [49; 46; 51; 46; 50; 0]))
         (map vi [49; 46; 51; 46; 50; 0]) (gv ___stringlit_rt_stream_1);
       mem_mgr gv; deflate_globals gv;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_in) (vi 0) vc;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) nullval vc;
       @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_out) (vi 0) vc;
       BoundKit.strm_pad vc; sa_buf (Zlength data) (Vptr bout oout); sa_buf cap (Vptr bc oc);
       sa_dobj (Vptr be oe) data; sa_dobj (Vptr bd od) data; data_at_ Tsh t_z vd; data_at_ BoundKit.Ecomp t_z vc;
       Zlib.proof.inflate.Rep.tables_rep Ers gv; Zlib.proof.inflate_api.Spec5.version_lit gv; data_at_ Tsh t_p va).

Lemma sa_stores {Espec : OracleKind} J gv vc vd va lvl wb mem str data cap bd od be oe bc oc bout oout s z' msgv' :
  urts_dfacts J -> 0 <= Zlength data <= max_size -> 0 <= cap <= max_size -> is_bytes data ->
  rs32 lvl -> rs32 wb -> rs32 mem -> rs32 str -> rparams_ok lvl 8 wb mem str = true ->
  J wb [] [] None s (z_total_in z') (z_total_out z') (z_adler z') ->
  msg_ok (z_msg z') msgv' ->
  semax Delta_m (PRE_stores gv vc vd va lvl wb mem str data cap bd od be oe bc oc bout oout s z' msgv') segA_stores
    (normal_ret_assert (EX u : setup, EX l : dls, DI gv vc vd va J u l)).
Proof.
  intros JF H3 H4 H6 Hlev Hwb Hmem Hstr Hpar HJ H10. unfold PRE_stores, segA_stores.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  (* next_in = data, next_out = compressed, offered = 0, flush = Z_NO_FLUSH *)
  rewrite sa_next_in_cs, sa_next_out_cs.
  forward. forward. forward. forward.
  rewrite <- sa_next_in_cs, <- sa_next_out_cs, <- sa_version_cs.
  change (Z_OK =? Z_OK) with true in *. change (Z_OK =? Z_VERSION_ERROR) with false in *. cbn [rfv] in *.
  destruct (ud_range _ JF _ _ _ _ _ _ _ _ HJ) as (Rtin & Rtout & Radl & _).
  Exists (mkSU lvl wb mem str data cap (Vptr bd od) (Vptr be oe) (Vptr bc oc) (Vptr bout oout))
    (mkDL [] [] None 0 0 (z_msg z')
       (mkCS s (offset_val 0 (Vptr bd od)) 0 (z_total_in z') (offset_val 0 (Vptr bc oc)) 0 (z_total_out z') msgv'
          (z_adler z'))).
  unfold DI, su_locals, lv_locals, cstream, srest, dobj, eobj, cobj, oobj, Rm.
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

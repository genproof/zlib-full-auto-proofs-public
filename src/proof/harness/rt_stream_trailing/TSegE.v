(* Law rt_stream_trailing (harness/rt_stream_trailing.c): main's final checks (statements 35...: next_in == input + compressed_len, next_out == out + data_len and the bytes against the copy expected) and the return, from IE_t. *)
(* The proof is rt_stream's (USegE.useg_e) on this program: next_in is compared with input + compressed_len, a
   pointer into or one past the end of the input object (|O| <= |src|), and the input object is given back to
   TT at the return. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegE.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainStmt.
Require Import Zlib.proof.harness.rt_stream_trailing.TMainKit.
Require Import Zlib.harness.rt_stream_trailing.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (e.g. _i against _input); each identifier comparison is decided by vm_compute instead. *)
Ltac te_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in te_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := te_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

Lemma tseg_e : segE_t_stmt.
Proof.
  intros Espec gv vc vd va u O c src ip z L.
  unfold segE_t, IE_t. Intros.
  rewrite istreamA_unfold. unfold cobj, oobj, dobj, eobj, su_locals, lv_locals, iobj. Intros. cbn [app].
  destruct u as [lv wb ml st data cap dp ep cp op]; unfold su_ok in H; simpl in *.
  destruct H as (Hl & Hw & Hm & Hs & Hn & Hd & Hc & Pd & Pc & Po).
  destruct H3 as (Hso & Hsub & Hsb).
  assert_PROP (isptr ep) as Pe by entailer!.
  unfold max_size in Hn, Hc, Hso.
  unfold istrm_tup. rewrite H1, H2.
  forward.
  forward_call (Int.repr 1).
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans; [ | apply (test_eq_self TT ip (Zlength O) (Zlength src) (map vi src))]; [cancel | | auto].
    pose proof (Zlength_nonneg O). lia. }
  { entailer!. rewrite add_ptr_long_tuchar by (auto; rep_lia). destruct ip; try contradiction.
    simpl. unfold sem_cmp_pp. simpl. rewrite peq_true, Ptrofs.eq_true. reflexivity. }
  forward.
  forward_if (PROP () LOCAL (temp _t'41 (vi 1); temp _compressed_len (vl (Zlength O));
    temp _after (vl (Zlength src - Zlength O)); temp _input ip; temp _level (vi lv);
    temp _window_bits (vi (IFacts.rts_iw wb)); temp _mem_level (vi ml); temp _strategy (vi st);
    temp _data_len (vl (Zlength data)); temp _out_size (vl cap); temp _data dp; temp _expected ep;
    temp _compressed cp;
    temp _out op; lvar _decompressor t_z vd; lvar _at t_p va; lvar _compressor t_z vc; gvars gv)
   SEP (data_at Tsh t_z
          (offset_val (Zlength O) ip, (vi (zf_ai z), (vl (zf_tin z), (offset_val (Zlength data) op,
           (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
           (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
           (adler_v (i_wrap (l_s L) =? 0) z Vundef, zf_res z))))))))))))) vd;
        state_mem gv vd L; head_mem L; cstream gv vc c; mem_mgr gv; zfuncs gv; Rm_t gv;
        malloc_token Ews (tarray tuchar (Zlength data)) dp;
        data_at Ews (tarray tuchar (Zlength data)) (map vi data) dp;
        malloc_token Ews (tarray tuchar (Zlength data)) ep;
        data_at Ews (tarray tuchar (Zlength data)) (map vi data) ep;
        malloc_token Ews (tarray tuchar cap) cp; data_at Ews (tarray tuchar cap) (cbytes cap O) cp;
        malloc_token Ews (tarray tuchar (Zlength data)) op;
        data_at Ews (tarray tuchar (Zlength data)) (cbytes (Zlength data) data) op; data_at_ Tsh t_p va;
        malloc_token Ews (tarray tuchar (Zlength src)) ip;
        data_at Ews (tarray tuchar (Zlength src)) (map vi src) ip)).
  { rewrite add_ptr_long_tuchar by (auto; rep_lia).
    eapply derives_trans;
      [ | apply (test_eq_self TT op (Zlength data) (Zlength data) (cbytes (Zlength data) data))];
      [cancel | | auto].
    pose proof (Zlength_nonneg data). lia. }
  { rewrite <- (bytes_a Ews (Zlength data) (cbytes (Zlength data) data) op).
    rewrite <- (bytes_a Ews (Zlength data) (map vi data) ep).
    forward_call (op, Ews, op, 0, Zlength data, cbytes (Zlength data) data, data,
                  ep, Ews, ep, 0, Zlength data, map vi data, data, Zlength data).
    { split; [apply cbuf_ok_data | apply cbuf_ok_data']; auto. }
    rewrite (bytes_a Ews (Zlength data) (cbytes (Zlength data) data) op).
    rewrite (bytes_a Ews (Zlength data) (map vi data) ep).
    destruct (list_eq_dec Z.eq_dec data data) as [_ | NE]; [ | congruence].
    forward. unfold POST_t. simpl RA_normal. entailer!. }
  { exfalso. rewrite add_ptr_long_tuchar in H by (auto; rep_lia). congruence. }
  forward_call (Int.repr 1).
  sep_apply (cstream_back gv vc c).
  forward.
  Exists (Int.repr 0).
  match goal with |- context [data_at Tsh t_z ?v vd] => sep_apply (data_at_data_at_ Tsh t_z v vd) end.
  entailer!.
Qed.

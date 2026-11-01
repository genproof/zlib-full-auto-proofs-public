(* Law api_deterministic (data of any length): the loop body up to the nondet_u8 test (DetKit2.det_pre_stmt): the
   next [offered] and flush (Z_FINISH only when the rest of the data fits in one call), take = clip(offered - read),
   the output space, the two copies of the piece and the two output spaces; from the NULL test on (NULL ends the
   run, else offer on both streams) the body is DetPreNull2.det_pre_tail. *)
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
Require Import Zlib.proof.deflate.DetFacts2.
Require Zlib.proof.deflate.DModel5.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_deterministic.DetCS2.
Require Import Zlib.proof.harness.api_deterministic.DetMainStmt2.
Require Import Zlib.proof.harness.api_deterministic.DetKit2.
Require Import Zlib.proof.harness.api_deterministic.DetPreOffer2.
Require Import Zlib.proof.harness.api_deterministic.DetPreNull2.
Require Import Zlib.harness.api_deterministic.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.


(* VST's after_forward_call simplifies [remove_localdef_temp i L] with [simpl], which takes minutes when the
   identifiers are built by $"name" (here out_second); the same list built syntactically (DetPreOffer2.rlt_list) *)
Ltac rlt_list i L := DetPreOffer2.rlt_list i L.
Local Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u' := rlt_list i L in change (remove_localdef_temp i L) with u' end.

(* copy_of(data + read, take)'s side conditions: the argument values and the slice [read, read + take) of data *)
Ltac det_copy_args :=
  entailer!; simpl;
  match goal with H : isptr ?d |- context [?d] => destruct d; try contradiction end;
  unfold vl; simpl; f_equal; f_equal; f_equal;
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_int64;
  rewrite Int64.unsigned_repr by rep_lia; reflexivity.

Lemma det_copy_cbuf (data : list Z) (datap : val) (n rd off : Z) :
  Zlength data = n -> bytes data -> 0 <= rd <= off -> off <= n ->
  cbuf_ok false (offset_val rd datap) Ews datap rd n (off - rd) (map vi data) (sublist rd off data).
Proof.
  intros H1 H2 H3 H4.
  unfold cbuf_ok. split; [reflexivity | ]. split; [auto | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist by lia; lia | ]. split.
  - unfold is_bytes. apply Forall_sublist. eapply Forall_impl; [ | exact H2 ]. simpl; intros; rep_lia.
  - replace (rd + (off - rd)) with off by lia. unfold bytes_rep. rewrite sublist_map. reflexivity.
Qed.

(* The helpers of the NULL test and the offers live in DetPreOffer2.v (used there and in the NULL files); the
   names below are those of this file's earlier version. *)

(* a branch of an if whose condition is known: its hypothesis is false *)
Ltac det_false := DetPreOffer2.det_false.

(* A stream between iterations as offer's precondition (the whole z_stream at the compress unit's compspecs),
   the rest of its state kept as a wand, and the other half of main's local *)
Lemma det_offer_open (p : val) (s : dstate) (sp : val) (tin tout : Z) (msgv : val) (adler : Z) (gv : globals) :
  shead p s sp tin tout msgv adler gv |--
  EX nin : val, EX ain : Z, EX nout : val, EX aout : Z,
    !! (u64_ok tin /\ u64_ok tout /\ u64_ok adler) &&
    (@data_at Zlib.units.Compress.CS Ews t_zs
       (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv sp (gv DC._zcalloc) (gv DC._zcfree) nullval
          (det_dt s) (vl adler) Vundef) p *
     (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p nullval sp gv) *
     data_at_ BoundKit.Ecomp t_strm p).
Proof. exact (DetPreOffer2.det_offer_open p s sp tin tout msgv adler gv). Qed.

(* offer's postcondition back to a live stream with the offered buffers ([za], [zf]: the allocator's
   function pointers, named so that entailer does not meet [gv] applied to them) *)
Lemma det_offer_close (p : val) (s : dstate) (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z)
    (msgv : val) (adler : Z) (gv : globals) (za zf : val) :
  za = gv DC._zcalloc -> zf = gv DC._zcfree ->
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  @data_at Zlib.units.Compress.CS Ews t_zs
    (zs_val nin (vi ain) (vl tin) nout (vi aout) (vl tout) msgv sp za zf nullval
       (det_dt s) (vl adler) Vundef) p *
  (strm_own_live p sp gv s -* dstream_sp 2 (Some s) p nullval sp gv) * data_at_ BoundKit.Ecomp t_strm p
  |-- strm_at p s sp nin ain tin nout aout tout msgv adler gv.
Proof. exact (DetPreOffer2.det_offer_close p s sp nin ain tin nout aout tout msgv adler gv za zf). Qed.

(* malloc's new object of [room] bytes is an output space with nothing written *)
Lemma det_out0 (room : Z) (q : val) :
  0 <= room -> data_at_ Ews (tarray tuchar room) q = data_at Ews (tarray tuchar room) (out_vals room []) q.
Proof. exact (DetPreOffer2.det_out0 room q). Qed.

(* (tbool) (p == NULL) is 0 for a malloc'd p *)
Ltac det_nonnull := DetPreOffer2.det_nonnull.

(* return 0 after a failed allocation: both streams back to main's locals, everything else dropped *)
Ltac det_ret := DetPreOffer2.det_ret.

Lemma det_pre : det_pre_stmt.
Proof.
  intros Espec J n data datap v1 v2 sp1 sp2 gv ls HC.
  unfold J_at, J_ok, J_loc, J_sep, setup_ok. Intros.
  unfold lbody, Rbody, loop1_ret_assert, POST_m, overridePost, frame_ret_assert. cbv beta iota.
  abbreviate_semax.
  forward_if (EX off : Z, EX fl : Z,
    PROP (ls_read ls <= off <= n; 0 <= fl <= 5; fl = 4 -> off = n /\ n - ls_read ls <= 4294967295;
          ls_fin ls <> None -> fl = 4)
    LOCAL (temp _data datap; temp _data_len (vl n); temp _offered (vl off); temp _read (vl (ls_read ls));
           temp _flush (vi fl); lvar _first t_strm v1; lvar _second t_strm v2; gvars gv)
    SEP (mem_mgr gv; deflate_globals gv; data_at Ews (tarray tuchar n) (map vi data) datap;
         shead v1 (ls_s ls) sp1 (ls_read ls) (ls_tout ls) (ls_msgv1 ls) (ls_adler ls) gv;
         shead v2 (ls_s ls) sp2 (ls_read ls) (ls_tout ls) (ls_msgv2 ls) (ls_adler ls) gv; TT)).
  { forward_call (n - ls_offered ls).
    Intros v.
    forward.
    rewrite <- seq_assoc. forward_call 5.
    Intros f.
    forward.
    rewrite Int64.unsigned_repr by rep_lia.
    assert (EF : ls_fin ls = None) by (destruct (ls_fin ls); [destruct H8; contradiction | reflexivity]).
    destruct (Z.eq_dec f 4) as [Ef|Ef].
    { (* Z_FINISH: kept only when the rest of the data fits in one call *)
      subst f. destruct (Z_lt_dec 4294967295 (n - ls_read ls)) as [Hb|Hb].
      { forward_if (temp _t'14 (vi 1)); [ | det_false | ].
        { forward. entailer!. simpl. unfold Int64.sub, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
          rewrite if_true by (simpl; lia). reflexivity. }
        forward_if (temp _flush (vi 0)); [ | det_false | ]. { forward. entailer!. }
        forward_if; [ det_false | ]. forward.
        Exists (ls_offered ls + v) 0. entailer!. }
      { forward_if (temp _t'14 (vi 0)); [ | det_false | ].
        { forward. entailer!. simpl. unfold Int64.sub, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
          rewrite if_false by (simpl; lia). reflexivity. }
        forward_if (temp _flush (vi 4)); [ det_false | | ]. { forward. entailer!. }
        forward_if; [ | det_false ]. forward.
        Exists n 4. entailer!. } }
    { forward_if (temp _t'14 (vi 0)); [ det_false | | ].
      { forward. entailer!. }
      forward_if (temp _flush (vi f)); [ det_false | | ]. { forward. entailer!. }
      forward_if; [ det_false | ]. forward.
      Exists (ls_offered ls + v) f. entailer!. } }
  { forward. Exists (ls_offered ls) (ls_flush ls). entailer!.
    destruct (ls_fin ls); [tauto | contradiction]. }
  Intros off fl.
  (* take = clip(offered - read) *)
  rewrite <- seq_assoc. forward_call (off - ls_read ls).
  forward.
  set (tk := Z.min (off - ls_read ls) Int.max_unsigned).
  assert (Htk0 : 0 <= tk <= 4294967295) by (unfold tk; rep_lia).
  rewrite Int.unsigned_repr by rep_lia.
  (* room = nondet_u32(), widened to size_t *)
  rewrite <- !seq_assoc. forward_call tt.
  Intros room.
  forward.
  rewrite Int.unsigned_repr by rep_lia.
  assert (Hcb : cbuf_ok false (offset_val (ls_read ls) datap) Ews datap (ls_read ls) n tk (map vi data)
                  (sublist (ls_read ls) (ls_read ls + tk) data)).
  { pose proof (det_copy_cbuf data datap n (ls_read ls) (ls_read ls + tk) H1 H2 ltac:(lia) ltac:(unfold tk in *; lia))
      as Hc.
    rewrite Z.add_simpl_l in Hc. exact Hc. }
  forward_call (offset_val (ls_read ls) datap, Ews, datap, ls_read ls, n, map vi data, tk,
                sublist (ls_read ls) (ls_read ls + tk) data, gv).
  { det_copy_args. }
  { rewrite det_bytes_cs. cancel. }
  Intros in1. rewrite !det_bytes_cs, !det_token_cs.
  forward_call (offset_val (ls_read ls) datap, Ews, datap, ls_read ls, n, map vi data, tk,
                sublist (ls_read ls) (ls_read ls + tk) data, gv).
  { det_copy_args. }
  { rewrite det_bytes_cs. cancel. }
  Intros in2. rewrite !det_bytes_cs, !det_token_cs.
  forward_call (tarray tuchar room, gv).
  { simpl; rep_lia. }
  Intros out1.
  forward_call (tarray tuchar room, gv).
  { simpl; rep_lia. }
  Intros out2.
  (* the NULL test and the offers *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  eapply semax_pre; [| apply (det_pre_tail J n data datap v1 v2 sp1 sp2 gv ls off fl room in1 in2 out1 out2 HC) ].
  unfold M_at. change (Z.min (off - ls_read ls) 4294967295) with tk.
  entailer!. unfold J_ok, setup_ok. tauto.
Qed.

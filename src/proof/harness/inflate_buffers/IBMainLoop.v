(* Law inflate_buffers, main: one iteration of the loop (the body after its leading Sskip): the nondet draws, the
   assumes, exact_copy / exact_space and the NULL test, nin/nout and the stores into s, tin/tout, reset = 0, then
   the dispatch and the checks, given by their statements ops_stmt (IBMainOps.seg_ops_ok) and checks_stmt
   (IBMainChecks.seg_checks_ok), hypotheses here (proved in IBMainOps.v and IBMainChecks.v, supplied in IBMain.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_buffers.IBLawCS Zlib.proof.harness.inflate_buffers.IBGlobals
               Zlib.proof.harness.inflate_buffers.IBFacts Zlib.proof.harness.inflate_buffers.IBMainKit.
Require Import Zlib.harness.x_inflate_buffers.code.
Require Import Zlib.proof.crc32.Spec.

(* the statement of IBMainOps.seg_ops_ok *)
Definition ops_stmt {Espec: OracleKind} : Prop :=
  forall gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr (Post: ret_assert),
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L ->
  semax Delta_m (ops_pre gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr)
    seg_ops
    (overridePost (ops_post gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr) Post).

(* the statement of IBMainChecks.seg_checks_ok *)
Definition checks_stmt {Espec: OracleKind} : Prop :=
  forall gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs z L Fr r reset z' L' obl snl,
  ops_hyps srcp src pos aout flush arg op innull outnull stop ain ibp obp q bs L -> zf_ok z ->
  semax Delta_m
    (ops_post_at gv vs vosn vdl srcp src pos aout flush arg op innull outnull stop ain ibp obp q z Fr
       r reset z' L' obl snl)
    seg_checks
    (loop_nocontinue_ret_assert (ib_loop_inv gv vs vosn vdl srcp src Fr)
       (overridePost (ib_loop_inv gv vs vosn vdl srcp src Fr) POST_m)).

(* a slice of a whole byte object as exact_copy takes it (adler32/Ptr.v cbuf_ok_slice) *)
Lemma ibl_cbuf_slice sh p data lo len:
  readable_share sh -> isptr p -> is_bytes data -> 0 <= lo -> 0 <= len -> lo + len <= Zlength data ->
  cbuf_ok false (offset_val lo p) sh p lo (Zlength data) len (bytes_rep data) (sublist lo (lo + len) data).
Proof.
  intros. unfold cbuf_ok. split; auto. split; auto. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist; lia | ]. split; [apply is_bytes_sublist; auto | ].
  apply sublist_bytes_rep.
Qed.

(* the stream (live) gives back the local variable's memory *)
Lemma ibl_istream_to_undef gv vs z L:
  istream gv Tsh vs z (Some L) |-- @data_at_ CS Tsh (Tstruct _z_stream_s noattr) vs * TT.
Proof. rewrite ib_istream_unfold. Intros. sep_apply (@data_at_data_at_ CS). cancel. Qed.

Ltac ifpost' t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint v) :: Q) (SEPx R))) end.
Ltac ifpostv t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.
Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Lemma seg_loop_ok {Espec: OracleKind} gv vs vosn vdl srcp src Fr pos z L :
  ops_stmt -> checks_stmt ->
  ib_facts -> Zlength src <= 2 ^ 24 -> is_bytes src -> isptr srcp -> ib_inv L -> 0 <= pos <= Zlength src ->
  semax Delta_m
    (PROP ()
     LOCAL (temp _n (Vint (Int.repr (Zlength src))); temp _src srcp; temp _pos (Vint (Int.repr pos));
            lvar _dl tuint vdl; lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs; gvars gv)
     SEP (istream gv Tsh vs z (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
          malloc_token Ews (tarray tuchar (Zlength src)) srcp;
          data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
          data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn; Fr))
    seg_loop
    (loop_nocontinue_ret_assert (ib_loop_inv gv vs vosn vdl srcp src Fr)
       (overridePost (ib_loop_inv gv vs vosn vdl srcp src Fr) POST_m)).
Proof.
  intros OPS CHK FI Hn Hsb Psrc HI Hpos.
  unfold seg_loop, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  forward_call tt. Intros arg.
  forward_call tt. Intros op.
  forward_call tt. Intros innull.
  forward_call tt. Intros outnull.
  forward_call tt. Intros stop.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  forward_if (PROP () LOCAL (temp _t'17 (Vint (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0))); temp _stop (Vint (Int.repr stop));
   temp _out_null (Vint (Int.repr outnull));
   temp _in_null (Vint (Int.repr innull)); temp _op (Vint (Int.repr op));
   temp _arg (Vint (Int.repr arg)); temp _flush (Vint (Int.repr flush));
   temp _aout (Vint (Int.repr aout)); temp _nlim (Vint (Int.repr nlim));
   temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
   temp _pos (Vint (Int.repr pos)); lvar _dl tuint vdl;
   lvar _osnap (tptr tuchar) vosn; lvar _s (Tstruct _z_stream_s noattr) vs;
   gvars gv)
   SEP (istream gv Tsh vs z (Some L); mem_mgr gv; 
   zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
   malloc_token Ews (tarray tuchar (Zlength src)) srcp;
   data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
   data_at_ Tsh tuint vdl; data_at_ Tsh (tptr tuchar) vosn; Fr)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  forward.
  rewrite sub_repr. set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= Zlength src) by (subst ain; lia). clearbody ain.
  forward_call (offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, ain,
                sublist pos (pos + ain) src, gv).
  { rewrite bytes_adler_cs. cancel. }
  { apply ibl_cbuf_slice; auto; lia. }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite ptr_adler_cs.
  match goal with Hb: Zlength bs = aout |- _ => rename Hb into Hbs end. subst aout.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpost' _t'20 (Int.repr 1). { forward. entailer!. } { infeas. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ibl_istream_to_undef. entailer!. }
    { infeas. } }
  Intros.
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpost' _t'20 (Int.repr 1).
    { apply (@malloc_test_eq Zlib.units.Adler32.CS _ ain); [lia | sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar ain)); cancel]. }
    { infeas. }
    { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ibl_istream_to_undef. entailer!. }
    { infeas. } }
  Intros.
  rewrite (bytes_adler_cs Ews ain _ ibp), (tok_adler_cs Ews ain ibp), (bytes_adler_cs Ews (Zlength bs) _ obp),
    (tok_adler_cs Ews (Zlength bs) obp), (bytes_adler_cs Ews (Zlength bs) _ q), (tok_adler_cs Ews (Zlength bs) q).
  assert_PROP (isptr obp /\ isptr ibp) as Pob by entailer!. destruct Pob as [Pob Pib].
  ifpost' _t'20 (Int.repr 0).
  { infeas. }
  { forward. entailer!. destruct obp; try contradiction; reflexivity. }
  forward_if.
  { infeas. }
  assert_PROP (isptr q) as Pq by entailer!.
  ifpost' _t'21 (Int.repr (if ib_nin op innull then 1 else 0)).
  { forward. entailer!.
    unfold ib_nin; destruct (Z.ltb_spec op 200); try lia; destruct (zeq innull 0), (Z.eqb_spec innull 0); try lia; reflexivity. }
  { forward. entailer!. rewrite ib_nin_ge by lia; reflexivity. }
  forward.
  ifpost' _t'22 (Int.repr (if ib_nout op outnull then 1 else 0)).
  { forward. entailer!.
    unfold ib_nout; destruct (Z.ltb_spec op 200); try lia; destruct (zeq outnull 0), (Z.eqb_spec outnull 0); try lia; reflexivity. }
  { forward. entailer!. rewrite ib_nout_ge by lia; reflexivity. }
  forward.
  rewrite ib_istream_unfold. Intros.
  ifpostv _t'23 (if ib_nin op innull then nullval else ibp).
  { forward. entailer!. destruct (ib_nin op innull); [reflexivity | contradiction]. }
  { forward. entailer!. destruct (ib_nin op innull); [discriminate | reflexivity]. }
  forward.
  forward.
  ifpostv _t'24 (if ib_nout op outnull then nullval else obp).
  { forward. entailer!. destruct (ib_nout op outnull); [reflexivity | contradiction]. }
  { forward. entailer!. destruct (ib_nout op outnull); [discriminate | reflexivity]. }
  forward.
  forward.
  forward.
  forward.
  forward.
  change (let (x, _) := snd (snd (snd (snd (snd (ib_tup gv z (l_sp L)))))) in x) with (Vlong (Int64.repr (zf_tout z))).
  change (fst (snd (snd (ib_tup gv z (l_sp L))))) with (Vlong (Int64.repr (zf_tin z))).
  set (zc := ib_zcall z (ib_nin op innull) (ib_nout op outnull) ibp obp ain (Zlength bs)).
  match goal with |- context [@data_at CS Tsh (Tstruct _z_stream_s noattr) ?v vs] =>
    replace v with (ib_tup gv zc (l_sp L)) by (unfold zc, ib_tup, ib_zcall; reflexivity) end.
  assert (Zc: zf_ok zc).
  { destruct H10 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6). unfold zc, ib_zcall, zf_ok; simpl.
    split; [rep_lia | ]. split; [rep_lia | ]. auto. }
  sep_apply (ib_istream_fold gv Tsh vs zc L); auto.
  assert (OH: ops_hyps srcp src pos (Zlength bs) flush arg op innull outnull stop ain ibp obp q bs L).
  { unfold ops_hyps. split; [exact FI | ]. split; [exact HI | ].
    repeat split; auto; try lia; try rep_lia. }
  match goal with |- semax _ _ (Ssequence ?c _) _ => change c with seg_ops end.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_seq.
  { eapply semax_pre; [ | apply (OPS gv vs vosn vdl srcp src pos (Zlength bs) flush arg op innull outnull stop ain
                                   ibp obp q bs z L Fr); exact OH].
    unfold ops_pre, ops_locals. fold zc. entailer!. }
  unfold ops_post. Intros r reset z' L' obl snl.
  match goal with |- semax _ _ ?c _ => change c with seg_checks end.
  apply (CHK gv vs vosn vdl srcp src pos (Zlength bs) flush arg op innull outnull stop ain ibp obp q bs z L Fr
           r reset z' L' obl snl OH H10).
Qed.

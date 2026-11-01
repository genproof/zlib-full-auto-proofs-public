(* Law inflate_check, main: the loop body up to the null check of ib / ob (IKMainKit.v): the nondet draws of
   nlim, aout, flush, stop, the two gp_assume, ain = nlim - pos, ib = exact_copy(src + pos, ain),
   ob = exact_space(aout, &osnap), `if (ib == NULL || ob == NULL) return 0;`; then seg_L1 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib Zlib.proof.harness.inflate_common.HarnessLe32.
Require Import Zlib.proof.harness.inflate_check.IKLawCS Zlib.proof.harness.inflate_check.IKGlobals
               Zlib.proof.harness.inflate_check.IKFacts.
Require Import Zlib.harness.x_inflate_check.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_check.IKMainKit.
Require Import Zlib.proof.adler32.Ptr.
Local Open Scope logic.

Ltac pre_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Lemma pre_ok {Espec: OracleKind} I gv vs vosn w srcp src adler0 Fr (Inv: environ -> mpred) pos out z L :
  ik_glob I w srcp src adler0 -> I w src pos out z L -> 0 <= pos <= Zlength src -> bytes_ok out ->
  (w < 0 -> zf_adler z = adler0) ->
  (forall ain aout flush stop ibp obp q bs,
     ik_buf_facts I w srcp src adler0 pos out z L ain aout flush stop ibp obp q bs ->
     semax Delta_m (ik_buf gv vs vosn w srcp src adler0 Fr pos out z L ain aout flush stop ibp obp q bs)
       seg_L1 (ik_PL Inv)) ->
  semax Delta_m (ik_at gv vs vosn w srcp src adler0 Fr pos out z L) seg_loop (ik_PL Inv).
Proof.
  intros G HI Hpos Hout Hraw K.
  pose proof G as G'. destruct G' as (CF & Wok & Hw & Hn & Hsb & Psrc & Had).
  unfold ik_at, seg_loop, Delta_m, Gmain_k, ik_PL, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros nlim.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  forward_call tt. Intros stop.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  ifpost _t'13 (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (pos <=? nlim) (nlim <=? Zlength src) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!. arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  rewrite sub_repr. set (ain := nlim - pos).
  assert (Hain: 0 <= ain /\ pos + ain <= Zlength src) by (subst ain; lia). clearbody ain.
  forward_call (offset_val pos srcp, Ews, srcp, pos, Zlength src, bytes_rep src, ain,
                sublist pos (pos + ain) src, gv).
  { rewrite ik_bytes_adler_cs. cancel. }
  { apply cbuf_ok_slice; auto; lia. }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite ik_ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite ik_ptr_adler_cs.
  match goal with Hb: Zlength bs = aout |- _ => rename Hb into Hbs end. subst aout.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpost _t'16 (Int.repr 1). { forward. entailer!. } { pre_infeas. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ik_istream_to_undef. entailer!. }
    { pre_infeas. } }
  Intros.
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpost _t'16 (Int.repr 1).
    { apply (@malloc_test_eq Zlib.units.Adler32.CS _ ain); [lia | sep_apply (@data_at_data_at_ Zlib.units.Adler32.CS Ews (tarray tuchar ain)); cancel]. }
    { pre_infeas. }
    { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply ik_istream_to_undef. entailer!. }
    { pre_infeas. } }
  Intros.
  rewrite (ik_bytes_adler_cs Ews ain _ ibp), (ik_tok_adler_cs Ews ain ibp), (ik_bytes_adler_cs Ews (Zlength bs) _ obp),
    (ik_tok_adler_cs Ews (Zlength bs) obp), (ik_bytes_adler_cs Ews (Zlength bs) _ q), (ik_tok_adler_cs Ews (Zlength bs) q).
  assert_PROP (isptr obp /\ isptr ibp /\ isptr q) as Pob by entailer!. destruct Pob as (Pob & Pib & Pq).
  ifpost _t'16 (Int.repr 0).
  { pre_infeas. }
  { forward. entailer!. destruct obp; try contradiction; reflexivity. }
  forward_if.
  { pre_infeas. }
  assert (BF: ik_buf_facts I w srcp src adler0 pos out z L ain (Zlength bs) flush stop ibp obp q bs).
  { unfold ik_buf_facts. split; [exact G | ]. split; [exact HI | ]. repeat split; auto; try exact H4; rep_lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K ain (Zlength bs) flush stop ibp obp q bs BF)].
  unfold ik_buf. entailer!.
Qed.

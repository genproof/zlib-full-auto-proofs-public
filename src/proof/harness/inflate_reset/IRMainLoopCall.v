(* Law inflate_reset, main, the loop body from `a.next_in = ia;` (IRMainLoopKit.seg_call): the four stores, a's
   inflate() call, `if (ra == Z_MEM_ERROR) return 0;`, `if (phase == 2) {...}` (IRMainKit.ph2_stmt; in phase 1
   IRFacts.rf_inflate1), then the tail (IRMainLoopKit.tail_stmt). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_reset.IRLawCS Zlib.proof.harness.inflate_reset.IRGlobals
               Zlib.proof.harness.inflate_reset.IRFacts Zlib.proof.harness.inflate_reset.IRMainKit
               Zlib.proof.harness.inflate_reset.IRMainLoopKit.
Require Import Zlib.harness.x_inflate_reset.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Definition call_pre (gv: globals) (va vb vsa vsb: val) (w: Z) (srcp: val) (src: list Z) (rb: rawf)
    (ph pos w2 aout flush wsel stop how ain: Z) (iap ibp oap obp qa qb: val) (bsa bsb: list Z)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _wbits (Vint (Int.repr w)); temp _n (Vint (Int.repr (Zlength src))); temp _src srcp;
         temp _phase (Vint (Int.repr ph)); temp _w2 (Vint (Int.repr w2)); temp _pos (Vint (Int.repr pos));
         temp _aout (Vint (Int.repr aout)); temp _flush (Vint (Int.repr flush));
         temp _wsel (Vint (Int.repr wsel)); temp _stop (Vint (Int.repr stop)); temp _how (Vint (Int.repr how));
         temp _ain (Vint (Int.repr ain)); temp _ia iap; temp _ib ibp; temp _oa oap; temp _ob obp;
         lvar _sb (tptr tuchar) vsb; lvar _sa (tptr tuchar) vsa; lvar _b t_z vb; lvar _a t_z va; gvars gv)
  SEP (istream gv Tsh va za (Some La); bmem gv vb ph rb zb Lb; mem_mgr gv; zfuncs gv; tables_rep Ers gv;
       crc_table_at Ers gv; version_lit gv; ir_hversion_lit gv; ir_msg_lits gv;
       malloc_token Ews (tarray tuchar (Zlength src)) srcp;
       data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) iap;
       malloc_token Ews (tarray tuchar ain) iap;
       data_at Ews (tarray tuchar ain) (bytes_rep (sublist pos (pos + ain) src)) ibp;
       malloc_token Ews (tarray tuchar ain) ibp;
       data_at Ews (tarray tuchar aout) (bytes_rep bsa) oap; malloc_token Ews (tarray tuchar aout) oap;
       data_at Ews (tarray tuchar aout) (bytes_rep bsb) obp; malloc_token Ews (tarray tuchar aout) obp;
       data_at Tsh (tptr tuchar) qa vsa; data_at Tsh (tptr tuchar) qb vsb;
       data_at Ews (tarray tuchar aout) (bytes_rep bsa) qa; malloc_token Ews (tarray tuchar aout) qa;
       data_at Ews (tarray tuchar aout) (bytes_rep bsb) qb; malloc_token Ews (tarray tuchar aout) qb).

Definition call_facts (I1: I1T) (I2: I2T) (w: Z) (srcp: val) (src: list Z) (rb: rawf) (va vb: val)
    (ph pos w2 aout flush wsel stop how ain: Z) (iap ibp oap obp qa qb: val) (bsa bsb: list Z)
    (za: zfields) (La: live) (zb: zfields) (Lb: live) : Prop :=
  g_facts I1 I2 w srcp src rb /\ ph_inv I1 I2 w src ph pos w2 za La zb Lb /\
  0 <= pos /\ 0 <= ain /\ pos + ain <= Zlength src /\ 0 <= aout <= 2 ^ 20 /\
  Int.min_signed <= w2 <= Int.max_signed /\ Int.min_signed <= flush <= Int.max_signed /\
  Int.min_signed <= wsel <= Int.max_signed /\ 0 <= stop <= 255 /\ 0 <= how <= 255 /\
  Zlength bsa = aout /\ is_bytes bsa /\ Zlength bsb = aout /\ is_bytes bsb /\
  isptr va /\ isptr vb /\ isptr iap /\ isptr ibp /\ isptr oap /\ isptr obp /\ isptr qa /\ isptr qb.

Lemma bmem_to_undef gv vb ph rb zb Lb: bmem gv vb ph rb zb Lb |-- data_at_ Tsh t_z vb * TT.
Proof.
  unfold bmem, braw, raw_strm. destruct (ph =? 1).
  - sep_apply strm_to_undef. cancel.
  - apply istream_to_undef.
Qed.

Lemma cmp_nonnull p: isptr p ->
  force_val (sem_cast_i2bool (force_val (sem_cmp_pp Ceq p (Vlong (Int64.repr 0))))) = Vint (Int.repr 0).
Proof. destruct p; try contradiction; reflexivity. Qed.

Lemma rel_some flush strmp z L ib inp ob r z' st' ow:
  inflate_rel flush strmp z (Some L) ib inp ob r z' st' ow -> exists L', st' = Some L'.
Proof.
  intros [(_ & _ & _ & E & _) | (_ & L0 & o & res & winp & _ & _ & _ & _ & _ & _ & _ & _ & E)]; eauto.
Qed.

Ltac infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                              | match goal with H: _ |- _ => solve [discriminate H] end
                              | contradiction
                              | lia ].

Ltac fcp p := entailer!; match goal with H: field_compatible _ _ p |- _ => exact (field_compatible_isptr _ _ _ H) end.

Ltac cmpz := entailer!; try (rewrite cmp_nonnull by assumption; reflexivity).

Ltac ret0m := forward; Exists (Int.repr 0); sep_apply istream_to_undef; sep_apply bmem_to_undef; entailer!;
  repeat (sep_apply data_at_data_at_); cancel.

Lemma call_of {Espec: OracleKind} I1 I2 gv va vb vsa vsb w srcp src rb ph pos w2 aout flush wsel stop how ain
    iap ibp oap obp qa qb bsa bsb za La zb Lb :
  ph2_stmt -> tail_stmt ->
  call_facts I1 I2 w srcp src rb va vb ph pos w2 aout flush wsel stop how ain iap ibp oap obp qa qb bsa bsb
    za La zb Lb ->
  semax Delta_m
    (call_pre gv va vb vsa vsb w srcp src rb ph pos w2 aout flush wsel stop how ain iap ibp oap obp qa qb
       bsa bsb za La zb Lb)
    seg_call
    (loop_post I1 I2 gv va vb vsa vsb w srcp src rb).
Proof.
  intros PH2 TAIL CF.
  pose proof CF as CF0.
  destruct CF as (GF & HPI & Hpos & Hain & Hpa & Haout & Hw2 & Hfl & Hws & Hst & Hhow & Hbsa & Hbya & Hbsb & Hbyb
                  & Pva & Pvb & Piap & Pibp & Poap & Pobp & Pqa & Pqb).
  pose proof GF as GF0.
  destruct GF as (RF & Wok & Hw & Hn & Hsb & Psrc & Hrb).
  unfold call_pre, seg_call, loop_post, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  rewrite ir_istream_unfold. Intros.
  forward. forward. forward. forward.
  rewrite <- ir_tup_call.
  set (sub := sublist pos (pos + ain) src) in *.
  assert (Hsub: Zlength sub = ain) by (unfold sub; rewrite Zlength_sublist; lia).
  assert (Hsubb: bytes_ok sub) by (apply Forall_sublist; exact Hsb).
  set (z1 := ir_call za iap ain oap aout).
  assert (Z1ok: zf_ok z1).
  { unfold zf_ok in H |- *. unfold z1, ir_call; simpl. rep_lia. }
  sep_apply (ir_istream_fold gv Tsh va z1 La); auto.
  sep_apply (ir_bufs_pre La iap oap ain aout (bytes_rep sub) (bytes_rep bsa)).
  { rewrite Zlength_bytes_rep; auto. }
  assert (Hhd: i_head (l_s La) = false).
  { unfold ph_inv in HPI. destruct (ph =? 1).
    - destruct HPI as [_ HI]. exact (rf_head1 _ _ RF _ _ _ _ _ HI).
    - destruct HPI as [_ HI]. exact (proj1 (rf_head2 _ _ RF _ _ _ _ _ _ _ HI)). }
  forward_call (gv, Tsh, va, z1, Some La, ir_ib iap ain (bytes_rep sub), sub,
                Some (ir_ob oap aout (bytes_rep bsa)), flush, Ers, Ers, true, true).
  { rewrite ir_istream_opt, ir_is_live by auto. simpl head_opt. unfold head_mem; rewrite Hhd. cancel. }
  { unfold z1, ir_call, ir_ib, ir_ob; simpl.
    rewrite !isptr_offset_val_zero by auto. rewrite ?Zlength_bytes_rep.
    repeat match goal with |- _ /\ _ => split end; auto with share; try rep_lia; rewrite ?Zlength_bytes_rep;
      try rep_lia; try (rewrite Z.add_0_l, sublist_same by (rewrite ?Zlength_bytes_rep; lia); reflexivity). }
  Intros vret. destruct vret as [[[ra za'] st'] owa]. cbn [fst snd] in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hrel end.
  destruct (rel_some _ _ _ _ _ _ _ _ _ _ _ Hrel) as [La' ->].
  rewrite ir_istream_opt, !ir_is_live by auto.
  sep_apply (ir_bufs_post La iap oap ain aout (bytes_rep sub) (bytes_rep bsa) owa).
  forward_if.
  { ret0m. }
  assert (Hra: ra <> Z_MEM_ERROR) by (intro E; apply H2; rewrite E; reflexivity).
  assert (Hrel': inflate_rel flush va
    (ir_call za (in_ptr (ir_ib iap ain (bytes_rep sub)) 0) ain (out_ptr (ir_ob oap aout (bytes_rep bsa)) 0) aout)
    (Some La) (ir_ib iap ain (bytes_rep sub)) sub (Some (ir_ob oap aout (bytes_rep bsa))) ra za' (Some La') owa).
  { rewrite ir_in_ptr, ir_out_ptr by auto. exact Hrel. }
  clear Hrel H2.
  unfold ph_inv in HPI. destruct (Z.eqb_spec ph 1) as [-> | Hph1].
  - (* phase 1 *)
    destruct HPI as [-> HI].
    destruct (rf_inflate1 _ _ RF w src pos za La va flush (ir_ib iap ain (bytes_rep sub)) sub
                (ir_ob oap aout (bytes_rep bsa)) ain aout ra za' (Some La') owa HI H1 H
                ltac:(destruct va; try contradiction; discriminate) Hpos Hain Hpa Hn Hsb Haout Hfl
                ltac:(discriminate) eq_refl Hrel' Hra) as (L' & EL & Hai & Hao & HI').
    injection EL as <-.
    assert (Hhd': i_head (l_s La') = false) by exact (rf_head1 _ _ RF _ _ _ _ _ HI').
    simpl head_opt. unfold head_mem at 1. rewrite Hhd'.
    forward_if (tail_pre gv va vb vsa vsb w srcp src rb 1 pos w aout wsel stop how ain iap ibp oap obp qa qb
                  (bytes_rep sub) (bytes_rep sub) (out_after (bytes_rep bsa) owa aout) (bytes_rep bsb)
                  (bytes_rep bsa) (bytes_rep bsb) za' La' zb Lb).
    { infeas. }
    { forward. unfold tail_pre. entailer!. }
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION, Delta. subst MORE_COMMANDS POSTCONDITION Delta.
    apply TAIL. unfold tail_facts, ph_inv. rewrite Z.eqb_refl.
    repeat match goal with |- _ /\ _ => split end; auto; lia.
  - (* phase 2 *)
    destruct HPI as [-> HI2].
    replace (bmem gv vb 2 rb zb Lb) with (istream gv Tsh vb zb (Some Lb)) by reflexivity.
    rewrite (ir_istream_unfold gv Tsh vb zb Lb). Intros.
    sep_apply (ir_istream_fold gv Tsh vb zb Lb); auto.
    assert (PF: ph2_facts I1 I2 w srcp src rb va vb w2 pos aout flush stop how wsel ain iap ibp oap obp bsa bsb
                  za La zb Lb ra za' La' owa).
    { unfold ph2_facts. repeat match goal with |- _ /\ _ => split end; auto; lia. }
    set (Fr := version_lit gv * ir_hversion_lit gv * malloc_token Ews (tarray tuchar (Zlength src)) srcp *
               data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) srcp *
               data_at Ews (tarray tuchar aout) (bytes_rep bsa) qa * malloc_token Ews (tarray tuchar aout) qa *
               data_at Ews (tarray tuchar aout) (bytes_rep bsb) qb * malloc_token Ews (tarray tuchar aout) qb).
    forward_if (ph2_post I2 gv va vb vsa vsb w srcp src w2 pos aout flush stop how wsel ain iap ibp oap obp qa qb
                  za' La' Fr).
    { unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
      eapply semax_pre; [ | eapply semax_post; [ | | | |
        apply (PH2 _ I1 I2 gv va vb vsa vsb w srcp src rb w2 pos aout flush stop how wsel ain iap ibp oap obp qa qb
                 bsa bsb za La zb Lb ra za' La' owa Fr PF)]].
      { unfold ph2_pre, Fr. simpl head_opt. entailer!. }
      { apply andp_left2; apply derives_refl. }
      { simpl RA_break. apply andp_left2. unfold POST_m. simpl RA_break. intro rho. normalize. }
      { simpl RA_continue. apply andp_left2. unfold POST_m. simpl RA_continue. intro rho; normalize. }
      { intros; apply andp_left2; apply derives_refl. } }
    { infeas. }
    unfold ph2_post. Intros zb' Lb' ca cb.
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (TAIL _ I1 I2 gv va vb vsa vsb w srcp src rb 2 pos w2 aout wsel stop how ain
                                   iap ibp oap obp qa qb (bytes_rep sub) (bytes_rep sub) ca cb (bytes_rep bsa)
                                   (bytes_rep bsb) za' La' zb' Lb') ].
    { unfold tail_pre, Fr. replace (bmem gv vb 2 rb zb' Lb') with (istream gv Tsh vb zb' (Some Lb')) by reflexivity.
      entailer!. }
    unfold tail_facts, ph_inv. simpl (2 =? 1). cbv iota.
    repeat match goal with |- _ /\ _ => split end; auto; lia.
Qed.
